#!/usr/bin/env bash
# Automated integration test for the headless CRM API (Crm.Api / crm-server).
# Asserts the §13 {data}/{error:{code,message}} envelope, HTTP status codes, the
# H1 bearer-token gate, and restart-replay — over real HTTP. Exits non-zero on any
# failed assertion. Prereqs: a built crm-server (cabal build crm-server), curl.
set -uo pipefail
cd "$(dirname "$0")/.."

BIN=$(cabal list-bin crm-server 2>/dev/null)
[ -x "$BIN" ] || { echo "✗ crm-server not built (cabal build crm-server)"; exit 1; }
PORT=8137; BASE="http://127.0.0.1:$PORT"
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

P=0; F=0
ok(){ echo "PASS $1"; P=$((P+1)); }
bad(){ echo "FAIL $1 — $2"; F=$((F+1)); }
has(){ case "$2" in *"$3"*) ok "$1";; *) bad "$1" "expected to contain '$3', got: $2";; esac; }
eq(){ [ "$2" = "$3" ] && ok "$1" || bad "$1" "expected '$3', got '$2'"; }

# req METHOD PATH [DATA] [AUTH] -> sets $body and $code
req(){
  local m=$1 p=$2 d=${3:-} a=${4:-} out
  if [ -n "$a" ]; then
    out=$(curl -s -w $'\n%{http_code}' -H "Authorization: Bearer $a" -X "$m" "$BASE$p" ${d:+-d "$d"})
  else
    out=$(curl -s -w $'\n%{http_code}' -X "$m" "$BASE$p" ${d:+-d "$d"})
  fi
  code=$(printf '%s' "$out" | tail -n1)
  body=$(printf '%s' "$out" | sed '$d')
}
wait_up(){ for _ in $(seq 1 50); do curl -s "$BASE/parties" -o /dev/null 2>&1 && return 0; sleep 0.1; done; return 1; }

start(){
  ( cd "$WORK"; exec env "$@" "$BIN" >"$WORK/srv.log" 2>&1 ) &
  echo $! > "$WORK/pid"
  wait_up || { echo "✗ server did not start"; cat "$WORK/srv.log"; exit 1; }
}
stop(){ kill "$(cat "$WORK/pid")" 2>/dev/null; wait "$(cat "$WORK/pid")" 2>/dev/null || true; }

echo "===== boot 1 (loopback, no token) ====="
start
req POST /accounts '{"balance":1000}'; has "create-account-data" "$body" '"data"'; has "create-account-id1" "$body" '"id":1'; eq "create-account-200" "$code" 200
req POST /charge '{"acc":1,"amt":300}'; has "charge-ok" "$body" '"ok":true'; eq "charge-200" "$code" 200
req POST /charge '{"acc":1,"amt":99999}'; eq "overdraft-402" "$code" 402; has "overdraft-code" "$body" '"code":"insufficient_funds"'
req POST /parties '{"name":"Полунин"}'; has "create-party-id2" "$body" '"id":2'
req POST /accounts '{}'; eq "missing-field-400" "$code" 400; has "missing-field-code" "$body" '"code":"validation"'
req GET /accounts; has "get-balance-700" "$body" '"balance":700'
req GET /parties; has "get-party-cyrillic" "$body" 'Полунин'
req GET /nope; eq "no-route-404" "$code" 404; has "no-route-code" "$body" '"code":"not_found"'
stop

echo "===== boot 2 (restart → replay) ====="
start
req GET /accounts; has "replay-balance-700" "$body" '"balance":700'
req GET /parties; has "replay-party" "$body" 'Полунин'
stop

echo "===== boot 3 (CRM_TOKEN gate, H1) ====="
rm -f "$WORK/crm.wal"
start CRM_TOKEN=s3cret
req GET /parties; eq "no-token-401" "$code" 401; has "no-token-code" "$body" '"code":"unauthorized"'
req GET /parties '' wrong; eq "wrong-token-401" "$code" 401
req GET /parties '' s3cret; eq "right-token-200" "$code" 200; has "right-token-data" "$body" '"data"'
stop

echo "===== boot 4 (full domain flow: client → case → session) ====="
rm -f "$WORK/crm.wal"
start
req POST /parties '{"name":"Иванов"}';                          has "df-party-id1" "$body" '"id":1'
req POST /engagements '{"caseType":1,"stage":1}';               has "df-eng-id2" "$body" '"id":2'; eq "df-eng-200" "$code" 200
req POST /participations '{"eng":2,"party":1,"role":"client"}'; has "df-part-id3" "$body" '"id":3'
req POST /participations '{"eng":99,"party":1}';                eq "df-part-fk-404" "$code" 404; has "df-part-fk-code" "$body" '"code":"not_found"'
req POST /activities '{"eng":2,"startsAt":1700000000}';         has "df-act-id4" "$body" '"id":4'
req POST /activities '{"eng":2,"startsAt":1700000000}';         eq "df-slot-conflict-409" "$code" 409; has "df-slot-code" "$body" '"code":"conflict"'
req POST /activities/by-engagement '{"eng":2}';                 has "df-byeng-id4" "$body" '"id":4'; has "df-byeng-status" "$body" 'scheduled'
req GET /engagements;                                           has "df-get-eng" "$body" '"caseType":1'
req POST /activities/cancel '{"id":4}';                         has "df-cancel-ok" "$body" '"ok":true'
req POST /activities/cancel '{"id":4}';                         eq "df-recancel-409" "$code" 409; has "df-recancel-code" "$body" '"code":"invalid_transition"'
req POST /engagements/delete '{"id":2}';                        has "df-cascade-ok" "$body" '"ok":true'
req POST /participations/by-engagement '{"eng":2}';             eq "df-cascade-empty" "$body" '{"data":[]}'
stop

echo "===== boot 5 (notifications: outbox §6, durable intent → worker drain) ====="
rm -f "$WORK/crm.wal"
start
req POST /notifications '{"to":"polunin@mail.ru","subject":"Сессия завтра","body":"…"}'; has "nf-enqueue-id1" "$body" '"id":1'
req POST /notifications '{"to":"client@mail.ru","subject":"Оплата"}';                    has "nf-enqueue-id2" "$body" '"id":2'
req GET /outbox; has "nf-pending"  "$body" '"status":"pending"'; has "nf-cyrillic" "$body" 'Сессия завтра'
req POST /notifications '{"subject":"no recipient"}'; eq "nf-missing-to-400" "$code" 400
stop
# restart: the queued intents must survive (durable in the WAL)
start
req GET /outbox; has "nf-durable-pending" "$body" '"status":"pending"'
req POST /outbox/drain; has "nf-drain-sent2" "$body" '"sent":2'
req GET /outbox; has "nf-marked-sent" "$body" '"status":"sent"'
req POST /outbox/drain; has "nf-drain-idempotent" "$body" '"sent":0'
stop

echo "===== boot 6 (psych pack: availability = grid − booked, durable booking) ====="
rm -f "$WORK/crm.wal"
start
req POST /psych/availability '{"type":"session"}'; has "ps-avail-slots" "$body" '"start":'
ST=$(printf '%s' "$body" | grep -oE '"start":[0-9]+' | head -1 | grep -oE '[0-9]+')
N1=$(printf "%s" "$body" | grep -oE '"start":' | wc -l)
req POST /psych/book "{\"type\":\"session\",\"start\":$ST,\"name\":\"Полунин\",\"email\":\"p@mail.ru\"}"
has "ps-book-id" "$body" '"id":'; eq "ps-book-200" "$code" 200
req POST /psych/availability '{"type":"session"}'
N2=$(printf "%s" "$body" | grep -oE '"start":' | wc -l)
case "$body" in *"\"start\":$ST,"*) bad "ps-slot-removed" "booked slot $ST still offered";; *) ok "ps-slot-removed";; esac
[ "$N2" -lt "$N1" ] && ok "ps-avail-decreased" || bad "ps-avail-decreased" "N1=$N1 N2=$N2"
req POST /psych/book "{\"type\":\"session\",\"start\":$ST,\"name\":\"X\",\"email\":\"x\"}"; eq "ps-double-409" "$code" 409
req POST /psych/book "{\"type\":\"session\",\"start\":$((ST+60)),\"name\":\"X\",\"email\":\"x\"}"; eq "ps-offgrid-400" "$code" 400
req POST /psych/book '{"type":"session","name":"X"}'; eq "ps-missing-start-400" "$code" 400
req GET /outbox; has "ps-confirm-enqueued" "$body" 'Подтверждение записи'
req GET /parties;  has "ps-client-created" "$body" 'Полунин'
stop
start   # durability: the booked slot stays occupied after a restart
req POST /psych/availability '{"type":"session"}'
case "$body" in *"\"start\":$ST,"*) bad "ps-durable-occupied" "slot reappeared after restart";; *) ok "ps-durable-occupied";; esac
req GET /activities; has "ps-session-survived" "$body" "\"startsAt\":$ST"
stop

echo "------------------------------------------------------------"
echo "API TOTAL: $P PASS, $F FAIL"
[ "$F" -eq 0 ] && { echo "✓ API integration green"; exit 0; } || { echo "✗ API integration FAILED"; exit 1; }
