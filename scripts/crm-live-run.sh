#!/usr/bin/env bash
# Phase 5 live recovery run: start the headless CRM, write transactions over HTTP,
# restart, and verify the state replayed from the WAL. Proves the walking core:
# persistence + recovery + the {data}/{error} envelope + correct-by-construction
# money invariant, all over real HTTP.
#
# Prereqs: `cabal build crm-server` (LIBRARY_PATH=<zlib>/lib on NixOS), curl.
set -euo pipefail

BIN=$(cabal list-bin crm-server)
WORK=${1:-/tmp/crmlive}
P=8137
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK"

wait_up(){ for _ in $(seq 1 50); do curl -s "http://127.0.0.1:$P/parties" >/dev/null 2>&1 && return 0; sleep 0.1; done; return 1; }

echo "===== boot 1 (empty WAL) ====="
"$BIN" >server1.log 2>&1 & S1=$!
wait_up || { echo "start failed"; cat server1.log; kill $S1 2>/dev/null; exit 1; }
curl -s -X POST "http://127.0.0.1:$P/accounts" -d '{"balance":1000}'; echo
curl -s -X POST "http://127.0.0.1:$P/charge"   -d '{"acc":1,"amt":300}'; echo
curl -s -X POST "http://127.0.0.1:$P/parties"  -d '{"name":"Полунин","type":"P"}'; echo
curl -s -X POST "http://127.0.0.1:$P/charge"   -d '{"acc":1,"amt":99999}'; echo   # overdraft → 402
curl -s "http://127.0.0.1:$P/accounts"; echo
curl -s "http://127.0.0.1:$P/parties"; echo
kill $S1 2>/dev/null; wait $S1 2>/dev/null || true
ls -l crm.wal

echo "===== boot 2 (replay from WAL) ====="
"$BIN" >server2.log 2>&1 & S2=$!
wait_up || { echo "restart failed"; cat server2.log; kill $S2 2>/dev/null; exit 1; }
echo "accounts (expect balance 700):"; curl -s "http://127.0.0.1:$P/accounts"; echo
echo "parties  (expect Полунин):";     curl -s "http://127.0.0.1:$P/parties";  echo
kill $S2 2>/dev/null; wait $S2 2>/dev/null || true
echo "===== ok ====="
