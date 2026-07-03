#!/usr/bin/env bash
# Two neutrality guards (SPEC §4) — keep the layer boundaries honest.
#  1. the agdelte framework (src/, hs/) must be domain-agnostic;
#  2. the neutral domain core (the agdelte-cxm library) must not name any vertical.
#     (agdelte-crm retired 2026-07-02 → the core is now agdelte-cxm/Cxm.)
set -uo pipefail
cd "$(dirname "$0")/.."

fail=0

# Guard 1: no domain vocabulary in the agdelte layer.
if grep -rIEn --include='*.agda' --include='*.hs' \
     -e '\b(party|engagement)\b' -e 'услуг' src hs 2>/dev/null; then
  echo "✗ neutrality: domain words leaked into the agdelte layer (src/, hs/)"
  fail=1
fi

# Guard 2: no vertical names in the neutral domain core (the agdelte-cxm library).
CXM_DIR="${AGDELTE_CXM_DIR:-$HOME/.agda/agdelte-cxm}"
if [ -d "$CXM_DIR/Cxm" ]; then
  # NB: the CRM-era word `transfer` was DROPPED from this list (2026-07-02): promise-transfer
  # is core economics vocabulary (Concept Ч.2 §3 futures), not a vertical name. The canonical
  # vertical-word list is agdelte-cxm/scripts/check-neutrality.sh — mirrored here.
  if grep -rIEn --include='*.agda' --include='*.hs' \
       -e '\b(psych|veterinar|clown)\b' -e '\bvet\b' -e 'курс|медцентр|психолог|ветклиник|ветеринар' \
       "$CXM_DIR/Cxm" 2>/dev/null; then
    echo "✗ neutrality: vertical names leaked into the CXM core ($CXM_DIR/Cxm)"
    fail=1
  fi
else
  echo "✗ neutrality: CXM core not found at $CXM_DIR/Cxm (set AGDELTE_CXM_DIR) — guard 2 cannot run"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "✓ neutrality guards: OK"
fi
exit "$fail"
