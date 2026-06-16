#!/usr/bin/env bash
# Two neutrality guards (SPEC §4) — keep the layer boundaries honest.
#  1. the agdelte framework (src/, hs/) must be domain-agnostic;
#  2. the neutral CRM core (the agdelte-crm library) must not name any vertical.
set -uo pipefail
cd "$(dirname "$0")/.."

fail=0

# Guard 1: no domain vocabulary in the agdelte layer.
if grep -rIEn --include='*.agda' --include='*.hs' \
     -e '\b(party|engagement)\b' -e 'услуг' src hs 2>/dev/null; then
  echo "✗ neutrality: domain words leaked into the agdelte layer (src/, hs/)"
  fail=1
fi

# Guard 2: no vertical names in the neutral CRM core (now the agdelte-crm library).
CRM_DIR="${AGDELTE_CRM_DIR:-$HOME/.agda/agdelte-crm}"
if [ -d "$CRM_DIR/Crm" ]; then
  if grep -rIEn --include='*.agda' --include='*.hs' \
       -e '\b(psych|vet|transfer)\b' -e 'медцентр' "$CRM_DIR/Crm" 2>/dev/null; then
    echo "✗ neutrality: vertical names leaked into the CRM core ($CRM_DIR/Crm)"
    fail=1
  fi
else
  echo "✗ neutrality: CRM core not found at $CRM_DIR/Crm (set AGDELTE_CRM_DIR) — guard 2 cannot run"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "✓ neutrality guards: OK"
fi
exit "$fail"
