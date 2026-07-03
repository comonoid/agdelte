#!/usr/bin/env bash
# Neutrality guard: the agdelte framework (src/, hs/) must be domain-agnostic.
#  - The neutral CXM domain core has its OWN guard in ~/cxm-core/cxm/scripts/check-neutrality.sh
#    (recomposition 2026-07-03: CXM moved to its own repo).
#  - agdelte-crm retired 2026-07-02.
set -uo pipefail
cd "$(dirname "$0")/.."

fail=0

# No domain vocabulary in the agdelte layer.
if grep -rIEn --include='*.agda' --include='*.hs' \
     -e '\b(party|engagement)\b' -e 'услуг' src hs 2>/dev/null; then
  echo "✗ neutrality: domain words leaked into the agdelte layer (src/, hs/)"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "✓ neutrality guard: OK (agdelte framework is domain-agnostic)"
fi
exit "$fail"
