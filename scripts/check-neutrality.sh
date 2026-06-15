#!/usr/bin/env bash
# Two neutrality guards (SPEC §4) — keep the layer boundaries honest in CI.
#  1. the agdelte framework (src/, hs/) must be domain-agnostic;
#  2. services-core/ must not name any specific vertical.
set -uo pipefail
cd "$(dirname "$0")/.."

fail=0

# Guard 1: no domain vocabulary in the agdelte layer.
if grep -rIEn --include='*.agda' --include='*.hs' \
     -e '\b(party|engagement)\b' -e 'услуг' src hs 2>/dev/null; then
  echo "✗ neutrality: domain words leaked into the agdelte layer (src/, hs/)"
  fail=1
fi

# Guard 2: no vertical names in neutral services-core.
if [ -d services-core ] && grep -rIEn --include='*.agda' --include='*.hs' \
     -e '\b(psych|vet|transfer)\b' -e 'медцентр' services-core 2>/dev/null; then
  echo "✗ neutrality: vertical names leaked into services-core/"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "✓ neutrality guards: OK"
fi
exit "$fail"
