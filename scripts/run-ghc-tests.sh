#!/usr/bin/env bash
# Run every GHC (MAlonzo) test in one shot and aggregate PASS/FAIL.
# Each `npm run test:<x>` regenerates + builds + runs its binary. Exits non-zero
# if any assertion failed, so this is the single "did I break anything" check.
set -uo pipefail
cd "$(dirname "$0")/.."

TESTS=(test:im test:crmwire test:crmstore test:crmcommands test:walrec test:json-ffi test:store-txn test:courses-smoke test:psych-schedule test:rbac)

total_pass=0 total_fail=0
declare -a failed=()
for t in "${TESTS[@]}"; do
  out=$(npm run -s "$t" 2>&1)
  p=$(printf '%s\n' "$out" | grep -c '^PASS')
  f=$(printf '%s\n' "$out" | grep -c '^FAIL')
  total_pass=$((total_pass + p)); total_fail=$((total_fail + f))
  if [ "$f" -gt 0 ] || [ "$p" -eq 0 ]; then
    failed+=("$t")
    printf '  %-20s %s\n' "$t" "${p} PASS ${f} FAIL  <-- problem"
    printf '%s\n' "$out" | grep -E '^FAIL|error:' | head -5
  else
    printf '  %-20s %s\n' "$t" "${p} PASS"
  fi
done

echo "------------------------------------------------------------"
echo "TOTAL: ${total_pass} PASS, ${total_fail} FAIL"
if [ "${#failed[@]}" -eq 0 ]; then
  echo "✓ all GHC tests green"
  exit 0
else
  echo "✗ problems in: ${failed[*]}"
  exit 1
fi
