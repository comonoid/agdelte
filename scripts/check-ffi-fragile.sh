#!/usr/bin/env bash
# Verify that all constructor names referenced in FFI-FRAGILE comments
# still exist in Agda sources. Catches silent breakage when constructors
# are renamed but the JS FFI code still uses the old names.
#
# Usage: bash scripts/check-ffi-fragile.sh
# Exit code: 0 if all OK, 1 if any broken reference found.

set -euo pipefail

status=0

while IFS= read -r line; do
  file=$(echo "$line" | cut -d: -f1)
  lineno=$(echo "$line" | cut -d: -f2)
  # Extract everything after "FFI-FRAGILE: "
  raw=$(echo "$line" | sed 's/.*FFI-FRAGILE: //')
  # Split on commas, strip parens and whitespace to get bare constructor names
  ctors=$(echo "$raw" | tr ',' '\n' | sed 's/([^)]*)//g; s/^ *//; s/ *$//')
  for ctor in $ctors; do
    [ -z "$ctor" ] && continue
    # Use -F (fixed string) because constructor names like [], _∷_, -[1+_]
    # contain regex special characters
    if ! grep -rqF --include='*.agda' -- "$ctor" src/; then
      echo "BROKEN FFI: '$ctor' referenced at $file:$lineno not found in sources"
      status=1
    fi
  done
done < <(grep -rn 'FFI-FRAGILE:' src/)

if [ "$status" -eq 0 ]; then
  echo "All FFI-FRAGILE references OK"
fi

exit $status
