#!/bin/bash
# E2E Build Verification Script
# Builds all browser examples and reports any failures

set -e

echo "=== Agdelte Build Verification ==="
echo ""

FAILED=0
PASSED=0

# Auto-discover browser example builds from package.json
# Excludes meta-targets (build:all, build:controls-css, build:test-server) and server builds
SERVER_BUILDS="main|server|multi-agent|shared-demo|inspector-demo"
EXCLUDE="all|controls-css|test-server|${SERVER_BUILDS}"
EXAMPLES=($(node -e "
  const pkg = require('./package.json');
  const exclude = new Set('${EXCLUDE}'.split('|'));
  Object.keys(pkg.scripts)
    .filter(k => k.startsWith('build:') && !exclude.has(k.slice(6)))
    .map(k => k.slice(6))
    .forEach(k => console.log(k));
"))

echo "--- Browser examples (Agda → JS) ---"
echo ""

for example in "${EXAMPLES[@]}"; do
  printf "  %-25s " "$example"
  if npm run "build:$example" > /dev/null 2>&1; then
    echo "✓"
    PASSED=$((PASSED + 1))
  else
    echo "✗ FAILED"
    FAILED=$((FAILED + 1))
  fi
done

# Server builds (Agda → Haskell) — optional, require GHC + packages
SERVERS=(
  "main"
  "server"
  "multi-agent"
  "shared-demo"
  "inspector-demo"
)

echo ""
echo "--- Server builds (Agda → Haskell) ---"
echo ""

for server in "${SERVERS[@]}"; do
  printf "  %-25s " "$server"
  if npm run "build:$server" > /dev/null 2>&1; then
    echo "✓"
    PASSED=$((PASSED + 1))
  else
    echo "✗ FAILED"
    FAILED=$((FAILED + 1))
  fi
done

echo ""
echo "--- CSS generation ---"
echo ""

printf "  %-25s " "css:all"
if npm run css:all > /dev/null 2>&1; then
  echo "✓"
  PASSED=$((PASSED + 1))
else
  echo "✗ FAILED"
  FAILED=$((FAILED + 1))
fi

echo ""
echo "=== Results ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo ""

if [ $FAILED -eq 0 ]; then
  echo "All examples build successfully!"
  exit 0
else
  echo "Some examples failed to build!"
  exit 1
fi
