#!/bin/bash
# E2E Build Verification Script
# Builds all browser examples and reports any failures

set -e

echo "=== Agdelte Build Verification ==="
echo ""

FAILED=0
PASSED=0

# Browser examples to build (Agda → JS)
EXAMPLES=(
  "counter"
  "timer"
  "todo"
  "keyboard"
  "http"
  "task"
  "websocket"
  "router"
  "composition"
  "transitions"
  "combinators"
  "optic-dynamic"
  "worker"
  "parallel"
  "session-form"
  "stress-test"
  "controls-demo"
  "css-demo"
  "css-full-demo"
  "anim-demo"
  "svg-test"
  "svg-smil"
  "svg-panzoom"
  "svg-chart"
  "svg-linedraw"
  "webgl-test"
  "webgl-full-demo"
  "webgl-controls-demo"
  "remote-agent"
  "styles"
  "agent-wiring"
  "dep-agent-demo"
  "session-dual"
)

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
