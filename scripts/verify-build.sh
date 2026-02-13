#!/bin/bash
# E2E Build Verification Script
# Builds all browser examples and reports any failures

set -e

echo "=== Agdelte Build Verification ==="
echo ""

FAILED=0
PASSED=0

# Browser examples to build
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
)

for example in "${EXAMPLES[@]}"; do
  printf "  %-20s " "$example"
  if npm run "build:$example" > /dev/null 2>&1; then
    echo "✓"
    ((PASSED++))
  else
    echo "✗ FAILED"
    ((FAILED++))
  fi
done

echo ""
echo "=== Results ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo ""

if [ $FAILED -eq 0 ]; then
  echo "✅ All examples build successfully!"
  exit 0
else
  echo "❌ Some examples failed to build!"
  exit 1
fi
