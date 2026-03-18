#!/bin/bash
# Typecheck all Agda modules and report all failures
# Unlike the chained && version, this reports ALL failures

FAILED=0
PASSED=0
ERRORS=""

typecheck() {
  local desc="$1"
  shift
  printf "  %-50s " "$desc"
  if agda "$@" > /dev/null 2>&1; then
    echo "✓"
    PASSED=$((PASSED + 1))
  else
    echo "✗ FAILED"
    FAILED=$((FAILED + 1))
    ERRORS="$ERRORS\n  - $desc"
  fi
}

echo "=== Agdelte Type Check ==="
echo ""

echo "--- Library modules ---"
echo ""
typecheck "Reactive.Node"          -i src src/Agdelte/Reactive/Node.agda

# Auto-discover Theory modules
for f in $(find src/Agdelte/Theory -name "*.agda" | sort); do
  mod=$(echo "$f" | sed 's|^src/||; s|/|.|g; s|\.agda$||')
  typecheck "$mod" -i src "$f"
done

# Auto-discover Test modules
for f in $(find src/Agdelte/Test -name "*.agda" | sort); do
  mod=$(echo "$f" | sed 's|^src/||; s|/|.|g; s|\.agda$||')
  typecheck "$mod" -i src "$f"
done

# test/ directory (separate include path)
for f in $(find test -name "*.agda" | sort); do
  mod=$(basename "$f" .agda)
  typecheck "test/$mod" -i src -i test "$f"
done

echo ""
echo "--- Examples ---"
echo ""
EXAMPLES=(
  Counter Timer Todo Keyboard Http Task WebSocket Router
  Composition Transitions Combinators OpticDynamic Worker
  Parallel SessionFormDemo StressTest CssDemo CssFullDemo
  AnimDemo SvgTest SvgSmil SvgPanZoom SvgChart SvgLineDraw
  WebGLTest WebGLFullDemo WebGLControlsDemo ControlsDemo
  Styles RemoteAgent AgentWiring DepAgentDemo SessionDual
)

for ex in "${EXAMPLES[@]}"; do
  typecheck "$ex" -i src -i examples "examples/$ex.agda"
done

echo ""
echo "=== Results ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"

if [ $FAILED -gt 0 ]; then
  echo ""
  echo "Failures:"
  echo -e "$ERRORS"
  echo ""
  exit 1
else
  echo ""
  echo "All modules typecheck successfully!"
  exit 0
fi
