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
typecheck "Theory/Poly"            -i src src/Agdelte/Theory/Poly.agda
typecheck "Theory/DepPoly"         -i src src/Agdelte/Theory/DepPoly.agda
typecheck "Theory/PolySignal"      -i src src/Agdelte/Theory/PolySignal.agda
typecheck "Theory/LensLaws"        -i src src/Agdelte/Theory/LensLaws.agda
typecheck "Theory/OpticPolyLens"   -i src src/Agdelte/Theory/OpticPolyLens.agda
typecheck "Theory/BigLensPolyLens" -i src src/Agdelte/Theory/BigLensPolyLens.agda
typecheck "Theory/SessionDualProof" -i src src/Agdelte/Theory/SessionDualProof.agda
typecheck "Theory/AgentCoalg"      -i src src/Agdelte/Theory/AgentCoalg.agda
typecheck "Test/OpticTest"         -i src src/Agdelte/Test/OpticTest.agda
typecheck "Test/Interpret"         -i src src/Agdelte/Test/Interpret.agda
typecheck "test/EventTest"         -i src -i test test/EventTest.agda

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
