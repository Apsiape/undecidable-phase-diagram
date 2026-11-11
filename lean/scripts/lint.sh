#!/usr/bin/env bash
# Reject forbidden constructs anywhere in the Lean sources (mentions inside `backticks` are fine).
cd "$(dirname "${BASH_SOURCE[0]}")/.."
status=0
pat='(^|[^`])(native_decide|implemented_by|@\[extern)|^[[:space:]]*axiom[[:space:]]|(^|[^`])autoImplicit[[:space:]]+true|decide[[:space:]]+\+native'
if grep -rnE "$pat" --include='*.lean' UndecidablePhaseDiagram UndecidablePhaseDiagram.lean; then
  echo "LINT: forbidden construct found"; status=1
fi
for f in UndecidablePhaseDiagram.lean $(find UndecidablePhaseDiagram -name '*.lean'); do
  grep -q 'set_option autoImplicit false' "$f" || { echo "LINT: $f lacks 'set_option autoImplicit false'"; status=1; }
done
[ $status -eq 0 ] && echo "lint ok"
exit $status
