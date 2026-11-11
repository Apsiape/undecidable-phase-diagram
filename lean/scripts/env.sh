# Pinned vendored dependencies and the serial replay output (Lean v4.35.0, Mathlib 56a0058).
PROJ="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LP="$PROJ/.lake/build/lib/lean"
for d in "$PROJ"/vendor/*/; do LP="$LP:${d}.lake/build/lib/lean"; done
export LEAN_PATH="$LP"
export LEAN_NUM_THREADS=1
