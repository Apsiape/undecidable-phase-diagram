#!/usr/bin/env bash
# Mutual exclusion for Lean processes (session 10): one Lean process at a time across a session and
# its subagents. Runs scripts/check.sh or scripts/build.sh (unchanged: same memory guard, caps and
# time limits) while holding the lock directory .build/lean.lock; if another process holds it, it
# does not wait and exits 4 ("BUSY"), so the caller retries later.
# Usage: scripts/locked.sh check.sh FILE [MB] [S]
#        scripts/locked.sh build.sh [Module.Path ...]
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lock="$here/../.build/lean.lock"
mkdir -p "$here/../.build"
case "${1:-}" in
  check.sh|build.sh) ;;
  *) echo "usage: scripts/locked.sh check.sh|build.sh ARGS"; exit 2 ;;
esac
if ! mkdir "$lock" 2>/dev/null; then
  echo "BUSY: another Lean process holds $lock (retry later; do not remove it unless stale)"
  exit 4
fi
trap 'rmdir "$lock" 2>/dev/null' EXIT
"$here/$1" "${@:2}"
