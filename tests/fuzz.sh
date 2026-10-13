#!/usr/bin/env bash
# Random well-typed programs under --selfcheck, and ill-typed mutants that must be rejected.
# Usage: tests/fuzz.sh [N] [SEED] [extra fuzz.py options]; reproduce one case with
# `tests/fuzz.py --seed SEED --case K --keep DIR`.
cd "$(dirname "$0")/.."
n=${1:-20}
seed=${2:-0}
shift 2 2>/dev/null
exec python3 tests/fuzz.py --cases "$n" --seed "$seed" "$@"
