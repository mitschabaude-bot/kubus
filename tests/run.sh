#!/usr/bin/env bash
# Runs the test suite: library files must check, tests/pass/*.ktt must produce
# tests/pass/*.out, tests/repl.in (on `kubus --interactive`) must produce tests/repl.out,
# and tests/fail/*.ktt must fail with the message in their `-- expect:` line.
# Library and tests also run under `--selfcheck`; no invariant violation may be reported.
cd "$(dirname "$0")/.."
export KUBUS_PATH=lib
bin=.lake/build/bin/kubus
fails=0
for f in lib/*.ktt; do
  if ! timeout 60 $bin "$f" > /dev/null 2> /tmp/kubus-err; then
    echo "FAIL $f"; cat /tmp/kubus-err; fails=$((fails+1))
  fi
done
# invariant self-checks on the library and the passing tests (SELFCHECK=0 to skip)
if [ "${SELFCHECK:-1}" = 1 ]; then
  if ! timeout 300 $bin --selfcheck lib/*.ktt > /dev/null 2> /tmp/kubus-err; then
    echo "FAIL selfcheck lib"; head -40 /tmp/kubus-err; fails=$((fails+1))
  else
    echo "lib: $(tail -1 /tmp/kubus-err)"
  fi
  for f in tests/pass/*.ktt; do
    if ! timeout 120 $bin --selfcheck-main "$f" > /dev/null 2> /tmp/kubus-err; then
      echo "FAIL selfcheck $f"; head -40 /tmp/kubus-err; fails=$((fails+1))
    fi
  done
fi
# certified kernel: every definition and data type of the library is certified
for f in lib/univalence.ktt lib/hits.ktt lib/loopspace.ktt; do
  if ! out=$(timeout 900 $bin --kernel "$f" 2>&1) || grep -q "kernel: skipped" <<< "$out"; then
    echo "FAIL kernel $f"; grep -E "REJECTED|skipped" <<< "$out" | head -10; fails=$((fails+1))
  else
    echo "$f: $(tail -1 <<< "$out")"
  fi
done
# kernel regression tests (signatures the kernel must reject or accept)
for f in tests/kernel/*.lean; do
  if ! lake env lean "$f" > /tmp/kubus-err 2>&1; then
    echo "FAIL $f"; head -10 /tmp/kubus-err; fails=$((fails+1))
  fi
done
for f in tests/pass/*.ktt; do
  exp="${f%.ktt}.out"
  out=$(timeout 60 $bin "$f" 2>&1)
  if [ "$1" = "--update" ]; then echo "$out" > "$exp"; fi
  if [ "$out" != "$(cat "$exp" 2>/dev/null)" ]; then
    echo "FAIL $f"; diff <(echo "$out") "$exp" | head -20; fails=$((fails+1))
  fi
done
# interactive mode
out=$(timeout 60 $bin --interactive < tests/repl.in 2>&1)
if [ "$1" = "--update" ]; then echo "$out" > tests/repl.out; fi
if [ "$out" != "$(cat tests/repl.out 2>/dev/null)" ]; then
  echo "FAIL tests/repl.in"; diff <(echo "$out") tests/repl.out | head -20; fails=$((fails+1))
fi
# the tutorial's examples
if ! python3 tests/tutorial.py; then fails=$((fails+1)); fi
# language server
if ! python3 tests/lsp.py; then fails=$((fails+1)); fi
for f in tests/fail/*.ktt; do
  exp=$(head -1 "$f" | sed -n 's/^-- expect: //p')
  if out=$(timeout 10 $bin --selfcheck "$f" 2>&1); then
    echo "FAIL $f: unexpectedly accepted"; fails=$((fails+1))
  elif ! grep -qF -- "$exp" <<< "$out" || grep -qE 'internal|\[(conv-refl|conv-symmetry|roundtrip|recheck|stability)\]' <<< "$out"; then
    echo "FAIL $f: expected '$exp', got:"; echo "$out" | head -5; fails=$((fails+1))
  fi
done
if [ $fails -eq 0 ]; then echo "all tests passed"; else echo "$fails failures"; exit 1; fi
