#!/usr/bin/env bash
# Runs the test suite: library files must check, tests/pass/*.ktt must produce
# tests/pass/*.out, tests/repl.in (on `kubus --interactive`) must produce tests/repl.out,
# and tests/fail/*.ktt must fail with the message in their `-- expect:` line.
# Library and tests also run under `--selfcheck`; no invariant violation may be reported.
cd "$(dirname "$0")/.."
export KUBUS_PATH=lib
bin=.lake/build/bin/kubus
fails=0
# the library checks, and the certified kernel certifies every definition and data type
for f in lib/*.ktt; do
  # (the adequacy of every certified statement is checked too: a mismatch fails the run)
  if ! out=$(timeout 120 $bin --verbose "$f" 2>&1) || grep -q "kernel: skipped" <<< "$out"; then
    echo "FAIL $f"; grep -vE "^kernel: (certified|adequate|.*: [0-9]+ ms$)" <<< "$out" | head -20; fails=$((fails+1))
  else
    echo "$f: $(grep "certified," <<< "$out"); $(grep "^adequacy:" <<< "$out")"
  fi
done
# invariant self-checks on the library and the passing tests (SELFCHECK=0 to skip)
if [ "${SELFCHECK:-1}" = 1 ]; then
  if ! timeout 300 $bin --no-kernel --selfcheck lib/*.ktt > /dev/null 2> /tmp/kubus-err; then
    echo "FAIL selfcheck lib"; head -40 /tmp/kubus-err; fails=$((fails+1))
  else
    echo "lib: $(tail -1 /tmp/kubus-err)"
  fi
  for f in tests/pass/*.ktt; do
    if ! timeout 120 $bin --no-kernel --selfcheck-main "$f" > /dev/null 2> /tmp/kubus-err; then
      echo "FAIL selfcheck $f"; head -40 /tmp/kubus-err; fails=$((fails+1))
    fi
  done
fi
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
# adequacy of the certified statements of the passing tests (mismatches fail), and a self-test:
# with deliberately wrong kernel statements, every definition of lib/basic.ktt must mismatch
for f in tests/pass/*.ktt; do
  out=$(timeout 120 $bin --verbose "$f" 2>&1)
  if grep -q "ADEQUACY MISMATCH" <<< "$out"; then
    echo "FAIL adequacy $f"; grep "ADEQUACY MISMATCH" <<< "$out" | head -5; fails=$((fails+1))
  fi
done
out=$(KUBUS_ADEQUACY_SELFTEST=1 timeout 120 $bin --verbose lib/basic.ktt 2>&1)
if ! grep -qE "^adequacy: [01] adequate, 0 not covered, [1-9][0-9]* mismatches" <<< "$out"; then
  echo "FAIL adequacy self-test"; grep "^adequacy" <<< "$out"; fails=$((fails+1))
fi
# interactive mode
out=$(timeout 60 $bin --interactive < tests/repl.in 2>&1)
if [ "$1" = "--update" ]; then echo "$out" > tests/repl.out; fi
if [ "$out" != "$(cat tests/repl.out 2>/dev/null)" ]; then
  echo "FAIL tests/repl.in"; diff <(echo "$out") tests/repl.out | head -20; fails=$((fails+1))
fi
# the website: every tutorial snippet elaborates and is certified, `fails` snippets fail
if ! out=$(python3 site/build.py --out "$(mktemp -d)/site" 2>&1); then
  echo "FAIL site"; echo "$out" | tail -20; fails=$((fails+1))
fi
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
