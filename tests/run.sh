#!/usr/bin/env bash
# Runs the test suite: library files must check, tests/pass/*.ktt must produce
# tests/pass/*.out, and tests/fail/*.ktt must fail with the message in their `-- expect:` line.
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
  if ! timeout 300 $bin --selfcheck lib/*.ktt tests/pass/*.ktt > /dev/null 2> /tmp/kubus-err; then
    echo "FAIL selfcheck"; head -40 /tmp/kubus-err; fails=$((fails+1))
  else
    tail -1 /tmp/kubus-err
  fi
fi
for f in tests/pass/*.ktt; do
  exp="${f%.ktt}.out"
  out=$(timeout 60 $bin "$f" 2>&1)
  if [ "$1" = "--update" ]; then echo "$out" > "$exp"; fi
  if [ "$out" != "$(cat "$exp" 2>/dev/null)" ]; then
    echo "FAIL $f"; diff <(echo "$out") "$exp" | head -20; fails=$((fails+1))
  fi
done
for f in tests/fail/*.ktt; do
  exp=$(head -1 "$f" | sed -n 's/^-- expect: //p')
  if out=$(timeout 10 $bin --selfcheck "$f" 2>&1); then
    echo "FAIL $f: unexpectedly accepted"; fails=$((fails+1))
  elif ! grep -qF -- "$exp" <<< "$out" || grep -qE 'internal|\[(conv-refl|conv-symmetry|roundtrip|recheck|stability)\]' <<< "$out"; then
    echo "FAIL $f: expected '$exp', got:"; echo "$out" | head -5; fails=$((fails+1))
  fi
done
if [ $fails -eq 0 ]; then echo "all tests passed"; else echo "$fails failures"; exit 1; fi
