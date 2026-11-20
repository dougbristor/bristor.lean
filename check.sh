#!/usr/bin/env bash
# check.sh — prove Bristor.lean, check it against the shipped test vectors, and prove the check can fire.
#   LEAN=<path to lean binary> ./check.sh      (default: `lean` on PATH)
# PASS needs all of:
#   1. Bristor.lean checks with no error and no sorry; its theorems use only Lean's standard axioms
#      (no sorryAx, no native_decide / Lean.ofReduceBool / trustCompiler).
#   2. mul reproduces every B3 case in vectors/vectors.json.
#   3. every plant FAILS, and fails inside the plant (an error above the plant would be a broken
#      base file, not a fired plant: "some check failed" is not "the plant fired").
set -u
here="$(cd "$(dirname "$0")" && pwd)"
LEAN="${LEAN:-$(command -v lean)}"
[ -n "$LEAN" ] && [ -x "$LEAN" ] || { echo "check.sh: no lean on PATH (install elan, see README) or set LEAN="; exit 2; }
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
base="$here/Bristor.lean"; nbase=$(wc -l < "$base")
fail=0

# 1. the theorems, plus an axiom audit
{ cat "$base"; echo; for t in mul_add_left mul_add_right mul_smul_left mul_smul_right commutator \
    square_closed jroll_is_reversal table commutator_signature not_assoc not_alternative \
    not_norm_mult not_quaternion; do echo "#print axioms B3.$t"; done; } > "$tmp/clean.lean"
out="$("$LEAN" "$tmp/clean.lean" 2>&1)"; rc=$?
if [ $rc -ne 0 ] || grep -qi "sorry\|error" <<<"$out"; then echo "FAIL theorems (rc=$rc)"; echo "$out" | head -20; fail=1
elif grep -q "sorryAx\|ofReduceBool\|trustCompiler" <<<"$out"; then echo "FAIL axioms"; grep "axioms" <<<"$out"; fail=1
else echo "ok   13 theorems; axioms used: $(grep -o '\[[^]]*\]' <<<"$out" | tr -d '[]' | tr ',' '\n' | sed 's/ //g' | sort -u | paste -sd' ')"; fi

# 2. parity with the shipped test vectors
VEC="$here/vectors/vectors.json"; [ -f "$VEC" ] || VEC="$here/../vectors.json"   # standalone bundle, or lean/ beside the block's vectors.json
python3 -I "$here/gen_vectors.py" "$VEC" "$tmp" || exit 2
cat "$base" "$tmp/vectors_body.lean" > "$tmp/vec.lean"
out="$("$LEAN" "$tmp/vec.lean" 2>&1)"; rc=$?
if [ $rc -ne 0 ] || grep -qi "sorry\|error" <<<"$out"; then echo "FAIL vectors"; echo "$out" | head -10; fail=1
else echo "ok   vectors: $(grep -c '^example' "$tmp/vectors_body.lean") B3 cases match canon"; fi

# 3. plants must fire, inside the plant
fired=0; total=0
for p in "$here"/plants/*.lean "$tmp/plant_vec.lean"; do
  total=$((total+1)); name="$(basename "$p" .lean)"
  cat "$base" "$p" > "$tmp/p.lean"
  out="$("$LEAN" "$tmp/p.lean" 2>&1)"; rc=$?
  line=$(grep -oE "p\.lean:[0-9]+" <<<"$out" | head -1 | cut -d: -f2)
  if { [ $rc -ne 0 ] || grep -q "sorry" <<<"$out"; } && [ -n "$line" ] && [ "$line" -gt "$nbase" ]; then
    fired=$((fired+1)); echo "ok   plant $name fired (line $((line-nbase)) of the plant)"
  else echo "FAIL plant $name did NOT fire in the plant (rc=$rc line=${line:-none})"; fail=1; fi
done
echo "plants fired $fired/$total"
[ $fail -eq 0 ] && echo "PASS" || { echo "FAIL"; exit 1; }
