#!/bin/sh
set -eu
run() {
  output=$(python3 "$@")
  printf '%s\n' "$output"
  printf '%s\n' "$output" | grep -q '^unsat '
}
for op in 0 1; do
 for sh in 0 1; do for internal in 2 3; do
   run synth_matching_shared_robust.py 13 "$op" "$sh" 300 "$internal" -1
 done; done
 run synth_matching_shared_robust.py 13 "$op" 0 300 2 5
 run synth_matching_shared_robust.py 13 "$op" 1 300 2 2
done
while read -r op sh third; do
 run synth_matching_shared_bitblast.py 13 "$op" "$sh" 300 2 "$third"
done <<'CASES'
0 0 3
0 1 1
1 0 3
1 1 1
1 1 8
CASES
while read -r op sh third; do
 for root in 0 1; do
  run synth_matching_one_primitive.py 13 "$op" "$sh" 300 2 "$third" "$root" 0
 done
done <<'CASES'
0 0 2
0 1 8
1 0 2
CASES
