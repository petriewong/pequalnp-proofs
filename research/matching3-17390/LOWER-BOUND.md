# Finite evidence for the 3×3 monotone perfect-matching lower bound

**Bounds established here: 13≤s≤14**, where s is the minimal binary AND/OR circuit size; this is computational lower-bound evidence, not a Lean certificate of the lower bound. The attached Lean code verifies the positive 14-gate example and pivotal primary pairs, not solver unsatisfiability. The 13-gate existence question remains open in this archive.

1. Minimal true and maximal false input rows characterize the function for monotone circuits. The formula DP exhausts sizes up to 13 without a witness. The positive 14-gate formula is separately checked.
2. Suppose there is one shared internal gate. Cutting its signal out leaves a formula above the cut and a formula below it. If the least cost of the signal is d, the formula above the cut receives at most 13−d gates and may use that signal as a free leaf. For d=1..8, exhaust the orbits of that signature under permutations of the bipartite rows and columns and transposition. If d≥9, the upper formula has at most four gates. The distinguished signal can be written at most once with no increase in size on every ≤4 formula (exhaustive exact truth-table check), contradicting the formula bound on inlining.
3. Any minimum live binary circuit with k gates has fanout excess 2k−(9+k−1)=k−8. The first AND/OR combines two distinct raw edges. For either edge it would fail to respond to some pivotal input if it were that edge's only reader (formal witnesses in `MatchingPivotal.lean`). Thus ≥2 shared raw and, by steps 1–2, ≥2 shared internal nodes. This implies k≥12. At k=12 there are exactly two of each, each excess one. The shared raw pair is the inputs of the first gate. They are adjacent or disjoint modulo graph symmetry, and the first op is AND or OR. All four exact-size SMT instances return UNSAT. Any expressively redundant gate (including duplicate evaluated signature) or constant can be eliminated in a minimum circuit, and the SMT encoding requires all nonoutputs live. Fixing the first gate is independent of the suffix order symmetry constraint.

Replay using Python and z3-solver, and a C++17 compiler (all files in this directory):

```sh
c++ -std=c++17 -O3 formula_dp.cpp -o formula
./formula 13
c++ -std=c++17 -O3 macro_batch.cpp -o macro
for d in 1 2 3 4 5 6 7 8; do
  ./macro orbits "$d" > "orbit-$d.txt"
  ./macro run "$((13-d))" "orbit-$d.txt" 0 1
done
python3 small_residual.py
for op in 0 1; do
  for shape in 0 1; do
    python3 synth_matching_shared_robust.py 12 "$op" "$shape" 180 2 -1
  done
done
```

The simple independent full-signature or shape enumerations for d=1..4 agree with the model above; the batched implementation caches raw-only optimal formula lengths and enumerates only signatures whose prior raw-only formula is longer. A timeout is not UNSAT.
