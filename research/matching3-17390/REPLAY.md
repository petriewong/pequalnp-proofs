# 3×3 monotone perfect matching: a 14-gate control and bounded searches

Nine raw wires are edges in row-major order. The output is true iff the input graph has a perfect matching. This is a research benchmark, not a proof of the public ≤13-gate target.

* `python3 check_matching.py` validates the 14-gate fan-out-one construction on all 512 rows. `PerfectMatching14.lean` checks the same truth table with a separate definition, AND/OR-only exact fan-in two, and every reference backward, using the project's Lean definitions.
* Compile `formula_dp.cpp` as C++17 with optimization. Run `./formula_dp 13` to check that **no formula** with at most 13 gates reaches the target. With only one use of each internal gate, formulas are strictly narrower than general circuits.
* `one_shared_small_cone_dp.cpp` (C++17) checks each named free-intermediate-signal formula model. Run `./macro operation shape 12` for both operation values (0 AND, 1 OR) and both shape values (0 adjacent, 1 disjoint raw pair). For compound three-raw-input macros, run `python3 representatives.py` and then `./macro operation shape 11 next_operation representative` for the listed shapes and representatives, both values of each operation. All finished negative at the given bounds. A general 13-gate circuit would need multiple shared gates, or a sole shared gate with an input cone of at least three gates. No general circuit lower bound follows here.

All bounded decision procedures use the 6 minimal true and 15 maximal false assignments. A monotone circuit matching these 21 boundary rows matches the whole 512-row truth table.
