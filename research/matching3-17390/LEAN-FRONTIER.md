# Lean reproduction for the final three 13-gate footprints

These are independent bounded Boolean theorems, not a theorem quantifying over all circuits. The mathematical reduction from an arbitrary minimum circuit to these footprints, and the other footprints, are described separately in EXACT-14.md.

From this folder, run python3 gen_lean_matching_flat.py. It writes three complete Lean files with monomorphic BitVec constraints, one for each final footprint. Compile MatchingNo13FlatRowAnd.lean, MatchingNo13FlatDiagAnd.lean and MatchingNo13FlatRowOr.lean with Lean 4.36.0 and the bundled CaDiCaL on PATH. Each should exit zero. The tactic bv_decide uses a checked LRAT certificate. The files do not use sorry or native_decide.

The constraints explicitly model Boolean operation, fanout, prior gate reads, raw slot usage, distinguishable truth signatures and pivotal assignments. The two signs of the final gate usage do not need separate files in this Lean encoding; the theorem closes both together.

To replay the other 21 bounded case theorems, run python3 gen_lean_matching_fanout.py with the provided lean-fanout-cases.txt in this folder. Then compile each MatchingFanout*.lean. The 21 plus the three one-primitive proofs cover all constrained 12/13 cases; the separate macro/formula finite computations and graph/symmetry reductions are not themselves in these Lean theorems.
