# Checking the fixed G11 edge function

The 16 edges are the concrete list in the upstream file PEqualNP/Outside/R_meta_2258_47.lean. The two related upstream bridge lemmas R_meta_1342_642 and L_meta_8231 use precisely the same 16 positive pairs and 24 maximal independent sets as seed.py. For a monotone circuit these rows suffice: every positive assignment contains a minimal positive pair, and every negative assignment extends to a maximal negative.

The included Lean positive control is exactly 22 gates, not an answer to a request for 21. A kernel-checked bitvector theorem verifies its truth table without using a native-decide axiom; a separate Python replay evaluates all 2,048 masks. The positive control chooses a seven-vertex cover and factors stars, then ORs the terms. The graph has 22 size-seven covers and no cover of size six, verified by seed.py; this cover count is not a circuit lower bound.

Exact-top.py searches only the specified terminal-product shape, with two junk ANDs and a fixed number of terminal products at total size 21. It makes no statement about other topologies; a timeout is unknown. search.cpp starts from one-gate simplifications of cover circuits and rewires by estimated errors. No-fit is not a lower bound.
