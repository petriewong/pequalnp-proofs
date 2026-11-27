# Scoped obstruction: pairing all seven raw input pairs cannot achieve 22 gates

Spend seven gates to make z_i = x_i OR y_i. The remainder must compute threshold two on all seven Boolean flags: on the promised Crown inputs, every singleton is false and every distinct pair is true, and these determine every assignment by monotonicity. At most 22 total gates would leave at most 15 gates for this logical threshold.

The established monotone OR lower bound for seven flags is 10 (Wegener, The Complexity of Boolean Functions, section 6.3 Theorem 3.1(ii)). The scoped independent lower arguments exclude at most four ANDs at logical size 15. Thus the only possibility has exactly five AND and ten OR gates. Earlier exact replay and structural cases exclude zero, one or two singleton-accepting helper ANDs.

* With three singleton-accepting helpers, normalize the two clean ANDs as terminal products with an OR root at no added size. Their removal from earlier routing preserves output (the first true clean gate is retained on a true row). If a clean gate becomes nonproductive, dropping it yields at most four ANDs without cost increase. Otherwise an omitted leaf costs a routing OR that collapses, paying for the final OR. There are nine preterminal ORs; each raw flag has exactly two OR readers (from six-variable projection and the fact a sole OR reader has a singleton-accepting companion in normalized routing). Fourteen direct raw incidences force at least five raw-raw ORs. The graph has maximum degree two, so it is a union of paths and cycles. All 15 canonical frontiers have no model.
* With four singleton-accepting helpers, the sole clean AND is the output in a live minimal circuit. A purely raw operand is impossible by removing its missing flag and projecting to six-input threshold, as in ThresholdPureSide.lean and the separate physical gate count. Otherwise both operands reach helpers. The ten ORs need at least four raw-raw ORs, and all 21 canonical frontiers in this case have no model.

The two scripts are independent bounded solvers for these last forms, and raw-or-prefixes.py enumerates the unlabeled graphs. Place them together under evidence/, install Python z3-solver, and run from the directory above evidence/:

    for i in $(seq 0 14); do python3 evidence/threshold-three-dirty-terminal-sat.py "$i" 180 1; done
    for i in $(seq 0 20); do python3 evidence/threshold-four-dirty-graph-bitblast.py "$i" 180; done

Every completed result is UNSAT. A timeout is not an exclusion. The 23-gate controls supply the upper bound. This excludes prepair-only architectures, not arbitrary circuits that read the original fourteen wires independently.
