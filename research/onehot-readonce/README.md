# One-hot read-once circuit controls

Run `node research/onehot-readonce/check.mjs`. No packages, network, Lean or Assay are required for this replay. This is a research benchmark, not an upstream submission or a Lean certificate.

The domain is the 16 pairs of one-hot choices from four row and four column inputs. Entry (i,j) is bit (4*i+j). With distinct rows and columns, at least six raw inputs are needed. Five binary gates connecting six distinct inputs force a read-once tree. The census compares an omitted-pattern comparability prefilter against exact read-once formula enumeration; the latter freely allows NOT and is therefore conservative as a five-total-gate rejection test. The DP combines disjoint leaf subsets and closes each result under complementation. Prefilter acceptance alone proves nothing about realizability.

| Truth mask | Row masks (decimal) | Prefilter | Minimum total gates |
|---|---|---|---:|
| 0x0421 | 1, 2, 4, 0 | pass | 5 |
| 0x0125 | 5, 2, 1, 0 | pass | 6 |

Both gate lists are checked on all 16 valid inputs. For the second table, any five-gate implementation would be read-once, but exact enumeration excludes it. A structural check reaches the same conclusion: comparability forces omission of row 3 and column 3 (zero-based); monotone read-once formulas with zero boundary give disjoint complete bipartite components, but rows 0 and 2 have overlapping unequal neighborhoods. The test distinguishes provisional filter results from checked witnesses and scoped lower bounds; Assay has not been run on this benchmark.

Across all 65,536 tables, 33,864 have distinct rows and columns. Of these, 12,672 pass the prefilter and 7,488 have a read-once formula on at least one six-input support. The gap consists of 5,184 false passes, not erroneous rejections.

## Root split and support provenance

After comparability fixes literal polarity, test all 31 unordered binary root splits. For an OR split each positive must be separable from every negative on at least one child projection. For AND each negative must be separable from every positive on at least one child projection. In both cases separation means some child coordinate is 1 on the positive and 0 on the negative. This checks arbitrary monotone children, so passing is not evidence for a read-once decomposition. A second rule rejects a constant omitted border if, after normalization to zero, two row neighborhoods overlap but differ.

The combined rule agrees with exact formula search on all 33,864 distinct-pattern tables in this 4×4 census. It is not a general sufficiency rule. For individual omission pairs it admits 31,104, of which exactly 24,192 have a formula.

- `0x0136`: passes comparability; no root split survives.
- `0x0125`: a root split survives; the constant-border rule rejects it.
- `0x0127`: omission (0,3) survives both rules but has no formula. Its positive result belongs to omissions (0,2) and (3,2), not (0,3). Preserve the actual checked omission when reporting a witness. Indices are zero-based.
