# Proof Lantern research archive

This branch preserves independently developed Lean work. It is not an upstream submission, and fork `main` is unchanged.

- `L_meta_17376.lean`: the exact monotone-boundary statement and our independent proof. The pinned Lean build and source/import guard passed. The full verifier did not return a verdict for this version. A different proof landed upstream in [PR #22170](https://github.com/open-goat/pequalnp-proofs/pull/22170); do not submit this duplicate.
- `NormalizedFrontierSupport.lean`: compiled under the project's pinned Lean 4.36.0. It establishes gate-to-formula evaluation equivalence, the backward-frontier counting identity, and the per-step support and occurrence invariants. The combined circuit lower bound is still in progress. Next: connect the per-step invariants through the full scan, establish monotonicity without a live NOT, and apply the one-hot matching argument.

To check locally after populating the project's pinned dependencies, run from the repository root:

```sh
cd lean
lake env lean ../research/proof-lantern/NormalizedFrontierSupport.lean
lake env lean ../research/proof-lantern/L_meta_17376.lean
```
