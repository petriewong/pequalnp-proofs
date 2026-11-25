# Proof Lantern research archive

Independent Lean work. This branch is not an upstream submission. The fork's `main` is unchanged.

- `MatchingCircuitLowerBound.lean`: Lean-checked lower bound of **2N − 1 gates** for representing an N-by-N perfect matching or its complement, for N ≥ 2. It uses the project's exact `FanInTwo` and `Represents` definitions. The final theorems are `ProofLanternMatch.project_matching_lower` and `ProofLanternMatch.project_crown_lower`. Those upstream targets have other contributors' PRs; do not submit duplicates.
- `NormalizedFrontierSupport.lean`: earlier standalone checkpoint for backwards expansion, counting and per-step support.
- `L_meta_17376.lean`: independent proof of the exact monotone-boundary statement. Pinned Lean build and source/import guard passed. The full local verifier did not return a verdict for this version. A different proof landed upstream in [PR #22170](https://github.com/open-goat/pequalnp-proofs/pull/22170).

To check after populating the repository's pinned Lean dependencies:

```sh
cd lean
lake build +PEqualNP.Defs.Represents
lake env lean ../research/proof-lantern/MatchingCircuitLowerBound.lean
lake env lean ../research/proof-lantern/NormalizedFrontierSupport.lean
lake env lean ../research/proof-lantern/L_meta_17376.lean
```
