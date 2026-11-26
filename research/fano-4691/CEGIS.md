# Counterexample-guided Fano search

This is an incomplete local search, not a proof or counterexample. `BoundaryCertificate.lean` proves the abstract boundary rule for bipartite graph functions. `python cegis.py` checks the fixed 27-gate negative and 30-gate positive controls, followed by a bounded search. In the recorded run, a candidate agreeing on the 14-row seed disagreed on 17 other boundary rows. The expanded 31-row query returned `unknown`. All candidates must be replayed over the full boundary and, if accepted there, all 16,384 inputs. `unknown` does not establish an exclusion.
