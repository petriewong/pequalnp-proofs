# Fano incidence circuit research (L-meta-4691)

Work in progress. This is a research checkpoint, not a solution, an upstream submission, or a proof of the 27-gate exclusion.

- `FanoGraph.lean`: finite incidence facts, a monotone boundary lemma, and the two-colour cover property under one choice per diagonal edge.
- `ConeTags.lean` and `FoldTag.lean`: local proofs of tagged ancestor propagation on cones and in a gate-input fold. They do not import or claim equivalence to the upstream circuit definitions.
- `baseline.py`: checks 36 structured 27-gate circuits against all 16,384 inputs. None has the specified motif.
- `boundary.py`: 21 minimal true rows and 37 maximal false rows suffice to distinguish the graph function among monotone functions.
- `flag_control.py`: checks the full truth table and flagged motif of a 30-gate example, outside the problem's bound.
- `tag_query.py` and `test_tag.py`: the compact query rejects the fixed 27-gate no-motif example and accepts the fixed 30-gate motif example. An unconstrained 27-gate run returned `unknown`, not an exclusion.

Replay with Lean 4.36.0 and Python 3. The two SMT scripts use the system `libz3` shared library.

```sh
lean FanoGraph.lean
lean ConeTags.lean
lean FoldTag.lean
python baseline.py
python boundary.py
python flag_control.py
python test_tag.py
```
