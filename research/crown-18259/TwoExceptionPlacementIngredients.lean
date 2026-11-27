import Std.Tactic.BVDecide

def pop5 (v : BitVec 5) : BitVec 5 :=
  (v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1) +
  ((v >>> 3) &&& 1) + ((v >>> 4) &&& 1)

example (dirty loc : BitVec 5)
    (hd : pop5 dirty ≥ 2) (h : pop5 (dirty &&& ~~~loc) ≤ 1)
    (hl : pop5 loc = 1) : (dirty &&& loc != 0) = true := by
  unfold pop5 at *
  bv_decide

example (x operand : Bool) : (x || (x && operand)) = x := by bv_decide

example (q d : Nat) (bounds : (q ≤ 6 ∧ 6 ≤ d) ∨ (q ≤ 7 ∧ 7 ≤ d) ∨ (q ≤ 8 ∧ 8 ≤ d)) :
    22 - d + (q - 1) ≤ 21 := by omega
