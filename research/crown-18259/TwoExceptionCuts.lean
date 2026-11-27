import Std.Tactic.BVDecide

-- The five split labels are 0..4. Exclude the exceptional label, the
-- other exceptional location if opposite, and the label to be retained.
-- At most one compatible ordinary feeder can overlap the shadow.
def pop5 (v : BitVec 5) : BitVec 5 :=
  (v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1) +
  ((v >>> 3) &&& 1) + ((v >>> 4) &&& 1)

example (excluded overlap : BitVec 5)
    (h₁ : pop5 excluded ≤ 3) (h₂ : pop5 overlap ≤ 1) :
    (~~~(excluded ||| overlap) != 0) = true := by
  unfold pop5 at *
  bv_decide

example (a q : Nat) (ha : a ≤ 7) (hq : q ≤ a) :
    22 - 7 + (q - 1) ≤ 21 := by omega

example (a q : Nat) (ha : a ≤ 8) (hq : q ≤ a) :
    22 - 8 + (q - 1) ≤ 21 := by omega

-- H is the exceptional raw's sole reader, and its companion is
-- independent of the exceptional and ordinary raws and false at zero.
example (r hOther : Bool) (ho : hOther = false) : (r && hOther) = false := by
  simp [ho]
