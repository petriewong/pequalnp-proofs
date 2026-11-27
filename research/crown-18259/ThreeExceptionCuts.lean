import Std.Tactic.BVDecide

def pop5 (v : BitVec 5) : BitVec 5 :=
  (v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1) +
  ((v >>> 3) &&& 1) + ((v >>> 4) &&& 1)

-- Search the few possible retained labels and exception masks independently:
-- given any two dirty labels and three exceptions, find an exceptional label
-- off the dirty labels with an eligible opposite ordinary cut also off them.
def canCut (exc other dirty : BitVec 5) (i : Nat) : Bool :=
  let label : BitVec 5 := (1 : BitVec 5) <<< i
  (exc &&& label != 0) && (dirty &&& label == 0) &&
  ((~~~(other ||| dirty ||| label)) != 0)

example (l r dirty : BitVec 5)
    (n : pop5 l + pop5 r = 3) (hd : pop5 dirty = 2)
    (ord : (l &&& r &&& dirty) = 0) :
    (canCut l r dirty 0 || canCut l r dirty 1 || canCut l r dirty 2 ||
     canCut l r dirty 3 || canCut l r dirty 4 || canCut r l dirty 0 ||
     canCut r l dirty 1 || canCut r l dirty 2 || canCut r l dirty 3 ||
     canCut r l dirty 4) = true := by
  unfold canCut pop5 at *
  bv_decide

example (a q : Nat) (ha : a ≤ 6) (hq : q ≤ a) :
    22 - 6 + (q - 1) ≤ 21 := by omega

-- If at most two of four compatible labels are blocked and at most one
-- ordinary feeder overlaps the forced region, a saturated away-cut exists.
def pop4 (v : BitVec 4) : BitVec 4 :=
  (v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1) + ((v >>> 3) &&& 1)

example (blocked overlap : BitVec 4) (hb : pop4 blocked ≤ 2) (ho : pop4 overlap ≤ 1) :
    (~~~(blocked ||| overlap) != 0) = true := by
  unfold pop4 at *
  bv_decide

example (q : Nat) (h : q ≤ 7) : 22 - 7 + (q - 1) ≤ 21 := by omega
