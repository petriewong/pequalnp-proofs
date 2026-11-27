import Std.Tactic.BVDecide

def pop4 (v : BitVec 4) : BitVec 4 :=
  (v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1) + ((v >>> 3) &&& 1)

example (kept overlap : BitVec 4) (hk : pop4 kept ≤ 2) (ho : pop4 overlap ≤ 1) :
    (~~~(kept ||| overlap) != 0) = true := by
  unfold pop4 at *
  bv_decide

example (d distinct : Nat) (hd : 2 ≤ d)
    (hf : d = 2 → 1 ≤ distinct) : 16 + 2 + d + distinct + 2 > 22 := by
  by_cases h : d = 2
  · have := hf h
    omega
  · omega

example (s a q : Nat) (hs : s ≤ 22) (ha : a ≤ 8) (hq : q ≤ a) :
    s - 8 + (q - 1) ≤ 21 := by omega

example (s a q : Nat) (hs : s ≤ 22) (ha : a ≤ 7) (hq : q ≤ a) :
    s - 7 + (q - 1) ≤ 21 := by omega

example (r h v : Bool) (hh : h = true → r = true) :
    (r || (h || v)) = (r || v) := by bv_decide
