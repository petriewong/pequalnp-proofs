import Std.Tactic.BVDecide

-- Outside-prefix cut budget and elementary shadow slot count.
example (g p d : Nat) (h : g ≤ 21) (hp : p = 2)
    (hle : 16 + p + d ≤ g) : d ≤ 3 := by omega

example (d : Nat) (hd : d ≤ 3) (hs : 4 ≤ d) : False := by omega

-- Kept-label availability to avoid up to three own-dirty labels.
example (bad : BitVec 5)
    (h : (bad &&& 1) + ((bad >>> 1) &&& 1) +
         ((bad >>> 2) &&& 1) + ((bad >>> 3) &&& 1) +
         ((bad >>> 4) &&& 1) ≤ 3) :
    ((~~~bad &&& (~~~bad - 1)) != 0) = true := by bv_decide

-- All-O loss and reconstruction arithmetic. No circuit assertion is in these lemmas.
example (n a q : Nat) (hn : n ≤ 22) (ha : a + 14 ≤ n) (hq : q ≤ a) :
    n - 8 + (q - 1) ≤ 21 := by omega

example (n a q : Nat) (hn : n ≤ 21) (ha : a + 14 ≤ n) (hq : q ≤ a) :
    n - 9 + (q - 1) ≤ 18 := by omega
