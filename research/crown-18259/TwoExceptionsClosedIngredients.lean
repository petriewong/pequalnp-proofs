import Std.Tactic.BVDecide

example (orig proj lost : Nat) (h₁ : 10 ≤ proj)
    (h₂ : 6 ≤ lost) (h₃ : proj + lost ≤ orig) : 16 ≤ orig := by omega

example (size ors ands : Nat) (hs : size ≤ 22)
    (ho : 16 ≤ ors) (h : ors + ands ≤ size) : ands ≤ 6 := by omega

example (size drops products : Nat) (hs : size ≤ 22)
    (hd : 6 ≤ drops) (hp : products ≤ 6) :
    size - drops + (products - 1) ≤ 21 := by omega
