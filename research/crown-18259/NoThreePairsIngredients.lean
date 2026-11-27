import Std.Tactic.BVDecide
namespace ProofLantern.Crown.NoThreePairs
theorem fiveCannotUseFour (a b c d e : BitVec 2) :
    a=b ∨ a=c ∨ a=d ∨ a=e ∨ b=c ∨ b=d ∨ b=e ∨ c=d ∨ c=e ∨ d=e := by bv_decide

theorem terminalCost (k removed q : Nat) (hk : k ≤ 22) (hr : removed ≤ k)
    (drop : 4 ≤ removed) (hq : q ≤ 6) (extra : 5 ≤ removed ∨ q ≤ 5) :
    k-removed+(q-1) ≤ 22 := by omega

theorem dirtyUnion (a b : Bool) : a = true ∨ b = true → a || b = true := by
  cases a <;> cases b <;> simp
end ProofLantern.Crown.NoThreePairs
