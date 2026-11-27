import PEqualNP.Defs.Represents
namespace ProofLantern.MatchingPivotal
def edge (x : Fin 512) (i j : Fin 3) : Bool := x.val.testBit (3*i.val + j.val)
def target (x : Fin 512) : Prop :=
  ∃ a b c : Fin 3, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ edge x 0 a = true ∧
    edge x 1 b = true ∧ edge x 2 c = true
instance (x : Fin 512) : Decidable (target x) := by unfold target; infer_instance

def seed (x y : Fin 9) : Nat :=
  (([84,98,140,161,266,273] : List Nat).find? fun s =>
    s.testBit x.val && !s.testBit y.val).getD 0

def without (sample bit : Nat) : Nat := sample - (if sample.testBit bit then 2^bit else 0)
def sample (x y : Fin 9) (side : Bool) : Fin 512 :=
  Fin.ofNat 512 (without (seed x y) x.val + (if side then 2^y.val else 0))
def flipped (x : Fin 9) (s : Fin 512) : Fin 512 := Fin.ofNat 512 (s.val + 2^x.val)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
/-- Every distinct pair has a pivotal row for the first primary with either value of the
second. Hence an AND or OR of two primaries cannot be either primary's sole reader. -/
theorem each_distinct_pair_has_both_pivots :
    ∀ x y : Fin 9, x ≠ y → ∀ side : Bool,
      let s := sample x y side
      s.val.testBit x.val = false ∧ s.val.testBit y.val = side ∧
      ¬ target s ∧ target (flipped x s) := by
  decide
end ProofLantern.MatchingPivotal
