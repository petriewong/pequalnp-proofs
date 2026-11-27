import PEqualNP.Defs.Represents
namespace ProofLantern.Matching3
open PEqualNP.CircuitLowerBounds

def bits (x : Fin 512) : List Bool :=
  List.ofFn fun i : Fin 9 => x.val.testBit i.val

def edge (x : Fin 512) (i j : Fin 3) : Bool := x.val.testBit (3*i.val + j.val)

def target (x : Fin 512) : Prop :=
  ∃ a b c : Fin 3, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ edge x 0 a = true ∧ edge x 1 b = true ∧ edge x 2 c = true

instance (x : Fin 512) : Decidable (target x) := by unfold target; infer_instance

def witness : Circuit :=
  ⟨[⟨.and,[4,8]⟩, ⟨.and,[5,7]⟩, ⟨.or,[9,10]⟩, ⟨.and,[0,11]⟩,
    ⟨.and,[3,8]⟩, ⟨.and,[5,6]⟩, ⟨.or,[13,14]⟩, ⟨.and,[1,15]⟩,
    ⟨.and,[3,7]⟩, ⟨.and,[4,6]⟩, ⟨.or,[17,18]⟩, ⟨.and,[2,19]⟩,
    ⟨.or,[12,16]⟩, ⟨.or,[20,21]⟩], 22⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
/-- A 14-gate upper bound for the research model; it does not meet the public 13-gate target. -/
theorem witness_checked : PEqualNP.TopForm.IsAO2 9 witness ∧ witness.size = 14 ∧
    ∀ bits9 : Fin 512, witness.eval (bits bits9) = true ↔ target bits9 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

end ProofLantern.Matching3
