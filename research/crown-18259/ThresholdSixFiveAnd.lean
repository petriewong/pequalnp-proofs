import PEqualNP.Defs.Represents
namespace ProofLantern.ThresholdSix.FiveAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.or,[2,5]⟩,⟨.and,[3,6]⟩,⟨.and,[2,5]⟩,⟨.or,[3,6]⟩,⟨.or,[4,7]⟩,⟨.and,[11,12]⟩,⟨.or,[8,9]⟩,⟨.or,[10,11]⟩,⟨.or,[13,14]⟩,⟨.or,[4,15]⟩,⟨.and,[16,17]⟩], 18⟩
def monoMark (a : Fin 6) : List Bool := List.ofFn fun i => decide (i = a)
def dualMark (a b : Fin 6) : List Bool := List.ofFn fun i => decide (i = a ∨ i = b)
set_option maxHeartbeats 4000000 in
theorem bound : Monotone2 witness ∧ witness.size = 13 ∧
    (witness.gates.filter (fun g => match g.op with | .and => true | _ => false)).length = 5 ∧
    (∀ a, witness.eval (monoMark a) = false) ∧
    (∀ a b, a ≠ b → witness.eval (dualMark a b) = true) := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  unfold Monotone2
  intro o h
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
end ProofLantern.ThresholdSix.FiveAND
