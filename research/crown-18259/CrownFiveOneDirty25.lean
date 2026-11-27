import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.FiveOneDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 7) : Bool := decide (u ≠ v)

def witness : Circuit := ⟨[
  ⟨.or, [0,7]⟩,
  ⟨.or, [1,8]⟩,
  ⟨.or, [2,9]⟩,
  ⟨.or, [3,10]⟩,
  ⟨.or, [4,11]⟩,
  ⟨.or, [5,12]⟩,
  ⟨.or, [6,13]⟩,
  ⟨.or, [14,17]⟩,
  ⟨.or, [21,18]⟩,
  ⟨.or, [15,17]⟩,
  ⟨.or, [16,18]⟩,
  ⟨.or, [23,24]⟩,
  ⟨.and, [22,25]⟩,
  ⟨.or, [15,19]⟩,
  ⟨.and, [22,27]⟩,
  ⟨.or, [19,20]⟩,
  ⟨.and, [25,29]⟩,
  ⟨.or, [14,16]⟩,
  ⟨.and, [26,31]⟩,
  ⟨.or, [21,27]⟩,
  ⟨.or, [24,20]⟩,
  ⟨.and, [33,34]⟩,
  ⟨.or, [28,30]⟩,
  ⟨.or, [36,32]⟩,
  ⟨.or, [37,35]⟩], 38⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem bound : RepSizeAtMost graph 25 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · unfold Monotone2
    intro h hd
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · exact of_decide_eq_true (rfl : decide (Represents graph witness) = true)

end ProofLantern.Crown.FiveOneDirty
