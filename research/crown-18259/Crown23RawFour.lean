import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.RawFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 7) : Bool := decide (u ≠ v)

def witness : Circuit := ⟨[
  ⟨.or, [4,11]⟩,
  ⟨.or, [5,12]⟩,
  ⟨.or, [6,13]⟩,
  ⟨.or, [0,7]⟩,
  ⟨.or, [1,8]⟩,
  ⟨.or, [2,9]⟩,
  ⟨.or, [3,10]⟩,
  ⟨.or, [14,16]⟩,
  ⟨.or, [15,16]⟩,
  ⟨.or, [17,18]⟩,
  ⟨.or, [17,19]⟩,
  ⟨.or, [18,20]⟩,
  ⟨.or, [19,20]⟩,
  ⟨.or, [24,25]⟩,
  ⟨.or, [14,27]⟩,
  ⟨.or, [15,27]⟩,
  ⟨.and, [29,21]⟩,
  ⟨.and, [28,22]⟩,
  ⟨.and, [24,25]⟩,
  ⟨.and, [23,26]⟩,
  ⟨.or, [30,31]⟩,
  ⟨.or, [34,32]⟩,
  ⟨.or, [35,33]⟩], 36⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem bound : RepSizeAtMost graph 23 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · unfold Monotone2
    intro h hd
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · exact of_decide_eq_true (rfl : decide (Represents graph witness) = true)

end ProofLantern.Crown.RawFour
