import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.FivePure
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
  ⟨.or, [14,15]⟩,
  ⟨.or, [21,16]⟩,
  ⟨.or, [22,17]⟩,
  ⟨.or, [23,19]⟩,
  ⟨.or, [18,20]⟩,
  ⟨.and, [24,25]⟩,
  ⟨.or, [23,18]⟩,
  ⟨.or, [19,20]⟩,
  ⟨.and, [27,28]⟩,
  ⟨.and, [14,15]⟩,
  ⟨.and, [16,21]⟩,
  ⟨.and, [17,22]⟩,
  ⟨.or, [26,29]⟩,
  ⟨.or, [33,30]⟩,
  ⟨.or, [34,31]⟩,
  ⟨.or, [35,32]⟩], 36⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem bound : RepSizeAtMost graph 23 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · unfold Monotone2
    intro h hd
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · exact of_decide_eq_true (rfl : decide (Represents graph witness) = true)

end ProofLantern.Crown.FivePure
