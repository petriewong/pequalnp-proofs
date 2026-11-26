/- SPDX-License-Identifier: Apache-2.0. Three sorted triples, followed by median selection.
   Research archive; no upstream submission. -/
import PEqualNP.Defs.MetaComplexity
namespace PEqualNP.Outside.L_meta_18354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def circuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩,
 ⟨.and, [9, 2]⟩,
 ⟨.and, [3, 4]⟩,
 ⟨.and, [11, 5]⟩,
 ⟨.and, [6, 7]⟩,
 ⟨.and, [13, 8]⟩,
 ⟨.or, [0, 1]⟩,
 ⟨.and, [15, 2]⟩,
 ⟨.or, [9, 16]⟩,
 ⟨.or, [3, 4]⟩,
 ⟨.and, [18, 5]⟩,
 ⟨.or, [11, 19]⟩,
 ⟨.or, [6, 7]⟩,
 ⟨.and, [21, 8]⟩,
 ⟨.or, [13, 22]⟩,
 ⟨.or, [15, 2]⟩,
 ⟨.or, [18, 5]⟩,
 ⟨.or, [21, 8]⟩,
 ⟨.or, [10, 12]⟩,
 ⟨.or, [27, 14]⟩,
 ⟨.and, [17, 20]⟩,
 ⟨.or, [17, 20]⟩,
 ⟨.and, [30, 23]⟩,
 ⟨.or, [29, 31]⟩,
 ⟨.and, [24, 25]⟩,
 ⟨.and, [33, 26]⟩,
 ⟨.and, [28, 32]⟩,
 ⟨.or, [28, 32]⟩,
 ⟨.and, [36, 34]⟩,
 ⟨.or, [35, 37]⟩], 38⟩
theorem gateBasis : FanInTwo circuit := by
  simp [FanInTwo, circuit, Set.mem_insert_iff, Set.mem_singleton_iff]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem correct :
    ∀ x : Fin 9 → Bool, circuit.eval (List.ofFn x) =
      decide (5 ≤ (List.ofFn x).count true) := by decide +kernel
end PEqualNP.Outside.L_meta_18354
theorem PEqualNP.Outside.L_meta_18354 :
  PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => decide (5 ≤ (List.ofFn x).count true)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_18354.circuit, PEqualNP.Outside.L_meta_18354.gateBasis, by decide, PEqualNP.Outside.L_meta_18354.correct⟩
