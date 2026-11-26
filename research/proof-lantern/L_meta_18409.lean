/- SPDX-License-Identifier: Apache-2.0. Exact researched witness; not an upstream submission. -/
import PEqualNP.Defs.Represents
namespace PEqualNP.Outside.L_meta_18409
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circuit : Circuit := ⟨[⟨.or, [0, 4]⟩,
 ⟨.or, [2, 8]⟩,
 ⟨.or, [5, 6]⟩,
 ⟨.or, [1, 10]⟩,
 ⟨.and, [9, 11]⟩,
 ⟨.or, [1, 8]⟩,
 ⟨.or, [7, 5]⟩,
 ⟨.or, [3, 14]⟩,
 ⟨.or, [2, 15]⟩,
 ⟨.and, [13, 16]⟩,
 ⟨.or, [12, 17]⟩], 18⟩
theorem hmono : Monotone2 circuit := by
  simp [Monotone2, circuit, Set.mem_insert_iff, Set.mem_singleton_iff]
theorem hcorrect : Represents (fun u v : Fin 4 => (6078 : ℕ).testBit (4 * u.val + v.val)) circuit :=
  by decide +kernel
end PEqualNP.Outside.L_meta_18409
theorem PEqualNP.Outside.L_meta_18409 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (6078 : ℕ).testBit (4 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_18409.circuit, PEqualNP.Outside.L_meta_18409.hmono,
    by decide, PEqualNP.Outside.L_meta_18409.hcorrect⟩
