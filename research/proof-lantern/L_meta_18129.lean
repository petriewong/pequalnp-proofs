import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace CrownWitnessFive

def c : Circuit := ⟨[
  ⟨.or,[0,5]⟩,⟨.or,[1,6]⟩,⟨.or,[2,7]⟩,⟨.or,[3,8]⟩,⟨.or,[4,9]⟩,
  ⟨.or,[10,11]⟩,⟨.or,[15,12]⟩,⟨.or,[16,13]⟩,
  ⟨.and,[10,11]⟩,⟨.and,[15,12]⟩,⟨.and,[16,13]⟩,⟨.and,[17,14]⟩,
  ⟨.or,[18,19]⟩,⟨.or,[22,20]⟩,⟨.or,[23,21]⟩],24⟩

theorem good : Monotone2 c := by
  intro g hg
  simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem size_ok : c.size ≤ 15 := by decide

def one (u v : Fin 5) : List Bool :=
  List.ofFn (fun i : Fin 5 => decide (i = u)) ++ List.ofFn (fun i : Fin 5 => decide (i = v))

theorem correct : ∀ u v : Fin 5, c.eval (one u v) = decide (u ≠ v) := by decide

end CrownWitnessFive

theorem ExactDesk18129 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (u ≠ v)) 15
) := ⟨CrownWitnessFive.c,CrownWitnessFive.good,CrownWitnessFive.size_ok,CrownWitnessFive.correct⟩
