import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Fin.Basic
open PEqualNP.CircuitLowerBounds
namespace ProofLanternOrJoin

def same (x y z : List Bool) : Prop :=
  x.length = y.length ∧ x.length = z.length ∧
  ∀ i, z.getD i false = (x.getD i false || y.getD i false)

theorem append_bit {α : Type} (w : List α) (b d : α) (i : Nat) :
    (w ++ [b]).getD i d = if i = w.length then b else w.getD i d := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · have hle := Nat.le_of_not_gt h
    rw [List.getD_append_right _ _ _ _ hle,List.getD_eq_default _ _ hle]
    by_cases he : i = w.length
    · simp [he]
    · have hl : 1 ≤ i - w.length := by omega
      rw [ite_eq_right he,List.getD_eq_default _ _ (by simpa using hl)]

theorem any_join (is : List Nat) (x y z : List Bool) (h : same x y z) :
    (is.any fun i => z.getD i false) =
     ((is.any fun i => x.getD i false) || (is.any fun i => y.getD i false)) := by
  induction is with
  | nil => rfl
  | cons i tail ih =>
    simp only [List.any_cons,h.2.2 i,ih]
    cases x.getD i false <;> cases y.getD i false <;>
      cases (tail.any fun i => x.getD i false) <;> cases (tail.any fun i => y.getD i false) <;> rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_join (x y z : List Bool) (h : same x y z) (g : Gate) (hg : g.op = .or) :
    same (step x g) (step y g) (step z g) := by
  refine ⟨by simp [step,h.1], by simp [step,h.2.1],?_⟩
  intro i
  unfold step
  rw [append_bit,append_bit,append_bit,←h.1,←h.2.1]
  by_cases hi : i = x.length
  · simp only [ite_eq_left hi,hg,GateOp.eval,List.any_map,Function.comp_def,id_eq]
    exact any_join g.inputs x y z h
  · simpa only [ite_eq_right hi] using h.2.2 i

theorem fold_join (gs : List Gate) (x y z : List Bool) (h : same x y z)
    (og : ∀ g ∈ gs, g.op = .or) :
    same (gs.foldl step x) (gs.foldl step y) (gs.foldl step z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ _ _ (step_join x y z h g (og g (by simp))) (fun h hh => og h (List.mem_cons_of_mem _ hh))

theorem eval_or_join (C : Circuit) (x y z : List Bool) (h : same x y z)
    (og : ∀ g ∈ C.gates, g.op = .or) :
    C.eval z = (C.eval x || C.eval y) :=
  (fold_join C.gates x y z h og).2.2 C.output

end ProofLanternOrJoin

namespace ProofLanternOrJoin

theorem inputs_join (n : Nat) (a b : Fin n → Bool) :
    same (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h),
        List.getD_eq_getElem _ _ (by simpa using h),
        List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
  · simp [Nat.le_of_not_gt h]

theorem only_or (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hn : ¬∃ i : Fin C.gates.length, (C.gates.get i).op = .and) :
    ∀ g ∈ C.gates, g.op = .or := by
  intro g hg
  have ht : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
  rcases ht with ha | ho
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    exact False.elim (hn ⟨i,by rw [hi]; exact ha⟩)
  · exact ho

theorem separate_any {n : Nat} (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hc : ∀ g ∈ C.gates, g.op = .or) (a b : Fin n → Bool)
    (h1 : f a = false) (h2 : f b = false) (h3 : f (fun i => a i || b i) = true) :
    ∃ x, C.eval (List.ofFn x) ≠ f x := by
  by_contra h
  have eq (x : Fin n → Bool) : C.eval (List.ofFn x) = f x := by
    by_contra e
    exact h ⟨x,e⟩
  have eqJoin := eval_or_join C _ _ _ (inputs_join n a b) hc
  rw [eq,eq,eq,h1,h2,h3] at eqJoin
  contradiction

end ProofLanternOrJoin

theorem ExactDesk18167 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)))
) := by
  intro C hm _ hn
  apply ProofLanternOrJoin.separate_any C _ (ProofLanternOrJoin.only_or C hm hn) (fun i => decide (i = 0)) (fun i => decide (i = 1)) <;> decide
