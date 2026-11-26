import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.Represents
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CrownDiagonal

def wire (n i : Nat) : Nat := if i<n then i else i-n
def renameGate (n : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire n)⟩
def rename (n : Nat) (c : Circuit) : Circuit := ⟨c.gates.map (renameGate n),wire n c.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem append_bit (w : List Bool) (b : Bool) (i : Nat) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · have hle := Nat.le_of_not_gt h
    rw [List.getD_append_right _ _ _ _ hle,List.getD_eq_default _ _ hle]
    by_cases he : i = w.length
    · simp [he]
    · have hl : 1 ≤ i - w.length := by omega
      rw [ite_eq_right he,List.getD_eq_default _ _ (by simpa using hl)]

def Inv (n : Nat) (a b : List Bool) : Prop :=
  n ≤ a.length ∧ b.length = a.length + n ∧
    ∀ i, a.getD (wire n i) false = b.getD i false

theorem start (a : List Bool) : Inv a.length a (a++a) := by
  refine ⟨Nat.le_refl _,by simp,?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [wire, ite_eq_left hi, List.getD_append _ _ _ _ hi]
  · rw [wire, ite_eq_right hi, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]

theorem inv_step (n : Nat) (a b : List Bool) (hinv : Inv n a b) (g : Gate) :
    Inv n (step a (renameGate n g)) (step b g) := by
  refine ⟨by simpa [step] using Nat.le_trans hinv.1 (Nat.le_succ _),
     by simp [step,hinv.2.1,Nat.add_right_comm],?_⟩
  have hv : (g.inputs.map (wire n)).map (fun i => a.getD i false) =
      g.inputs.map (fun i => b.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hinv.2.2 i)
  intro i
  have hi : wire n i = a.length ↔ i = b.length := by
    have ha := hinv.1
    have hb := hinv.2.1
    unfold wire
    split <;> omega
  simp only [step, renameGate,hv,append_bit,hi,hinv.2.2]

theorem inv_fold (n : Nat) (gs : List Gate) (a b : List Bool) (hi : Inv n a b) :
    Inv n ((gs.map (renameGate n)).foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact hi
  | cons g gs ih => exact ih _ _ (inv_step n a b hi g)

theorem eval_diag (c : Circuit) (x : List Bool) :
    (rename x.length c).eval x = c.eval (x++x) :=
  (inv_fold _ c.gates x (x++x) (start x)).2.2 c.output

theorem rename_size (n : Nat) (c : Circuit) : (rename n c).size = c.size := by
  simp [rename,Circuit.size]

theorem rename_mono (n : Nat) (c : Circuit) (hc : Monotone2 c) : Monotone2 (rename n c) := by
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using hc v hv

end CrownDiagonal

namespace CrownDiagonal
def boundaryWireLE (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

theorem appendBoundaryRead (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i = l.length then b else l.getD i false := by
  by_cases hp : i < l.length
  · have hn : i ≠ l.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hp, hn]
  · have hn : l.length ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hn]
    by_cases he : i = l.length
    · simp [he]
    · have hs : 1 ≤ i - l.length := by omega
      have hout : l[i]? = none := List.getElem?_eq_none hn
      have hsingle : ([b] : List Bool)[i - l.length]? = none :=
        List.getElem?_eq_none (by simpa using hs)
      simp [hsingle, he, List.getD_eq_getElem?_getD, hout]

theorem boundaryOpMono (g : Gate) (h : g.op = .and ∨ g.op = .or)
    {x y : List Bool} (xy : boundaryWireLE x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) ≤
    g.op.eval (g.inputs.map fun i => y.getD i false) := by
  apply Bool.le_iff_imp.mpr
  intro yes
  rcases h with h | h
  · simp only [h,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true] at yes ⊢
    intro i hi
    exact Bool.le_iff_imp.mp (xy.2 i) (yes i hi)
  · simp only [h,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true] at yes ⊢
    obtain ⟨i, hi, hx⟩ := yes
    exact ⟨i,hi,Bool.le_iff_imp.mp (xy.2 i) hx⟩

def boundaryStep (a : List Bool) (g : Gate) : List Bool :=
  a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]

theorem boundaryStepMono (g : Gate) (h : g.op = .and ∨ g.op = .or)
    {x y : List Bool} (xy : boundaryWireLE x y) :
    boundaryWireLE (boundaryStep x g) (boundaryStep y g) := by
  constructor
  · simp [boundaryStep,xy.1]
  · intro i
    unfold boundaryStep
    rw [appendBoundaryRead,appendBoundaryRead,xy.1]
    by_cases hi : i = y.length
    · simpa [hi] using boundaryOpMono g h xy
    · simpa [hi] using xy.2 i

theorem boundaryFoldMono (gs : List Gate) (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {x y : List Bool} (xy : boundaryWireLE x y) :
    boundaryWireLE (gs.foldl boundaryStep x) (gs.foldl boundaryStep y) := by
  induction gs generalizing x y with
  | nil => exact xy
  | cons g tail ih =>
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) (boundaryStepMono g (h g (by simp)) xy)

theorem boundaryCircuitMono (T : Circuit) (h : Monotone2 T) (n : Nat) :
    Monotone (circuitFun n T) := by
  intro x y xy
  have inps : boundaryWireLE (List.ofFn x) (List.ofFn y) := by
    constructor
    · simp
    · intro i
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi)]
        simpa using xy ⟨i,hi⟩
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
  exact (boundaryFoldMono T.gates (fun g hg => by simpa using (h g hg).1) inps).2 T.output


end CrownDiagonal

namespace CrownDiagonal
open PEqualNP.Represents

theorem fn_le {n : Nat} (a b : Fin n → Bool) (hh : a ≤ b) :
    boundaryWireLE (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using hh ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

theorem append_le {a b c d : List Bool} (h : boundaryWireLE a b) (k : boundaryWireLE c d) :
    boundaryWireLE (a++c) (b++d) := by
  refine ⟨by simp [h.1,k.1],?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by rwa [←h.1])]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi),
        List.getD_append_right _ _ _ _ (by rw [←h.1]; exact Nat.le_of_not_gt hi),h.1]
    exact k.2 _

theorem eval_le (C : Circuit) (hm : Monotone2 C) {a b : List Bool} (h : boundaryWireLE a b) :
    C.eval a ≤ C.eval b :=
  (boundaryFoldMono C.gates (fun g hg => by simpa using (hm g hg).1) h).2 C.output

def hot {n : Nat} (u : Fin n) : Fin n → Bool := fun i => decide (i = u)

theorem hot_lo {n : Nat} (x : Fin n → Bool) (u : Fin n) (hu : x u = true) : hot u ≤ x := by
  intro i
  by_cases h : i = u
  · subst i; simp [hot,hu]
  · simp [hot,h]

theorem le_hot {n : Nat} (x : Fin n → Bool) (u : Fin n)
    (h : ∀ i, x i = true → i = u) : x ≤ hot u := by
  intro i
  cases e : x i
  · exact Bool.false_le _
  · simp [hot,h i e]

theorem crown_threshold (n s : Nat)
    (hr : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨⟨[],0⟩,by simp [Monotone2],by simp [Circuit.size],?_⟩
    intro x
    simp [Circuit.eval,Circuit.wires, List.ofFn_zero]
  obtain ⟨C,hm,hsize,hrep⟩ := hr
  refine ⟨rename n C, rename_mono n C hm, by rwa [rename_size],?_⟩
  intro x
  have diagEq : (rename n C).eval (List.ofFn x) = C.eval (List.ofFn x ++ List.ofFn x) := by
    simpa only [List.length_ofFn] using eval_diag C (List.ofFn x)
  rw [diagEq,List.count_ofFn]
  let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
  change C.eval (List.ofFn x ++ List.ofFn x) = decide (2 ≤ S.card)
  by_cases hc : 2 ≤ S.card
  · obtain ⟨u,hu,v,hv,hnuv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have huu : x u = true := (Finset.mem_filter.mp hu).2
    have hvv : x v = true := (Finset.mem_filter.mp hv).2
    have yes := hrep u v
    change C.eval (List.ofFn (hot u) ++ List.ofFn (hot v)) = decide (u ≠ v) at yes
    rw [decide_eq_true hnuv] at yes
    have hl := eval_le C hm (append_le (fn_le _ _ (hot_lo x u huu)) (fn_le _ _ (hot_lo x v hvv)))
    rw [yes] at hl
    rw [decide_eq_true hc]
    exact Bool.le_antisymm (Bool.le_true _) hl
  · have o : ∃ u : Fin n, x ≤ hot u := by
      by_cases he : ∃ u : Fin n, x u = true
      · obtain ⟨u,hu⟩ := he
        refine ⟨u,le_hot x u (fun i hi => ?_)⟩
        exact Finset.card_le_one.mp (by omega : S.card ≤ 1) i
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩) u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)
      · refine ⟨⟨0,Nat.zero_lt_of_ne_zero hn⟩,le_hot x _ (fun i hi => False.elim (he ⟨i,hi⟩))⟩
    obtain ⟨u,hu⟩ := o
    have no := hrep u u
    change C.eval (List.ofFn (hot u) ++ List.ofFn (hot u)) = decide (u ≠ u) at no
    simp only [ne_eq,not_true_eq_false,decide_false] at no
    have le := eval_le C hm (append_le (fn_le _ _ hu) (fn_le _ _ hu))
    rw [no] at le
    rw [decide_eq_false_iff_not.mpr hc]
    exact Bool.le_antisymm le (Bool.false_le _)

end CrownDiagonal

theorem ExactDesk18193 : (∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true)
) := CrownDiagonal.crown_threshold
