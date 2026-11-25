import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def boundaryRank (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Nat :=
  (Finset.univ.filter fun i => x i = f x).card

theorem boundaryRankDrop (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n)
    (hi : x i = f x) (hs : f (Function.update x i (!x i)) = f x) :
    boundaryRank f (Function.update x i (!x i)) < boundaryRank f x := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => x j = f x
  have hiS : i ∈ S := by simp [S, hi]
  have setEq :
      (Finset.univ.filter fun j => Function.update x i (!x i) j = f (Function.update x i (!x i))) = S.erase i := by
    simp only [hs]
    ext j
    by_cases e : j = i
    · subst j
      cases b : x i <;> simp [S, ← hi, b]
    · simp [S, e]
  unfold boundaryRank
  rw [setEq]
  exact Finset.card_erase_lt_of_mem hiS

theorem monotoneBoundaryGeneric (f g : (Fin n → Bool) → Bool) (mg : Monotone g)
    (agree : ∀ x, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) → g x = f x) :
    ∀ x, g x = f x := by
  classical
  have run : ∀ k : Nat, ∀ x, boundaryRank f x = k → g x = f x := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro x hx
      by_cases hb : ∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x
      · exact agree x hb
      · push Not at hb
        obtain ⟨i,bi,stays⟩ := hb
        let y := Function.update x i (!x i)
        have eq : g y = f y := ih (boundaryRank f y) (by rw [← hx]; exact boundaryRankDrop f x i bi stays) y rfl
        cases fcase : f x
        · have le : x ≤ y := by
            intro j
            by_cases e : j = i
            · subst j
              simp [y, bi, fcase]
            · simp [y, Function.update_of_ne e]
          have lr := mg le
          rw [eq, stays, fcase] at lr
          exact Bool.le_antisymm lr (Bool.false_le _)
        · have le : y ≤ x := by
            intro j
            by_cases e : j = i
            · subst j
              simp [y, bi, fcase]
            · simp [y, Function.update_of_ne e]
          have lr := mg le
          rw [eq, stays, fcase] at lr
          exact Bool.le_antisymm (Bool.le_true _) lr
  intro x
  exact run _ x rfl



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

theorem boundaryForCircuit (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Circuit)
    (_mf : Monotone f) (mt : Monotone2 T)
    (agree : ∀ x, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) →
      circuitFun n T x = f x) : ∀ x, circuitFun n T x = f x :=
  monotoneBoundaryGeneric f (circuitFun n T) (boundaryCircuitMono T mt n) agree



theorem PEqualNP.Outside.L_meta_17376 : (∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), Monotone x2 → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x6 x7 = x2 x6 → x2 (Function.update x6 x7 !x6 x7) ≠ x2 x6) → PEqualNP.MetaComplexity.circuitFun x1 x3 x6 = x2 x6) → ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x7 = x2 x7) := boundaryForCircuit
