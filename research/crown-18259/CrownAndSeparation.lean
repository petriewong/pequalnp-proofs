import PEqualNP.Defs.Represents
import Mathlib.Data.Fintype.BigOperators

namespace ProofLantern.Crown.First
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def bitAt (x : List Bool) (i : Nat) : Bool := x.getD i false

def runGate (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (bitAt x))

def push (x : List Bool) (g : Gate) : List Bool := x ++ [runGate x g]

private theorem at_push (x : List Bool) (g : Gate) (i : Nat) :
    bitAt (push x g) i = if i < x.length then bitAt x i else if i = x.length then runGate x g else false := by
  unfold push bitAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rw [List.getD_eq_getElem?_getD]
  · split
    · rename_i hi he
      simp [he]
    · rename_i hi he
      have q : i - x.length ≠ 0 := by omega
      simp [q]

private theorem legal_op (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using h

def coverage (p a b : List Bool) : Prop :=
  p.length = a.length ∧ p.length = b.length ∧
  ∀ i, bitAt p i = true → bitAt a i = true ∨ bitAt b i = true

def crosses (a b : List Bool) (g : Gate) : Prop :=
  g.op = GateOp.and ∧ ∃ i ∈ g.inputs, ∃ j ∈ g.inputs,
    bitAt a i = true ∧ bitAt b i = false ∧
    bitAt b j = true ∧ bitAt a j = false

private theorem crosses_when_new (g : Gate) (p a b : List Bool)
    (legal : g.op = GateOp.and ∨ g.op = GateOp.or) (h : coverage p a b)
    (xy : runGate p g = true) (xa : runGate a g = false) (xb : runGate b g = false) :
    crosses a b g := by
  rcases legal with isAnd|isOr
  · refine ⟨isAnd, ?_⟩
    have pred {r : List Bool} :
        runGate r g = true ↔ (∀ i ∈ g.inputs, bitAt r i = true) := by
      simp only [runGate,isAnd,GateOp.eval,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
    have getFalse (r : List Bool) (c : runGate r g = false) :
        ∃ i ∈ g.inputs, bitAt r i = false := by
      by_contra hh
      have t : runGate r g = true := pred.mpr (by
        intro i gi
        cases he : bitAt r i
        · exact (hh ⟨i,gi,he⟩).elim
        · rfl)
      exact Bool.noConfusion (c.symm.trans t)
    obtain ⟨i,hi,bi⟩ := getFalse b xb
    obtain ⟨j,hj,aj⟩ := getFalse a xa
    have pi := h.2.2 i (pred.mp xy i hi)
    have pj := h.2.2 j (pred.mp xy j hj)
    exact ⟨i,hi,j,hj,by simpa [bi] using pi,bi,by simpa [aj] using pj,aj⟩
  · have pred {r : List Bool} :
        runGate r g = true ↔ (∃ i ∈ g.inputs, bitAt r i = true) := by
      simp only [runGate,isOr,GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
    obtain ⟨i,hi,ip⟩ := pred.mp xy
    rcases h.2.2 i ip with ia|ib
    · exact (Bool.noConfusion (xa.symm.trans (pred.mpr ⟨i,hi,ia⟩)) : False).elim
    · exact (Bool.noConfusion (xb.symm.trans (pred.mpr ⟨i,hi,ib⟩)) : False).elim

private theorem push_cover_or_cross (g : Gate) (p a b : List Bool)
    (legal : g.op = GateOp.and ∨ g.op = GateOp.or) (h : coverage p a b) :
    coverage (push p g) (push a g) (push b g) ∨ crosses a b g := by
  by_cases x : runGate p g = true → runGate a g = true ∨ runGate b g = true
  · left
    refine ⟨by simpa [push] using h.1, by simpa [push] using h.2.1, ?_⟩
    intro i
    rw [at_push,at_push,at_push,← h.1,← h.2.1]
    split
    · exact h.2.2 i
    · split
      · exact x
      · simp
  · right
    cases hp : runGate p g <;> cases ha : runGate a g <;> cases hb : runGate b g <;> simp_all
    exact crosses_when_new g p a b legal h hp ha hb

/-- On arbitrary legal AND/OR circuits, if a paired input can produce a truth
that neither singleton produces, some actual AND gate has oppositely exclusive operands
on the singleton evaluations at that prefix. No assumption on layers or on output index. -/
theorem fold_cover_or_cross (gs : List Gate) (p a b : List Bool)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : coverage p a b) :
    coverage (gs.foldl push p) (gs.foldl push a) (gs.foldl push b) ∨
      ∃ pre g post, gs = pre ++ g :: post ∧
      crosses (pre.foldl push a) (pre.foldl push b) g := by
  induction gs generalizing p a b with
  | nil => exact Or.inl h
  | cons first tail ih =>
    rcases push_cover_or_cross first p a b (legal first (List.mem_cons_self ..)) h with step|hit
    · rcases ih (push p first) (push a first) (push b first)
        (fun g hg => legal g (List.mem_cons_of_mem _ hg)) step with good|result
      · exact Or.inl good
      · obtain ⟨pre,g,post,shape,x⟩ := result
        exact Or.inr ⟨first::pre,g,post,by simp [shape],x⟩
    · exact Or.inr ⟨[],first,tail,rfl,hit⟩

theorem actual_cross (C : Circuit) (p a b : List Bool)
    (legal : Monotone2 C) (h : coverage p a b)
    (yes : C.eval p = true) (noa : C.eval a = false) (nob : C.eval b = false) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧
      crosses (pre.foldl push a) (pre.foldl push b) g := by
  rcases fold_cover_or_cross C.gates p a b (fun g hg => legal_op g (legal g hg).1) h with good|hit
  · have out : C.eval a = true ∨ C.eval b = true := good.2.2 C.output yes
    simp [noa,nob] at out
  · exact hit


def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def andCount (gs : List Gate) : Nat := (gs.filter (fun g => isAnd g.op)).length

def andCode (x : List Bool) : List Gate → List Bool
  | [] => []
  | g :: gs =>
    let tail := andCode (push x g) gs
    if isAnd g.op then bitAt x (g.inputs.headD 0) :: tail else tail

theorem andCode_len (x : List Bool) (gs : List Gate) :
    (andCode x gs).length = andCount gs := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [andCode,andCount,List.filter_cons]
    split <;> simp [ih,andCount]

private theorem crosses_head (a b : List Bool) (g : Gate) (h : crosses a b g)
    (fan : g.inputs.length ≤ 2) :
    bitAt a (g.inputs.headD 0) ≠ bitAt b (g.inputs.headD 0) := by
  obtain ⟨_,i,hi,j,hj,ai,bi,bj,aj⟩ := h
  have ne : i ≠ j := by intro e; subst j; simp [ai] at aj
  cases hs : g.inputs with
  | nil => simp [hs] at hi
  | cons h t =>
    have v : i = h ∨ j = h := by
      cases t with
      | nil => simp [hs] at hi hj; exact Or.inl hi
      | cons k t =>
        have z : t = [] := by simpa [hs] using fan
        subst t
        simp [hs] at hi hj
        rcases hi with rfl|rfl
        · exact Or.inl rfl
        · rcases hj with rfl|rfl
          · exact Or.inr rfl
          · exact (ne rfl).elim
    rcases v with rfl|rfl
    · simp [ai,bi]
    · simp [aj,bj]

theorem crossed_codes (pre : List Gate) (g : Gate) (post : List Gate)
    (a b : List Bool)
    (h : crosses (pre.foldl push a) (pre.foldl push b) g)
    (fan : g.inputs.length ≤ 2) :
    andCode a (pre ++ g :: post) ≠ andCode b (pre ++ g :: post) := by
  induction pre generalizing a b with
  | nil =>
    have head := crosses_head a b g h fan
    have yes : isAnd g.op = true := by simp [h.1,isAnd]
    intro eq
    have shaped : bitAt a (g.inputs.headD 0) :: andCode (push a g) post =
        bitAt b (g.inputs.headD 0) :: andCode (push b g) post := by
      simpa [andCode,yes] using eq
    exact head (List.cons.inj shaped).1
  | cons f pre ih =>
    have ne := ih (push a f) (push b f) h
    intro eq
    by_cases ha : isAnd f.op = true
    · simp only [List.cons_append,andCode,ha,ite_true,List.cons.injEq] at eq
      exact ne eq.2
    · simp only [List.cons_append,andCode,ha] at eq
      exact ne eq

def oneMark {n : Nat} (u : Fin n) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u))

def twoMarks {n : Nat} (u v : Fin n) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))

private theorem mark_get {n : Nat} (f : Fin n → Bool) (i : Nat) :
    bitAt (List.ofFn f) i = if hi : i < n then f ⟨i,hi⟩ else false := by
  unfold bitAt
  simp only [List.getD_eq_getElem?_getD]
  split
  · rename_i hi
    have wh : i < (List.ofFn f).length := by simp [hi]
    simp [hi]
  · rename_i hi
    have wh : (List.ofFn f).length ≤ i := by simp; omega
    simp [List.getElem?_eq_none wh]

theorem marks_covered {n : Nat} (u v : Fin n) : coverage (twoMarks u v) (oneMark u) (oneMark v) := by
  refine ⟨by simp [oneMark,twoMarks],by simp [oneMark,twoMarks],?_⟩
  intro i
  simp only [oneMark,twoMarks,mark_get]
  split <;> simp

def indexCode (C : Circuit) {n : Nat} (u : Fin n) :
    Fin (andCount C.gates) → Bool :=
  fun i => bitAt (andCode (oneMark u) C.gates) i.val

/-- The AND gates suffice to label all n input names distinctly, regardless of interleaving.
In particular a threshold-two circuit for seven distinct names has at least three AND gates. -/
theorem pair_separation_and_bound {n : Nat} (C : Circuit) (legal : Monotone2 C)
    (single : ∀ u : Fin n, C.eval (oneMark u) = false)
    (pairs : ∀ u v : Fin n, u ≠ v → C.eval (twoMarks u v) = true) :
    n ≤ 2 ^ andCount C.gates := by
  have inj : Function.Injective (indexCode C (n := n)) := by
    intro u v eq
    by_contra diff
    obtain ⟨pre,g,post,layout,x⟩ :=
      actual_cross C (twoMarks u v) (oneMark u) (oneMark v) legal (marks_covered u v)
        (pairs u v diff) (single u) (single v)
    have gm : g ∈ C.gates := by simp [layout]
    have ne := crossed_codes pre g post (oneMark u) (oneMark v) x (legal g gm).2
    apply ne
    rw [←layout]
    apply List.ext_getElem (by rw [andCode_len,andCode_len])
    intro i hi hj
    have hfin : i < andCount C.gates := by simpa only [andCode_len] using hi
    have vv := congrFun eq ⟨i,hfin⟩
    simpa [indexCode,bitAt,List.getD_eq_getElem?_getD,List.getD_getElem?,hi,hj] using vv
  have h := Fintype.card_le_of_injective _ inj
  simpa [Fintype.card_fun,Fintype.card_bool] using h


theorem at_least_three_and (C : Circuit) (legal : Monotone2 C)
    (single : ∀ u : Fin 7, C.eval (oneMark u) = false)
    (pairs : ∀ u v : Fin 7, u ≠ v → C.eval (twoMarks u v) = true) :
    3 ≤ andCount C.gates := by
  have bound := pair_separation_and_bound C legal single pairs
  by_contra! notThree
  have finite : ∀ k : Fin 3, ¬ (7 : Nat) ≤ 2 ^ k.val := by decide
  exact finite ⟨andCount C.gates,notThree⟩ bound

end ProofLantern.Crown.First
