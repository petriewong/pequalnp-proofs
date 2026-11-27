import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.Read
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def bitAt (x : List Bool) (i : Nat) : Bool := x.getD i false

def before (x y : List Bool) (skip : Option Nat) : Prop :=
  x.length = y.length ∧ ∀ i, some i ≠ skip → bitAt x i = true → bitAt y i = true

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

private theorem gate_mono (g : Gate) (x y : List Bool)
    (op : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i ∈ g.inputs, bitAt x i = true → bitAt y i = true) :
    runGate x g = true → runGate y g = true := by
  rcases op with hA|hO
  · simp only [runGate,hA,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true]
    exact fun r i hi => h i hi (r i hi)
  · simp only [runGate,hO,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true]
    rintro ⟨i,hi,r⟩
    exact ⟨i,hi,h i hi r⟩

private theorem push_mono (g : Gate) (x y : List Bool) (skip : Option Nat)
    (h : before x y skip) (gh : runGate x g = true → runGate y g = true) :
    before (push x g) (push y g) skip := by
  refine ⟨by simpa [push] using h.1, ?_⟩
  intro i hs
  rw [at_push,at_push,← h.1]
  split
  · exact h.2 i hs
  · split
    · exact gh
    · simp

/-- Comparing evaluations while one primary input is ignored.
Every gate that does read the exceptional input must supply a local implication. -/
theorem fold_order (gs : List Gate) (x y : List Bool) (skip : Option Nat)
    (initial : before x y skip)
    (le : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (exception : ∀ g ∈ gs, ∀ a b,
      before a b skip → (∃ i ∈ g.inputs, some i = skip) →
      runGate a g = true → runGate b g = true) :
    before (gs.foldl push x) (gs.foldl push y) skip := by
  induction gs generalizing x y with
  | nil => exact initial
  | cons g gs ih =>
    apply ih (push x g) (push y g)
    · apply push_mono g x y skip initial
      by_cases other : ∃ i ∈ g.inputs, some i = skip
      · exact exception g (List.mem_cons_self ..) x y initial other
      · apply gate_mono g x y (le g (List.mem_cons_self ..))
        intro i hi
        exact initial.2 i (fun hh => other ⟨i,hi,hh⟩)
    · intro g hg
      exact le g (List.mem_cons_of_mem _ hg)
    · intro g hg
      exact exception g (List.mem_cons_of_mem _ hg)

theorem general_order (C : Circuit) (m : Monotone2 C) (x y : List Bool)
    (h : before x y none) : C.eval x = true → C.eval y = true := by
  have b := fold_order C.gates x y none h (fun g mem => legal_op g (m g mem).1)
    (by rintro g hg a b ab ⟨i,hi,hs⟩; contradiction)
  exact b.2 C.output (by simp)

theorem no_read_order (C : Circuit) (m : Monotone2 C) (x y : List Bool) (i : Nat)
    (h : before x y (some i)) (hout : C.output ≠ i)
    (omits : ∀ g ∈ C.gates, i ∉ g.inputs) : C.eval x = true → C.eval y = true := by
  have b := fold_order C.gates x y (some i) h (fun g mem => legal_op g (m g mem).1)
    (by
      rintro g hg a b ab ⟨j,hj,hs⟩
      have eq : j = i := Option.some.inj hs
      exact (omits g hg (eq ▸ hj)).elim)
  exact b.2 C.output (by simpa using hout)


def crown (u v : Fin 7) : Bool := decide (u ≠ v)

def row (u v : Fin 7) : List Bool := oneEach u v

@[simp] theorem row_len (u v : Fin 7) : (row u v).length = 14 := by
  simp [row,oneEach]

theorem row_outside (u v : Fin 7) (i : Nat) (h : 14 ≤ i) : bitAt (row u v) i = false := by
  have ge : (row u v).length ≤ i := by simpa using h
  simp [bitAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none ge]

set_option maxHeartbeats 4000000 in
private theorem read_cases :
    ∀ (i : Fin 14), ∃ (u v d d0 : Fin 7), u ≠ v ∧ bitAt (row d0 d0) i.val = true ∧
      ∀ (j : Fin 14), j ≠ i → bitAt (row u v) j.val = true → bitAt (row d d) j.val = true := by
  decide

/-- Every primary must actually appear among the inputs of a gate, not merely as the output.
The proof uses only one-row/one-column promised outputs and monotonicity. -/
theorem every_primary_read (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (i : Fin 14) : ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  obtain ⟨u,v,d,d0,uv,diag,ord⟩ := read_cases i
  have off : C.eval (row u v) = true := by simpa [row,crown,uv] using h u v
  have no : C.eval (row d d) = false := by simpa [row,crown] using h d d
  have out0 : C.eval (row d0 d0) = false := by simpa [row,crown] using h d0 d0
  have out : C.output ≠ i.val := by
    intro hh
    have ex : C.eval (row d0 d0) = true := by
      rw [Circuit.eval,hh]
      have hn : i.val < (row d0 d0).length := by simp [i.isLt]
      change bitAt (C.gates.foldl push (row d0 d0)) i.val = true
      have aux (G : List Gate) (x : List Bool) (hx : i.val < x.length) :
          bitAt (G.foldl push x) i.val = bitAt x i.val := by
        induction G generalizing x with
        | nil => rfl
        | cons a b ih =>
          change bitAt (b.foldl push (push x a)) i.val = _
          rw [ih _ (by simp [push]; omega)]
          simp [at_push,hx]
      rw [aux _ _ hn]
      exact diag
    exact Bool.noConfusion (out0.symm.trans ex)
  by_contra bad
  have absence : ∀ g ∈ C.gates, i.val ∉ g.inputs := by
    intro g gm gi
    exact bad ⟨g,gm,gi⟩
  have rel : before (row u v) (row d d) (some i.val) := by
    refine ⟨by simp, ?_⟩
    intro j jn jt
    by_cases jj : j < 14
    · exact ord ⟨j,jj⟩ (by intro eq; apply jn; cases eq; rfl) jt
    · rw [row_outside u v j (by omega)] at jt
      contradiction
  exact Bool.noConfusion (no.symm.trans (no_read_order C m _ _ i.val rel out absence off))


theorem fold_order_right (gs : List Gate) (x y : List Bool) (i k : Nat)
    (initial : before x y (some i)) (hk : k < y.length) (active : bitAt y k = true)
    (le : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (exception : ∀ g ∈ gs, ∀ a b, before a b (some i) → bitAt b k = true →
      i ∈ g.inputs → runGate a g = true → runGate b g = true) :
    before (gs.foldl push x) (gs.foldl push y) (some i) := by
  induction gs generalizing x y with
  | nil => exact initial
  | cons g gs ih =>
    apply ih (push x g) (push y g)
    · apply push_mono g x y _ initial
      by_cases other : i ∈ g.inputs
      · exact exception g (List.mem_cons_self ..) x y initial active other
      · apply gate_mono g x y (le g (List.mem_cons_self ..))
        intro j hj
        exact initial.2 j (by intro eq; exact other (Option.some.inj eq ▸ hj))
    · simp [push]; omega
    · simpa [at_push,hk] using active
    · intro g hg
      exact le g (List.mem_cons_of_mem _ hg)
    · intro g hg
      exact exception g (List.mem_cons_of_mem _ hg)

def left (u : Fin 7) : Fin 14 := ⟨u.val,by omega⟩
def right (v : Fin 7) : Fin 14 := ⟨7+v.val,by omega⟩

set_option maxHeartbeats 4000000 in
private theorem cross_left_cases :
    ∀ u v : Fin 7, u ≠ v →
      bitAt (row v v) (right v).val = true ∧
      ∀ j : Fin 14, j ≠ left u → bitAt (row u v) j.val = true → bitAt (row v v) j.val = true := by
  decide

set_option maxHeartbeats 4000000 in
private theorem cross_right_cases :
    ∀ u v : Fin 7, u ≠ v →
      bitAt (row u u) (left u).val = true ∧
      ∀ j : Fin 14, j ≠ right v → bitAt (row u v) j.val = true → bitAt (row u u) j.val = true := by
  decide

private theorem no_raw_output (C : Circuit) (h : Represents crown C) (i : Fin 14) :
    C.output ≠ i.val := by
  obtain ⟨_,_,_,d,_,diag,_⟩ := read_cases i
  intro out
  have bad : C.eval (row d d) = false := by simpa [row,crown] using h d d
  rw [Circuit.eval, out] at bad
  change bitAt (C.gates.foldl push (row d d)) i.val = false at bad
  have aux (G : List Gate) (x : List Bool) (hx : i.val < x.length) :
      bitAt (G.foldl push x) i.val = bitAt x i.val := by
    induction G generalizing x with
    | nil => rfl
    | cons a b ih =>
      change bitAt (b.foldl push (push x a)) i.val = _
      rw [ih _ (by simp [push]; omega)]
      simp [at_push,hx]
  rw [aux _ _ (by simp [i.isLt]), diag] at bad
  contradiction

private theorem make_order (u v d : Fin 7) (i : Fin 14)
    (ob : ∀ j : Fin 14, j ≠ i → bitAt (row u v) j.val = true → bitAt (row d d) j.val = true) :
    before (row u v) (row d d) (some i.val) := by
  refine ⟨by simp, ?_⟩
  intro j jn jt
  by_cases jj : j < 14
  · exact ob ⟨j,jj⟩ (by intro eq; apply jn; cases eq; rfl) jt
  · rw [row_outside u v j (by omega)] at jt
    contradiction

private theorem crossed_or_general (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v d : Fin 7) (i k : Fin 14) (diff : u ≠ v)
    (same : bitAt (row d d) k.val = true)
    (ob : ∀ j : Fin 14, j ≠ i → bitAt (row u v) j.val = true → bitAt (row d d) j.val = true)
    (allReaders : ∀ g ∈ C.gates, i.val ∈ g.inputs → g.op = GateOp.or ∧ k.val ∈ g.inputs) : False := by
  have beforeOut := fold_order_right C.gates (row u v) (row d d) i.val k.val (make_order _ _ _ _ ob)
    (by simp [k.isLt]) same (fun g mem => legal_op g (m g mem).1)
    (by
      intro g hg a b _ present heed _
      obtain ⟨ho,hk⟩ := allReaders g hg heed
      simp only [runGate,ho,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true]
      exact ⟨k.val,hk,present⟩)
  have firstTrue : C.eval (row u v) = true := by simpa [row,crown,diff] using h u v
  have secondFalse : C.eval (row d d) = false := by simpa [row,crown] using h d d
  have secondTrue : C.eval (row d d) = true :=
    beforeOut.2 C.output (by simpa using no_raw_output C h i) firstTrue
  exact Bool.noConfusion (secondFalse.symm.trans secondTrue)

/-- An off-diagonal cross-OR cannot be the only way a row input enters the circuit. -/
theorem not_only_crossed_left (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v : Fin 7) (diff : u ≠ v)
    (allReaders : ∀ g ∈ C.gates, (left u).val ∈ g.inputs →
      g.op = GateOp.or ∧ (right v).val ∈ g.inputs) : False := by
  obtain ⟨active,ord⟩ := cross_left_cases u v diff
  exact crossed_or_general C m h u v v (left u) (right v) diff active ord allReaders

/-- The symmetric statement for a column input. -/
theorem not_only_crossed_right (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v : Fin 7) (diff : u ≠ v)
    (allReaders : ∀ g ∈ C.gates, (right v).val ∈ g.inputs →
      g.op = GateOp.or ∧ (left u).val ∈ g.inputs) : False := by
  obtain ⟨active,ord⟩ := cross_right_cases u v diff
  exact crossed_or_general C m h u v u (right v) (left u) diff active ord allReaders


theorem fold_order_pinned_left (gs : List Gate) (x y fixed : List Bool) (i : Nat)
    (initial : before x y (some i)) (hx : fixed.length ≤ x.length)
    (keep : ∀ j < fixed.length, bitAt x j = bitAt fixed j)
    (le : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (exception : ∀ g ∈ gs, ∀ a b, before a b (some i) →
      (∀ j < fixed.length, bitAt a j = bitAt fixed j) →
      i ∈ g.inputs → runGate a g = true → runGate b g = true) :
    before (gs.foldl push x) (gs.foldl push y) (some i) := by
  induction gs generalizing x y with
  | nil => exact initial
  | cons g gs ih =>
    apply ih (push x g) (push y g)
    · apply push_mono g x y _ initial
      by_cases other : i ∈ g.inputs
      · exact exception g (List.mem_cons_self ..) x y initial keep other
      · apply gate_mono g x y (le g (List.mem_cons_self ..))
        intro j hj
        exact initial.2 j (by intro eq; exact other (Option.some.inj eq ▸ hj))
    · simp [push]; omega
    · intro j hj
      have hh : j < x.length := by omega
      simp [at_push,hh,keep j hj]
    · intro g hg
      exact le g (List.mem_cons_of_mem _ hg)
    · intro g hg
      exact exception g (List.mem_cons_of_mem _ hg)

private theorem live_reader_of_offdiag (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v d : Fin 7) (i : Fin 14) (diff : u ≠ v)
    (ob : ∀ j : Fin 14, j ≠ i → bitAt (row u v) j.val = true → bitAt (row d d) j.val = true) :
    ∃ g ∈ C.gates, i.val ∈ g.inputs ∧
      (g.op ≠ GateOp.and ∨ ∀ j ∈ g.inputs, j < 14 → bitAt (row u v) j = true) := by
  by_contra miss
  have beforeOut := fold_order_pinned_left C.gates (row u v) (row d d) (row u v) i.val
    (make_order _ _ _ _ ob) (Nat.le_refl _) (by simp)
    (fun g mem => legal_op g (m g mem).1)
    (by
      intro g hg a b _ same heed old
      have isAnd : g.op = GateOp.and := by
        by_contra no
        exact miss ⟨g,hg,heed,Or.inl no⟩
      exfalso
      apply miss
      refine ⟨g,hg,heed,Or.inr ?_⟩
      intro j hj jn
      have z : j < (row u v).length := by simp [jn]
      rw [← same j z]
      simp only [runGate,isAnd,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true] at old
      exact old j hj)
  have firstTrue : C.eval (row u v) = true := by simpa [row,crown,diff] using h u v
  have secondFalse : C.eval (row d d) = false := by simpa [row,crown] using h d d
  have secondTrue : C.eval (row d d) = true :=
    beforeOut.2 C.output (by simpa using no_raw_output C h i) firstTrue
  exact Bool.noConfusion (secondFalse.symm.trans secondTrue)

/-- Each positive pair requires a reader of its row input that is not blocked by an off raw AND operand. -/
theorem live_reader_of_row (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v : Fin 7) (diff : u ≠ v) :
    ∃ g ∈ C.gates, (left u).val ∈ g.inputs ∧
      (g.op ≠ GateOp.and ∨ ∀ j ∈ g.inputs, j < 14 → bitAt (row u v) j = true) :=
  live_reader_of_offdiag C m h u v v (left u) diff (cross_left_cases u v diff).2

/-- The symmetric statement for the column input. -/
theorem live_reader_of_col (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (u v : Fin 7) (diff : u ≠ v) :
    ∃ g ∈ C.gates, (right v).val ∈ g.inputs ∧
      (g.op ≠ GateOp.and ∨ ∀ j ∈ g.inputs, j < 14 → bitAt (row u v) j = true) :=
  live_reader_of_offdiag C m h u v u (right v) diff (cross_right_cases u v diff).2


/-- A promised crown representation rejects every singleton row and the empty row.
This strengthens the 49-row solver input to 64 exact bit lanes without additional assumptions. -/
theorem zero_or_singleton_false (C : Circuit) (m : Monotone2 C) (h : Represents crown C)
    (x : List Bool) (nx : x.length = 14) (i : Fin 14)
    (s : ∀ j : Fin 14, bitAt x j.val = true → j = i) : C.eval x = false := by
  obtain ⟨_,_,_,d,_,diag,_⟩ := read_cases i
  have neg : C.eval (row d d) = false := by simpa [row,crown] using h d d
  have rel : before x (row d d) none := by
    refine ⟨by simp [nx], ?_⟩
    intro j _ hj
    by_cases small : j < 14
    · have e := congrArg (fun f : Fin 14 => f.val) (s ⟨j,small⟩ hj)
      change j = i.val at e
      simpa [e] using diag
    · have bounds : x.length ≤ j := by omega
      simp [bitAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none bounds] at hj
  cases hc : C.eval x
  · rfl
  · exact Bool.noConfusion (neg.symm.trans (general_order C m _ _ rel hc))

end ProofLantern.Crown.Read

namespace ProofLantern.Crown.ThresholdLift

def singleton {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)
def pair {n : Nat} (i j : Fin n) : Fin n → Bool := fun k => decide (k = i ∨ k = j)

def pointwise {n : Nat} (x y : Fin n → Bool) : Prop :=
  ∀ k, x k = true → y k = true

/-- On a nonempty input set, a monotone map agreeing with threshold-two on singleton and pair
rows agrees on every input, including the all-zero row. -/
theorem lift_monotone_threshold_two {n : Nat} (f : (Fin n → Bool) → Bool)
    (j0 : Fin n)
    (mono : ∀ x y, pointwise x y → f x = true → f y = true)
    (single : ∀ i, f (singleton i) = false)
    (double : ∀ i j, i ≠ j → f (pair i j) = true)
    (x : Fin n → Bool) :
    f x = true ↔ ∃ i j, i ≠ j ∧ x i = true ∧ x j = true := by
  classical
  constructor
  · intro yes
    by_contra no
    have small : ∃ i, pointwise x (singleton i) := by
      by_cases existsTrue : ∃ i, x i = true
      · obtain ⟨i,hi⟩ := existsTrue
        refine ⟨i, ?_⟩
        intro j hj
        have eq : j = i := by
          by_contra d
          exact no ⟨j,i,d,hj,hi⟩
        simp [singleton,eq]
      · exact ⟨j0,fun j hj => (existsTrue ⟨j,hj⟩).elim⟩
    obtain ⟨k,le⟩ := small
    exact Bool.noConfusion ((single k).symm.trans (mono x _ le yes))
  · rintro ⟨i,j,d,hi,hj⟩
    apply mono (pair i j) x _ (double i j d)
    intro k hk
    simp [pair] at hk
    rcases hk with rfl|rfl
    · exact hi
    · exact hj

end ProofLantern.Crown.ThresholdLift

namespace ProofLantern.Crown.Identify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open ProofLantern.Crown.Read ProofLantern.Crown.ThresholdLift

def bundle (x y : Fin 7 → Bool) : List Bool := List.ofFn x ++ List.ofFn y

private theorem bundle_order {a b c d : Fin 7 → Bool}
    (ac : pointwise a c) (bd : pointwise b d) :
    before (bundle a b) (bundle c d) none := by
  refine ⟨by simp [bundle],?_⟩
  intro i _ h
  simp only [bundle,bitAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,
    List.getElem?_ofFn] at h ⊢
  by_cases q : i < 7
  · simpa [q] using ac ⟨i,q⟩ (by simpa [q] using h)
  · have narrow : i-7 < 7 := by
      by_contra! bad
      have nn : ¬ i-7 < 7 := by omega
      simp [q,nn] at h
    simpa [q,narrow] using bd ⟨i-7,narrow⟩ (by simpa [q,narrow] using h)

/-- Identifying each pair of inputs of an arbitrary raw Crown circuit with one Boolean
name yields exact threshold two. The original gate topology need not pre-pair the inputs. -/
theorem raw_identification (C : Circuit) (legal : Monotone2 C)
    (exact : Represents (fun u v : Fin 7 => decide (u ≠ v)) C)
    (z : Fin 7 → Bool) :
    C.eval (bundle z z) = true ↔ ∃ i j, i ≠ j ∧ z i = true ∧ z j = true := by
  apply lift_monotone_threshold_two (fun x => C.eval (bundle x x)) (0 : Fin 7) _ _ _ z
  · intro x y h
    exact general_order C legal _ _ (bundle_order h h)
  · intro i
    change C.eval (oneEach i i) = false
    simpa using exact i i
  · intro i j ne
    have smaller : before (oneEach i j) (bundle (pair i j) (pair i j)) none := by
      apply bundle_order
      · intro k hk
        change decide (k = i) = true at hk
        have e := of_decide_eq_true hk
        simp [ThresholdLift.pair,e]
      · intro k hk
        change decide (k = j) = true at hk
        have e := of_decide_eq_true hk
        simp [ThresholdLift.pair,e]
    apply general_order C legal _ _ smaller
    simpa [ne] using exact i j

end ProofLantern.Crown.Identify
