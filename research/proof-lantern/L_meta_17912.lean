import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Finset.Card
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace RowExtension

inductive E where
  | leaf (i : Nat)
  | node (b : Bool) (l r : E)

def exprEval (w : List Bool) : E → Bool
  | .leaf i => w.getD i false
  | .node b l r => if b then exprEval w l && exprEval w r else exprEval w l || exprEval w r

def withinScope (k : Nat) : E → Prop
  | .leaf i => i < k
  | .node _ l r => withinScope k l ∧ withinScope k r

def gateOp (b : Bool) : GateOp := if b then .and else .or

def emit : E → Nat → List Gate × Nat
  | .leaf i, _ => ([],i)
  | .node b l r, k =>
    let el := emit l k
    let er := emit r (k + el.1.length)
    (el.1 ++ er.1 ++ [⟨gateOp b, [el.2,er.2]⟩], k + el.1.length + er.1.length)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem prefix_read (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem scoped_weaken (e : E) {k t : Nat} (h : withinScope k e) (ht : k ≤ t) : withinScope t e := by
  induction e with
  | leaf i => exact Nat.lt_of_lt_of_le h ht
  | node b l r il ir => exact ⟨il h.1,ir h.2⟩

theorem eval_prefix (e : E) (gs : List Gate) (w : List Bool) (h : withinScope w.length e) :
    exprEval (gs.foldl step w) e = exprEval w e := by
  induction e with
  | leaf i => exact prefix_read gs w i h
  | node b l r il ir => simp only [exprEval, il h.1, ir h.2]

theorem emit_bound (e : E) (k : Nat) (h : withinScope k e) :
    (emit e k).2 < k + (emit e k).1.length := by
  cases e with
  | leaf i => simpa [emit,withinScope] using h
  | node b l r =>
    simp only [emit, List.length_append, List.length_cons, List.length_nil]
    omega

theorem op_eval (b a c : Bool) : (gateOp b).eval [a,c] =
    (if b then a && c else a || c) := by cases b <;> simp [gateOp,GateOp.eval]

theorem emit_eval (e : E) (w : List Bool) (h : withinScope w.length e) :
    ((emit e w.length).1.foldl step w).getD (emit e w.length).2 false = exprEval w e := by
  induction e generalizing w with
  | leaf i => rfl
  | node b l r il ir =>
    let el := emit l w.length
    let wl := el.1.foldl step w
    have hw : wl.length = w.length + el.1.length := fold_length _ _
    let er := emit r wl.length
    let wr := er.1.foldl step wl
    have hwr : wr.length = wl.length + er.1.length := fold_length _ _
    have hr : withinScope wl.length r := scoped_weaken r h.2 (by omega)
    have evl : wl.getD el.2 false = exprEval w l := il w h.1
    have evr : wr.getD er.2 false = exprEval w r := (ir wl hr).trans (eval_prefix r el.1 w h.2)
    have lex : wr.getD el.2 false = exprEval w l := by
      have leftBound := emit_bound l w.length h.1
      exact (prefix_read er.1 wl el.2 (by rwa [hw])).trans evl
    simp only [emit, List.foldl_append, List.foldl_cons,List.foldl_nil]
    change (step ((emit r (w.length + el.1.length)).1.foldl step wl)
        ⟨gateOp b,[el.2,(emit r (w.length + el.1.length)).2]⟩).getD
          (w.length + el.1.length + (emit r (w.length + el.1.length)).1.length) false = _
    rw [← hw]
    change (step wr ⟨gateOp b,[el.2,er.2]⟩).getD (wl.length + er.1.length) false = _
    rw [← hwr]
    simp only [step,List.getD_append_right _ _ _ _ (Nat.le_refl wr.length),Nat.sub_self,List.getD_cons_zero,List.map_cons,List.map_nil]
    rw [op_eval,lex,evr]
    rfl

end RowExtension

namespace RowExtension

def cost : E → Nat
  | .leaf _ => 0
  | .node _ a b => cost a + cost b + 1

theorem emit_length (e : E) (n : Nat) : (emit e n).1.length = cost e := by
  induction e generalizing n with
  | leaf i => rfl
  | node b l r il ir => simp [emit, cost, il, ir, Nat.add_assoc]

theorem emit_monotone (e : E) (n : Nat) :
    ∀ g ∈ (emit e n).1, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction e generalizing n with
  | leaf i => simp [emit]
  | node b l r il ir =>
    intro g hg
    simp only [emit,List.mem_append,List.mem_singleton] at hg
    rcases hg with (hl | hr) | hs
    · exact il _ g hl
    · exact ir _ g hr
    · subst g
      cases b <;> simp [gateOp]

theorem emit_at_least (e : E) (n : Nat) (hne : 0 < cost e) :
    n ≤ (emit e n).2 := by
  cases e with
  | leaf i => simp [cost] at hne
  | node b l r => simp only [emit]; omega

theorem extend_expr (n : Nat) (C : Circuit) (e : E) (hc : Monotone2 C)
    (hout : C.output < n+C.size) (he : withinScope n e) (hne : 0 < cost e) :
    ∃ (T : Circuit) (o : Nat), Monotone2 T ∧ T.size = C.size + cost e ∧ C.output < o ∧
      ∀ x : List Bool, x.length = n →
        (T.wires x).getD C.output false = C.eval x ∧ (T.wires x).getD o false = exprEval x e := by
  let extra := emit e (n + C.size)
  let T : Circuit := ⟨C.gates ++ extra.1,extra.2⟩
  refine ⟨T,extra.2,?_,?_,Nat.lt_of_lt_of_le hout (emit_at_least e _ hne),?_⟩
  · intro g hg
    change g ∈ C.gates ++ extra.1 at hg
    rcases List.mem_append.mp hg with h | h
    · exact hc g h
    · exact emit_monotone e _ _ h
  · simp [T, extra, Circuit.size, emit_length]
  · intro x hx
    let w := C.gates.foldl step x
    have hw : w.length = n + C.size := by rw [show w.length = x.length + C.gates.length from fold_length _ _, hx]; rfl
    have ws : withinScope w.length e := scoped_weaken e he (by omega)
    have xs : withinScope x.length e := by rwa [hx]
    constructor
    · change ((C.gates ++ extra.1).foldl step x).getD C.output false = w.getD C.output false
      rw [List.foldl_append]
      exact prefix_read extra.1 w _ (by omega)
    · change ((C.gates ++ extra.1).foldl step x).getD extra.2 false = _
      rw [List.foldl_append]
      change (extra.1.foldl step w).getD extra.2 false = _
      have ev := emit_eval e w ws
      rw [hw] at ev
      exact ev.trans (eval_prefix e C.gates x xs)

end RowExtension

namespace RowExtension

abbrev P := Fin 13
def inc (p q : P) : Prop := (p.val + q.val) % 13 ∈ ([0,1,3,9] : List Nat)
instance (p q : P) : Decidable (inc p q) :=
  inferInstanceAs (Decidable ((p.val + q.val) % 13 ∈ ([0,1,3,9] : List Nat)))
def rest : List P := [4,5,7,8,9,10,11,12]
def nb (p : P) : List P := [0-p,1-p,3-p,9-p]
theorem nb_exact : ∀ p q : P, inc p q ↔ q ∈ nb p := by decide
theorem rest_exact : ∀ p : P, p ∈ rest ↔ p.val ∉ ([0,1,2,3,6] : List Nat) := by decide
def input (x y : Finset P) : List Bool :=
  List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ x)
    else decide (Fin.ofNat 13 i.val ∈ y)

theorem input_len (x y : Finset P) : (input x y).length = 26 := by simp [input]

theorem read_point (x y : Finset P) (p : P) :
    (input x y).getD p.val false = decide (p ∈ x) := by
  rw [List.getD_eq_getElem _ _ (by rw [input_len]; have hp := p.isLt; omega)]
  simp only [input, List.getElem_ofFn]
  simp [p.isLt]

theorem read_line (x y : Finset P) (p : P) :
    (input x y).getD (13+p.val) false = decide (p ∈ y) := by
  have hp := p.isLt
  rw [List.getD_eq_getElem _ _ (by rw [input_len]; omega)]
  have hh : ¬13 + p.val < 13 := by omega
  have hfin : Fin.ofNat 13 (13+p.val) = p := by
    apply Fin.ext
    change (13+p.val)%13 = p.val
    omega
  simp only [input, List.getElem_ofFn]
  change (if 13+p.val < 13 then decide (Fin.ofNat 13 (13+p.val) ∈ x) else decide (Fin.ofNat 13 (13+p.val) ∈ y)) = _
  rw [ite_eq_right hh, hfin]

def eitherOf (x : E) (xs : List E) : E := xs.foldl (E.node false) x
theorem eval_either (w : List Bool) (x : E) (xs : List E) :
    exprEval w (eitherOf x xs) = (exprEval w x || xs.any (exprEval w)) := by
  induction xs generalizing x with
  | nil => simp [eitherOf]
  | cons a t ih =>
    change exprEval w (eitherOf (.node false x a) t) = _
    rw [ih]
    simp [exprEval, Bool.or_assoc]

def nbr (p : P) : E :=
  eitherOf (.leaf (13 + (0-p).val)) [(.leaf (13 + (1-p).val)),
    (.leaf (13 + (3-p).val)), (.leaf (13 + (9-p).val))]
def row (p : P) : E := .node true (.leaf p.val) (nbr p)
def whole : E := eitherOf (row 4) ([5,7,8,9,10,11,12].map row)

def wc (n : Nat) : (e : E) → Decidable (withinScope n e)
  | .leaf i => inferInstanceAs (Decidable (i < n))
  | .node _ l r => @instDecidableAnd (withinScope n l) (withinScope n r) (wc n l) (wc n r)
instance (n : Nat) (e : E) : Decidable (withinScope n e) := wc n e
theorem whole_scoped : withinScope 26 whole := by decide
theorem whole_cost : cost whole = 39 := by decide

theorem nbr_eval (x y : Finset P) (p : P) :
    exprEval (input x y) (nbr p) = (nb p).any (fun q => decide (q ∈ y)) := by
  simp [nbr, nb, eval_either, exprEval, -List.getD_eq_getElem?_getD, read_line]

theorem row_eval (x y : Finset P) (p : P) :
    exprEval (input x y) (row p) = (decide (p ∈ x) && (nb p).any (fun q => decide (q ∈ y))) := by
  simp [row, exprEval, -List.getD_eq_getElem?_getD, read_point, nbr_eval]

theorem whole_eval (x y : Finset P) :
    exprEval (input x y) whole =
      decide (∃ p ∈ x, p.val ∉ ([0,1,2,3,6] : List Nat) ∧ ∃ q ∈ y, inc p q) := by
  have h : exprEval (input x y) whole = rest.any (fun p => exprEval (input x y) (row p)) := by
    simp [whole, rest, eval_either]
  rw [h]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, row_eval, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨p,hp,hx,q,hq,hy⟩
    exact ⟨p,hx,rest_exact p |>.mp hp,q,hy,(nb_exact p q).mpr hq⟩
  · rintro ⟨p,hx,hp,q,hy,hq⟩
    exact ⟨p,(rest_exact p).mpr hp,hx,q,(nb_exact p q).mp hq,hy⟩

theorem extension (C : Circuit) (hc : Monotone2 C) (hb : C.size ≤ 23)
    (hout : C.output < 26 + C.size) :
    ∃ (T : Circuit) (o : Nat), Monotone2 T ∧ T.size ≤ 62 ∧ C.output < o ∧
      ∀ x y : Finset P, (T.wires (input x y)).getD C.output false = C.eval (input x y) ∧
        (T.wires (input x y)).getD o false =
          decide (∃ p ∈ x, p.val ∉ ([0,1,2,3,6] : List Nat) ∧ ∃ q ∈ y, inc p q) := by
  obtain ⟨T,o,ht,hs,ho,h⟩ := extend_expr 26 C whole hc hout whole_scoped (by rw [whole_cost]; decide)
  rw [whole_cost] at hs
  refine ⟨T,o,ht,by omega,ho,?_⟩
  intro x y
  obtain ⟨old,next⟩ := h (input x y) (input_len x y)
  exact ⟨old,next.trans (whole_eval x y)⟩

end RowExtension

theorem ExactDesk17912 : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (23 : ℕ) → x3.output < (26 : ℕ) + x3.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ (62 : ℕ) ∧ x3.output < x8 ∧ ∀ (x9 x10 : Finset (Fin (13 : ℕ))), (x7.wires (x2 x9 x10)).getD x3.output Bool.false = x3.eval (x2 x9 x10) ∧ (x7.wires (x2 x9 x10)).getD x8 Bool.false = Decidable.decide (∃ x11 ∈ x9, ↑x11 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧ ∃ x12 ∈ x10, x1 x11 x12)
) := RowExtension.extension
