import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.ReadK
import PEqualNP.Defs.TopForm

namespace ProofLanternLinearPath

def mulPart (x y : Bool × Bool) : Bool × Bool :=
  (x.1 && y.1, (x.1 && y.2) || (x.2 && y.1))

def pairGate (isAnd : Bool) (x y : Bool × Bool) : Bool × Bool :=
  if isAnd then mulPart (mulPart (true,false) x) y else (x.1 || y.1,x.2 || y.2)

def valGate (isAnd x y : Bool) : Bool := if isAnd then x && y else x || y

theorem part_zero_below (c : Bool) (x y : Bool × Bool) (u v : Bool)
    (hx : x.1 ≤ u) (hy : y.1 ≤ v) : (pairGate c x y).1 ≤ valGate c u v := by
  obtain ⟨a,b⟩ := x
  obtain ⟨d,e⟩ := y
  cases c <;> cases a <;> cases b <;> cases d <;> cases e <;> cases u <;> cases v <;>
    simp_all [pairGate,valGate,mulPart]

theorem follows_one_branch (c : Bool) (x y : Bool × Bool) (u v : Bool)
    (hx : x.1 ≤ u) (hy : y.1 ≤ v) (hp : (pairGate c x y).2 = true) :
      (x.2 = true ∧ (c = false ∨ v = true)) ∨
      (y.2 = true ∧ (c = false ∨ u = true)) := by
  obtain ⟨a,b⟩ := x
  obtain ⟨d,e⟩ := y
  cases c <;> cases a <;> cases b <;> cases d <;> cases e <;> cases u <;> cases v <;>
    simp_all [pairGate,mulPart] <;> contradiction

end ProofLanternLinearPath

namespace ProofLanternLinearPath
open PEqualNP.CircuitLowerBounds
open PEqualNP.ReadK

def linearStep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => w.getD i (false,false)
  w ++ [match g.op with
    | .or => (ins.any (·.1),ins.any (·.2))
    | .and => ins.foldl mulPart (true,false)
    | _ => (false,false)]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem linear_step2 (w : List (Bool × Bool)) (c : Bool) (a b : Nat) :
    linearStep w ⟨if c then .and else .or,[a,b]⟩ =
    w ++ [pairGate c (w.getD a (false,false)) (w.getD b (false,false))] := by
  cases c <;> simp [linearStep,pairGate]

theorem bool_step2 (w : List Bool) (c : Bool) (a b : Nat) :
    boolStep w ⟨if c then .and else .or,[a,b]⟩ =
    w ++ [valGate c (w.getD a false) (w.getD b false)] := by
  cases c <;> simp [boolStep,valGate,GateOp.eval]

theorem lookup_append_new {α : Type} (w : List α) (x z : α) (i : Nat) :
    (w ++ [x]).getD i z = if i = w.length then x else w.getD i z := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · have hw : w.length ≤ i := Nat.le_of_not_gt h
    rw [List.getD_append_right _ _ _ _ hw, List.getD_eq_default _ _ hw]
    by_cases he : i = w.length
    · simp [he]
    · have hh : 1 ≤ i - w.length := by omega
      rw [ite_eq_right he, List.getD_eq_default _ _ (by simpa using hh)]

def Inv (rel : Nat → Nat → Prop) (l : Nat) (w : List (Bool × Bool)) (z : List Bool) : Prop :=
  w.length=z.length ∧ (∀ i, (w.getD i (false,false)).1 ≤ z.getD i false) ∧
    ∀ i, (w.getD i (false,false)).2 = true → Relation.ReflTransGen rel l i

theorem propagate (rel : Nat → Nat → Prop) (l : Nat) (w : List (Bool × Bool))
    (z : List Bool) (c : Bool) (a b : Nat) (h : Inv rel l w z)
    (left : c = false ∨ z.getD b false = true → rel a z.length)
    (right : c = false ∨ z.getD a false = true → rel b z.length) :
    Inv rel l (linearStep w ⟨if c then .and else .or,[a,b]⟩)
      (boolStep z ⟨if c then .and else .or,[a,b]⟩) := by
  rw [linear_step2,bool_step2]
  refine ⟨by simp [h.1],?_,?_⟩
  · intro i
    rw [lookup_append_new,lookup_append_new,h.1]
    by_cases hi : i=z.length
    · simp only [ite_eq_left hi]
      exact part_zero_below c _ _ _ _ (h.2.1 a) (h.2.1 b)
    · simp only [ite_eq_right hi]
      exact h.2.1 i
  · intro i hi
    rw [lookup_append_new,h.1] at hi
    by_cases hj : i=z.length
    · rw [ite_eq_left hj] at hi
      rcases follows_one_branch c _ _ _ _ (h.2.1 a) (h.2.1 b) hi with hleft | hright
      · exact hj ▸ (h.2.2 a hleft.1).tail (left hleft.2)
      · exact hj ▸ (h.2.2 b hright.1).tail (right hright.2)
    · rw [ite_eq_right hj] at hi
      exact h.2.2 i hi

end ProofLanternLinearPath

namespace ProofLanternLinearPath
open PEqualNP.CircuitLowerBounds
open PEqualNP.ReadK

def hop (C : Circuit) (n : Nat) (seed : List Bool) (a o : Nat) : Prop :=
  ∃ (j b : Nat) (g : Gate), o = n+j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a,b] ∨ g.inputs = [b,a]) ∧
    (g.op = .or ∨ (C.wires seed).getD b false = true)

theorem bool_fold_len (gs : List Gate) (z : List Bool) :
    (gs.foldl boolStep z).length = z.length + gs.length := by
  induction gs generalizing z with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [boolStep,List.length_append,List.length_cons,List.length_nil]
    omega

theorem bool_fold_read (gs : List Gate) (z : List Bool) (i : Nat) (hi : i < z.length) :
    (gs.foldl boolStep z).getD i false = z.getD i false := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [boolStep]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem prefix_true (todo : List Gate) (z : List Bool) (i : Nat) (hi : z.getD i false = true) :
    (todo.foldl boolStep z).getD i false = true := by
  have h : i < z.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at hi
    contradiction
  rwa [bool_fold_read todo z i h]

theorem find_shape (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (hl : g.inputs.length = 2) :
    ∃ (c : Bool) (a b : Nat), g = ⟨if c then .and else .or,[a,b]⟩ := by
  obtain ⟨op,inp⟩ := g
  cases inp with
  | nil => simp at hl
  | cons a inp =>
    cases inp with
    | nil => simp at hl
    | cons b tail =>
      have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst tail
      rcases h with h | h
      · exact ⟨true,a,b,by cases h; rfl⟩
      · exact ⟨false,a,b,by cases h; rfl⟩

theorem full_inv (C : Circuit) (n l : Nat) (seed : List Bool) (w : List (Bool × Bool))
    (hlen : seed.length = n)
    (hc : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (pref todo : List Gate) (hcat : C.gates = pref ++ todo)
    (hi : Inv (hop C n seed) l (pref.foldl linearStep w) (pref.foldl boolStep seed)) :
    Inv (hop C n seed) l (C.gates.foldl linearStep w) (C.gates.foldl boolStep seed) := by
  induction todo generalizing pref with
  | nil => simpa [hcat] using hi
  | cons g todo ih =>
    have hm : g ∈ C.gates := by simp [hcat]
    obtain ⟨c,a,b,hg⟩ := find_shape g (hc g hm).1 (hc g hm).2
    subst g
    let gate : Gate := ⟨if c then .and else .or,[a,b]⟩
    let z := pref.foldl boolStep seed
    have hz : z.length = n + pref.length := by rw [show z.length = seed.length + pref.length from bool_fold_len _ _, hlen]
    have hidx : C.gates[pref.length]? = some gate := by
      rw [hcat, List.getElem?_append_right (Nat.le_refl _)]
      simp [gate]
    have hfull (i : Nat) (ht : z.getD i false = true) : (C.wires seed).getD i false = true := by
      change (C.gates.foldl boolStep seed).getD i false = true
      rw [hcat, List.foldl_append]
      exact prefix_true _ z _ ht
    have left (h : c = false ∨ z.getD b false = true) : hop C n seed a z.length := by
      refine ⟨pref.length,b,gate,hz,hidx,Or.inl rfl,?_⟩
      rcases h with h | h
      · exact Or.inl (by simp [gate,h])
      · exact Or.inr (hfull b h)
    have right (h : c = false ∨ z.getD a false = true) : hop C n seed b z.length := by
      refine ⟨pref.length,a,gate,hz,hidx,Or.inr rfl,?_⟩
      rcases h with h | h
      · exact Or.inl (by simp [gate,h])
      · exact Or.inr (hfull a h)
    apply ih (pref ++ [gate])
    · simpa [gate,List.append_assoc] using hcat
    · simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using
        propagate (hop C n seed) l (pref.foldl linearStep w) z c a b hi left right

end ProofLanternLinearPath

namespace ProofLanternLinearPath
open PEqualNP.CircuitLowerBounds
open PEqualNP.ReadK

def startPair (n p l : Nat) : List (Bool × Bool) :=
  ((((List.range n).map fun i => i == p || i == l).zipIdx).map
    fun (b,i) => if decide (i = l) then (false,b) else (b,false))
def startBool (n p : Nat) : List Bool := List.ofFn fun i : Fin n => decide (i.val = p)

theorem start_pair_len (n p l : Nat) : (startPair n p l).length = n := by simp [startPair]
theorem start_bool_len (n p : Nat) : (startBool n p).length = n := by simp [startBool]

theorem start_pair_at (n p l i : Nat) (hi : i < n) :
    (startPair n p l).getD i (false,false) =
    (if i = l then (false,true) else (decide (i = p),false)) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [start_pair_len] using hi)]
  simp only [startPair,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,List.getElem_range]
  by_cases hl : i = l
  · simp [hl]
  · have hn : (i == l) = false := by simpa using hl
    have he : (i == p) = decide (i = p) := by by_cases h : i = p <;> simp [h]
    simp [hl, hn, he]

theorem start_bool_at (n p i : Nat) (hi : i < n) :
    (startBool n p).getD i false = decide (i = p) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [start_bool_len] using hi)]
  simp only [startBool,List.getElem_ofFn]

theorem start_inv (rel : Nat → Nat → Prop) (n p l : Nat) :
    Inv rel l (startPair n p l) (startBool n p) := by
  refine ⟨by simp [start_pair_len,start_bool_len],?_,?_⟩
  · intro i
    by_cases hi : i < n
    · rw [start_pair_at n p l i hi,start_bool_at n p i hi]
      by_cases hl : i = l
      · simp [hl]
      · simp [hl]
    · rw [List.getD_eq_default _ _ (by rw [start_pair_len]; omega)]
      exact Bool.false_le _
  · intro i hp
    by_cases hi : i < n
    · rw [start_pair_at n p l i hi] at hp
      by_cases hl : i = l
      · subst i; exact Relation.ReflTransGen.refl
      · simp [hl] at hp
    · rw [List.getD_eq_default _ _ (by rw [start_pair_len]; omega)] at hp
      contradiction

theorem line_path (n : Nat) (C : Circuit) (p l : Nat)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (h : lineSingle C n (fun k => decide (k = l)) p l = true) :
    Relation.ReflTransGen (hop C n (startBool n p)) l C.output := by
  have hc : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hC.1 g hg,hC.2.2 g hg⟩
  have v := full_inv C n l (startBool n p) (startPair n p l) (start_bool_len n p) hc
    [] C.gates rfl (start_inv _ n p l)
  exact v.2.2 C.output h

end ProofLanternLinearPath

theorem ExactDesk18049 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x2 < (26 : ℕ) → x3 < (26 : ℕ) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = x3)) x2 x3 = Bool.true → Relation.ReflTransGen (fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x9 = (26 : ℕ) + x10 ∧ x1.gates[x10]? = Option.some x12 ∧ (x12.inputs = [x8, x11] ∨ x12.inputs = [x11, x8]) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (x1.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = x2))).getD x11 Bool.false = Bool.true)) x3 x1.output
) := by
  intro c p l hc _ _ h
  exact ProofLanternLinearPath.line_path 26 c p l hc h
