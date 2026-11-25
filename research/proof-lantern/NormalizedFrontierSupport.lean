import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Erase

namespace ProofLanternUnate
inductive F where
  | var (i : Nat) | const (b : Bool) | neg (f : F) | bin (isAnd : Bool) (l r : F)

def eval (x : Nat → Bool) : F → Bool
  | .var i => x i
  | .const b => b
  | .neg f => !(eval x f)
  | .bin b f g => if b then eval x f && eval x g else eval x f || eval x g

def uses (k : Nat) : F → Nat
  | .var i => if i = k then 1 else 0
  | .const _ => 0
  | .neg f => uses k f
  | .bin _ f g => uses k f + uses k g

def Adj (k : Nat) (x y : Nat → Bool) : Prop :=
  x k ≤ y k ∧ ∀ i, i ≠ k → x i = y i

def Up (k : Nat) (f : F) : Prop := ∀ x y, Adj k x y → eval x f ≤ eval y f
def Down (k : Nat) (f : F) : Prop := ∀ x y, Adj k x y → eval y f ≤ eval x f

theorem no_uses (f : F) (k : Nat) (h : uses k f = 0) :
    ∀ x y, Adj k x y → eval x f = eval y f := by
  induction f with
  | var i =>
    intro x y hxy
    have hne : i ≠ k := by simpa [uses] using h
    exact hxy.2 i hne
  | const b => intro x y hxy; rfl
  | neg f ih =>
    intro x y hxy
    simp only [uses] at h
    simp only [eval, ih h x y hxy]
  | bin b f g ihf ihg =>
    intro x y hxy
    simp only [uses, Nat.add_eq_zero_iff] at h
    simp only [eval, ihf h.1 x y hxy, ihg h.2 x y hxy]

private theorem neg_antitone {a b : Bool} (h : a ≤ b) : (!b) ≤ (!a) := by
  cases a <;> cases b <;> simp_all

private theorem bin_mono (s a b c d : Bool) (h : a ≤ c) (i : b ≤ d) :
    (if s then a && b else a || b) ≤ (if s then c && d else c || d) := by
  cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem leEq {a b : Bool} (h : a = b) : a ≤ b := by subst b; exact Bool.le_refl a

theorem once_unate (f : F) (k : Nat) (h : uses k f ≤ 1) : Up k f ∨ Down k f := by
  induction f with
  | var i =>
    left
    intro x y hxy
    by_cases hi : i = k
    · subst i; exact hxy.1
    · change x i ≤ y i
      rw [hxy.2 i hi]
  | const b => left; intro x y hxy; exact Bool.le_refl _
  | neg f ih =>
    rcases ih (by simpa only [uses] using h) with hf | hf
    · right; intro x y hxy; exact neg_antitone (hf x y hxy)
    · left; intro x y hxy; exact neg_antitone (hf x y hxy)
  | bin s f g ihf ihg =>
    simp only [uses] at h
    by_cases hz : uses k g = 0
    · have hg := no_uses g k hz
      rcases ihf (by omega) with hf | hf
      · left
        intro x y hxy
        exact bin_mono s _ _ _ _ (hf x y hxy) (leEq (hg x y hxy))
      · right
        intro x y hxy
        exact bin_mono s _ _ _ _ (hf x y hxy) (leEq (hg x y hxy).symm)
    · have hf := no_uses f k (by omega)
      rcases ihg (by omega) with hg | hg
      · left
        intro x y hxy
        exact bin_mono s _ _ _ _ (leEq (hf x y hxy)) (hg x y hxy)
      · right
        intro x y hxy
        exact bin_mono s _ _ _ _ (leEq (hf x y hxy).symm) (hg x y hxy)

end ProofLanternUnate


namespace ProofLanternUnate

def subst (k : Nat) (g : F) : F → F
  | .var i => if i = k then g else .var i
  | .const b => .const b
  | .neg f => .neg (subst k g f)
  | .bin b f t => .bin b (subst k g f) (subst k g t)

theorem eval_subst (f g : F) (w : Nat) (x : Nat → Bool) :
    eval x (subst w g f) = eval (fun i => if i = w then eval x g else x i) f := by
  induction f with
  | var i => by_cases hi : i = w <;> simp [subst, eval, hi]
  | const b => rfl
  | neg f ih => simp only [subst, eval, ih]
  | bin s f t ihf iht => simp only [subst, eval, ihf, iht]

theorem uses_subst_same (f g : F) (w : Nat) :
    uses w (subst w g f) = uses w f * uses w g := by
  induction f with
  | var i => by_cases hi : i = w <;> simp [subst, uses, hi]
  | const b => simp [subst, uses]
  | neg f ih => simp only [subst, uses, ih]
  | bin s f t ihf iht => simp only [subst, uses, ihf, iht, Nat.add_mul]

theorem uses_subst_other (f g : F) {k w : Nat} (hkw : k ≠ w) :
    uses k (subst w g f) = uses k f + uses w f * uses k g := by
  induction f with
  | var i =>
    by_cases hi : i = w
    · subst i; simp [subst, uses, Ne.symm hkw]
    · simp [subst, uses, hi]
  | const b => simp [subst, uses]
  | neg f ih => simp only [subst, uses, ih]
  | bin s f t ihf iht =>
    simp only [subst, uses, ihf, iht, Nat.add_mul]
    omega

theorem fresh_subst_once (f g : F) (w : Nat)
    (hf : ∀ k, uses k f ≤ 1) (hg : ∀ k, uses k g ≤ 1)
    (hprev : uses w g = 0)
    (hdisj : ∀ k, k ≠ w → uses k g ≠ 0 → uses k f = 0) :
    ∀ k, uses k (subst w g f) ≤ 1 := by
  intro k
  by_cases hkw : k = w
  · subst k
    rw [uses_subst_same, hprev]
    simp
  · rw [uses_subst_other f g hkw]
    by_cases hz : uses k g = 0
    · simpa [hz] using hf k
    · rw [hdisj k hkw hz]
      simp only [Nat.zero_add]
      have hw := hf w
      have hk := hg k
      exact Nat.mul_le_mul hw hk

end ProofLanternUnate


namespace ProofLanternUnate
open PEqualNP.CircuitLowerBounds

def inputTerm (w i : Nat) : F := if i < w then .var i else .const false

theorem inputTerm_eq (wire : List Bool) (i : Nat) :
    eval (fun j => wire.getD j false) (inputTerm wire.length i) = wire.getD i false := by
  by_cases h : i < wire.length
  · simp [inputTerm, h, eval]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp [inputTerm, h, eval]

theorem inputTerm_eq_getElem (wire : List Bool) (i : Nat) :
    eval (fun j => (wire[j]?).getD false) (inputTerm wire.length i) = (wire[i]?).getD false := by
  simpa only [List.getD_eq_getElem?_getD] using inputTerm_eq wire i

def gateTerm (w : Nat) (g : Gate) : F :=
  let v := inputTerm w
  match g.op, g.inputs with
  | .and, [] => .const true
  | .or, [] => .const false
  | .not, [] => .const true
  | .not, a :: _ => .neg (v a)
  | .and, [a] => v a
  | .or, [a] => v a
  | .and, a :: b :: _ => .bin true (v a) (v b)
  | .or, a :: b :: _ => .bin false (v a) (v b)
  | _, _ => .const false

theorem eval_gateTerm (wire : List Bool) (g : Gate)
    (he : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    eval (fun j => wire.getD j false) (gateTerm wire.length g) =
      g.op.eval (g.inputs.map fun j => wire.getD j false) := by
  obtain ⟨op, inp⟩ := g
  cases inp with
  | nil =>
    rcases he with he | he | he <;> cases he <;> rfl
  | cons a rest =>
    cases rest with
    | nil => rcases he with he | he | he <;> cases he <;> simp [gateTerm, GateOp.eval, eval, inputTerm_eq_getElem]
    | cons b tail =>
      cases tail with
      | nil => rcases he with he | he | he <;> cases he <;> simp [gateTerm, GateOp.eval, eval, inputTerm_eq_getElem]
      | cons c zs => simp at hl

end ProofLanternUnate

namespace ProofLanternUnate
open PEqualNP.CircuitLowerBounds
def projectStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem append_bit_lookup (w : List Bool) (b : Bool) (i : Nat) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · have hw : w.length ≤ i := Nat.le_of_not_gt h
    rw [List.getD_append_right _ _ _ _ hw, List.getD_eq_default _ _ hw]
    by_cases he : i = w.length
    · simp [he]
    · have hh : 1 ≤ i - w.length := by omega
      rw [ite_eq_right he, List.getD_eq_default _ _ (by simpa using hh)]

theorem eval_one_rewind (wire : List Bool) (f : F) (g : Gate)
    (he : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    eval (fun i => wire.getD i false) (subst wire.length (gateTerm wire.length g) f) =
      eval (fun i => (projectStep wire g).getD i false) f := by
  rw [eval_subst, eval_gateTerm wire g he hl]
  congr 1
  funext i
  exact (append_bit_lookup wire _ i).symm

def rewind (n : Nat) : List Gate → F → F
  | [], f => f
  | g :: gs, f =>
    rewind n gs (subst (n + gs.length) (gateTerm (n + gs.length) g) f)

theorem projectFold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl projectStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [projectStep, List.length_append, List.length_nil, List.length_cons]
    omega

theorem eval_rewind (gs : List Gate) (x : List Bool) (f : F)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    eval (fun i => x.getD i false) (rewind x.length gs f) =
      eval (fun i => (gs.reverse.foldl projectStep x).getD i false) f := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    have og := ok g (by simp)
    have ogs : ∀ z ∈ gs, (z.op = .and ∨ z.op = .or ∨ z.op = .not) ∧ z.inputs.length ≤ 2 := by
      intro z hz; exact ok z (List.mem_cons_of_mem _ hz)
    simp only [rewind, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih _ ogs]
    have hlen : (gs.reverse.foldl projectStep x).length = x.length + gs.length := by
      rw [projectFold_length, List.length_reverse]
    rw [← hlen]
    exact eval_one_rewind _ f g og.1 og.2

theorem circuit_expands (C : Circuit) (x : List Bool)
    (ok : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    eval (fun i => x.getD i false)
      (rewind x.length C.gates.reverse (inputTerm (x.length + C.gates.length) C.output)) =
    C.eval x := by
  have revOK : ∀ g ∈ C.gates.reverse,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg; exact ok g (by simpa using hg)
  rw [eval_rewind _ _ _ revOK, List.reverse_reverse]
  change eval (fun i => (C.wires x).getD i false)
      (inputTerm (x.length + C.gates.length) C.output) = (C.wires x).getD C.output false
  have h : (C.wires x).length = x.length + C.gates.length := projectFold_length C.gates x
  rw [← h]; exact inputTerm_eq _ _
end ProofLanternUnate

namespace ProofLanternUnate
open PEqualNP.CircuitLowerBounds

def readArgs (w : Nat) (g : Gate) : List Nat :=
  (match g.op with
    | .not => g.inputs.take 1
    | _ => g.inputs).filter fun i => decide (i < w)

theorem readArgs_lt {w i : Nat} {g : Gate} (hi : i ∈ readArgs w g) : i < w := by
  simpa [readArgs] using (List.mem_filter.mp hi).2

theorem count_args (g : Gate) (w k : Nat)
    (he : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    uses k (gateTerm w g) = (readArgs w g).count k := by
  obtain ⟨op, inp⟩ := g
  cases inp with
  | nil => rcases he with he | he | he <;> cases he <;> rfl
  | cons a rest =>
    cases rest with
    | nil =>
      rcases he with he | he | he <;> cases he <;>
        by_cases h : a < w <;> simp [readArgs, gateTerm, inputTerm, uses, h, List.count_cons]
    | cons b tail =>
      cases tail with
      | nil =>
        rcases he with he | he | he <;> cases he <;>
          by_cases h : a < w <;> by_cases i : b < w <;>
          simp [readArgs, gateTerm, inputTerm, uses, h, i, List.count_cons, Nat.add_comm]
      | cons c zs => simp at hl

def notCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

theorem ports_bound (w : Nat) (g : Gate) (hl : g.inputs.length ≤ 2) :
    (readArgs w g).length + notCost g ≤ 2 := by
  cases op : g.op
  all_goals
    unfold readArgs notCost
    rw [op]
    dsimp only
  all_goals first
  | exact Nat.le_trans (List.length_filter_le _ _) hl
  | have h := List.length_filter_le (fun i => decide (i < w)) (g.inputs.take 1)
    simp only [List.length_take] at h
    omega

end ProofLanternUnate

namespace ProofLanternFrontier

def coll (s : Finset Nat) (a : Nat) : Nat := if a ∈ s then 1 else 0

def pushMany (s : Finset Nat) : List Nat → Finset Nat
  | [] => s
  | a :: args => pushMany (insert a s) args

def collisions (s : Finset Nat) : List Nat → Nat
  | [] => 0
  | a :: args => coll s a + collisions (insert a s) args

theorem insert_balance (s : Finset Nat) (a : Nat) :
    (insert a s).card + coll s a = s.card + 1 := by
  by_cases h : a ∈ s
  · simp [coll, h]
  · simp [coll, h, Finset.card_insert_of_notMem h]

theorem push_balance (s : Finset Nat) (xs : List Nat) :
    (pushMany s xs).card + collisions s xs = s.card + xs.length := by
  induction xs generalizing s with
  | nil => simp [pushMany, collisions]
  | cons a xs ih =>
    simp only [pushMany, collisions, List.length_cons]
    have hp := ih (insert a s)
    have hs := insert_balance s a
    omega

theorem replace_balance {s : Finset Nat} {w : Nat} (hw : w ∈ s)
    (args : List Nat) (isNot loss : Nat) (hargs : args.length + isNot + loss = 2) :
    (pushMany (s.erase w) args).card + collisions (s.erase w) args + isNot + loss =
      s.card + 1 := by
  have he := Finset.card_erase_add_one hw
  have hp := push_balance (s.erase w) args
  omega

structure Step where
  wire : Nat
  args : List Nat
  isNot : Nat
  loss : Nat
  arity : args.length + isNot + loss = 2

def run (s : Finset Nat) : List Step → Finset Nat × Nat × Nat × Nat × Nat
  | [] => (s, 0, 0, 0, 0)
  | g :: gs =>
    if g.wire ∈ s then
      let t := s.erase g.wire
      let (u, c, n, l, a) := run (pushMany t g.args) gs
      (u, c + collisions t g.args, n + g.isNot, l + g.loss, a + 1)
    else run s gs

theorem run_balance (s : Finset Nat) (gs : List Step) :
    let (u, c, n, l, a) := run s gs
    u.card + c + n + l = s.card + a := by
  induction gs generalizing s with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run]
    by_cases hw : g.wire ∈ s
    · simp only [ite_eq_left hw]
      let t := s.erase g.wire
      have h := replace_balance hw g.args g.isNot g.loss g.arity
      have hr := ih (pushMany t g.args)
      rcases eq : run (pushMany t g.args) gs with ⟨u, c, n, l, a⟩
      rw [eq] at hr
      change u.card + (c + collisions t g.args) + (n + g.isNot) + (l + g.loss) = s.card + (a + 1)
      change u.card + c + n + l = (pushMany t g.args).card + a at hr
      change (pushMany t g.args).card + collisions t g.args + g.isNot + g.loss = s.card + 1 at h
      omega
    · simpa only [ite_eq_right hw] using ih s

theorem run_gates_le (s : Finset Nat) (gs : List Step) :
    (run s gs).2.2.2.2 ≤ gs.length := by
  induction gs generalizing s with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run]
    by_cases hw : g.wire ∈ s
    · simp only [ite_eq_left hw]
      let t := s.erase g.wire
      have hr := ih (pushMany t g.args)
      rcases eq : run (pushMany t g.args) gs with ⟨u, c, n, l, a⟩
      rw [eq] at hr
      change a + 1 ≤ gs.length + 1
      exact Nat.succ_le_succ hr
    · simp only [ite_eq_right hw, List.length_cons]
      exact Nat.le_trans (ih s) (Nat.le_succ _)

theorem binate_budget_from_scan {root : Nat} {gs : List Step} {u : Finset Nat} {c n l a : Nat}
    (hr : run {root} gs = (u, c, n, l, a)) (hc : 0 < c) (hn : 0 < n) :
    u.card + 1 ≤ gs.length := by
  have h := run_balance {root} gs
  have ha := run_gates_le {root} gs
  rw [hr] at h ha
  simp at h ha
  omega

end ProofLanternFrontier


namespace ProofLanternFrontier
open ProofLanternUnate

theorem mem_push (s : Finset Nat) (xs : List Nat) (k : Nat) :
    k ∈ pushMany s xs ↔ k ∈ s ∨ k ∈ xs := by
  induction xs generalizing s with
  | nil => simp [pushMany]
  | cons a xs ih =>
    rw [pushMany, ih, Finset.mem_insert, List.mem_cons]
    tauto

theorem zero_collisions_nodup {s : Finset Nat} {xs : List Nat}
    (hc : collisions s xs = 0) :
    xs.Nodup ∧ (∀ k ∈ xs, k ∉ s) := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    simp only [collisions, Nat.add_eq_zero_iff] at hc
    have hna : a ∉ s := by
      intro ha; simp [coll, ha] at hc
    obtain ⟨hnd, hs⟩ := ih hc.2
    constructor
    · rw [List.nodup_cons]
      exact ⟨fun ha => hs a ha (Finset.mem_insert_self _ _), hnd⟩
    · intro k hk hsK
      rcases List.mem_cons.mp hk with h | h
      · subst k; exact hna hsK
      · exact hs k h (Finset.mem_insert_of_mem hsK)

theorem count_zero_of_absent {k : Nat} {xs : List Nat} (h : k ∉ xs) :
    xs.count k = 0 := by
  exact List.count_eq_zero_of_not_mem h

theorem substitute_support (s : Finset Nat) (f g : F) (w : Nat) (args : List Nat)
    (hf : ∀ k, 0 < uses k f ↔ k ∈ s)
    (hg : ∀ k, uses k g = args.count k) (hws : w ∈ s) (hwargs : w ∉ args) :
    ∀ k, 0 < uses k (subst w g f) ↔ k ∈ pushMany (s.erase w) args := by
  intro k
  rw [mem_push, Finset.mem_erase]
  by_cases hkw : k = w
  · subst k
    rw [uses_subst_same, hg w, count_zero_of_absent hwargs]
    simp [hwargs]
  · have hwp : 0 < uses w f := (hf w).2 hws
    have hm : 0 < uses w f * args.count k ↔ 0 < args.count k := by
      constructor
      · intro hp
        by_contra hn
        have hz : args.count k = 0 := by omega
        simp [hz] at hp
      · exact Nat.mul_pos hwp
    rw [uses_subst_other f g hkw, hg k, Nat.add_pos_iff_pos_or_pos, hm, hf, List.count_pos_iff]
    simp [hkw]

end ProofLanternFrontier


namespace ProofLanternFrontier
open ProofLanternUnate
open PEqualNP.CircuitLowerBounds

theorem preserve_once_zero (s : Finset Nat) (f g : F) (w : Nat) (args : List Nat)
    (hf : ∀ k, 0 < uses k f ↔ k ∈ s)
    (hg : ∀ k, uses k g = args.count k) (hwa : w ∉ args)
    (hc : collisions (s.erase w) args = 0) (honce : ∀ k, uses k f ≤ 1) :
    ∀ k, uses k (subst w g f) ≤ 1 := by
  obtain ⟨hn, hd⟩ := zero_collisions_nodup hc
  apply fresh_subst_once f g w honce
  · intro k
    rw [hg]
    exact List.nodup_iff_count_le_one.mp hn k
  · rw [hg, count_zero_of_absent hwa]
  · intro k hkw hp
    have hka : k ∈ args := List.count_pos_iff.mp (by rw [hg] at hp; omega)
    have hn := hd k hka
    by_contra hz
    exact hn (Finset.mem_erase.mpr ⟨hkw, (hf k).mp (by omega)⟩)

theorem unused_substitute (f g : F) (w : Nat) (hw : uses w f = 0) :
    ∀ k, uses k (subst w g f) = uses k f := by
  intro k
  by_cases hkw : k = w
  · subst k
    rw [uses_subst_same, hw]
    simp
  · rw [uses_subst_other f g hkw, hw]
    simp

def normalized (w : Nat) (g : Gate) (h : g.inputs.length ≤ 2) : Step :=
  let args := readArgs w g
  let c := notCost g
  ⟨w, args, c, 2 - (args.length + c), by
     have hb := ports_bound w g h
     change (readArgs w g).length + notCost g + (2 - ((readArgs w g).length + notCost g)) = 2
     omega⟩

end ProofLanternFrontier
