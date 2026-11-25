import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.Represents
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


namespace ProofLanternFrontier
open ProofLanternUnate
open PEqualNP.CircuitLowerBounds

def normSteps (n : Nat) : List Gate → List Step
  | [] => []
  | g :: gs =>
    (if h : g.inputs.length ≤ 2 then normalized (n + gs.length) g h
     else ⟨n + gs.length, [], 0, 2, by decide⟩) :: normSteps n gs

theorem normSteps_length (n : Nat) (gs : List Gate) : (normSteps n gs).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [normSteps, ih]

def Matches (s : Finset Nat) (f : F) : Prop := ∀ k, 0 < uses k f ↔ k ∈ s
def Once (f : F) : Prop := ∀ k, uses k f ≤ 1

theorem scan_invariant (n : Nat) (gs : List Gate) (s : Finset Nat) (f : F)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hfs : Matches s f) :
    Matches (run s (normSteps n gs)).1 (rewind n gs f) ∧
      (Once f → (run s (normSteps n gs)).2.1 = 0 → Once (rewind n gs f)) := by
  induction gs generalizing s f with
  | nil => simp only [normSteps, run, rewind]; exact ⟨hfs, fun h _ => h⟩
  | cons g gs ih =>
    have og := ok g (by simp)
    have ot : ∀ h ∈ gs, (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ h.inputs.length ≤ 2 := by
      intro h hh; exact ok h (List.mem_cons_of_mem _ hh)
    let w := n + gs.length
    let a := readArgs w g
    let v := gateTerm w g
    have hv : ∀ k, uses k v = a.count k := fun k => count_args g w k og.1 og.2
    have hwa : w ∉ a := fun h => (Nat.lt_irrefl w) (readArgs_lt h)
    simp only [normSteps, dite_eq_left og.2, run, normalized, rewind]
    change Matches (if w ∈ s then
        let u := run (pushMany (s.erase w) a) (normSteps n gs)
        (u.1, u.2.1 + collisions (s.erase w) a, u.2.2.1 + notCost g,
          u.2.2.2.1 + (2 - (a.length + notCost g)), u.2.2.2.2 + 1)
      else run s (normSteps n gs)).1 (rewind n gs (subst w v f)) ∧
      (Once f → (if w ∈ s then
        let u := run (pushMany (s.erase w) a) (normSteps n gs)
        (u.1, u.2.1 + collisions (s.erase w) a, u.2.2.1 + notCost g,
          u.2.2.2.1 + (2 - (a.length + notCost g)), u.2.2.2.2 + 1)
        else run s (normSteps n gs)).2.1 = 0 → Once (rewind n gs (subst w v f)))
    by_cases hs : w ∈ s
    · simp only [ite_eq_left hs]
      let t := pushMany (s.erase w) a
      obtain ⟨hm, hn⟩ := ih t (subst w v f) ot (substitute_support s f v w a hfs hv hs hwa)
      refine ⟨hm, ?_⟩
      intro ho hc
      have hsum : (run t (normSteps n gs)).2.1 = 0 ∧ collisions (s.erase w) a = 0 :=
        Nat.add_eq_zero_iff.mp hc
      exact hn (preserve_once_zero s f v w a hfs hv hwa hsum.2 ho) hsum.1
    · simp only [ite_eq_right hs]
      have hw : uses w f = 0 := by
        by_contra hn
        exact hs ((hfs w).mp (by omega))
      have he := unused_substitute f v w hw
      have hm : Matches s (subst w v f) := fun k => by rw [he]; exact hfs k
      obtain ⟨m, h⟩ := ih s (subst w v f) ot hm
      refine ⟨m, fun ho hc => h ?_ hc⟩
      intro k
      rw [he]
      exact ho k

end ProofLanternFrontier

namespace ProofLanternUnate
open PEqualNP.CircuitLowerBounds

def Pos : F → Prop
  | .var _ => True
  | .const _ => True
  | .neg _ => False
  | .bin _ f g => Pos f ∧ Pos g

theorem absent_subst_eq (f g : F) (w : Nat) (h : uses w f = 0) : subst w g f = f := by
  induction f with
  | var i =>
    have hne : i ≠ w := by simpa [uses] using h
    simp [subst, hne]
  | const b => rfl
  | neg f ih => simp [subst, ih h]
  | bin s f t ihf iht =>
    simp only [uses, Nat.add_eq_zero_iff] at h
    simp [subst, ihf h.1, iht h.2]

theorem pos_subst (f g : F) (w : Nat) (pf : Pos f) (pg : Pos g) : Pos (subst w g f) := by
  induction f with
  | var i => by_cases hi : i = w <;> simp [subst, Pos, hi, pg]
  | const b => trivial
  | neg f ih => exact False.elim pf
  | bin s f t ihf iht => exact ⟨ihf pf.1, iht pf.2⟩

theorem pos_inputTerm (n i : Nat) : Pos (inputTerm n i) := by
  by_cases hi : i < n <;> simp [inputTerm, hi, Pos]

theorem pos_gateTerm (w : Nat) (g : Gate)
    (he : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hn : notCost g = 0) :
    Pos (gateTerm w g) := by
  obtain ⟨o, inp⟩ := g
  rcases he with he | he | he <;> cases he
  · cases inp with
    | nil => trivial
    | cons a tail =>
      cases tail with
      | nil => exact pos_inputTerm _ _
      | cons b bs => exact ⟨pos_inputTerm _ _, pos_inputTerm _ _⟩
  · cases inp with
    | nil => trivial
    | cons a tail =>
      cases tail with
      | nil => exact pos_inputTerm _ _
      | cons b bs => exact ⟨pos_inputTerm _ _, pos_inputTerm _ _⟩
  · simp [notCost] at hn

theorem pos_up (f : F) (k : Nat) (pf : Pos f) : Up k f := by
  induction f with
  | var i =>
    intro x y h
    by_cases hi : i = k
    · subst i; exact h.1
    · change x i ≤ y i
      rw [h.2 i hi]
  | const b => intro x y h; exact Bool.le_refl _
  | neg f ih => exact False.elim pf
  | bin s f g ihf ihg =>
    intro x y h
    exact bin_mono s _ _ _ _ (ihf pf.1 x y h) (ihg pf.2 x y h)

end ProofLanternUnate

namespace ProofLanternFrontier
open ProofLanternUnate
open PEqualNP.CircuitLowerBounds

theorem scan_pos (n : Nat) (gs : List Gate) (s : Finset Nat) (f : F)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hfs : Matches s f) (hp : Pos f)
    (hn : (run s (normSteps n gs)).2.2.1 = 0) :
    Pos (rewind n gs f) := by
  induction gs generalizing s f with
  | nil => exact hp
  | cons g gs ih =>
    have og := ok g (by simp)
    have ot : ∀ h ∈ gs, (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ h.inputs.length ≤ 2 := by
      intro h hh; exact ok h (List.mem_cons_of_mem _ hh)
    let w := n + gs.length
    let a := readArgs w g
    let v := gateTerm w g
    change Pos (rewind n gs (subst w v f))
    simp only [normSteps, dite_eq_left og.2, run, normalized] at hn
    change (if w ∈ s then
        let u := run (pushMany (s.erase w) a) (normSteps n gs)
        (u.1, u.2.1 + collisions (s.erase w) a, u.2.2.1 + notCost g,
          u.2.2.2.1 + (2 - (a.length + notCost g)), u.2.2.2.2 + 1)
        else run s (normSteps n gs)).2.2.1 = 0 at hn
    by_cases hs : w ∈ s
    · simp only [ite_eq_left hs] at hn
      obtain ⟨hn, hgn⟩ := Nat.add_eq_zero_iff.mp hn
      have hv : ∀ k, uses k v = a.count k := fun k => count_args g w k og.1 og.2
      have hwa : w ∉ a := fun h => (Nat.lt_irrefl w) (readArgs_lt h)
      exact ih _ _ ot (substitute_support s f v w a hfs hv hs hwa)
        (pos_subst f v w hp (pos_gateTerm w g og.1 hgn)) hn
    · simp only [ite_eq_right hs] at hn
      have hw : uses w f = 0 := by
        by_contra h
        exact hs ((hfs w).mp (by omega))
      rw [absent_subst_eq f v w hw]
      exact ih _ _ ot hfs hp hn

def outputFormula (n : Nat) (C : Circuit) : F :=
  rewind n C.gates.reverse (inputTerm (n + C.gates.length) C.output)

theorem gate_budget (n : Nat) (C : Circuit)
    (ok : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hv : C.output < n + C.gates.length) :
    let t := (run {C.output} (normSteps n C.gates.reverse)).1
    Matches t (outputFormula n C) ∧ t.card ≤ C.size + 1 ∧
      (∀ k, ¬ (Up k (outputFormula n C) ∨ Down k (outputFormula n C)) → t.card + 1 ≤ C.size) := by
  have hrev : ∀ g ∈ C.gates.reverse, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg; exact ok g (by simpa using hg)
  let f := inputTerm (n + C.gates.length) C.output
  have hf : Matches {C.output} f := by
    intro k
    by_cases hk : k = C.output
    · subst k; simp [f, inputTerm, hv, uses]
    · simp [f, inputTerm, hv, uses, hk, Ne.symm hk]
  have ho : Once f := by
    intro k
    simp only [f, inputTerm, ite_eq_left hv, uses]
    split <;> decide
  have hp : Pos f := pos_inputTerm _ _
  have hscan := scan_invariant n C.gates.reverse {C.output} f hrev hf
  have hpScan := scan_pos n C.gates.reverse {C.output} f hrev hf hp
  let gs := normSteps n C.gates.reverse
  have hlen : gs.length = C.size := by simp [gs, normSteps_length, Circuit.size]
  have bal := run_balance {C.output} gs
  have lb := run_gates_le {C.output} gs
  rcases he : run {C.output} gs with ⟨t, cc, nc, los, num⟩
  change Matches t (outputFormula n C) ∧ t.card ≤ C.size + 1 ∧ _
  change Matches (run {C.output} gs).1 (outputFormula n C) ∧
     (Once f → (run {C.output} gs).2.1 = 0 → Once (outputFormula n C)) at hscan
  change (run {C.output} gs).2.2.1 = 0 → Pos (outputFormula n C) at hpScan
  rw [he] at bal lb hscan hpScan
  change Matches t (outputFormula n C) ∧ (Once f → cc = 0 → Once (outputFormula n C)) at hscan
  change nc = 0 → Pos (outputFormula n C) at hpScan
  change t.card + cc + nc + los = _ at bal
  simp at bal
  change num ≤ gs.length at lb
  refine ⟨hscan.1, by omega, ?_⟩
  intro k h
  change t.card + 1 ≤ C.size
  have hcc : 0 < cc := by
    by_contra hcc
    exact h (once_unate _ k (hscan.2 ho (by omega) k))
  have hnc : 0 < nc := by
    by_contra hnc
    exact h (Or.inl (pos_up _ k (hpScan (by omega))))
  omega

end ProofLanternFrontier

namespace ProofLanternUnate

theorem support_congr (f : F) (x y : Nat → Bool)
    (agree : ∀ k, 0 < uses k f → x k = y k) : eval x f = eval y f := by
  induction f with
  | var i => exact agree i (by simp [uses])
  | const b => rfl
  | neg f ih =>
    simp only [uses] at agree
    simp only [eval, ih agree]
  | bin op f g ihf ihg =>
    have a : ∀ k, 0 < uses k f → x k = y k := by
      intro k hk
      apply agree k
      simp only [uses]; omega
    have b : ∀ k, 0 < uses k g → x k = y k := by
      intro k hk
      apply agree k
      simp only [uses]; omega
    simp only [eval, ihf a, ihg b]

end ProofLanternUnate


namespace ProofLanternMatch
open ProofLanternUnate
open ProofLanternFrontier
open PEqualNP.CircuitLowerBounds

def pairFlags {N : Nat} (a b : Fin N → Nat) (u v : Fin N) (k : Nat) : Bool :=
  decide (k = a u ∨ k = b v)

def diag {N : Nat} (yes : Bool) (u v : Fin N) : Bool :=
  if u = v then yes else !yes

theorem eraseLeft {N : Nat} (f : F) (a b : Fin N → Nat) (u v : Fin N)
    (ha : uses (a u) f = 0) :
    eval (pairFlags a b u v) f = eval (fun k => decide (k = b v)) f := by
  apply support_congr
  intro k hk
  have hne : k ≠ a u := by
    intro hh; rw [hh, ha] at hk; omega
  simp [pairFlags, hne]

theorem missing_unique {N : Nat} (f : F) (a b : Fin N → Nat) (yes : Bool)
    (h : ∀ u v, eval (pairFlags a b u v) f = diag yes u v)
    (u v : Fin N) (hu : uses (a u) f = 0) (hv : uses (a v) f = 0) : u = v := by
  by_contra hne
  have hi := eraseLeft f a b u u hu
  have hj := eraseLeft f a b v u hv
  rw [h] at hi hj
  simp [diag, Ne.symm hne] at hi hj
  cases yes <;> simp_all

theorem missing_forces_binate {N : Nat} (f : F) (a b : Fin N → Nat) (yes : Bool)
    (dis : ∀ u v, a u ≠ b v)
    (h : ∀ u v, eval (pairFlags a b u v) f = diag yes u v)
    (i j : Fin N) (hi : uses (a i) f = 0) (hij : i ≠ j) :
    ¬(Up (a j) f ∨ Down (a j) f) := by
  have adj (v : Fin N) : Adj (a j) (fun k => decide (k = b v)) (pairFlags a b j v) := by
    constructor
    · simp [pairFlags, dis j v]
    · intro k hk; simp [pairFlags, hk]
  have h0 : eval (fun k => decide (k = b i)) f = yes := by
    rw [← eraseLeft f a b i i hi, h]
    simp [diag]
  have h1 : eval (pairFlags a b j i) f = !yes := by
    rw [h]; simp [diag, Ne.symm hij]
  have h2 : eval (fun k => decide (k = b j)) f = !yes := by
    rw [← eraseLeft f a b i j hi, h]; simp [diag, hij]
  have h3 : eval (pairFlags a b j j) f = yes := by
    rw [h]; simp [diag]
  intro hp
  rcases hp with hp | hp
  · have hA := hp _ _ (adj i)
    have hB := hp _ _ (adj j)
    rw [h0, h1] at hA
    rw [h2, h3] at hB
    cases yes <;> simp_all <;> contradiction
  · have hA := hp _ _ (adj i)
    have hB := hp _ _ (adj j)
    rw [h0, h1] at hA
    rw [h2, h3] at hB
    cases yes <;> simp_all <;> contradiction

theorem swapped {N : Nat} (f : F) (a b : Fin N → Nat) (yes : Bool)
    (h : ∀ u v, eval (pairFlags a b u v) f = diag yes u v) :
    ∀ u v, eval (pairFlags b a u v) f = diag yes u v := by
  intro u v
  have he : pairFlags b a u v = pairFlags a b v u := by funext k; simp [pairFlags, or_comm]
  rw [he,h]
  by_cases he : u = v
  · subst v; rfl
  · simp [diag, he, Ne.symm he]

end ProofLanternMatch

namespace ProofLanternMatch
open ProofLanternUnate ProofLanternFrontier
open PEqualNP.CircuitLowerBounds

def liveIndices {N : Nat} (a : Fin N → Nat) (f : F) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < uses (a i) f)

theorem one_side_count {N : Nat} (a b : Fin N → Nat) (f : F) (yes : Bool)
    (h : ∀ u v, eval (pairFlags a b u v) f = diag yes u v) :
    N - 1 ≤ (liveIndices a f).card := by
  let absent := (Finset.univ : Finset (Fin N)).filter (fun i => ¬0 < uses (a i) f)
  have hle : absent.card ≤ 1 := Finset.card_le_one.mpr (by
    intro u hu v hv
    have hu' : ¬0 < uses (a u) f := (Finset.mem_filter.mp hu).2
    have hv' : ¬0 < uses (a v) f := (Finset.mem_filter.mp hv).2
    exact missing_unique f a b yes h u v (by omega) (by omega))
  have hsum : (liveIndices a f).card + absent.card = N := by
    simpa [liveIndices, absent] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
        (fun i => 0 < uses (a i) f))
  omega

theorem both_sides_count {N : Nat} (a b : Fin N → Nat) (f : F) (t : Finset Nat)
    (ia : Function.Injective a) (ib : Function.Injective b)
    (dis : ∀ u v, a u ≠ b v) (ht : Matches t f) :
    (liveIndices a f).card + (liveIndices b f).card ≤ t.card := by
  let A := (liveIndices a f).image a
  let B := (liveIndices b f).image b
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro k hA hB
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hA
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hB
    exact dis u v (hu.trans hv.symm)
  have hsubA : A ⊆ t := by
    intro k hk
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact (ht (a u)).mp (Finset.mem_filter.mp hu).2
  have hsubB : B ⊆ t := by
    intro k hk
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact (ht (b u)).mp (Finset.mem_filter.mp hu).2
  have hcard := Finset.card_le_card (Finset.union_subset hsubA hsubB)
  rw [Finset.card_union_of_disjoint hd] at hcard
  simpa only [A, B, Finset.card_image_of_injective _ ia, Finset.card_image_of_injective _ ib] using hcard

theorem abstract_lower {N s : Nat} (hn : 2 ≤ N) (a b : Fin N → Nat)
    (ia : Function.Injective a) (ib : Function.Injective b)
    (dis : ∀ u v, a u ≠ b v) (f : F) (yes : Bool) (t : Finset Nat)
    (ht : Matches t f) (hsmall : t.card ≤ s + 1)
    (hb : ∀ i, ¬(Up i f ∨ Down i f) → t.card + 1 ≤ s)
    (h : ∀ u v, eval (pairFlags a b u v) f = diag yes u v) : 2 * N - 1 ≤ s := by
  have htally := both_sides_count a b f t ia ib dis ht
  have hswap := swapped f a b yes h
  have la := one_side_count a b f yes h
  have lb := one_side_count b a f yes hswap
  have other (i : Fin N) : ∃ j : Fin N, i ≠ j := by
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun he => by have he' := congrArg Fin.val he; simp [hi] at he'⟩
    · exact ⟨⟨0, by omega⟩, fun he => hi (congrArg Fin.val he)⟩
  by_cases ha : ∃ i : Fin N, uses (a i) f = 0
  · obtain ⟨i, hz⟩ := ha
    obtain ⟨j, hij⟩ := other i
    have hh := hb _ (missing_forces_binate f a b yes dis h i j hz hij)
    omega
  by_cases hc : ∃ i : Fin N, uses (b i) f = 0
  · obtain ⟨i, hz⟩ := hc
    obtain ⟨j, hij⟩ := other i
    have hh := hb _ (missing_forces_binate f b a yes (fun u v => Ne.symm (dis v u)) hswap i j hz hij)
    omega
  have htop {c : Fin N → Nat} (hnz : ¬ ∃ i : Fin N, uses (c i) f = 0) :
      (liveIndices c f).card = N := by
    have eq : liveIndices c f = Finset.univ := by
      ext i
      simp only [liveIndices, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_contra hz
      exact hnz ⟨i, by omega⟩
    simp [eq]
  have ea := htop ha
  have eb := htop hc
  omega

end ProofLanternMatch

namespace ProofLanternMatch
open ProofLanternUnate ProofLanternFrontier
open PEqualNP.CircuitLowerBounds

def leftIdx {N : Nat} (u : Fin N) : Nat := u.val
def rightIdx {N : Nat} (v : Fin N) : Nat := N + v.val

def pairList {N : Nat} (u v : Fin N) : List Bool :=
  List.ofFn (fun i : Fin N => decide (i = u)) ++ List.ofFn (fun j : Fin N => decide (j = v))

theorem pairList_length {N : Nat} (u v : Fin N) : (pairList u v).length = N + N := by
  simp [pairList]

theorem pairList_flags {N : Nat} (u v : Fin N) :
    (fun k => (pairList u v).getD k false) = pairFlags leftIdx rightIdx u v := by
  funext k
  have hu : u.val < N := u.isLt
  have hv : v.val < N := v.isLt
  unfold pairList pairFlags leftIdx rightIdx
  let a := List.ofFn (fun i : Fin N => decide (i = u))
  let b := List.ofFn (fun j : Fin N => decide (j = v))
  have ha : a.length = N := by simp [a]
  have hb : b.length = N := by simp [b]
  change (a ++ b).getD k false = decide (k = u.val ∨ k = N + v.val)
  by_cases kl : k < N
  · have nah : k ≠ N + v.val := by omega
    rw [List.getD_append _ _ _ _ (by simpa [ha] using kl), List.getD_eq_getElem _ _ (by simpa [ha] using kl)]
    have he : (⟨k, kl⟩ : Fin N) = u ↔ k = u.val := Fin.ext_iff
    simp [a, List.getElem_ofFn, he, nah]
  · rw [List.getD_append_right _ _ _ _ (by rw [ha]; omega), ha]
    have nau : k ≠ u.val := by omega
    by_cases kr : k - N < N
    · rw [List.getD_eq_getElem _ _ (by simpa [hb] using kr)]
      have he : (⟨k - N, kr⟩ : Fin N) = v ↔ k = N + v.val := by rw [Fin.ext_iff]; change k - N = v.val ↔ _; omega
      simp [b, List.getElem_ofFn, he, nau]
    · rw [List.getD_eq_default _ _ (by rw [hb]; omega)]
      have nav : k ≠ N + v.val := by omega
      simp [nau, nav]

theorem matching_gate_lower {N : Nat} (hn : 2 ≤ N) (C : Circuit) (yes : Bool)
    (ok : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (reps : ∀ u v : Fin N, C.eval (pairList u v) = diag yes u v) : 2 * N - 1 ≤ C.size := by
  have valid : C.output < N + N + C.gates.length := by
    by_contra hout
    have off (u v : Fin N) : C.eval (pairList u v) = false := by
      unfold Circuit.eval
      apply List.getD_eq_default
      change (C.gates.foldl projectStep (pairList u v)).length ≤ C.output
      rw [projectFold_length, pairList_length]
      omega
    let a : Fin N := ⟨0, by omega⟩
    let b : Fin N := ⟨1, by omega⟩
    have diff : a ≠ b := by intro h; have h1 := congrArg Fin.val h; simp [a,b] at h1
    have p := reps a a
    have q := reps a b
    rw [off] at p q
    simp [diag,diff] at p q
    rw [p] at q; contradiction
  let f := outputFormula (N + N) C
  obtain ⟨hs,hcard,hb⟩ := gate_budget (N + N) C ok valid
  have t (u v : Fin N) : eval (pairFlags leftIdx rightIdx u v) f = diag yes u v := by
    rw [← pairList_flags]
    have he := circuit_expands C (pairList u v) ok
    rw [pairList_length] at he
    exact he.trans (reps u v)
  exact abstract_lower hn leftIdx rightIdx Fin.val_injective
    (fun u v h => Fin.val_injective (Nat.add_left_cancel h))
    (fun u v hv => by have hu := u.isLt; unfold leftIdx rightIdx at hv; omega)
    f yes _ hs hcard hb t

end ProofLanternMatch

namespace ProofLanternMatch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem project_diagonal_lower (N : Nat) (hn : 2 ≤ N) (C : Circuit) (yes : Bool)
    (hc : FanInTwo C) (hr : Represents (diag yes : Fin N → Fin N → Bool) C) :
    2 * N - 1 ≤ C.size := by
  apply matching_gate_lower hn C yes _ hr
  intro g hg
  simpa using hc g hg

theorem project_matching_lower (N : Nat) (hn : 2 ≤ N) (C : Circuit)
    (hc : FanInTwo C) (hr : Represents (fun u v : Fin N => decide (u = v)) C) :
    2 * N - 1 ≤ C.size := by
  apply project_diagonal_lower N hn C true hc
  intro u v
  have h := hr u v
  by_cases he : u = v <;> simpa [diag, he] using h

theorem project_crown_lower (N : Nat) (hn : 2 ≤ N) (C : Circuit)
    (hc : FanInTwo C) (hr : Represents (fun u v : Fin N => decide (u ≠ v)) C) :
    2 * N - 1 ≤ C.size := by
  apply project_diagonal_lower N hn C false hc
  intro u v
  have h := hr u v
  by_cases he : u = v <;> simpa [diag, he] using h

end ProofLanternMatch
