import Init

namespace ProofLantern.ORFrontier

def push (v : Nat) (todo : List Nat) : List Nat :=
  if v ∈ todo then todo else v :: todo

theorem mem_push (u v : Nat) (xs : List Nat) : u ∈ push v xs ↔ u = v ∨ u ∈ xs := by
  unfold push
  split
  · rename_i hv
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact hv
      · exact h
  · simp

theorem len_push (v : Nat) (xs : List Nat) : (push v xs).length ≤ xs.length + 1 := by
  unfold push
  split <;> simp

def remove (g : Nat) (xs : List Nat) := xs.filter (fun x => decide (x ≠ g))

theorem mem_remove (g x : Nat) (xs : List Nat) : x ∈ remove g xs ↔ x ∈ xs ∧ x ≠ g := by
  simp [remove]

theorem len_remove_lt (g : Nat) (xs : List Nat) (hg : g ∈ xs) :
    (remove g xs).length < xs.length := by
  induction xs with
  | nil => simp at hg
  | cons x xs ih =>
    by_cases h : x = g
    · subst x
      simpa [remove] using Nat.lt_succ_of_le (List.length_filter_le (fun x => decide (x ≠ g)) xs)
    · have ht : g ∈ xs := (List.mem_cons.mp hg).resolve_left (Ne.symm h)
      simpa [remove, h] using ih ht

def expand (todo : List Nat) (g a b : Nat) := push a (push b (remove g todo))

theorem len_expand (todo : List Nat) (g a b : Nat) (hg : g ∈ todo) :
    (expand todo g a b).length ≤ todo.length + 1 := by
  have e := len_remove_lt g todo hg
  have h₁ := len_push a (push b (remove g todo))
  have h₂ := len_push b (remove g todo)
  unfold expand
  omega

def Live (S : Nat → Nat → Prop) (xs : List Nat) (x : Nat) :=
  ∃ q ∈ xs, S q x

theorem live_expand (S : Nat → Nat → Prop) (todo : List Nat) (g a b x : Nat)
    (hg : g ∈ todo) (hS : S g x ↔ S a x ∨ S b x) :
    Live S (expand todo g a b) x ↔ Live S todo x := by
  unfold Live expand
  constructor
  · rintro ⟨q, hq, hx⟩
    rw [mem_push, mem_push] at hq
    rcases hq with rfl | rfl | hq
    · exact ⟨g, hg, hS.mpr (Or.inl hx)⟩
    · exact ⟨g, hg, hS.mpr (Or.inr hx)⟩
    · exact ⟨q, ((mem_remove g q todo).mp hq).1, hx⟩
  · rintro ⟨q, hq, hx⟩
    by_cases eq : q = g
    · subst q
      rcases hS.mp hx with ha | hb
      · exact ⟨a, (mem_push _ _ _).mpr (Or.inl rfl), ha⟩
      · exact ⟨b, (mem_push _ _ _).mpr (Or.inr ((mem_push _ _ _).mpr (Or.inl rfl))), hb⟩
    · exact ⟨q, (mem_push _ _ _).mpr (Or.inr ((mem_push _ _ _).mpr
        (Or.inr ((mem_remove g q todo).mpr ⟨hq, eq⟩)))), hx⟩

inductive ExpandSteps (S : Nat → Nat → Prop) : List Nat → List Nat → Nat → Prop
  | done (xs) : ExpandSteps S xs xs 0
  | step {xs ys g a b m} : g ∈ xs → (∀ x, S g x ↔ S a x ∨ S b x) →
      ExpandSteps S (expand xs g a b) ys m → ExpandSteps S xs ys (m + 1)

theorem frontier_bound (S : Nat → Nat → Prop) {xs ys : List Nat} {m : Nat}
    (h : ExpandSteps S xs ys m) :
    ys.length ≤ xs.length + m ∧ ∀ x, Live S ys x ↔ Live S xs x := by
  induction h with
  | done => simp
  | @step xs ys g a b m hg hS _ ih =>
    have hb := len_expand xs g a b hg
    exact ⟨by omega, fun x => (ih.2 x).trans (live_expand S xs g a b x hg (hS x))⟩


/-- Backward scheduling with an arbitrary terminal set: the largest nonterminal
index is expanded at most once; all new nonterminals have smaller indices. -/
theorem exists_schedule (S : Nat → Nat → Prop) (T : Nat → Prop) (bound : Nat)
    (rule : ∀ q < bound, ¬ T q → ∃ a b,
       (a < q ∨ T a) ∧ (b < q ∨ T b) ∧ (∀ x, S q x ↔ S a x ∨ S b x))
    (xs : List Nat) (hxs : ∀ q ∈ xs, q < bound ∨ T q) :
    ∃ ys m, m ≤ bound ∧ (∀ q ∈ ys, T q) ∧ ExpandSteps S xs ys m := by
  classical
  induction bound generalizing xs with
  | zero =>
    exact ⟨xs, 0, Nat.le_refl _, fun q hq => (hxs q hq).resolve_left (Nat.not_lt_zero q),
      ExpandSteps.done xs⟩
  | succ j ih =>
    have rule' : ∀ q < j, ¬ T q → ∃ a b,
        (a < q ∨ T a) ∧ (b < q ∨ T b) ∧ (∀ x, S q x ↔ S a x ∨ S b x) :=
      fun q hq => rule q (Nat.lt_succ_of_lt hq)
    by_cases active : j ∈ xs ∧ ¬ T j
    · obtain ⟨a,b,ha,hb,hs⟩ := rule j (Nat.lt_succ_self j) active.2
      have hnew : ∀ q ∈ expand xs j a b, q < j ∨ T q := by
        intro q hq
        unfold expand at hq
        rw [mem_push, mem_push] at hq
        rcases hq with rfl | rfl | hq
        · exact ha
        · exact hb
        · obtain ⟨hq, hne⟩ := (mem_remove j q xs).mp hq
          exact (hxs q hq).imp_left (fun ht => by omega)
      obtain ⟨ys,m,hcap,hy,steps⟩ := ih rule' (expand xs j a b) hnew
      exact ⟨ys,m+1,by omega,hy,ExpandSteps.step active.1 hs steps⟩
    · have hnew : ∀ q ∈ xs, q < j ∨ T q := by
        intro q hq
        rcases hxs q hq with ht | hT
        · by_cases he : q = j
          · subst q
            exact Or.inr (Classical.byContradiction (fun hn => active ⟨hq,hn⟩))
          · exact Or.inl (by omega)
        · exact Or.inr hT
      obtain ⟨ys,m,hcap,hy,steps⟩ := ih rule' xs hnew
      exact ⟨ys,m,by omega,hy,steps⟩

theorem terminal_frontier_bound (S : Nat → Nat → Prop) (T : Nat → Prop) (bound : Nat)
    (rule : ∀ q < bound, ¬ T q → ∃ a b,
       (a < q ∨ T a) ∧ (b < q ∨ T b) ∧ (∀ x, S q x ↔ S a x ∨ S b x))
    (xs : List Nat) (hxs : ∀ q ∈ xs, q < bound ∨ T q) :
    ∃ ys : List Nat, ys.length ≤ xs.length + bound ∧ (∀ q ∈ ys, T q) ∧
      ∀ x, Live S ys x ↔ Live S xs x := by
  obtain ⟨ys,m,hcap,hy,steps⟩ := exists_schedule S T bound rule xs hxs
  obtain ⟨hlen,hs⟩ := frontier_bound S steps
  exact ⟨ys,by omega,hy,hs⟩


theorem terminal_support (S : Nat → Nat → Prop) (T : Nat → Prop) (bound : Nat)
    (rule : ∀ q < bound, ¬ T q → ∃ a b,
       (a < q ∨ T a) ∧ (b < q ∨ T b) ∧ (∀ x, S q x ↔ S a x ∨ S b x))
    (base : ∀ q, T q → ∀ x, S q x ↔ q = x)
    (xs : List Nat) (hxs : ∀ q ∈ xs, q < bound ∨ T q) :
    ∃ ys : List Nat, ys.length ≤ xs.length + bound ∧ (∀ q ∈ ys, T q) ∧
      ∀ x, x ∈ ys ↔ Live S xs x := by
  obtain ⟨ys,hlen,hy,hS⟩ := terminal_frontier_bound S T bound rule xs hxs
  refine ⟨ys, hlen, hy, ?_⟩
  intro x
  rw [← hS x]
  constructor
  · intro hx
    exact ⟨x,hx,(base x (hy x hx) x).mpr rfl⟩
  · rintro ⟨q,hq,hs⟩
    have he := (base q (hy q hq) x).mp hs
    simpa [he] using hq

end ProofLantern.ORFrontier

namespace ProofLantern.DenseOR

/-- Number of selected OR gate wires strictly before the index. -/
def rank (sel : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j+1 => rank sel j + if sel j then 1 else 0

theorem rank_mono (sel : Nat → Bool) {i j : Nat} (h : i ≤ j) :
    rank sel i ≤ rank sel j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem rank_strict (sel : Nat → Bool) {i j : Nat} (hs : sel i = true) (h : i < j) :
    rank sel i < rank sel j := by
  have hi : rank sel i.succ = rank sel i + 1 := by simp [rank, hs]
  have hj := rank_mono sel (Nat.succ_le_of_lt h)
  rw [hi] at hj
  omega

/-- Nonselected (terminal) wires are carried into a disjoint index region. -/
def encode (sel : Nat → Bool) (wireCap i : Nat) : Nat :=
  if sel i then rank sel i else rank sel wireCap + i

theorem gate_below (sel : Nat → Bool) {i cap} (hi : i < cap) (hs : sel i = true) :
    encode sel cap i < rank sel cap := by
  simp only [encode, hs, ite_true]
  exact rank_strict sel hs hi

theorem terminal_above (sel : Nat → Bool) {i cap} (hs : sel i = false) :
    rank sel cap ≤ encode sel cap i := by
  simp [encode, hs]

theorem earlier_than_parent (sel : Nat → Bool) {i j cap} (h : i < j) (hi : sel i = true)
    (hj : sel j = true) : encode sel cap i < encode sel cap j := by
  simpa [encode,hi,hj] using rank_strict sel hi h

theorem encode_injective_below (sel : Nat → Bool) {i j cap} (hi : i < cap) (hj : j < cap)
    (h : encode sel cap i = encode sel cap j) : i = j := by
  cases si : sel i <;> cases sj : sel j
  · simp [encode,si,sj] at h
    exact h
  · have a := terminal_above sel (cap := cap) si
    have b := gate_below sel hj sj
    omega
  · have a := gate_below sel hi si
    have b := terminal_above sel (cap := cap) sj
    omega
  · rcases Nat.lt_trichotomy i j with hij | hEq | hji
    · have t := earlier_than_parent sel (cap := cap) hij si sj
      omega
    · exact hEq
    · have t := earlier_than_parent sel (cap := cap) hji sj si
      omega


/-- Every packed OR position corresponds to a selected wire. -/
theorem rank_surj (sel : Nat → Bool) (cap : Nat) {r : Nat} (hr : r < rank sel cap) :
    ∃ i < cap, sel i = true ∧ encode sel cap i = r := by
  induction cap with
  | zero => simp [rank] at hr
  | succ j ih =>
    cases h : sel j
    · have hr' : r < rank sel j := by simpa [rank, h] using hr
      obtain ⟨i,hi,hs,he⟩ := ih hr'
      exact ⟨i,Nat.lt_succ_of_lt hi,hs,by simpa [encode,hs] using he⟩
    · by_cases be : r < rank sel j
      · obtain ⟨i,hi,hs,he⟩ := ih be
        exact ⟨i,Nat.lt_succ_of_lt hi,hs,by simpa [encode,hs] using he⟩
      · have he : r = rank sel j := by
          simp [rank,h] at hr
          omega
        exact ⟨j,Nat.lt_succ_self j,h,by simp [encode,h,he]⟩

end ProofLantern.DenseOR


namespace ProofLantern.DenseOR

open ProofLantern.ORFrontier

/-- Count OR dependencies by selected gates, rather than by the enclosing raw
wire index range. Non-OR wires are terminals; selected-node support is the
union of the two earlier operand supports. -/
theorem packed_support (sel : Nat → Bool) (cap : Nat) (S : Nat → Nat → Prop)
    (step : ∀ w < cap, sel w = true → ∃ a b, a < w ∧ b < w ∧
      (∀ x, S w x ↔ S a x ∨ S b x))
    (base : ∀ w < cap, sel w = false → ∀ x, S w x ↔ w = x)
    (roots : List Nat) (hroots : ∀ w ∈ roots, w < cap) :
    ∃ zs : List Nat, zs.length ≤ roots.length + rank sel cap ∧
      ∀ x < cap, encode sel cap x ∈ zs ↔ Live S roots x := by
  let T : Nat → Prop := fun e => rank sel cap ≤ e
  let R : Nat → Nat → Prop := fun e x => ∃ w < cap, encode sel cap w = e ∧ S w x
  have hR (w x : Nat) (h : w < cap) : R (encode sel cap w) x ↔ S w x := by
    constructor
    · rintro ⟨v,hv,he,hs⟩
      have e := encode_injective_below sel hv h he
      simpa [e] using hs
    · intro hs
      exact ⟨w,h,rfl,hs⟩
  have ltTerm (a w : Nat) (haz : a < w) (hwsel : sel w = true) :
      encode sel cap a < encode sel cap w ∨ T (encode sel cap a) := by
    cases ha : sel a
    · exact Or.inr (terminal_above sel ha)
    · exact Or.inl (earlier_than_parent sel haz ha hwsel)
  have rule : ∀ e < rank sel cap, ¬ T e → ∃ a b,
       (a < e ∨ T a) ∧ (b < e ∨ T b) ∧ (∀ x, R e x ↔ R a x ∨ R b x) := by
    intro e he _
    obtain ⟨w,hw,hs,rfl⟩ := rank_surj sel cap he
    obtain ⟨a,b,ha,hb,hsup⟩ := step w hw hs
    refine ⟨encode sel cap a, encode sel cap b, ltTerm a w ha hs, ltTerm b w hb hs, ?_⟩
    intro x
    rw [hR w x hw, hR a x (Nat.lt_trans ha hw), hR b x (Nat.lt_trans hb hw)]
    exact hsup x
  have start : ∀ e ∈ roots.map (encode sel cap), e < rank sel cap ∨ T e := by
    intro e he
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
    cases ho : sel w
    · exact Or.inr (terminal_above sel ho)
    · exact Or.inl (gate_below sel (hroots w hw) ho)
  obtain ⟨zs,hlen,hT,hlive⟩ :=
    terminal_frontier_bound R T (rank sel cap) rule (roots.map (encode sel cap)) start
  have rootsLive (x : Nat) : Live R (roots.map (encode sel cap)) x ↔ Live S roots x := by
    constructor
    · rintro ⟨e,he,hr⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
      exact ⟨w,hw,(hR w x (hroots w hw)).mp hr⟩
    · rintro ⟨w,hw,hs⟩
      exact ⟨encode sel cap w,List.mem_map.mpr ⟨w,hw,rfl⟩,(hR w x (hroots w hw)).mpr hs⟩
  refine ⟨zs,by simpa using hlen, ?_⟩
  intro x hx
  rw [← rootsLive x, ← hlive x]
  constructor
  · intro hmem
    have ht := hT _ hmem
    have hsel : sel x = false := by
      cases hv : sel x
      · rfl
      · have hlt := gate_below sel hx hv
        exact False.elim (Nat.not_lt_of_ge ht hlt)
    exact ⟨encode sel cap x,hmem,(hR x x hx).mpr ((base x hx hsel x).mpr rfl)⟩
  · rintro ⟨e,he,hr⟩
    obtain ⟨w,hw,hwEq,hs⟩ := hr
    have ht := hT e he
    have hsel : sel w = false := by
      cases hv : sel w
      · rfl
      · have hlt := gate_below sel hw hv
        rw [hwEq] at hlt
        exact False.elim (Nat.not_lt_of_ge ht hlt)
    have hEq := (base w hw hsel x).mp hs
    simpa [← hEq,hwEq] using he

end ProofLantern.DenseOR
