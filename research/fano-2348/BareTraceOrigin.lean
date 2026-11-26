import Init

namespace ProofLantern.EdgeOrigin

inductive Op where
  | any | both

def Cross (base line delta : Nat → Bool) (a b : Nat) : Prop :=
  base a = false ∧ line a = true ∧ delta a = true ∧
  base b = true ∧ line b = false

private theorem and_step (ba bb la lb da db : Bool)
    (h0 : (ba && bb) = false) (h7 : (la && lb) = false)
    (hd : ((ba && db) || (da && bb)) = true) :
    (ba = false ∧ la = false ∧ da = true) ∨
    (bb = false ∧ lb = false ∧ db = true) ∨
    (ba = false ∧ la = true ∧ da = true ∧ bb = true ∧ lb = false) ∨
    (bb = false ∧ lb = true ∧ db = true ∧ ba = true ∧ la = false) := by
  cases ba <;> cases bb <;> cases la <;> cases lb <;> cases da <;> cases db <;>
    simp_all

inductive Supports (g : Nat → Option (Op × Nat × Nat)) : Nat → Nat → Prop
  | refl (i) : Supports g i i
  | left {j a b i op} : Supports g j a → g i = some (op,a,b) → Supports g j i
  | right {j a b i op} : Supports g j b → g i = some (op,a,b) → Supports g j i

theorem origin (g : Nat → Option (Op × Nat × Nat))
    (base line delta : Nat → Bool)
    (leaf : ∀ i, g i = none → delta i = true → line i = true)
    (earlier : ∀ i op a b, g i = some (op,a,b) → a < i ∧ b < i)
    (orStep : ∀ i a b, g i = some (.any,a,b) →
      base i = (base a || base b) ∧ line i = (line a || line b) ∧
      delta i = (delta a || delta b))
    (andStep : ∀ i a b, g i = some (.both,a,b) →
      base i = (base a && base b) ∧ line i = (line a && line b) ∧
      delta i = ((base a && delta b) || (delta a && base b)))
    (i : Nat) (h0 : base i = false) (h7 : line i = false) (hd : delta i = true) :
    ∃ j ≤ i, Supports g j i ∧ ∃ a b, g j = some (.both,a,b) ∧
      (Cross base line delta a b ∨ Cross base line delta b a) := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    cases hg : g i with
    | none => exact False.elim (Bool.noConfusion (h7.symm.trans (leaf i hg hd)))
    | some z =>
      obtain ⟨op,a,b⟩ := z
      obtain ⟨ha,hb⟩ := earlier i op a b hg
      cases op with
      | any =>
        obtain ⟨hba,hla,hda⟩ := orStep i a b hg
        rw [hba, Bool.or_eq_false_iff] at h0
        rw [hla, Bool.or_eq_false_iff] at h7
        rw [hda, Bool.or_eq_true] at hd
        rcases hd with hd | hd
        · obtain ⟨j,hj,hc,hh⟩ := ih a ha h0.1 h7.1 hd
          exact ⟨j,Nat.le_trans hj (Nat.le_of_lt ha),Supports.left hc hg,hh⟩
        · obtain ⟨j,hj,hc,hh⟩ := ih b hb h0.2 h7.2 hd
          exact ⟨j,Nat.le_trans hj (Nat.le_of_lt hb),Supports.right hc hg,hh⟩
      | both =>
        obtain ⟨hba,hla,hda⟩ := andStep i a b hg
        rw [hba] at h0
        rw [hla] at h7
        rw [hda] at hd
        rcases and_step _ _ _ _ _ _ h0 h7 hd with u | u | h | h
        · obtain ⟨j,hj,hc,hh⟩ := ih a ha u.1 u.2.1 u.2.2
          exact ⟨j,Nat.le_trans hj (Nat.le_of_lt ha),Supports.left hc hg,hh⟩
        · obtain ⟨j,hj,hc,hh⟩ := ih b hb u.1 u.2.1 u.2.2
          exact ⟨j,Nat.le_trans hj (Nat.le_of_lt hb),Supports.right hc hg,hh⟩
        · exact ⟨i,Nat.le_refl _,Supports.refl i,a,b,hg,Or.inl h⟩
        · exact ⟨i,Nat.le_refl _,Supports.refl i,a,b,hg,Or.inr h⟩

theorem redundant (read : Bool → Bool) (lineMono : read true = true)
    (lv : Bool) : (lv && read lv) = lv := by
  cases lv <;> simp [lineMono]

/-- For an AND that reads the bare line, the other operand either absorbs
the whole AND or has an earlier, dependency-connected edge-origin AND. -/
theorem bare_dichotomy (g : Nat → Option (Op × Nat × Nat))
    (base line delta : Nat → Bool)
    (leaf : ∀ i, g i = none → delta i = true → line i = true)
    (earlier : ∀ i op a b, g i = some (op,a,b) → a < i ∧ b < i)
    (orStep : ∀ i a b, g i = some (.any,a,b) →
      base i = (base a || base b) ∧ line i = (line a || line b) ∧
      delta i = (delta a || delta b))
    (andStep : ∀ i a b, g i = some (.both,a,b) →
      base i = (base a && base b) ∧ line i = (line a && line b) ∧
      delta i = ((base a && delta b) || (delta a && base b)))
    (value : Nat → Bool) (j bare other : Nat)
    (mark : g j = some (.both,bare,other) ∨ g j = some (.both,other,bare))
    (otherBase : base other = false) (otherDelta : delta other = true)
    (lineDom : line other = true → value bare = true → value other = true) :
    (line other = true ∧ (value bare && value other) = value bare) ∨
    (∃ i < j, Supports g i j ∧ ∃ a b, g i = some (.both,a,b) ∧
      (Cross base line delta a b ∨ Cross base line delta b a)) := by
  cases h : line other with
  | true =>
    left
    refine ⟨rfl, ?_⟩
    cases v : value bare with
    | false => rfl
    | true => exact lineDom h v
  | false =>
    right
    obtain ⟨i,hi,hs,hg⟩ := origin g base line delta leaf earlier orStep andStep
      other otherBase h otherDelta
    rcases mark with hm | hm
    · exact ⟨i,Nat.lt_of_le_of_lt hi (earlier j .both bare other hm).2,Supports.right hs hm,hg⟩
    · exact ⟨i,Nat.lt_of_le_of_lt hi (earlier j .both other bare hm).1,Supports.left hs hm,hg⟩

end ProofLantern.EdgeOrigin


namespace ProofLantern.BarePrefix

structure Signal where
  value : Bool
  base : Bool
  delta : Bool

def bor (a b : Signal) : Signal :=
  ⟨a.value || b.value, a.base || b.base, a.delta || b.delta⟩

def band (a b : Signal) : Signal :=
  ⟨a.value && b.value, a.base && b.base, (a.base && b.delta) || (a.delta && b.base)⟩

def ReadsEndpoint (s : Signal) (p l : Bool) :=
  (s.base = true → p = true → s.value = true) ∧
  (s.delta = true → l = true → s.value = true)

def Primary (s : Signal) (p l : Bool) :=
  (s.base = true → s.value = p) ∧ (s.delta = true → s.value = l) ∧
  ¬ (s.base = true ∧ s.delta = true)

theorem primary_reads (s : Signal) (p l : Bool)
    (h : Primary s p l) : ReadsEndpoint s p l := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · exact (h.1 h1).trans h2
  · exact (h.2.1 h1).trans h2

theorem or_reads (a b : Signal) (p l : Bool)
    (ha : ReadsEndpoint a p l) (hb : ReadsEndpoint b p l) :
    ReadsEndpoint (bor a b) p l := by
  rcases a with ⟨av, ab, ad⟩
  rcases b with ⟨bv, bb, bd⟩
  cases av <;> cases ab <;> cases ad <;> cases bv <;> cases bb <;> cases bd <;>
    cases p <;> cases l <;> simp_all [ReadsEndpoint, bor]

theorem absorbs (s : Signal) (p l : Bool)
    (h : ReadsEndpoint s p l) (d : s.delta = true) : (l && s.value) = l := by
  cases l
  · rfl
  · exact h.2 d rfl

theorem and_primary_left (a b : Signal) (p l : Bool)
    (ha : Primary a p l) (hb : ReadsEndpoint b p l) (hd : (band a b).delta = true) :
    (l && (band a b).value) = (band a b).value ∨
      (l && (band a b).value) = (l && p) := by
  rcases a with ⟨av, ab, ad⟩
  rcases b with ⟨bv, bb, bd⟩
  cases av <;> cases ab <;> cases ad <;> cases bv <;> cases bb <;> cases bd <;>
    cases p <;> cases l <;> simp_all [Primary, ReadsEndpoint, band]

-- Stronger, uniform classification: base-read orientation depends only
-- on the fixed trace bits, not on the evaluation input.
theorem and_primary_uniform (a b : Signal) (p l : Bool)
    (ha : Primary a p l) (hb : ReadsEndpoint b p l) (hd : (band a b).delta = true) :
    ((a.delta = true) ∧ (l && (band a b).value) = (band a b).value) ∨
    ((a.base = true) ∧ (l && (band a b).value) = (l && p)) := by
  rcases a with ⟨av, ab, ad⟩
  rcases b with ⟨bv, bb, bd⟩
  cases av <;> cases ab <;> cases ad <;> cases bv <;> cases bb <;> cases bd <;>
    cases p <;> cases l <;> simp_all [Primary, ReadsEndpoint, band]

end ProofLantern.BarePrefix
