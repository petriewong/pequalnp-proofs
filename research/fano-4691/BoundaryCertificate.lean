import Init
namespace LocalBoundary

def occurs {P L : Type} (E : P → L → Prop) (ps : P → Bool) (ls : L → Bool) : Prop :=
  ∃ p l, E p l ∧ ps p = true ∧ ls l = true

def bitOnly {X : Type} [DecidableEq X] (x : X) : X → Bool := fun y => decide (y=x)

def contained {X : Type} (u v : X → Bool) : Prop :=
  ∀ x, u x = true → v x = true

noncomputable def compatible {P L : Type} (E : P → L → Prop) (ps : P → Bool) : L → Bool :=
  fun l => @decide (¬ ∃ p, E p l ∧ ps p = true) (Classical.propDecidable _)

theorem compatible_iff {P L : Type} (E : P → L → Prop) (ps : P → Bool) (l : L) :
    compatible E ps l = true ↔ ¬ ∃ p, E p l ∧ ps p = true := by
  unfold compatible
  exact Iff.of_eq (@decide_eq_true_eq (¬ ∃ p, E p l ∧ ps p = true) (Classical.propDecidable _))

theorem compatible_negative {P L : Type} (E : P → L → Prop) (ps : P → Bool) :
    ¬ occurs E ps (compatible E ps) := by
  rintro ⟨p,l,he,hp,hl⟩
  exact (compatible_iff E ps l).mp hl ⟨p,he,hp⟩

theorem extends_compatible {P L : Type} (E : P → L → Prop) (ps : P → Bool) (ls : L → Bool)
    (neg : ¬ occurs E ps ls) : contained ls (compatible E ps) := by
  intro l hl
  apply (compatible_iff E ps l).mpr
  rintro ⟨p,hp,hb⟩
  exact neg ⟨p,l,hp,hb,hl⟩

theorem graph_boundary_certificate {P L : Type} [DecidableEq P] [DecidableEq L]
    (E : P → L → Prop) (C : (P → Bool) → (L → Bool) → Bool)
    (mono : ∀ {ps qs ls ms}, contained ps qs → contained ls ms → C ps ls = true → C qs ms = true)
    (pos : ∀ p l, E p l → C (bitOnly p) (bitOnly l) = true)
    (closed_neg : ∀ ps, C ps (compatible E ps) = false) :
    ∀ ps ls, C ps ls = true ↔ occurs E ps ls := by
  intro ps ls
  constructor
  · intro ct
    apply Classical.byContradiction
    intro nh
    have same : contained ps ps := fun _ h => h
    have yes := mono same (extends_compatible E ps ls nh) ct
    rw [closed_neg] at yes
    cases yes
  · rintro ⟨p,l,he,hp,hl⟩
    have ep : contained (bitOnly p) ps := by
      intro q h
      have e : q = p := of_decide_eq_true h
      simpa [e] using hp
    have el : contained (bitOnly l) ls := by
      intro m h
      have e : m = l := of_decide_eq_true h
      simpa [e] using hl
    exact mono ep el (pos p l he)


def flip {P L : Type} (E : P → L → Prop) : L → P → Prop := fun l p => E p l

theorem extend_both_negative {P L : Type} (E : P → L → Prop) (ps : P → Bool) (ls : L → Bool)
    (neg : ¬ occurs E ps ls) :
    ∃ qs ms, contained ps qs ∧ contained ls ms ∧ ¬ occurs E qs ms ∧
      qs = compatible (flip E) ms ∧ ms = compatible E qs := by
  let ms := compatible E ps
  let qs := compatible (flip E) ms
  have noCross : ¬ occurs E qs ms := by
    rintro ⟨p,l,he,hp,hl⟩
    exact (compatible_iff (flip E) ms p).mp hp ⟨l,he,hl⟩
  have p_in : contained ps qs := by
    intro p hp
    apply (compatible_iff (flip E) ms p).mpr
    rintro ⟨l,he,hl⟩
    exact compatible_negative E ps ⟨p,l,he,hp,hl⟩
  have l_in : contained ls ms := extends_compatible E ps ls neg
  refine ⟨qs,ms,p_in,l_in,noCross,rfl,?_⟩
  funext l
  have fwd : ms l = true → compatible E qs l = true := extends_compatible E qs ms noCross l
  have rev : compatible E qs l = true → ms l = true := by
    intro h
    apply (compatible_iff E ps l).mpr
    rintro ⟨p,he,hp⟩
    exact (compatible_iff E qs l).mp h ⟨p,he,p_in p hp⟩
  cases a : ms l <;> cases b : compatible E qs l <;> simp_all

theorem graph_maximal_boundary_certificate {P L : Type} [DecidableEq P] [DecidableEq L]
    (E : P → L → Prop) (C : (P → Bool) → (L → Bool) → Bool)
    (mono : ∀ {ps qs ls ms}, contained ps qs → contained ls ms → C ps ls = true → C qs ms = true)
    (pos : ∀ p l, E p l → C (bitOnly p) (bitOnly l) = true)
    (max_neg : ∀ qs ms, qs = compatible (flip E) ms → ms = compatible E qs → C qs ms = false) :
    ∀ ps ls, C ps ls = true ↔ occurs E ps ls := by
  intro ps ls
  constructor
  · intro ct
    apply Classical.byContradiction
    intro hn
    obtain ⟨qs,ms,hp,hl,_,hqs,hms⟩ := extend_both_negative E ps ls hn
    have yes := mono hp hl ct
    rw [max_neg qs ms hqs hms] at yes
    cases yes
  · rintro ⟨p,l,he,hp,hl⟩
    have ep : contained (bitOnly p) ps := by
      intro q h
      have e : q = p := of_decide_eq_true h
      simpa [e] using hp
    have el : contained (bitOnly l) ls := by
      intro m h
      have e : m = l := of_decide_eq_true h
      simpa [e] using hl
    exact mono ep el (pos p l he)

end LocalBoundary
