import Init

namespace ProofLantern.FanoCoverage

theorem counts_split {α : Type} (xs : List α) (p q : α → Bool) :
    xs.countP p + xs.countP q =
      xs.countP (fun x => p x || q x) + xs.countP (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

theorem count_le_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have hh := h x (List.mem_cons.mpr (Or.inl rfl))
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem count_pos_of_mem {α : Type} (xs : List α) (p : α → Bool)
   (x : α) (hm : x ∈ xs) (h : p x = true) : 0 < xs.countP p := by
  exact List.countP_pos_iff.mpr ⟨x, hm, h⟩

def pairs : List (Nat × Nat) :=
  (List.range 7).flatMap (fun p => (List.range 7).map (fun l => (p,l)))

def edge (v : Nat × Nat) : Bool := let d := (v.1 + 7 - v.2) % 7
  d == 0 || d == 1 || d == 3

theorem edge_count : pairs.countP edge = 21 := by decide

theorem marked_present : (0,0) ∈ pairs := by decide

/-- Cover all Fano edge cells by oriented star supports; the fixed marked cell
is charged to both centers. Counting separates the repeat from the union. -/
theorem oriented_lower (P L : (Nat × Nat) → Bool)
    (cover : ∀ x ∈ pairs, edge x = true → (P x || L x) = true)
    (markedP : P (0,0) = true) (markedL : L (0,0) = true) :
    22 ≤ pairs.countP P + pairs.countP L := by
  have a := count_le_of_imp pairs edge (fun x => P x || L x) cover
  rw [edge_count] at a
  have b := count_pos_of_mem pairs (fun x => P x && L x) (0,0) marked_present
    (by simp [markedP,markedL])
  rw [counts_split]
  omega

theorem total_lower (payloadOr stars topOr total : Nat)
    (hpayload : 22 ≤ payloadOr + (stars + 2))
    (hstars : 6 ≤ stars) (htop : stars + 2 ≤ topOr + 1)
    (hcount : payloadOr + stars + 3 + topOr ≤ total) : 30 ≤ total := by omega


def diagonal : List Nat := [1,2,3,4,5,6]

theorem diagonal_present : diagonal.all (fun i => edge (i,i)) = true := by decide

/-- A residual star does not cover two different surviving diagonal edges,
even if several stars share the same center. -/
theorem six_stars (stars : List Nat) (center : Nat → Sum Nat Nat)
    (cover : ∀ i ∈ diagonal, ∃ s ∈ stars, center s = .inl i ∨ center s = .inr i) :
    6 ≤ stars.length := by
  classical
  let pick : Nat → Nat := fun i => if h : i ∈ diagonal then Classical.choose (cover i h) else 0
  have hp (i : Nat) (hi : i ∈ diagonal) :
      pick i ∈ stars ∧ (center (pick i) = .inl i ∨ center (pick i) = .inr i) := by
    simpa [pick, hi] using Classical.choose_spec (cover i hi)
  have hd : diagonal.Nodup := by decide
  have hn : (diagonal.map pick).Nodup := by
    change List.Pairwise (· ≠ ·) (diagonal.map pick)
    rw [List.pairwise_map]
    apply hd.imp_of_mem
    intro i j hi hj hne he
    have a := (hp i hi).2
    have b := (hp j hj).2
    rw [he] at a
    rcases a with a | a <;> rcases b with b | b <;> simp_all
  have hsub : diagonal.map pick ⊆ stars := by
    intro s hs
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
    exact (hp i hi).1
  simpa [diagonal] using hn.length_le_of_subset hsub

end ProofLantern.FanoCoverage

namespace ProofLantern.CenterCount

def tally {α : Type} (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

theorem tally_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : tally xs f ≤ tally xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have hx := h x (List.mem_cons.mpr (Or.inl rfl))
    have ht := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    simpa [tally] using Nat.add_le_add hx ht

theorem tally_add {α : Type} (xs : List α) (f g : α → Nat) :
    tally xs (fun x => f x + g x) = tally xs f + tally xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + g x + tally xs (fun x => f x + g x) =
      f x + tally xs f + (g x + tally xs g)
    rw [ih]
    omega

theorem tally_transpose {α β : Type} (xs : List α) (ys : List β)
    (cost : α → β → Nat) :
    tally xs (fun x => tally ys (cost x)) =
      tally ys (fun y => tally xs (fun x => cost x y)) := by
  induction xs with
  | nil =>
    change 0 = tally ys (fun _ => 0)
    induction ys with
    | nil => rfl
    | cons y ys hp => simpa [tally] using hp
  | cons x xs ih =>
    change tally ys (cost x) + tally xs (fun x => tally ys (cost x)) =
      tally ys (fun y => cost x y + tally xs (fun x => cost x y))
    rw [tally_add, ih]

theorem countP_as_tally {α : Type} (xs : List α) (p : α → Bool) :
    xs.countP p = tally xs (fun x => if p x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [tally,h] at ih ⊢ <;> omega

/-- Orientations of star support are charged to the actual center. -/
theorem oriented_as_centers {α β : Type} (xs : List α) (ys : List β)
    (P L : α × β → Bool) :
    let pairs := xs.flatMap (fun x => ys.map (fun y => (x,y)))
    pairs.countP P + pairs.countP L =
      tally xs (fun a => ys.countP (fun b => P (a,b))) +
      tally ys (fun b => xs.countP (fun a => L (a,b))) := by
  dsimp
  simp only [List.countP_flatMap,Function.comp_def,List.countP_map]
  change
    tally xs (fun a => ys.countP (fun b => P (a,b))) +
      tally xs (fun a => ys.countP (fun b => L (a,b))) =
    tally xs (fun a => ys.countP (fun b => P (a,b))) +
      tally ys (fun b => xs.countP (fun a => L (a,b)))
  congr 1
  simp only [countP_as_tally]
  exact tally_transpose xs ys (fun a b => if L (a,b) then 1 else 0)


theorem count_at_most_one {α : Type} (xs : List α) (p : α → Bool)
    (hn : xs.Nodup)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, p a = true → p b = true → a = b) :
    xs.countP p ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    have tailUnique : ∀ a ∈ xs, ∀ b ∈ xs, p a = true → p b = true → a = b :=
      fun a ha b hb => unique a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb))
    cases hx : p x
    · simpa [hx] using ih hn'.2 tailUnique
    · have hzero : xs.countP p = 0 := by
        by_cases hp : 0 < xs.countP p
        · obtain ⟨a,ha,ht⟩ := List.countP_pos_iff.mp hp
          have he := unique x (List.mem_cons.mpr (Or.inl rfl))
            a (List.mem_cons.mpr (Or.inr ha)) hx ht
          exact False.elim (hn'.1 (by simpa [he] using ha))
        · omega
      simp [hx,hzero]

/-- A physically shared OR is charged to at most one center; sum the charges
without requiring that every physical OR is used by a counted center. -/
theorem sum_disjoint_charge {α β : Type} (centers : List α) (wires : List β)
    (used : α → β → Bool) (physical : β → Bool) (hn : centers.Nodup)
    (real : ∀ c ∈ centers, ∀ w ∈ wires, used c w = true → physical w = true)
    (unique : ∀ w ∈ wires, ∀ a ∈ centers, ∀ b ∈ centers,
      used a w = true → used b w = true → a = b) :
    tally centers (fun c => wires.countP (used c)) ≤ wires.countP physical := by
  simp only [countP_as_tally]
  rw [tally_transpose]
  apply tally_mono
  intro w hw
  rw [← countP_as_tally]
  cases h : physical w
  · have z : centers.countP (fun c => used c w) = 0 := by
      by_cases hp : 0 < centers.countP (fun c => used c w)
      · obtain ⟨c,hc,hu⟩ := List.countP_pos_iff.mp hp
        have t := real c hc w hw hu
        simp [h] at t
      · omega
    simp [z]
  · simpa [h] using count_at_most_one centers (fun c => used c w) hn (unique w hw)

end ProofLantern.CenterCount


namespace ProofLantern.StarTemplate

open ProofLantern.CenterCount ProofLantern.FanoCoverage

def vertices := List.range 7
def centers : List (Sum Nat Nat) := vertices.map Sum.inl ++ vertices.map Sum.inr

def degrees (P L : Nat × Nat → Bool) : Sum Nat Nat → Nat
  | .inl p => vertices.countP (fun l => P (p,l))
  | .inr l => vertices.countP (fun p => L (p,l))

theorem degree_total (P L : Nat × Nat → Bool) :
    tally centers (degrees P L) = pairs.countP P + pairs.countP L := by
  unfold pairs
  rw [oriented_as_centers (List.range 7) (List.range 7) P L]
  simp [centers,vertices,tally, List.sum_append, List.map_map, Function.comp_def, degrees]

/-- Certificate-level bound for sound stars and two direct marks. Local OR networks
supply `localCount`, the top OR network supplies `topCount`, and their physical
gate budgets are disjoint. This is not a decomposition theorem for arbitrary DAGs. -/
theorem at_least_thirty (P L : Nat × Nat → Bool) (wires roots : List Nat)
    (center : Nat → Sum Nat Nat) (payloadRoots : Sum Nat Nat → Nat)
    (used : Sum Nat Nat → Nat → Bool) (isPayloadOR : Nat → Bool)
    (topOR total : Nat)
    (cover : ∀ x ∈ pairs, edge x = true → (P x || L x) = true)
    (markP : P (0,0) = true) (markL : L (0,0) = true)
    (matchCover : ∀ i ∈ diagonal, ∃ s ∈ roots, center s = .inl i ∨ center s = .inr i)
    (localCount : ∀ c ∈ centers,
      degrees P L c ≤ wires.countP (used c) + payloadRoots c)
    (real : ∀ c ∈ centers, ∀ w ∈ wires, used c w = true → isPayloadOR w = true)
    (unique : ∀ w ∈ wires, ∀ a ∈ centers, ∀ b ∈ centers,
      used a w = true → used b w = true → a = b)
    (rootCount : tally centers payloadRoots ≤ roots.length + 2)
    (topCount : roots.length + 2 ≤ topOR + 1)
    (disjointCost : wires.countP isPayloadOR + roots.length + 3 + topOR ≤ total) :
    30 ≤ total := by
  have hl := FanoCoverage.oriented_lower P L cover markP markL
  rw [← degree_total P L] at hl
  have hn := tally_mono centers (degrees P L)
    (fun c => wires.countP (used c) + payloadRoots c) localCount
  rw [tally_add] at hn
  have hg := sum_disjoint_charge centers wires used isPayloadOR (by decide) real unique
  have ht : 22 ≤ wires.countP isPayloadOR + (roots.length + 2) := by omega
  exact total_lower _ _ _ _ ht (six_stars roots center matchCover) topCount disjointCost

end ProofLantern.StarTemplate
