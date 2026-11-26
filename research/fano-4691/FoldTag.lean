import Init

namespace LocalConeFold

def parentGates (n len : Nat) (wires : List Nat) : List Nat :=
  (wires.filter (fun w => decide (n ≤ w ∧ w < n+len))).map (fun w => w-n)

def explicitStep (n : Nat) (cs : List (List Nat)) (wires : List Nat) : List (List Nat) :=
  cs ++ [(parentGates n cs.length wires).flatMap (fun p => p :: cs.getD p [])]

def compactStep (n : Nat) (probe : Nat → Bool) (bits : List Bool) (wires : List Nat) : List Bool :=
  bits ++ [(parentGates n bits.length wires).any (fun p => probe p || bits.getD p false)]

theorem map_getD {α β : Type} (f : α → β) (xs : List α) (a : α) (i : Nat) :
    (xs.map f).getD i (f a) = f (xs.getD i a) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> rfl

theorem project_flat (probe : Nat → Bool) (reads : List Nat) (cs : List (List Nat)) :
    (reads.flatMap (fun p => p :: cs.getD p [])).any probe =
      reads.any (fun p => probe p || (cs.map (fun a => a.any probe)).getD p false) := by
  induction reads with
  | nil => rfl
  | cons r rem ih =>
    have hm := map_getD (fun (l : List Nat) => l.any probe) cs [] r
    change (cs.map (fun l => l.any probe)).getD r false = (cs.getD r []).any probe at hm
    simp only [List.flatMap_cons,List.any_append,List.any_cons,hm,ih]

theorem project_step (n : Nat) (probe : Nat → Bool) (cs : List (List Nat)) (wires : List Nat) :
    (explicitStep n cs wires).map (fun a => a.any probe) =
      compactStep n probe (cs.map (fun a => a.any probe)) wires := by
  simp only [explicitStep,compactStep,List.map_append,List.map_cons,List.map_nil,List.length_map,project_flat]

theorem project_fold (n : Nat) (probe : Nat → Bool)
    (cs : List (List Nat)) (gates : List (List Nat)) :
    (gates.foldl (explicitStep n) cs).map (fun a => a.any probe) =
      gates.foldl (compactStep n probe) (cs.map (fun a => a.any probe)) := by
  induction gates generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,← project_step]
    exact ih (explicitStep n cs g)

theorem exact_strict_gate_tag (n i j : Nat) (gates : List (List Nat)) :
    (gates.foldl (compactStep n (fun a => decide (a=i))) []).getD j false = true ↔
      i ∈ (gates.foldl (explicitStep n) []).getD j [] := by
  have h := project_fold n (fun a => decide (a=i)) [] gates
  have h' := map_getD (fun (a : List Nat) => a.any (fun a => decide (a=i)))
      (gates.foldl (explicitStep n) []) [] j
  change ((gates.foldl (explicitStep n) []).map (fun a => a.any (fun a => decide (a=i)))).getD j false =
     ((gates.foldl (explicitStep n) []).getD j []).any (fun a => decide (a=i)) at h'
  simp only [List.map_nil] at h
  rw [← h, h', List.any_eq_true]
  simp


theorem exact_strict_probe (n j : Nat) (probe : Nat → Bool) (gates : List (List Nat)) :
    (gates.foldl (compactStep n probe) []).getD j false = true ↔
      ∃ i ∈ (gates.foldl (explicitStep n) []).getD j [], probe i = true := by
  have h := project_fold n probe [] gates
  have h' := map_getD (fun (a : List Nat) => a.any probe) (gates.foldl (explicitStep n) []) [] j
  change ((gates.foldl (explicitStep n) []).map (fun a => a.any probe)).getD j false =
    ((gates.foldl (explicitStep n) []).getD j []).any probe at h'
  simp only [List.map_nil] at h
  rw [← h, h', List.any_eq_true]

end LocalConeFold
