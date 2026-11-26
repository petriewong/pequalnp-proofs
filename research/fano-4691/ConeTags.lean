import Init
namespace LocalCone

inductive Cone where
  | leaf
  | gate (idx : Nat) (pure : Bool) (left right : Cone)

def Cone.visits (i : Nat) : Cone → Prop
  | .leaf => False
  | .gate j _ l r => i = j ∨ l.visits i ∨ r.visits i

def Cone.strict (i : Nat) : Cone → Prop
  | .leaf => False
  | .gate _ _ l r => l.visits i ∨ r.visits i

def Cone.pureSomewhere : Cone → Prop
  | .leaf => False
  | .gate _ q l r => q = true ∨ l.pureSomewhere ∨ r.pureSomewhere

def Cone.pureBelow : Cone → Prop
  | .leaf => False
  | .gate _ _ l r => l.pureSomewhere ∨ r.pureSomewhere

def Cone.flags (i j : Nat) : Cone → Bool × Bool × Bool
  | .leaf => (false,false,false)
  | .gate k q l r =>
    let a := l.flags i j
    let b := r.flags i j
    (decide (i=k) || a.1 || b.1, decide (j=k) || a.2.1 || b.2.1, q || a.2.2 || b.2.2)

theorem Cone.flags_spec (i j : Nat) (t : Cone) :
    ((t.flags i j).1 = true ↔ t.visits i) ∧
    ((t.flags i j).2.1 = true ↔ t.visits j) ∧
    ((t.flags i j).2.2 = true ↔ t.pureSomewhere) := by
  induction t with
  | leaf => simp [flags,visits,pureSomewhere]
  | gate k q l r ihl ihr =>
    obtain ⟨lx,ly,lp⟩ := ihl
    obtain ⟨rx,ry,rp⟩ := ihr
    simp [flags,visits,pureSomewhere,lx,ly,lp,rx,ry,rp,or_assoc]

def Cone.incoming (i j : Nat) : Cone → Bool × Bool × Bool
  | .leaf => (false,false,false)
  | .gate _ _ l r =>
    let a := l.flags i j
    let b := r.flags i j
    (a.1 || b.1, a.2.1 || b.2.1, a.2.2 || b.2.2)

theorem Cone.incoming_spec (i j : Nat) (t : Cone) :
    ((t.incoming i j).1 = true ↔ t.strict i) ∧
    ((t.incoming i j).2.1 = true ↔ t.strict j) ∧
    ((t.incoming i j).2.2 = true ↔ t.pureBelow) := by
  cases t with
  | leaf => simp [incoming,strict,pureBelow]
  | gate k q l r =>
    obtain ⟨lx,ly,lp⟩ := l.flags_spec i j
    obtain ⟨rx,ry,rp⟩ := r.flags_spec i j
    simp [incoming,strict,pureBelow,lx,ly,lp,rx,ry,rp]

end LocalCone
