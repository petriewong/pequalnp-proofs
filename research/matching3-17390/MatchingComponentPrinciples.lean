import Std

namespace ProofLantern.MatchingComponentPrinciples
def sign (p x : Bool) : Bool := if p then x else !x
def unary (v0 v1 b : Bool) : Bool := if b then v1 else v0
def result (p q o v0 v1 x y : Bool) : Bool :=
  unary v0 v1 (if o then sign p x || sign q y else sign p x && sign q y)

/-- With a fixed two-literal connective and fixed literal signs, no choice of unary
continuations can realize one positive AND and one positive OR. -/
theorem fixed_pair_operator :
    ∀ p q o a0 a1 b0 b1 : Bool,
      ¬ ((∀ x y : Bool, result p q o a0 a1 x y = (x && y)) ∧
         (∀ x y : Bool, result p q o b0 b1 x y = (x || y))) := by decide

/-- If six nodes each contribute an extra edge and all others are live, counting
binary and unary operands yields the claimed gate lower bound. -/
theorem arithmetic (k t arcs : Nat) (shape : arcs + t = 2*k)
    (reuse : k+8+6 ≤ arcs) : 14+t ≤ k := by omega

theorem component_capacity (h r u : Nat) (all : u+r=9) (cap : u≤h+3) : 6≤h+r := by
  omega
theorem one_bit_mediator {α : Type} (continuation : Bool → α → Bool)
    (a b c : Bool) :
    continuation a = continuation b ∨ continuation a = continuation c ∨
      continuation b = continuation c := by
  cases a <;> cases b <;> cases c <;> simp

end ProofLantern.MatchingComponentPrinciples
