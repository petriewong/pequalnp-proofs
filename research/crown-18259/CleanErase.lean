import Init

namespace ProofLantern.Crown.CleanErase

structure Term where
  /-- True when this term individually rejects every diagonal and can appear at the final OR. -/
  clean : Bool
  /-- The evaluator reads original inputs and only the preceding term values. -/
  eval : List Bool → Bool

def traceAny (clearClean : Bool) (prev : List Bool) : List Term → Bool
  | [] => false
  | g :: tail =>
    let here := g.eval prev
    (g.clean && here) ||
      traceAny clearClean (prev ++ [if clearClean && g.clean then false else here]) tail

/-- Earlier clean term values can be erased inside later term evaluators without changing their
collective OR: either a clean term is already true, or the two traces agree at the next step. -/
theorem erase_clean_inputs_preserves_final_or (prev : List Bool) (terms : List Term) :
    traceAny true prev terms = traceAny false prev terms := by
  induction terms generalizing prev with
  | nil => rfl
  | cons g tail ih =>
    have step : ∀ (clean value : Bool),
        (clean && value ||
          traceAny true (prev ++ [if true && clean then false else value]) tail) =
        (clean && value ||
          traceAny false (prev ++ [if false && clean then false else value]) tail) := by
      intro c q
      cases c <;> cases q <;> simp [ih]
    exact step g.clean (g.eval prev)

end ProofLantern.Crown.CleanErase
