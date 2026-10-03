import SigGolfCandidate.T3M.Witness.CanonicalAdapter
import SigGolfCandidate.Bridge.Basic

/-! Source semantics and a witness reduction for canonical scheduling research.
No submission security or native refinement theorem is asserted here. -/
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Bridge
open CanonicalAdapter

def verifyC (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some first ← digestP m w | pure false
  let some second ← digestP m w | pure false
  if second ≠ first then return false
  verifyTailP pk (normalize (selections first) w) first

/-- A public witness adapter queries the digest before submitting its rewritten
bytes to the original verifier. The original verifier queries it again. -/
def adaptedOld (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some first ← digestP m w | pure false
  verifyP m pk (normalize (selections first) w)

def WinCount (left right : Bool × Nat) : Prop :=
  left.1=true → right.1=true ∧ right.2 ≤ left.2

theorem witness_reduction (cost : Spec.Domain → Nat) (m : Message) (pk : Digest)
    (w : WBytes) (c : Nat) :
    Rel (countFrom cost (verifyC m pk w) c)
      (countFrom cost (adaptedOld m pk w) c) WinCount := by
  unfold verifyC adaptedOld
  rw [countFrom_bind,countFrom_bind]
  apply Rel.bind_eq
  rintro ⟨answer,c'⟩
  cases answer with
  | none =>
    dsimp only
    simp only [countFrom_pure]
    exact Rel.pure_left _ _ (by intro r h; cases h)
  | some first =>
    dsimp only
    rw [verifyP_eq_tail,digestP_normalize]
    rw [countFrom_bind,countFrom_bind]
    apply Rel.bind_eq
    rintro ⟨answer,c''⟩
    cases answer with
    | none =>
      dsimp only
      simp only [countFrom_pure]
      exact Rel.pure_left _ _ (by intro r h; cases h)
    | some second =>
      dsimp only
      by_cases he : second=first
      · subst second
        simp only [ne_eq,not_true_eq_false,if_false]
        apply (Rel.of_eq _).mono
        intro a b hab
        subst b
        exact fun h => ⟨h,le_rfl⟩
      · simp only [if_pos he,countFrom_pure]
        exact Rel.pure_left _ _ (by intro r h; cases h)

end SigGolfCandidate.T3M.CanonicalSource
