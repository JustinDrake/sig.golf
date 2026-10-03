import SigGolfCandidate.T3M.CanonicalFinal.Pending
import SigGolfCandidate.T3.BPORS

/-! Discharge every source interface field except the separately supplied padded-game security.

Authored by cert-coord (thread 01a0f49a, /projects/golf/sig-t3-cert, uncommitted there since 12:26); adopted verbatim
into t3/shared by COORD-2 because the certificate needs it and the source closure it wraps is on this branch (914f795). -/
namespace SigGolfCandidate.T3M.CanonicalFinal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem everyMessageProgram_eq : everyMessageProgram = T3.Completeness.everyMessageProgram := rfl
private theorem honestSignCount_eq (message : T3.Message) :
    honestSignCount message = T3.BudgetClosure.honestSignCount message := rfl
private theorem honestJointCounts_eq (message : T3.Message) :
    honestJointCounts message = T3.ExpansionClosure.honestJointCounts message := rfl

/-- The checked source closure supplies all fields other than padded-game security. -/
theorem sourceFacts_of_securityP (security : SecurityP) : SourceFacts where
  source_completeness := by
    intro secret
    rw [everyMessageProgram_eq]
    exact T3.Completeness.source_completeness secret
  honest_sign_exponential_budget := by
    intro secret message
    rw [honestSignCount_eq]
    exact T3.BudgetClosure.honest_sign_exponential_budget secret message
  honest_expand_exponential_budget := by
    intro secret message
    rw [honestJointCounts_eq]
    exact T3.ExpansionClosure.honest_expand_exponential_budget secret message
  hashOnly_keygen := T3.SourceReplay.hashOnly_keygen
  hashOnly_sign := T3.SourceReplay.hashOnly_sign
  hashOnly_expand := T3.SourceReplay.hashOnly_expand
  hashOnly_verify := T3.SourceReplay.hashOnly_verify
  securityP := security

end SigGolfCandidate.T3M.CanonicalFinal
