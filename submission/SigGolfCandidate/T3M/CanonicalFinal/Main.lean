import SigGolfCandidate.T3M.Final.CanonicalSecurityTail
import SigGolfCandidate.T3M.CanonicalFinal.Budgets
import SigGolfCandidate.T3M.CanonicalFinal.BridgeMain

/-!
# The T3 certificate (legacy contract)

`certificate_of : Pending → SourceFacts → Legacy.Certificate T3M.CanonicalNative.candidateSub 8554` — every organizer requirement from the
named machine statements (`Pending`) and source statements (`SourceFacts`), nothing else:

| field | proof |
|---|---|
| `admissible` | `T3M.CanonicalNative.candidateSub_admissible` (M0, kernel `decide` on chunked images) |
| `termination` | keygen exact (`KeygenRunWith`: 39,960,239 cycles), sign / expand / verify `…Terminates` |
| `completeness` | `submission_complete` (`Final/Completeness`) |
| `compressionBounds` | `submission_compressionBounds` (`Final/Budgets`) |
| `security` | `submission_secure` (`Final/BridgeMain`) with `qfacts` |
| `verificationBound` | `honest_success_verify` + `VerifyAcceptCycles` (8455) + `witnessCycles 25240 = 99` |
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.T3M.CanonicalFinal
open SigGolfCandidate.Legacy

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.T3M.submission SigGolfCandidate.T3M.CanonicalNative.candidateSub SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Legacy.Input

set_option maxRecDepth 100000 in
/-- The query-shape facts of the security bridge: CLOSURE's hash-only facts and stream W's query lemmas. -/
theorem qfacts (S : SourceFacts) : QFacts where
  hashOnly_keygen := S.hashOnly_keygen
  hashOnly_sign := S.hashOnly_sign
  hashOnly_expandB := T3M.hashOnly_expandB
  hashOnly_verifyP := fun m pk w => T3M.allQ_mono (CanonicalSource.pubGood_verifyC m pk w) (fun _ h => h.hashGood.1)
  public_expandB m pk σ := T3M.allQ_mono (T3M.pubGood_expandB m pk σ) fun _ h => h.1
  public_verifyP := fun m pk w => T3M.allQ_mono (CanonicalSource.pubGood_verifyC m pk w) (fun _ h => h.1)
  good_keygen := T3M.goodQ_keygen
  good_sign := T3M.goodQ_sign
  good_expandB m pk σ := T3M.allQ_mono (T3M.pubGood_expandB m pk σ) fun _ h => h.2
  good_verifyP := fun m pk w => T3M.allQ_mono (CanonicalSource.pubGood_verifyC m pk w) (fun _ h => h.2)

/-- **Termination**: keygen exact, sign / expand / verify by their statements. -/
theorem submission_terminates (P : Pending) : CanonicalNative.candidateSub.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    rw [P.keygen_runWith hash input]
    exact ⟨rfl, show (39960239 : ℕ) < 2 ^ 32 by norm_num⟩
  | sign =>
    obtain ⟨sk, cache, m⟩ := input
    exact P.sign_terminates hash sk cache m
  | expand =>
    obtain ⟨m, pk, s⟩ := input
    exact P.expand_terminates hash m pk s
  | verify =>
    obtain ⟨m, pk, w⟩ := input
    exact P.verify_terminates hash m pk w

theorem witnessCycles_eq : witnessCycles CanonicalNative.candidateSub.sizes.witness = 99 := rfl

theorem claimedC_eq : claimedC = verifyCycleBound + witnessCycles CanonicalNative.candidateSub.sizes.witness := rfl

/-- **Verification bound** `8554 = 8455 + ⌈25240 / 256⌉`. -/
theorem submission_verificationBound (P : Pending) : CanonicalNative.candidateSub.VerificationBound 8554 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ := honest_success_verify CanonicalNative.candidateSub hash sk m h
  rw [hcyc, witnessCycles_eq]
  have := P.verify_accept_cycles hash m' pk w hacc
  unfold verifyCycleBound at this
  omega

/-- **The T3 certificate** (legacy contract), from the machine and source statements. -/
theorem certificate_of (P : Pending) (S : SourceFacts) : Certificate CanonicalNative.candidateSub 8554 where
  admissible := CanonicalNative.candidateSub_admissible
  termination := submission_terminates P
  completeness := submission_complete P S
  compressionBounds := submission_compressionBounds P S
  security := submission_secure (qfacts S) P S.securityP
  verificationBound := submission_verificationBound P

end SigGolfCandidate.T3M.CanonicalFinal
