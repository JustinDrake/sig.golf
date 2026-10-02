import SigGolfCandidate.T3M.Final.Budgets
import SigGolfCandidate.T3M.Final.BridgeMain

/-!
# The T3 certificate (legacy contract)

`certificate_of : Pending → SourceFacts → Legacy.Certificate T3M.submission 9202` — every organizer requirement from the
named machine statements (`Pending`) and source statements (`SourceFacts`), nothing else:

| field | proof |
|---|---|
| `admissible` | `T3M.submission_admissible` (M0, kernel `decide` on chunked images) |
| `termination` | keygen exact (`KeygenRunWith`: 37,152,877 cycles), sign / expand / verify `…Terminates` |
| `completeness` | `submission_complete` (`Final/Completeness`) |
| `compressionBounds` | `submission_compressionBounds` (`Final/Budgets`) |
| `security` | `submission_secure` (`Final/BridgeMain`) with `qfacts` |
| `verificationBound` | `honest_success_verify` + `VerifyAcceptCycles` (9103) + `witnessCycles 25240 = 99` |
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.Legacy

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.T3M.submission SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Legacy.Input

set_option maxRecDepth 100000 in
/-- The query-shape facts of the security bridge: CLOSURE's hash-only facts and stream W's query lemmas. -/
theorem qfacts (S : SourceFacts) : QFacts where
  hashOnly_keygen := S.hashOnly_keygen
  hashOnly_sign := S.hashOnly_sign
  hashOnly_expandB := T3M.hashOnly_expandB
  hashOnly_verifyP := T3M.hashOnly_verifyP
  public_expandB m pk σ := T3M.allQ_mono (T3M.pubGood_expandB m pk σ) fun _ h => h.1
  public_verifyP := T3M.publicOnly_verifyP
  good_keygen := T3M.goodQ_keygen
  good_sign := T3M.goodQ_sign
  good_expandB m pk σ := T3M.allQ_mono (T3M.pubGood_expandB m pk σ) fun _ h => h.2
  good_verifyP := T3M.goodQ_verifyP

/-- **Termination**: keygen exact, sign / expand / verify by their statements. -/
theorem submission_terminates (P : Pending) : submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    rw [P.keygen_runWith hash input]
    exact ⟨rfl, show (37152877 : ℕ) < 2 ^ 32 by norm_num⟩
  | sign =>
    obtain ⟨sk, cache, m⟩ := input
    exact P.sign_terminates hash sk cache m
  | expand =>
    obtain ⟨m, pk, s⟩ := input
    exact P.expand_terminates hash m pk s
  | verify =>
    obtain ⟨m, pk, w⟩ := input
    exact P.verify_terminates hash m pk w

theorem witnessCycles_eq : witnessCycles submission.sizes.witness = 99 := rfl

theorem claimedC_eq : claimedC = verifyCycleBound + witnessCycles submission.sizes.witness := rfl

/-- **Verification bound** `9202 = 9103 + ⌈25240 / 256⌉`. -/
theorem submission_verificationBound (P : Pending) : submission.VerificationBound 9202 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ := honest_success_verify submission hash sk m h
  rw [hcyc, witnessCycles_eq]
  have := P.verify_accept_cycles hash m' pk w hacc
  unfold verifyCycleBound at this
  omega

/-- **The T3 certificate** (legacy contract), from the machine and source statements. -/
theorem certificate_of (P : Pending) (S : SourceFacts) : Certificate submission 9202 where
  admissible := submission_admissible
  termination := submission_terminates P
  completeness := submission_complete P S
  compressionBounds := submission_compressionBounds P S
  security := submission_secure (qfacts S) P S.securityP
  verificationBound := submission_verificationBound P

end SigGolfCandidate.T3M.Final
