import SigGolfCandidate.T3M.Verify.CanonicalRun
import SigGolfCandidate.T3M.CanonicalFinal.Pending
import SigGolfCandidate.T3M.Keygen.Main
import SigGolfCandidate.T3M.Sign.Main
import SigGolfCandidate.T3M.Expand.Main

/-!
# Discharging the machine statements (as far as proved)

Stream K's theorems (`T3M.Keygen.keygen_run_counts`, `T3M.Keygen.keygen_runWith`, t3m/m0k 924ddbe, on t3/shared
2517582) are exactly `Pending`'s keygen fields, and stream V3's (`CanonicalNative.verify_c_refines`, `CanonicalNative.verify_c_terminates`,
`CanonicalNative.verify_c_accept_cycles`, t3m/v3 8416a0a) are exactly its three verify fields. stream S's (`T3M.Sign.sign_refines`, `T3M.Sign.sign_terminates`, t3m/s c4912c2) are its two sign fields.
stream E's (`T3M.Expand.expand_refines_holds`, `T3M.Expand.expand_terminates_holds`, t3m/e 81f84d3) are its two
expand fields, so every `Pending` field is proved (`pending_holds`);
the source fields are CLOSURE's theorems by unfolding (cert-coord's `sourceFacts_of_securityP`) plus SEC's `SecurityP`.
When all are proved, `Pending.mk keygen_run_counts_holds keygen_runWith_holds …` and the `SourceFacts` instance give
`certificate_of` / `certificateNew_of` without hypotheses.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.CanonicalFinal

theorem keygen_run_counts_holds : KeygenRunCounts := fun sk => Keygen.keygen_run_counts sk

theorem keygen_runWith_holds : KeygenRunWith := fun hash sk => Keygen.keygen_runWith hash sk

theorem verify_refines_holds : VerifyRefines := CanonicalNative.verify_c_refines

theorem verify_terminates_holds : VerifyTerminates := CanonicalNative.verify_c_terminates

theorem verify_accept_cycles_holds : VerifyAcceptCycles := CanonicalNative.verify_c_accept_cycles

theorem sign_refines_holds : SignRefines := Sign.sign_refines

theorem sign_terminates_holds : SignTerminates := Sign.sign_terminates

theorem expand_refines_holds : ExpandRefines := Expand.expand_refines_holds

theorem expand_terminates_holds : ExpandTerminates := Expand.expand_terminates_holds

/-- All nine machine statements of the T3 CanonicalNative.candidateSub, proved. -/
theorem pending_holds : Pending where
  keygen_run_counts := keygen_run_counts_holds
  keygen_runWith := keygen_runWith_holds
  sign_refines := sign_refines_holds
  sign_terminates := sign_terminates_holds
  expand_refines := expand_refines_holds
  expand_terminates := expand_terminates_holds
  verify_refines := verify_refines_holds
  verify_terminates := verify_terminates_holds
  verify_accept_cycles := verify_accept_cycles_holds

end SigGolfCandidate.T3M.CanonicalFinal
