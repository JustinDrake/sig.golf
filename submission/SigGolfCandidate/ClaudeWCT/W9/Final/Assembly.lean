import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Conditional
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.Final

namespace ClaudeWCT.W9.Final
open ClaudeWCT.W9.T3M (Images)
abbrev submission (I : Images) : SigGolf.Submission := ClaudeWCT.W9.T3M.Final.submissionNew I
theorem signature_bytes (I : Images) : (submission I).sizes.signature = 5456 := rfl
theorem witness_bytes (I : Images) : (submission I).sizes.witness = 24264 := rfl
theorem cache_bytes (I : Images) : (submission I).sizes.cache = 131072 := rfl
theorem layout_offsets (I : Images) : (submission I).layout =
    { message := 64, secretKey := 128, publicKey := 160,
      cache := 524288, signature := 28672, witness := 2048 } := rfl
theorem keygen_image (I : Images) :
    (submission I).image .keygen =
      ⟨SigGolfCandidate.T3M.Images.keygenImage.code, SigGolfCandidate.T3M.Images.keygenImage.data⟩ :=
  rfl
structure PendingInputs (I : Images) : Prop where
  large_route : ClaudeWCT.W9.T3.Secc.LargeRouteBound
  pair_bound : ClaudeWCT.W9.T3.Security.WPair.PairGuessBound SigGolfCandidate.T3.Security.BPair.pairTerm
  near_bound : ClaudeWCT.W9.T3.Security.CaseC.NearBound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.Wots.nearTerm
  admissible : (ClaudeWCT.W9.T3M.submission I).Admissible
  verify_refines : ClaudeWCT.W9.T3M.Final.VerifyRefines I
  verify_terminates : ClaudeWCT.W9.T3M.Final.VerifyTerminates I
  verify_accept_cycles : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I
  sign_refines : ClaudeWCT.W9.T3M.Final.SignRefines I
  sign_terminates : ClaudeWCT.W9.T3M.Final.SignTerminates I
  expand_refines : ClaudeWCT.W9.T3M.Final.ExpandRefines I
  expand_terminates : ClaudeWCT.W9.T3M.Final.ExpandTerminates I
theorem PendingInputs.machine {I : Images} (h : PendingInputs I) : ClaudeWCT.W9.T3M.Final.MachineFacts I where
  admissible := h.admissible
  sign_refines := h.sign_refines
  sign_terminates := h.sign_terminates
  expand_refines := h.expand_refines
  expand_terminates := h.expand_terminates
  verify_refines := h.verify_refines
  verify_terminates := h.verify_terminates
  verify_accept_cycles := h.verify_accept_cycles
theorem PendingInputs.securityP {I : Images} (h : PendingInputs I) : ClaudeWCT.W9.T3M.Final.SecurityP :=
  ClaudeWCT.W9.T3.Secc.t3_securityP h.near_bound h.pair_bound h.large_route
theorem certificate_of_pending {I : Images} (h : PendingInputs I) : SigGolf.Certificate (submission I) 7722 :=
  ClaudeWCT.W9.T3M.Final.certificate_of_security h.securityP h.machine
end ClaudeWCT.W9.Final
