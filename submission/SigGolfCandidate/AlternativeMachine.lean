import SigGolfCandidate.AlternativeMachineWords

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal



namespace SigGolfCandidate.Base4Candidate
open SigGolfCandidate.Legacy

/-- The four alternate programs and their actual declared input/output buffers.
This value is not selected in Solution.lean until its complete certificate exists. -/
def candidateSubmission : Submission where
  sizes := ⟨7232,19200,131072⟩
  layout := ⟨64,128,160,32768,196608,2048⟩
  image
    | .keygen => Reference.KeygenCode.image
    | .sign => Reference.SignLayerCode.image
    | .expand => Reference.ExpandCode.image
    | .verify => Reference.VerifyImage.image

theorem candidate_sizes_valid : candidateSubmission.sizes.Valid := by
  change 1 ≤ 7232 ∧ 7232 ≤ MAX_SIGNATURE_BYTES ∧
    19200 ≤ MAX_WITNESS_BYTES ∧ 131072 ≤ MAX_CACHE_BYTES
  decide

theorem candidate_image_valid (phase : Phase) :
    (candidateSubmission.image phase).Valid candidateSubmission.sizes candidateSubmission.layout := by
  cases phase with
  | keygen => exact ⟨Reference.KeygenCode.image_room, by decide⟩
  | sign => exact ⟨Reference.SignLayerCode.image_room, by decide⟩
  | expand => exact ⟨Reference.ExpandCode.image_room, by decide⟩
  | verify => exact ⟨Reference.VerifyImage.image_room, by decide⟩

theorem candidate_witness_charge : witnessCycles candidateSubmission.sizes.witness = 75 := rfl

/-- The alternate images under the pinned organizer contract. -/
def candidateCurrent : SigGolf.Submission := Transfer.currentOf candidateSubmission

theorem candidate_legacy_admissible : candidateSubmission.Admissible :=
  ⟨candidate_sizes_valid, candidate_image_valid⟩

theorem candidate_current_legacy : Transfer.legacyOf candidateCurrent = candidateSubmission :=
  Transfer.legacyOf_currentOf candidateSubmission

/-- Admission is only one certificate field: this makes no claim about the
remaining security, completeness, cost or termination obligations. -/
theorem candidate_current_admission : candidateCurrent.Admission := by
  apply Transfer.admission_of_legacy
  rw [candidate_current_legacy]
  exact candidate_legacy_admissible

theorem candidate_current_run_agrees : Transfer.RunAgrees candidateCurrent := by
  apply Transfer.runAgrees_of_admissible
  rw [candidate_current_legacy]
  exact candidate_legacy_admissible

end SigGolfCandidate.Base4Candidate
