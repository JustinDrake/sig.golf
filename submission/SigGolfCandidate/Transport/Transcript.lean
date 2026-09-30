import SigGolfCandidate.Transport.Adversary
import SigGolfCandidate.Transport.Counting

set_option backward.isDefEq.respectTransparency false

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec Bridge

/-- The legacy replay set is the successful part of the native log, newest entry first. -/
def transcript {sz : Legacy.Sizes} (log : SigGolf.SigningLog (sizes sz)) (calls : Nat) :
    Legacy.Transcript sz :=
  ⟨log.reverse.filterMap (fun e => e.2.map (e.1.message, ·)), log.length, calls⟩

theorem transcript_record {sz : Legacy.Sizes} (log : SigGolf.SigningLog (sizes sz))
    (calls : Nat) (req : SigGolf.SigningRequest (sizes sz))
    (r : Legacy.RunResult (Legacy.Bytes sz.signature)) :
    transcript (log ++ [⟨req, r.value⟩]) (calls + r.hashCalls) =
      (transcript log calls).record req.message r := by
  simp [transcript, Legacy.Transcript.record, List.reverse_append]
  cases r.value <;> simp

theorem transcript_mem {sz : Legacy.Sizes} (log : SigGolf.SigningLog (sizes sz))
    (calls : Nat) (m : SigGolf.Message) (sig : SigGolf.Bytes (sizes sz).signature) :
    (m, sig) ∈ (transcript log calls).signed ↔
      ∃ e ∈ log, e.1.message = m ∧ e.2 = some sig := by
  simp [transcript, List.mem_filterMap, List.mem_reverse]

theorem fresh_message {sz : Legacy.Sizes} (log : SigGolf.SigningLog (sizes sz))
    (calls : Nat) (m : SigGolf.Message) :
    (transcript log calls).freshMessage m = decide (¬ log.Signed m) := by
  have hany : (transcript log calls).signed.any (fun e => e.1 == m) = decide (log.Signed m) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨m', sig⟩, he, hm⟩
      obtain ⟨e, he, hm', hs⟩ := (transcript_mem log calls m' sig).mp he
      exact ⟨e, he, hm'.trans hm, by simp [hs]⟩
    · rintro ⟨e, he, hm, hs⟩
      cases hv : e.2 with
      | none => simp [hv] at hs
      | some sig => exact ⟨(m, sig), (transcript_mem log calls m sig).mpr ⟨e, he, hm, hv⟩, rfl⟩
  simp [Legacy.Transcript.freshMessage, hany]

theorem fresh_signature {sz : Legacy.Sizes} (log : SigGolf.SigningLog (sizes sz))
    (calls : Nat) (m : SigGolf.Message) (sig : SigGolf.Bytes (sizes sz).signature) :
    (transcript log calls).freshSignature m sig = decide (¬ log.Contains m sig) := by
  apply Bool.eq_iff_iff.mpr
  simp [Legacy.Transcript.freshSignature, transcript, SigGolf.SigningLog.Contains,
    List.contains_iff_mem, List.mem_filterMap, List.mem_reverse]

set_option allowUnsafeReducibility true in
attribute [local reducible] program input output sizes layout submission Legacy.Input Legacy.Output
  SigGolf.Input SigGolf.Output

theorem checkForgery_count (s : Legacy.Submission) (h : s.Admissible)
    (pk : SigGolf.PublicKey) (log : SigGolf.SigningLog (sizes s.sizes))
    (f : SigGolf.Forgery (sizes s.sizes)) (c : Nat) :
    countFrom (fun _ => 1) ((submission s).checkForgery pk log f) c =
      (fun r => (r.won, r.hashCalls)) <$>
        s.checkForgery pk (transcript log c) (forgery f) := by
  cases f with
  | witness m w =>
    unfold SigGolf.Submission.checkForgery Legacy.Submission.checkForgery forgery
    rw [countFrom_bind, native_run_count s h .verify (m, pk, w)]
    simp [bind_map_left, countFrom_pure, map_bind, runResult, output, fresh_message]
    rfl
  | signature m sig =>
    unfold SigGolf.Submission.checkForgery Legacy.Submission.checkForgery forgery
    rw [countFrom_bind, native_run_count s h .expand (m, pk, sig)]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro expand
    simp only [runResult, output]
    cases he : expand.value with
    | none => simp [he, countFrom_pure, transcript]
    | some w =>
      simp only [he, Option.map_some, output]
      rw [countFrom_bind, native_run_count s h .verify (m, pk, w)]
      simp [bind_map_left, countFrom_pure, map_bind, runResult, output, fresh_signature]
      rfl

end SigGolfCandidate.Transport
