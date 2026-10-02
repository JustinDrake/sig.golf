import SigGolfCandidate.T3.Secc.LargeContactMonitor
import SigGolfCandidate.T3.Secc.WotsTransport

/-!
# LR-34 (LR-5): every query of a recorded run lies in R3's eager universe

`record_inputs`: if every path of `program` from `state` queries inside `U` (F2's `InputsIn`), every public event of
a lazy record of `program` is in `U`. With F2's `referenceInputs_inputsIn` this puts every adversary and verifier
query of the actual padded run in `Wots.referenceInputs adversary`, the universe the monitor tests.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **Every public event of a lazy record lies in an `InputsIn` universe.** -/
theorem record_inputs (U : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State)
    (hin : Wots.Ref.InputsIn U program state) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program state)) :
    ∀ e ∈ result.events, ∀ x, e.input = .inl (.inr x) → x ∈ U := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at hr
      subst hr
      intro e he
      cases he
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hl, rfl⟩ := hr
      have hadv := FirstHit.query_advance state input middle hm
      rcases input with (n | y) | c
      · have hin' := Wots.Ref.InputsIn.coin hin middle.1
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
        · have hst : middle.2 = state := by rw [hadv]; rfl
          rw [hst] at hl
          exact ih middle.1 state hin' last hl e he x hx
      · obtain ⟨hy, hnext⟩ := Wots.Ref.InputsIn.public hin
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
          exact hy
        · rw [hadv] at hl
          exact ih middle.1 _ (hnext middle.1) last hl e he x hx
      · have hcached : ∀ v, state.1 c = some v → v = middle.1 := by
          intro v hv
          have hext := SourceReplay.query_extends (.inr c) state middle hm
          have h1 : SourceReplay.known middle.2 (.inr c) = some v :=
            SourceReplay.known_mono _ _ hext (show SourceReplay.known state (.inr c) = some v from hv)
          have h2 := SourceReplay.hash_query_caches (.inr c) trivial state middle hm
          rw [h1] at h2
          exact Option.some.inj h2
        have hin' := Wots.Ref.InputsIn.priv hin middle.1 hcached
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
        · rw [hadv] at hl
          exact ih middle.1 _ hin' last hl e he x hx

/-- Every public event of the recorded padded run lies in R3's universe. -/
theorem trace_inputs (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support) :
    ∀ e ∈ (QueryRecorded.recordedTrace result).events, ∀ x, e.input = .inl (.inr x) →
      x ∈ Wots.referenceInputs adversary :=
  record_inputs _ _ (∅, ∅) (Wots.Ref.referenceInputs_inputsIn adversary) _
    (PaddedExtraction.traced_record_support adversary q hq result hr)

end SigGolfCandidate.T3.Security.LargeCoupling
