import SigGolfCandidate.T3.Secc.LargeContactEvents
import SigGolfCandidate.T3.Secc.LargeContactInputs
import SigGolfCandidate.T3.Secc.SeccSufSigned
import SigGolfCandidate.T3.Secc.WotsExtractSplit

/-!
# LR-34 (LR-5): a contact-free clean win is in case (C)

**`noContact_caseC`**: on the shared law `SeccLaw.completedExperiment`, a clean win whose recorded run has no
large-route contact (`¬Contact`) is B-SUF's `BPB.CaseCFresh` — all four layers `Good`, the FTS part honest-shaped,
the forgery's digest query recorded, and the forgery's randomizer never signer-accepted for its message.

Route: the actual run is the tagged split on which the monitor finds no contact; every adversary/verifier input it
saw is clear for the final knowledge (`monitorRun_clear`); the verifier's queries were seen (`events_seen`); W's
refined extraction with route leaves (`verifyP_wots_cases_route`) gives a route-sized W event — impossible on clear
queries (`wotsPrimitiveRoute_false`) — or case (C); signature reuse is impossible (`BPB.caseC_signed_impossible`).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Every hash event of a lazy record is cached in its final state (any program, coins included). -/
theorem record_events_known {α : Type} (program : M α) (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) :
    ∀ event ∈ result.events, SourceReplay.IsHash event.input →
      SourceReplay.known result.state event.input = some event.answer := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at hr
      subst hr
      intro event he; cases he
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hl, rfl⟩ := hr
      have hext := SourceReplay.run_extends (next middle.1) middle.2 (last.value, last.state)
        (FirstHit.recorded_support _ _ _ hl)
      intro event he hi
      rcases List.mem_cons.mp he with rfl | he
      · exact SourceReplay.known_mono middle.2 last.state hext
          (SourceReplay.hash_query_caches input hi before middle hm)
      · exact ih middle.1 middle.2 last hl event he hi

/-- **LR-5: no contact ⇒ case (C) with a fresh digest.** -/
theorem noContact_caseC (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) : BPB.CaseCFresh adversary z := by
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).contact = false := by simpa using hmon
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have hpk : g.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  obtain ⟨hlen, forgery, hf, hfresh, m, w, hof, hv, hsub⟩ :=
    WotsExtract.verdict_accepting g.value.1 t.value t.state c hc z.2 hac hcval
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_route z.2 m g.value.1 w hpk hv
  -- the verifier's queries are clear for the final knowledge
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  -- every adversary/verifier call is within the budget (the source count charges all recorded events)
  have hcalls : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    have hseen := events_seen (Wots.referenceInputs adversary) z.2 q c.events _ hmon' _ hev X rfl
    have hXU : X ∈ Wots.referenceInputs adversary := by
      have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
      have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
      rw [← hev'] at hmem
      exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
    have hcl := monitorRun_clear (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events hsteps hverdict
      hmon' hcalls X hseen hXU
    exact hcl.mono fun d hd => monitorRun_known (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, -⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  -- case (C)
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgood, hfts⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  by_cases hsd : BPB.SignedDigest t.value.2 m w
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩).elim
  · exact ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩

end SigGolfCandidate.T3.Security.LargeCoupling
