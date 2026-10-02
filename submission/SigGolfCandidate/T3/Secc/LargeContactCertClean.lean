import SigGolfCandidate.T3.Secc.LargeContactCert

/-!
# LR-34 (certificate coupling): `cert_of_clean`

A contact-free clean win of the shared law satisfies the real certificate event `CertR` (see `LargeContactCert`).
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
noncomputable local instance instDecidableEqCache_largeContactCertClean : DecidableEq T3.Cache := Classical.decEq _

/-- **A contact-free clean win carries the router's certificate.** -/
theorem cert_of_clean (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) :
    CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  set U := Wots.referenceInputs adversary with hUdef
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun U z.2 q g.value.2 t.steps c.events).contact = false := by simpa using hmon
  intro g' t' c' hsplit'
  obtain ⟨rfl, rfl, rfl⟩ := taggedSplit_unique hsplit hsplit'
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
  have hgate : digestGate N=true := by simpa only [← hN] using verifyP_digestGate z.2 m g.value.1 w hv
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun U z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le U z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  -- verifier queries lie in the universe and were seen; they are clear for the final knowledge
  have hXU : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events → X ∈ U := by
    intro X prior hev
    have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
    have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    rw [← hev'] at hmem
    exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
  have hclearV : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events →
      Clear z.2 (monitorRun U z.2 q g.value.2 t.steps c.events).known X (z.2 (.inl (.inr X))) := by
    intro X prior hev
    have hseen := events_seen U z.2 q c.events _ hmon' _ hev X rfl
    exact monitorRun_clear U z.2 q g.value.2 t.steps c.events hsteps hverdict hmon' hcalls X hseen
      (hXU X prior hev)
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    exact (hclearV X prior hev).mono fun d hd =>
      monitorRun_known U z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, -⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  -- case (C): the forgery's randomizer was never signer-accepted
  have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgate, hgood, hfts⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  have hsd : ¬BPB.SignedDigest t.value.2 m w := fun hsd =>
    BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩
  refine ⟨hcval, hmon', hcalls, ?_⟩
  set st := routerFold U z.2 g.value.2 t.steps c.events with hst
  have hlog : t.value.2 = stepLog t.steps := taggedRecord_log _ _ _ t ht
  -- alive
  have halive : st.exposures.length ≤ BPORS.Numeric.proposalLength := by
    have h1 : st.exposures.length ≤ signCount t.steps := exposures_fold_le U z.2 g.value.2 t.steps c.events
    rw [signCount_eq_length, ← hlog] at h1
    have : BPORS.Numeric.proposalLength = 4573625196 := rfl
    omega
  refine ⟨halive, ?_⟩
  by_cases hr : st.reused = true
  · exact Or.inl hr
  right
  -- the forgery's digest row is a birth
  set Xs := pad64 (digestInput (wrho w) m (wdc w)) with hXs
  have hXsU : Xs ∈ U := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    exact hXU Xs prior hev
  have hXsd : IsDigestRow Xs := ⟨wrho w, m, wdc w, rfl⟩
  have hres' := BPB.logged_resolves g.value.2 (adversary g.value.1 g.value.2) g.state (t.untag.value, t.untag.state)
    (FirstHit.recorded_support _ _ _ hu)
  have hagree' : ∀ input answer, SourceReplay.known t.state input = some answer → z.2 input = answer :=
    fun input answer h => hac input answer (SourceReplay.known_mono _ _ htc h)
  have hnot := BPB.caseC_fresh_not_signer z.2 g.value.2 t.value.2 t.state hres' hagree' m w N hN hS hgate hgood hsd
  have hnotrial : Xs ∉ (t.steps.foldl (routerStep U z.2 (honestNonce z.2) g.value.2) RouterState.initial).trials := by
    intro hm
    rcases trials_steps U z.2 g.value.2 t.steps RouterState.initial Xs hm with h0 | ⟨r, o, e, hmem, hcr, hrow⟩
    · cases h0
    · have hq' := trialRows_queried z.2 g.value.2 r hcr Xs hrow
      have hlogm : (⟨r, o⟩ : (r : Requests.Domain) × Requests.Range r) ∈ t.value.2 := by
        rw [hlog]; exact sign_mem_stepLog hmem
      exact hnot _ hlogm hq'
  have hansSteps : ∀ s ∈ t.steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro s hs e hse b y he
    have h1 := hsteps s hs e hse (by rw [he]; trivial)
    rw [he] at h1
    exact h1.symm.trans hNz
  have hansV : ∀ e ∈ c.events, ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro e he b y hee
    have h1 := hverdict e he (by rw [hee]; trivial)
    rw [hee] at h1
    exact h1.symm.trans hNz
  have hbirth : (Xs, N) ∈ st.births := by
    have hI := birthInv_steps U z.2 g.value.2 Xs N hXsU hXsd t.steps hansSteps RouterState.initial hnotrial
      (fun h => by cases h)
    have hI2 := birthInv_events U Xs N hXsU hXsd c.events hansV _ hnotrial hI
    obtain ⟨prior, hev⟩ := hsub _ hdq
    apply hI2
    exact seen_events_self U c.events _ prior Xs _ hev
  refine ⟨(Xs, N), hbirth, hS.2.1, hgate, ?_⟩
  -- every opened position is opened by an exposure
  intro f hfo
  have hS' : Shaped (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))) w := by rw [hN]; exact hS
  have hF' : FtsExtract.FtsShaped z.2 (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))) w := by rw [hN]; exact hfts
  have hfo' : f ∈ BPair.openedPositions (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))) := by rw [hN]; exact hfo
  have hq1 := CertLeaf.verifyP_leaf_queried z.2 m g.value.1 w hv hS' hF' f hfo'
  obtain ⟨prior, hev⟩ := hsub _ hq1
  have hcl := hclearV _ prior hev
  have hk := hcl.2.1 (CanonGraph.Node.ftsLeaf (BPair.toLeafPos f)) (posOf_probeInput f _)
    (.inr (.inr (BPair.toLeafPos f))) 2 rfl (by rw [slotValue_probeInput]; rfl)
  have hk' := known_secret hk
  rcases hk' with hkg | hkd
  · exact (not_inr_keygenDisclosed _ hkg).elim
  have hkd' : (.inr (.inr (BPair.toLeafPos f)) : Coord) ∈
      (t.steps.foldl (Monitor.step U z.2 q g.value.2) Monitor.initial).disclosed := by
    unfold monitorRun at hkd
    rwa [disclosed_events] at hkd
  rcases disclosed_steps_mem U z.2 q g.value.2 t.steps Monitor.initial _ hkd' with h0 | ⟨r, o, e, hmem, hdis⟩
  · cases h0
  unfold signDisclosed at hdis
  split_ifs at hdis with hcr
  · rcases hsr : LargeResidual.signDigest z.2 r.message with _ | ⟨c', N'⟩
    · rw [hsr] at hdis; cases hdis
    · rw [hsr] at hdis
      dsimp only at hdis
      split_ifs at hdis with hok
      · have hfN' := secret_mem_signItems _ N' _ hdis
        rw [BPair.ofLeafPos_toLeafPos] at hfN'
        rcases covered_fold U z.2 g.value.2 t.steps c.events r o e hmem hcr c' N' hsr with hx | hx
        · exact ⟨N', hx, hfN'⟩
        · exact (hr hx).elim
      · cases hdis
  · cases hdis

end SigGolfCandidate.T3.Security.LargeCoupling
