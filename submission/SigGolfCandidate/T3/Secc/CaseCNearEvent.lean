import SigGolfCandidate.T3.Secc.CaseCSplit

/-!
# Stream CC: the near event on (answers, log, verifier entries) — for B-PAIR's `near_chain`

`NearIn A log entries`: the verifier entries contain a digest row `x = pad64 (digestInput (wrho w) m (wdc w))` with its
answer `N` (shaped, all four layers `Good`, no successful logged signature on `m` with the forgery's randomizer, log
of length ≤ 2^32), and `N` is near-certified: one opened position `f` is guessed (B-PAIR's `GuessedIn`), the other
twenty are `Disclosed` by the log.

* `nearIn_short` / `nearIn_mono`: the two side conditions of B-PAIR's `shared_le_pair` / `near_chain`;
* `near_shared`: on the shared law, `CleanWin ∧ PinnedC NearQ` gives `NearIn` for every decomposition of the run;
* `caseC_not_signer_eval`: B-SUF's R6 with the logged signatures given as honest evaluations (the form the lazy world
  provides): no logged signer call queries the forgery's digest row.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Good layers read the answers only on short queries -/

theorem honestMsg_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (index : Nat) (lay : Layer) :
    Extract.honestMsg A index lay = Extract.honestMsg T index lay := by
  unfold Extract.honestMsg
  split_ifs
  · exact Wots.Ref.honestRoot_short h _ _
  · exact Wots.Ref.honestForest_short h _

theorem good_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (w : WBytes) (index : Nat) (lay : Layer)
    (hg : Extract.Good A w index lay) : Extract.Good T w index lay := by
  obtain ⟨digits, ⟨hctr, hdec⟩, hpath, hchain⟩ := hg
  refine ⟨digits, ⟨hctr, ?_⟩, ?_, ?_⟩
  · rw [← honestMsg_short h]
    rw [← Wots.Ref.ShortRespects.shortHash _ (Wots.Ref.short_of_le _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])) A T h]
    exact hdec
  · intro j hj
    obtain ⟨h1, h2⟩ := hpath j hj
    exact ⟨by rw [h1, Wots.Ref.builtTree_short h], h2⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hchain i hi
    refine ⟨?_, h2⟩
    rw [h1]
    unfold Correctness.leafValue
    rw [Wots.Ref.leafSeed_short h, Wots.Ref.chainValue_short h]

/-! ## The event -/

/-- **The near event** on the answers, the actual log and the verifier's public entries. -/
def NearIn (A : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ (m : Message) (w : WBytes) (N : HashOutput) (f : BPair.FtsCoord),
    (pad64 (digestInput (wrho w) m (wdc w)), N) ∈ entries ∧
    evalWithAnswerFn A (digest (wrho w) m (wdc w)) = N ∧ Shaped N w ∧
    (∀ lay : Layer, Extract.Good A w (N.toNat % 2 ^ 31) lay) ∧ ¬BPB.SignedDigest log m w ∧ log.length ≤ 2 ^ 32 ∧
    f ∈ BPair.openedPositions N ∧ BPair.GuessedIn A log entries f ∧
    ∀ g ∈ BPair.openedPositions N, g ≠ f → BPair.Disclosed A log g

theorem nearIn_short (A T : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (h : Wots.Ref.ShortAgree A T) (hn : NearIn A log entries) : NearIn T log entries := by
  obtain ⟨m, w, N, f, hx, hN, hS, hgood, hsd, hlen, hf, hguess, hdis⟩ := hn
  refine ⟨m, w, N, f, hx, ?_, hS, fun lay => good_short h w _ lay (hgood lay), hsd, hlen, hf,
    BPair.guessedIn_short h log entries f hguess, fun g hg hne => BPair.disclosed_short h log g (hdis g hg hne)⟩
  rw [← BPair.eval_congr_allowed (BPair.digest_short _ _ _) h]
  exact hN

theorem nearIn_mono (A : Correctness.Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (hn : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨m, w, N, f, hx, hN, hS, hgood, hsd, hlen, hf, hguess, hdis⟩ := hn
  exact ⟨m, w, N, f, hsub _ hx, hN, hS, hgood, hsd, hlen, hf, BPair.guessedIn_mono A log entries entries' hsub f hguess,
    hdis⟩

/-! ## The shared-law side -/

/-- **On the shared law, the pinned near case gives the near event for every decomposition.** -/
theorem near_shared (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hnear : PinnedC adversary NearQ z) :
    ∀ generated interaction checked, Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction
      checked → NearIn z.2 interaction.value.2 (BPair.publicEntries checked.events) := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, hQ⟩ := hnear
  intro g' i' c' hs'
  obtain ⟨hg', hi', hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce, hi']
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hs.2.2.2).symm.trans hclean.1
  have ha : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)
  obtain ⟨N, -, hN, -, hS, hgood, -⟩ := hCat
  -- the verifier's own digest event
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting g.value.1 i.value i.state c hs.2.2.1 z.2 ha hvalue f hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  obtain ⟨N', -, hN', hdq, -⟩ := WotsExtract.verifyP_walk_wots_route z.2 m g.value.1 w hpk hv
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  obtain ⟨prior, hevent⟩ := PaddedExtraction.public_occurrence _ (PaddedExtraction.check_hashOnly _ _ f) _ check hcheck
    z.2 (by rw [hst]; exact ha) _ (hsub _ hdq)
  rw [hev] at hevent
  have hans : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N' := hN'
  rw [hans] at hevent
  obtain ⟨f0, hf0, hguess, hdis⟩ := hQ
  rw [hN'] at hf0 hdis
  exact ⟨m, w, N', f0, mem_publicEntries hevent, hN', hS, hgood, hsd, hlen, hf0, hguess, hdis⟩

/-! ## B-SUF's R6 with honest logged signatures -/

/-- No logged signer call queries the forgery's digest row (the logged signatures are the honest evaluations). -/
theorem caseC_not_signer_eval (answers : Correctness.Answers) (published : T3.Cache) (log : QueryLog Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (FullGame.authenticatedSign published entry.1))
    (m : Message) (w : WBytes) (N : HashOutput)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay)
    (hfresh : ¬BPB.SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : T3.Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, hq'⟩ := BPB.signer_digest_query answers published entry.1 _ _ _ hq
  rw [← BPB.ofNat_toNat32 (wdc w)] at hq'
  have hacc := BPB.rejected_trial_inadmissible answers (wrho w) m (wdc w).toNat hq'
    (by rw [BPB.ofNat_toNat32, hN]; exact hS.2.1)
  rw [BPB.ofNat_toNat32, hN] at hacc
  have hsel : (evalWithAnswerFn answers (payloadRecordForNonce published (wrho w) m)).2 = some N := by
    unfold payloadRecordForNonce
    simp only [evalWithAnswerFn_bind, hacc, evalWithAnswerFn_pure]
  obtain ⟨sig, hsig', hsrho⟩ := BPB.selected_payload_succeeds answers published (wrho w) m N w hsel hgood
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [hsig entry he, BPB.eval_authenticatedSign, if_pos hc, hm, ← hm, ← hrho, hm]
  exact hsig'

end SigGolfCandidate.T3.Security.CaseC
