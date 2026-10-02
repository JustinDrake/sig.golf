import SigGolfCandidate.T3.Secc.CaseCLinkSplit

/-!
# Stream CC: the full certificate (all 21 opened secrets disclosed) costs one bank unit

`PinnedC adversary Q z`: F2's pinned fresh case (C) (`Wots.CaseCFreshPinned`), carrying a further property `Q` of
the same decomposition (answers, actual log, message, witness, verifier events).
`FullQ`: every opened position of the forgery's digest is disclosed by a returned signature of the actual log.

`full_potential`: on a bank sample whose projection is a clean win in the full case, the bank potential is ≥ 1.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFull : DecidableEq T3.Cache := Classical.decEq _

/-- Pinned fresh case (C) with an extra property `Q` of the same decomposition. -/
def PinnedC (adversary : AdversaryP)
    (Q : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop)
    (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  ∃ generated interaction checked, Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = Extract.honestRoot z.2 0 0 ∧ interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf z.2 generated.value.1 forgery message witness ∧
      ¬BPB.SignedDigest interaction.value.2 message witness ∧
      BPB.CaseCAt z.2 message witness (QueryRecorded.recordedTrace z.1).events ∧
      Q z.2 interaction.value.2 message witness checked.events

/-- Every opened position of the forgery's digest is disclosed by the actual log. -/
def FullQ (answers : Correctness.Answers) (log : QueryLog Requests) (message : Message) (witness : WBytes)
    (_events : List FirstHit.QueryEvent) : Prop :=
  ∀ f ∈ BPair.openedPositions (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))),
    BPair.Disclosed answers log f

theorem pinned_of_caseC {adversary : AdversaryP} {z : PaddedGame.TraceResult × Correctness.Answers}
    (h : Wots.CaseCFreshPinned adversary z) : PinnedC adversary (fun _ _ _ _ _ => True) z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC⟩ := h
  exact ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC, trivial⟩

theorem queried_notDigest_keygen (A : Correctness.Answers) (input : T3.Spec.Domain)
    (h : input ∈ SourceReplay.queried A keygen) : BPB.NotDigestQ input :=
  BPB.allQ_queried A BPB.NotDigestQ keygen keygen_notDigest input h

/-- **The full case costs at least one bank unit.** -/
theorem full_potential (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (b : Bool × BankState)
    (hb : b ∈ (bankExperiment adversary q).support) (hist : MonitoredPrivate.History) (A : Correctness.Answers)
    (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (hfull : PinnedC adversary FullQ ((b.1, (hist, b.2.2)), A)) : 1 ≤ potential q b.2 := by
  obtain ⟨generated, hg, int0, hint0, ⟨rest, hrest⟩, hlog, hinv⟩ := bank_actual adversary q b hb
  obtain ⟨gen', int', chk', hsplit, -, hlen, forgery, -, -, m, w, -, hnsd, hCat, hQ⟩ := hfull
  have hR : QueryRecorded.recordedTrace (b.1, (hist, b.2.2)) = ⟨b.1, b.2.2.events, lazyOf b.2.2⟩ := rfl
  rw [hR] at hsplit hCat
  obtain ⟨hgen, hint⟩ := split_unique adversary _ (genRecord generated) (genRecord_support generated hg) int0
    hint0 rest hrest gen' int' chk' hsplit
  subst hgen hint
  -- the bank is alive
  have halive : b.2.1.dead = false := by
    cases hd : b.2.1.dead
    · rfl
    · exfalso
      have h1 := hinv.dead hd
      rw [hlog] at h1
      have : horizon = 4573625196 := rfl
      omega
  -- the forgery's digest is a target
  obtain ⟨N, hdc, hN, ⟨prior, hev⟩, hS, hgood, -⟩ := hCat
  have hRsupp : (⟨b.1, b.2.2.events, lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)) := by
    have hm : (b.1, b.2.2) ∈ ((fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$>
        PaddedGame.tracedExperiment adversary q hq).support := by
      rw [← bank_traced adversary q hq, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
      exact ⟨b, hb, rfl⟩
    rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hm
    obtain ⟨r, hr, hre⟩ := hm
    have := PaddedExtraction.traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1, b.2.2.events, lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first, hfirst, hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior _ N hev
  have hdig : IsDigestInput (pad64 (digestInput (wrho w) m (wdc w))) := ⟨wrho w, m, wdc w, rfl⟩
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅, ∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [← hkg]
        exact List.mem_map_of_mem hk
      have hnd := queried_notDigest_keygen _ _ hmem
      exact hnd (BPB.hdrTag_digestInput (wrho w) m (wdc w))
    · rcases hp _ N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q < countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry, hentry, hq'⟩ := hs
        have hres := BPB.logged_resolves generated.1.2 (adversary generated.1.1 generated.1.2) (lazyOf generated.2)
          (int'.value, int'.state) (FirstHit.recorded_support _ _ _ hint0)
        have hext : SourceReplay.Extends int'.state (lazyOf b.2.2) := hsplit.extends
        have hagree : ∀ input answer, SourceReplay.known int'.state input = some answer → A input = answer :=
          (hA.mono hext)
        have hnot := BPB.caseC_fresh_not_signer A generated.1.2 int'.value.2 int'.state hres hagree m w N hN hS hgood
          hnsd
        rw [hlog] at hentry
        exact hnot entry hentry (hq' A hA)
  -- the forgery's digest is covered by the exposures
  have hcov : ∀ c, CoordCovered b.2.1.exposures N c := by
    intro c
    apply coordCovered_of_opened
    intro j
    have hopen := opened_mem N c j
    rw [← hN] at hopen
    obtain ⟨entry, hentry, σ, out, hσ, hout, hf⟩ := hQ _ hopen
    rw [hN] at hf
    rw [← hlog] at hentry
    obtain ⟨-, hcached, hrho⟩ := hinv.logged entry hentry σ hσ
    unfold BPair.signedOutput at hout
    rw [hrho] at hout
    cases hs : evalWithAnswerFn A (digestSearch (nonceOf (lazyOf b.2.2) entry.1.message) entry.1.message 0
        attemptLimit) with
    | none => rw [hs] at hout; cases hout
    | some found =>
        rw [hs] at hout
        simp only [Option.map_some, Option.some.injEq] at hout
        rcases found with ⟨c', out'⟩
        simp only at hout
        subst hout
        exact ⟨out', hinv.exposed halive entry.1.message hcached A hA c' out' hs, hf⟩
  have hscore : 1 ≤ score b.2.1.exposures N := one_le_score _ N (outLeaves_injective N hS.2.1) hcov
  -- the potential
  have hnot : ¬q < countOf b.2.2 := by omega
  unfold potential
  by_cases hr : b.2.1.reused = true
  · rw [livePotential_reused q _ b.2.1 _ halive hnot hr]
    exact le_add_right le_rfl
  · have hr' : b.2.1.reused = false := by simpa using hr
    rw [livePotential_alive q _ b.2.1 _ halive hnot hr']
    calc
      (1 : ENNReal) ≤ score b.2.1.exposures N := hscore
      _ ≤ forecast (horizon - b.2.1.exposures.length) b.2.1.exposures N := score_le_forecast _ _ _
      _ ≤ bankValue b.2.1 := List.le_sum_of_mem (List.mem_map_of_mem htarget)
      _ ≤ _ := le_self_add.trans le_self_add

end SigGolfCandidate.T3.Security.CaseC
