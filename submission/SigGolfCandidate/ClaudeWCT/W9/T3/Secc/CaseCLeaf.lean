import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared
import SigGolfCandidate.ClaudeWCT.GuessV2.WCTCoords
import SigGolfCandidate.T3.Secc.CaseCLeaf

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
open ClaudeWCT.W9.T3M (WBytes Shaped verifyP wctChainP wctChainInputP recoverFtsP witDecP padDecP wreveal wcpads)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP checkForgeryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wctChainP_first_queried (answers : Correctness.Answers) (index coord child t start count : Nat)
    (p0 p1 v : Digest) (hc : 1 ≤ count) :
    (.inl (.inr (pad64 (wctChainInputP index coord child t start p0 p1 v))) : Spec.Domain) ∈
      queried answers (wctChainP index coord child t start count p0 p1 v) := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n + 1 := ⟨count - 1, by omega⟩
  unfold wctChainP
  rw [List.range'_succ, List.foldlM_cons, queried_bind, queried_shortHash]
  exact List.mem_append_left _ (List.mem_singleton_self _)
theorem recoverFtsP_chain_queried (answers : Correctness.Answers) (N : HashOutput) (w : WBytes) (k : WCT9.Coord)
    (t : Fin 7) (hu : 1 ≤ WCT9.digit (WCT9.rank N k) t) :
    (.inl (.inr (pad64 (wctChainInputP (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val t.val
        (3 - WCT9.digit (WCT9.rank N k) t) (wcpads w k.val t.val).1 (wcpads w k.val t.val).2
        (wreveal w k.val t.val (WCT9.digit (WCT9.rank N k) t))))) : Spec.Domain) ∈
      queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) := by
  unfold recoverFtsP
  rw [queried_bind]
  apply List.mem_append_left
  rw [ClaudeWCT.W9.T3M.WctExtract.queried_mapM]
  refine List.mem_flatMap.mpr ⟨k, List.mem_finRange k, ?_⟩
  rw [ClaudeWCT.W9.T3M.WctExtract.recoverCoordinateP_dec, queried_bind]
  apply List.mem_append_left
  rw [ClaudeWCT.W9.T3M.WctExtract.queried_mapM]
  refine List.mem_flatMap.mpr ⟨t, List.mem_finRange t, ?_⟩
  exact wctChainP_first_queried answers _ _ _ _ _ _ _ _ _ hu
theorem witnessOf_unique {answers : Correctness.Answers} {pk : Digest} {forgery : ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : PaddedExtraction.WitnessOf answers pk forgery m w)
    (h' : PaddedExtraction.WitnessOf answers pk forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, h1⟩ := h
      obtain ⟨rfl, h2⟩ := h'
      rw [h1] at h2
      exact ⟨rfl, Option.some.inj h2⟩
theorem verdict_accepting (pk : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (checked : FirstHit.Recorded Bool)
    (hr : checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker pk interaction) before))
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer)
    (hwin : checked.value = true) (forgery : ForgeryP) (hf : interaction.1 = some forgery) :
    ∃ check ∈ support (FirstHit.record (checkForgeryP pk interaction.2 forgery) before),
      check.events = checked.events ∧ check.state = checked.state ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers pk forgery message witness ∧
        evalWithAnswerFn answers (verifyP message pk witness) = true ∧
        ∀ input ∈ queried answers (verifyP message pk witness),
          input ∈ queried answers (checkForgeryP pk interaction.2 forgery) := by
  simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
  obtain ⟨check, hcheck, last, hlast, hvalue, hevents, hstate⟩ := FirstHit.record_bind_support _ _ before checked hr
  rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
  subst last
  simp only [List.append_nil] at hevents
  have hand : (decide (interaction.2.length ≤ 2 ^ 32) && check.value) = true := hvalue.symm.trans hwin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
  have ha' : ∀ input answer, SourceReplay.known check.state input = some answer → answers input = answer := by
    simpa only [hstate] using ha
  have hw := (SourceReplay.resolves_of_run _ (PaddedExtraction.check_hashOnly pk interaction.2 forgery) before
    (check.value, check.state) (FirstHit.recorded_support _ _ _ hcheck)).eval answers ha'
  rw [hand.2] at hw
  obtain ⟨-, message, witness, hof, hv, hsub⟩ := PaddedExtraction.check_accepting answers pk interaction.2 forgery hw
  exact ⟨check, hcheck, hevents.symm, hstate.symm, message, witness, hof, hv, hsub⟩
theorem chainValue_eq_wctValue (answers : Correctness.Answers) (a : Guess.ChainAddr) (p : Nat) :
    Guess.chainValue answers a p =
      ClaudeWCT.W9.T3M.Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p := rfl
theorem honestProbe_slot (answers : Correctness.Answers) (N : HashOutput) (k : WCT9.Coord) (t : Fin 7)
    (p : Fin 3) :
    Guess.honestProbe answers (Guess.chainOf N k t, p) =
      pad64 (wctChainInputP (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val t.val p.val 0 0
        (ClaudeWCT.W9.T3M.Extract.wctValue answers (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val t.val p.val)) := by
  rw [ClaudeWCT.W9.T3M.wctChainInputP_zero, ClaudeWCT.W9.T3M.Extract.pad64_wctChainInput]
  rfl
theorem verdict_chain_entries (pk : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (checked : FirstHit.Recorded Bool)
    (hr : checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker pk interaction) before))
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer)
    (hwin : checked.value = true) (forgery : ForgeryP) (hf : interaction.1 = some forgery)
    (m : Message) (w : WBytes) (hof : PaddedExtraction.WitnessOf answers pk forgery m w)
    (hH : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w) :
    ∀ (k : WCT9.Coord) (t : Fin 7) (c : Guess.GCoord),
      c.1 = Guess.chainOf (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) k t →
      c.2.val = 3 - Guess.deficit (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) k t →
      ∃ answer, (Guess.honestProbe answers c, answer) ∈ BPair.publicEntries checked.events := by
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting pk interaction before checked hr answers ha hwin forgery hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  set N := evalWithAnswerFn answers (digest (wrho w) m (wdc w)) with hN
  obtain ⟨N', -, hN', -, -, -, hqF, -⟩ := ClaudeWCT.W9.T3M.WctExtract.verifyP_walk_wct answers m pk w hv
  rw [← hN] at hN'
  subst hN'
  intro k t c hc1 hc2
  obtain ⟨a, p⟩ := c
  simp only at hc1 hc2
  subst hc1
  have hu : 1 ≤ WCT9.digit (WCT9.rank N k) t := by
    have := p.isLt
    unfold Guess.deficit at hc2
    omega
  have hq := recoverFtsP_chain_queried answers N w k t hu
  obtain ⟨hval, hpad⟩ := (hH.2 k).1 t
  rw [hval, hpad hu] at hq
  have hp : 3 - WCT9.digit (WCT9.rank N k) t = p.val := by
    unfold Guess.deficit at hc2
    omega
  rw [hp] at hq
  have hq' : (.inl (.inr (Guess.honestProbe answers (Guess.chainOf N k t, p))) : Spec.Domain) ∈
      queried answers (checkForgeryP pk interaction.2 forgery) := by
    rw [honestProbe_slot]
    exact hsub _ (hqF _ hq)
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
    (PaddedExtraction.check_hashOnly pk interaction.2 forgery) before check hcheck answers
    (by rw [hst]; exact ha) _ hq'
  rw [hev] at hevent
  exact ⟨_, SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hevent⟩
end ClaudeWCT.W9.T3.Security.CaseC
