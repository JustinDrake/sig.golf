import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCLeaf
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufPayload
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSmall

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def loggedOutputs (answers : Correctness.Answers) (log : QueryLog Requests) : List HashOutput :=
  log.filterMap fun entry => entry.2.bind fun signature => CaseC.signedOutput answers entry.1.message signature
theorem mem_loggedOutputs {answers : Correctness.Answers} {log : QueryLog Requests} {out : HashOutput} :
    out ∈ loggedOutputs answers log ↔ ∃ entry ∈ log, ∃ signature, entry.2 = some signature ∧
      CaseC.signedOutput answers entry.1.message signature = some out := by
  unfold loggedOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, he, hb⟩
    cases hs : entry.2 with
    | none => rw [hs] at hb; cases hb
    | some signature =>
        rw [hs] at hb
        exact ⟨entry, he, signature, hs, hb⟩
  · rintro ⟨entry, he, signature, hs, ho⟩
    exact ⟨entry, he, by rw [hs]; exact ho⟩
def Disclosed (answers : Correctness.Answers) (log : QueryLog Requests) (a : Guess.ChainAddr) (p : Nat) : Prop :=
  Guess.ChainCovered (loggedOutputs answers log) a p
def GuessedIn (answers : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (c : Guess.GCoord) : Prop :=
  ¬Disclosed answers log c.1 c.2.val ∧ ∃ answer, (Guess.honestProbe answers c, answer) ∈ entries
def PairGuessIn (answers : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ c c' : Guess.GCoord, c.1 ≠ c'.1 ∧ GuessedIn answers log entries c ∧ GuessedIn answers log entries c'
def PairGuess (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  ∀ generated interaction checked,
    CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      PairGuessIn z.2 interaction.value.2 (BPair.publicEntries checked.events)
def PairGuessBound (pairTerm : Nat → ENNReal) : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127),
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PairGuess adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      pairTerm q
theorem slotDisclosed_iff (answers : Correctness.Answers) (log : QueryLog Requests) (N : HashOutput)
    (k : WCT9.Coord) (t : Fin 7) :
    CaseC.SlotDisclosed answers log N k t ↔ Guess.SlotCovered (loggedOutputs answers log) N k t := by
  constructor
  · rintro ⟨entry, he, signature, out, hs, ho, h1, h2, h3⟩
    exact ⟨out, mem_loggedOutputs.mpr ⟨entry, he, signature, hs, ho⟩, congrArg Fin.val h1, h2, h3⟩
  · rintro ⟨out, hout, h1, h2, h3⟩
    obtain ⟨entry, he, signature, hs, ho⟩ := mem_loggedOutputs.mp hout
    exact ⟨entry, he, signature, out, hs, ho, Fin.ext h1, h2, h3⟩
theorem slotDisclosed_iff_disclosed (answers : Correctness.Answers) (log : QueryLog Requests) (N : HashOutput)
    (k : WCT9.Coord) (t : Fin 7) :
    CaseC.SlotDisclosed answers log N k t ↔ Disclosed answers log (Guess.chainOf N k t) (3 - Guess.deficit N k t) := by
  rw [slotDisclosed_iff, Guess.slotCovered_iff_chainCovered]
  rfl
theorem Disclosed.mono_pos {answers : Correctness.Answers} {log : QueryLog Requests} {a : Guess.ChainAddr}
    {p p' : Nat} (h : p ≤ p') (hd : Disclosed answers log a p) : Disclosed answers log a p' :=
  Guess.ChainCovered.mono_pos h hd
theorem loggedOutputs_mono {answers : Correctness.Answers} {log log' : QueryLog Requests}
    (h : ∀ entry ∈ log, entry ∈ log') : ∀ out ∈ loggedOutputs answers log, out ∈ loggedOutputs answers log' := by
  intro out hout
  obtain ⟨entry, he, signature, hs, ho⟩ := mem_loggedOutputs.mp hout
  exact mem_loggedOutputs.mpr ⟨entry, h entry he, signature, hs, ho⟩
theorem Disclosed.mono_log {answers : Correctness.Answers} {log log' : QueryLog Requests} {a : Guess.ChainAddr}
    {p : Nat} (h : ∀ entry ∈ log, entry ∈ log') (hd : Disclosed answers log a p) : Disclosed answers log' a p :=
  Guess.ChainCovered.mono_log (loggedOutputs_mono h) hd
theorem GuessedIn.not_disclosed_le {answers : Correctness.Answers} {log : QueryLog Requests}
    {entries : List Wots.Entry} {c : Guess.GCoord} (h : GuessedIn answers log entries c) {p : Nat}
    (hp : p ≤ c.2.val) : ¬Disclosed answers log c.1 p :=
  fun hd => h.1 (hd.mono_pos hp)
end ClaudeWCT.W9.T3.Security.WPair
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def GameCaseCPinned (adversary : AdversaryP) (answers : Correctness.Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated interaction checked, GameSplit adversary result generated interaction checked ∧
    generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
    interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
      signed (BPB.SignedDigest interaction.value.2 message witness) ∧
      BPB.CaseCAt answers message witness result.events
abbrev CaseCFreshPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseCPinned adversary z.2 Not (QueryRecorded.recordedTrace z.1)
abbrev CaseCSignedPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseCPinned adversary z.2 id (QueryRecorded.recordedTrace z.1)
theorem GameCaseCPinned.linked {adversary : AdversaryP} {answers : Correctness.Answers} {signed : Prop → Prop}
    {result : FirstHit.Recorded Bool} (h : GameCaseCPinned adversary answers signed result) :
    BPB.GameCaseC adversary answers signed result := by
  obtain ⟨generated, interaction, checked, hsplit, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hs, hC⟩ := h
  exact ⟨generated, hsplit.1, interaction, hsplit.2.1, hsplit.extends, hpk, hlen, forgery, hf, hfresh, message,
    witness, hof, hs, hC⟩
theorem caseCSignedPinned_impossible (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSignedPinned adversary z :=
  fun h => BPB.caseC_signed_impossible adversary q hq z hz hclean h.linked
def caseCExtraction : CaseCExtraction where
  CaseCAt := BPB.CaseCAt
  digest_event := by
    intro answers message witness events h
    obtain ⟨N, -, hN, ⟨prior, hp⟩, hS, -, -⟩ := h
    subst hN
    exact ⟨hS, prior, hp⟩
  fresh_not_signer := by
    intro answers published log state hres hagree message witness events hC hsd
    exact BPB.caseCAt_fresh_not_signer answers published log state hres hagree message witness events hC hsd
theorem caseCExtraction_caseCAt : caseCExtraction.CaseCAt = BPB.CaseCAt := rfl
theorem pinned_of_caseC {adversary : AdversaryP} {z : PaddedGame.TraceResult × Correctness.Answers}
    (h : CaseCFreshPinned adversary z) : PinnedC caseCExtraction adversary (fun _ _ _ _ _ => True) z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC⟩ := h
  exact ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC, trivial⟩
def NearQ (answers : Correctness.Answers) (log : QueryLog Requests) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (k : WCT9.Coord) (t : Fin 7) (c : Guess.GCoord),
    c.1 = Guess.chainOf (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k t ∧
    c.2.val = 3 - Guess.deficit (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k t ∧
    WPair.GuessedIn answers log (BPair.publicEntries events) c ∧
    ∀ k' t', (k', t') ≠ (k, t) →
      SlotDisclosed answers log (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k' t'
theorem NearQ.slot {answers : Correctness.Answers} {log : QueryLog Requests} {message : Message} {witness : WBytes}
    {events : List FirstHit.QueryEvent} (h : NearQ answers log message witness events) :
    ∃ (k : WCT9.Coord) (t : Fin 7),
      1 ≤ Guess.deficit (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k t ∧
      ¬SlotDisclosed answers log (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k t := by
  obtain ⟨k, t, ⟨a, p⟩, h1, h2, ⟨hnd, -⟩, -⟩ := h
  simp only at h1 h2
  subst h1
  refine ⟨k, t, by have := p.isLt; omega, fun hd => hnd ?_⟩
  rw [WPair.slotDisclosed_iff_disclosed, ← h2] at hd
  exact hd
theorem split_events_unique (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (g i c g' i' c') (h : GameSplit adversary result g i c) (h' : GameSplit adversary result g' i' c') :
    g' = g ∧ i' = i ∧ c'.events = c.events := by
  have hev : result.events = g.events ++ (i.events ++ c.events) := by rw [h.2.2.2]
  obtain ⟨rfl, rfl⟩ := split_unique adversary result g h.1 i h.2.1 c.events hev g' i' c' h'
  refine ⟨rfl, rfl, ?_⟩
  have h1 := congrArg FirstHit.Recorded.events h.2.2.2
  have h2 := congrArg FirstHit.Recorded.events h'.2.2.2
  simp only at h1 h2
  rw [h1] at h2
  exact (List.append_cancel_left (List.append_cancel_left h2)).symm
def slotCoord (N : HashOutput) (k : WCT9.Coord) (t : Fin 7) (hu : 1 ≤ Guess.deficit N k t) : Guess.GCoord :=
  (Guess.chainOf N k t, ⟨3 - Guess.deficit N k t, by omega⟩)
theorem wct_caseC_three_way (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hC : CaseCFreshPinned adversary z) :
    PinnedC caseCExtraction adversary FullQ z ∨ PinnedC caseCExtraction adversary NearQ z ∨
      WPair.PairGuess adversary z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat⟩ := hC
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hres := hs.2.2.2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hres).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hres).symm.trans hclean.1
  have hCat' := hCat
  obtain ⟨N, -, hN, -, -, -, hH⟩ := hCat
  have hprobe := verdict_chain_entries g.value.1 i.value i.state c hs.2.2.1 z.2
    (fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)) hvalue f hf m w hof
    (by rw [hN]; exact hH)
  rw [hN] at hprobe
  have hguess : ∀ (k : WCT9.Coord) (t : Fin 7) (hu : 1 ≤ Guess.deficit N k t),
      ¬Guess.ChainCovered (WPair.loggedOutputs z.2 i.value.2) (Guess.chainOf N k t) (3 - Guess.deficit N k t) →
      WPair.GuessedIn z.2 i.value.2 (BPair.publicEntries c.events) (slotCoord N k t hu) :=
    fun k t hu hnc => ⟨hnc, hprobe k t (slotCoord N k t hu) rfl rfl⟩
  rcases Guess.caseC_slots (WPair.loggedOutputs z.2 i.value.2) N with
    hall | ⟨k, t, hu, hnc, hrest⟩ | ⟨k, t, k', t', hne, hu, hnc, hu', hnc'⟩
  · refine Or.inl ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat', fun k t => ?_⟩
    rw [hN]
    exact (WPair.slotDisclosed_iff _ _ _ k t).mpr (hall k t)
  · refine Or.inr (Or.inl ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat', ?_⟩)
    unfold NearQ
    rw [hN]
    exact ⟨k, t, slotCoord N k t hu, rfl, rfl, hguess k t hu hnc,
      fun k' t' hne => (WPair.slotDisclosed_iff _ _ _ k' t').mpr (hrest k' t' hne)⟩
  · refine Or.inr (Or.inr ?_)
    intro g' i' c' hs'
    obtain ⟨rfl, rfl, hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
    rw [hce]
    exact ⟨slotCoord N k t hu, slotCoord N k' t' hu', Guess.chainOf_ne hne, hguess k t hu hnc, hguess k' t' hu' hnc'⟩
noncomputable def caseCSplitInterface (pairTerm : Nat → ENNReal) (hpair : WPair.PairGuessBound pairTerm) :
    CaseCSplitInterface caseCExtraction where
  CaseCFreshPinned := CaseCFreshPinned
  NearQ := NearQ
  PairGuess := WPair.PairGuess
  pairTerm := pairTerm
  three_way := wct_caseC_three_way
  pair_guess_bound := hpair
end ClaudeWCT.W9.T3.Security.CaseC
