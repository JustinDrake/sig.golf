import SigGolfCandidate.T3.Secc.CaseCLeaf

/-!
# Stream CC: the three-way split of the pinned fresh case (C)

On a shared-law sample, every opened position of the forgery's digest is disclosed by the actual log or probed by
the final verifier (`verdict_leaf_entries`), hence

    CleanWin ∧ CaseCFreshPinned  ⇒  PinnedC FullQ ∨ PinnedC NearQ ∨ BPair.PairGuess

(`caseC_three_way`): all 21 disclosed, exactly one undisclosed (and guessed), or two distinct undisclosed (both
guessed: B-PAIR's pair event, for every decomposition of the run by `GameSplit` uniqueness).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **Near certificate**: exactly one opened position of the forgery's digest is undisclosed, and the verifier
probed its honest leaf input (B-PAIR's `GuessedIn`). -/
def NearQ (answers : Correctness.Answers) (log : QueryLog Requests) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ f ∈ BPair.openedPositions (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))),
    BPair.GuessedIn answers log (BPair.publicEntries events) f ∧
    ∀ g ∈ BPair.openedPositions (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))),
      g ≠ f → BPair.Disclosed answers log g

/-- Two decompositions of a run share the keygen and interaction records and the verifier's events. -/
theorem split_events_unique (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (g i c g' i' c') (h : Wots.GameSplit adversary result g i c) (h' : Wots.GameSplit adversary result g' i' c') :
    g' = g ∧ i' = i ∧ c'.events = c.events := by
  have hev : result.events = g.events ++ (i.events ++ c.events) := by rw [h.2.2.2]
  obtain ⟨rfl, rfl⟩ := split_unique adversary result g h.1 i h.2.1 c.events hev g' i' c' h'
  refine ⟨rfl, rfl, ?_⟩
  have h1 := congrArg FirstHit.Recorded.events h.2.2.2
  have h2 := congrArg FirstHit.Recorded.events h'.2.2.2
  simp only at h1 h2
  rw [h1] at h2
  exact (List.append_cancel_left (List.append_cancel_left h2)).symm

/-- **The three-way split.** -/
theorem caseC_three_way (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hC : Wots.CaseCFreshPinned adversary z) :
    PinnedC adversary FullQ z ∨ PinnedC adversary NearQ z ∨ BPair.PairGuess adversary z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, -⟩ := pinned_of_caseC hC
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hres := hs.2.2.2
  have hstate : c.state = z.1.2.2.base.source.2 := by
    have := congrArg FirstHit.Recorded.state hres
    exact this.symm
  have hvalue : c.value = true := by
    have := congrArg FirstHit.Recorded.value hres
    exact this.symm.trans hclean.1
  have hCat' := hCat
  obtain ⟨N, -, hN, -, hS, -, -, hF⟩ := hCat
  have hprobe := verdict_leaf_entries g.value.1 i.value i.state c hs.2.2.1 z.2
    (fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)) hvalue f hf m w hof
    (by rw [hN]; exact hS) (by rw [hN]; exact hF)
  have hsplit : ∀ x ∈ BPair.openedPositions (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))),
      BPair.Disclosed z.2 i.value.2 x ∨ BPair.GuessedIn z.2 i.value.2 (BPair.publicEntries c.events) x := by
    intro x hx
    by_cases hd : BPair.Disclosed z.2 i.value.2 x
    · exact Or.inl hd
    · exact Or.inr ⟨hd, hprobe x hx⟩
  by_cases hall : ∀ x ∈ BPair.openedPositions (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))),
      BPair.Disclosed z.2 i.value.2 x
  · exact Or.inl ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat', hall⟩
  push Not at hall
  obtain ⟨f0, hf0, hnd0⟩ := hall
  by_cases hone : ∀ x ∈ BPair.openedPositions (evalWithAnswerFn z.2 (digest (wrho w) m (wdc w))),
      x ≠ f0 → BPair.Disclosed z.2 i.value.2 x
  · refine Or.inr (Or.inl ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat', f0, hf0, ?_, hone⟩)
    exact (hsplit f0 hf0).resolve_left hnd0
  push Not at hone
  obtain ⟨g0, hg0, hne, hnd1⟩ := hone
  refine Or.inr (Or.inr ?_)
  intro g' i' c' hs'
  obtain ⟨rfl, rfl, hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce]
  exact ⟨f0, g0, fun h => hne h.symm, (hsplit f0 hf0).resolve_left hnd0, (hsplit g0 hg0).resolve_left hnd1⟩

end SigGolfCandidate.T3.Security.CaseC
