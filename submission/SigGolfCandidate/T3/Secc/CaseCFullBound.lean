import SigGolfCandidate.T3.Secc.CaseCFull

/-!
# Stream CC: the full-certificate bound on the shared law

`full_bound`: `Pr[CleanWin ∧ pinned case (C) with all 21 opened secrets disclosed | completedExperiment]
≤ (theta + 1/1024)/2^128 · E[digest births] + q·13145/10^8/2^128`, and with SEC's `expectedBirths_le_shared` the births are at
most the shared-law digest-class charge.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFullBound : DecidableEq T3.Cache := Classical.decEq _

/-- The full-case event read through the projection `(value, recorded state)` and the completion. -/
def FullEvent (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) (A : Correctness.Answers) : Prop :=
  y.1 = true ∧ countOf y.2 ≤ q ∧ PinnedC adversary FullQ ((y.1, ([], y.2)), A)

/-- Completion probability of the full event at a projected sample. -/
noncomputable def fullWeight (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) : ENNReal :=
  Pr[fun t => FullEvent adversary q y (SeccLaw.completeWith (lazyOf y.2) t) |
    (PMF.uniformOfFintype SeccLaw.CompletionTables)]

theorem pmf_probEvent_bind {α β : Type} (p : PMF α) (K : α → PMF β) (F : β → Prop) :
    Pr[F | p.bind K] = expectedValue p (fun a => Pr[F | K a]) := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  rfl

theorem pmf_probEvent_map {α β : Type} (p : PMF α) (f : α → β) (F : β → Prop) :
    Pr[F | p.map f] = Pr[fun a => F (f a) | p] := by
  rw [← PMF.monad_map_eq_map, probEvent_map]
  rfl

theorem pmf_probEvent_mono {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hF : F x
  · simp [hF, h x hF]
  · simp [hF]

theorem pmf_probEvent_eq_zero {α : Type} (p : PMF α) {F : α → Prop} (h : ∀ x, ¬F x) : Pr[F | p] = 0 := by
  simp only [probEvent_eq_tsum_ite]
  simp [h]

theorem fullWeight_le_one (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) :
    fullWeight adversary q y ≤ 1 := probEvent_le_one

theorem completed_full_eq (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] =
      expectedValue (bankExperiment adversary q) (fun b => fullWeight adversary q (b.1, b.2.2)) := by
  unfold SeccLaw.completedExperiment
  rw [pmf_probEvent_bind]
  have hinner : ∀ r : PaddedGame.TraceResult,
      Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 |
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map
          (fun t => (r, SeccLaw.completeWith r.2.2.base.source.2 t))] = fullWeight adversary q (r.1, r.2.2) := by
    intro r
    rw [pmf_probEvent_map]
    rfl
  simp_rw [hinner]
  have h1 := expectedValue_pmf_map (PaddedGame.tracedExperiment adversary q hq)
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) (fullWeight adversary q)
  have h2 := expectedValue_pmf_map (bankExperiment adversary q)
    (fun b : Bool × BankState => (b.1, b.2.2)) (fullWeight adversary q)
  rw [← h1, ← h2]
  have ht := bank_traced adversary q hq
  rw [PMF.monad_map_eq_map, PMF.monad_map_eq_map] at ht
  rw [ht]

/-- **The full-certificate bound** (births form). -/
theorem full_bound_births (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | SeccLaw.completedExperiment adversary q hq] ≤
      (theta + 1 / 1024) / 2 ^ 128 * CreationGame.expectedBirths IsDigestInput adversary q hq +
        (q : ENNReal) * (13145 / 100000000) / 2 ^ 128 := by
  calc
    _ ≤ Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] := by
      apply pmf_probEvent_mono
      intro z hz
      exact ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = expectedValue (bankExperiment adversary q) (fun b => fullWeight adversary q (b.1, b.2.2)) :=
      completed_full_eq adversary q hq
    _ ≤ expectedValue (bankExperiment adversary q) (fun b => potential q b.2) := by
      apply pmf_expectedValue_mono
      intro b hb
      by_cases hex : ∃ t, FullEvent adversary q (b.1, b.2.2) (SeccLaw.completeWith (lazyOf b.2.2) t)
      · obtain ⟨t, ht⟩ := hex
        have hA : Agrees (SeccLaw.completeWith (lazyOf b.2.2) t) (lazyOf b.2.2) :=
          fun input answer hk => SeccLaw.completeWith_agrees _ t input answer hk
        exact (fullWeight_le_one adversary q _).trans
          (full_potential adversary q hq b hb [] _ hA ht.2.1 ht.2.2)
      · push Not at hex
        have h0 : fullWeight adversary q (b.1, b.2.2) = 0 := by
          unfold fullWeight
          exact pmf_probEvent_eq_zero _ hex
        rw [h0]
        exact bot_le
    _ ≤ _ := bank_potential_le adversary q hq

end SigGolfCandidate.T3.Security.CaseC
