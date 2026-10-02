import SigGolfCandidate.T3.Secc.CaseCNearFinal

/-!
# Stream CC: `NearChainHyp` from B-PAIR's §8 deliverables (stated as hypotheses until they land)

* `BPairNearChain`: B-PAIR's `near_chain` (§8.5), for an arbitrary law of `ω` (B-PAIR's has `restLaw adversary`);
* `BPairGhosts`: the world ghost facts on eager fixed runs (§8.3 `worldGameL_ghosts`, `worldGameL_tracking`, and
  CC-4's G2/G3/G5);
* `BPairLaw`: §8.3 `fixed_worldGameL`;
* `nearChainHyp_of_bpair`: these give `NearChainHyp` (CC discharges `hshort`, `hmono`, `hevent`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The eager fixed run of the lazy world on `ω`'s own tables. -/
noncomputable abbrev fixedL (adversary : AdversaryP) (ω : BPair.Omega (Wots.referenceInputs adversary))
    (fts : BPair.FtsCoord → Digest) :=
  SecretGuessObservation.fixedRun (BPair.envE (BPair.digestOf ω) (BPair.nonceOf ω)) fts
    (BPair.worldGameL (BPair.canon_subset adversary) ω adversary) BPair.initL

/-- **B-PAIR's `near_chain`** (§8.5), for some law of `ω`. -/
def BPairNearChain : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Correctness.Answers → QueryLog Requests → List Wots.Entry → Prop)
    (_hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (_hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × BPair.WStateL → ENNReal)
    (_hevent : ∀ ω fts r, fixedL adversary ω fts r ≠ 0 → r.1.2.2.length ≤ q →
      P (BPair.Omega.answers (BPair.canon_subset adversary) ω fts) r.1.2.1 r.1.2.2 →
        r.2.guesses.Nonempty ∧ 1 ≤ payoff r),
    ∃ L : ProbComp (BPair.Omega (Wots.referenceInputs adversary)),
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
          Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
            P z.2 interaction.value.2 (BPair.publicEntries checked.events) |
          SeccLaw.completedExperiment adversary q hq] ≤
        ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | L] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot
            (BPair.worldGameL (BPair.canon_subset adversary) ω adversary) BPair.initL] * payoff r

/-- **The world ghost facts** on eager fixed runs (§8.3 + CC-4's G2/G3/G5). -/
def BPairGhosts : Prop :=
  ∀ (adversary : AdversaryP) ω fts r, fixedL adversary ω fts r ≠ 0 →
    let A := BPair.Omega.answers (BPair.canon_subset adversary) ω fts
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        BPair.signedOutput A entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
    (∀ x a, (x, a) ∈ r.1.2.2 → x ∈ BPair.digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)) ∧
    (∀ f, BPair.GuessedIn A r.1.2.1 r.1.2.2 f → f ∈ r.2.guesses) ∧
    r.2.memory.births.length ≤ r.1.2.2.length ∧
    (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
      queried A (FullGame.authenticatedSign (evalWithAnswerFn A keygen).2 entry.1)) ∧
    r.2.memory.exposures.length ≤ r.1.2.1.length

/-- **B-PAIR's `fixed_worldGameL`** (§8.3). -/
def BPairLaw : Prop :=
  ∀ (adversary : AdversaryP) ω fts, Prod.fst <$> fixedL adversary ω fts =
    𝒮[BPair.pairRun (BPair.Omega.answers (BPair.canon_subset adversary) ω fts) adversary]

theorem fixed_support_pairRun (hlaw : BPairLaw) (adversary : AdversaryP) (ω) (fts) (r)
    (hr : fixedL adversary ω fts r ≠ 0) :
    r.1 ∈ support (BPair.pairRun (BPair.Omega.answers (BPair.canon_subset adversary) ω fts) adversary) := by
  rw [mem_support_iff, probOutput_def, ← hlaw adversary ω fts, map_eq_bind_pure_comp]
  rw [RetainedObservation.bind_nonzero]
  exact ⟨r, hr, by simp [Function.comp_def]⟩

/-- **`NearChainHyp` from B-PAIR's deliverables.** -/
theorem nearChainHyp_of_bpair (hchain : BPairNearChain) (hghosts : BPairGhosts) (hlaw : BPairLaw) :
    NearChainHyp := by
  intro adversary q hq
  refine hchain adversary q hq NearIn nearIn_short nearIn_mono (nearPayoff q) ?_
  intro ω fts r hr hq' hP
  obtain ⟨hexp, hrows, htrack, hbirths, htrials, hexplen⟩ := hghosts adversary ω fts r hr
  obtain ⟨hlog, hent⟩ := pairRun_honest _ adversary r.1 (fixed_support_pairRun hlaw adversary ω fts r hr)
  refine ⟨?_, payoff_of_ghosts q _ _ r hlog hent hexp (fun x a hx hd => (hrows x a hx hd).2) htrials hbirths
    hexplen hq' hP⟩
  obtain ⟨-, -, -, f, -, -, -, -, -, -, -, hguess, -⟩ := hP
  exact ⟨f, htrack f hguess⟩

/-- **The small route from B-PAIR's §8 deliverables** (the case-(C) contract with `K = 104`). -/
theorem small_route_of_bpair (hchain : BPairNearChain) (hghosts : BPairGhosts) (hlaw : BPairLaw) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_of_nearChain (nearChainHyp_of_bpair hchain hghosts hlaw)

end SigGolfCandidate.T3.Security.CaseC
