import SigGolfCandidate.T3.Secc.PairGuessCouple

/-!
# B-PAIR (4/4): the pair and one-guess bounds

* per `ω` (everything except the FTS secrets): the reference run on G's eager table with uniform FTS secrets
  `fts`, read through any event that implies a world event on the coupled fixed run, is bounded by the lazy world
  (`fts_event_le_world`); two guessed secrets within `q` entries: `pairTerm q` (`fts_pair_le`), one: `guessTerm q`
  (`fts_one_le`).
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Per `ω`: the reference run with uniform FTS secrets against the lazy world -/

section WorldBound
open SecretGuessObservation (fixedRun lazyRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

/-- The uniform law of the FTS secrets (the world's initial completion). -/
noncomputable def secretsLaw : SPMF (FtsCoord → Digest) := UniformTableCompletion.complete init.allowed

/-- The reference run with uniform FTS secrets, paired with the secrets. -/
noncomputable def ftsRun (adversary : AdversaryP) : SPMF ((FtsCoord → Digest) × (Bool × QueryLog Requests × List Wots.Entry)) :=
  secretsLaw >>= fun fts => (fun run => (fts, run)) <$> 𝒮[pairRun (Omega.answers hU ω fts) adversary]

/-- Any event of the reference run implying a world event on the coupled fixed run is bounded by the lazy world. -/
theorem fts_event_le_world (adversary : AdversaryP)
    (event : (FtsCoord → Digest) → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WState → Prop)
    (himp : ∀ fts result, fixedRun env fts (worldGame hU ω adversary) init result ≠ 0 → event fts result.1 →
      wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤ Pr[wevent | lazyRun env (worldGame hU ω adversary) init] := by
  rw [← SecretGuessObservation.run_erasure env (worldGame hU ω adversary) init (fun _ => Finset.univ_nonempty)]
  unfold ftsRun secretsLaw
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro fts
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGame hU ω fts adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp fts result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he

/-- **Two guessed secrets** within `q` recorded entries. -/
theorem fts_pair_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun x => x.2.2.2.length ≤ q ∧ PairGuessIn (Omega.answers hU ω x.1) x.2.2.1 x.2.2.2 | ftsRun hU ω adversary] ≤
      pairTerm q := by
  refine (fts_event_le_world hU ω adversary
    (fun fts run => run.2.2.length ≤ q ∧ PairGuessIn (Omega.answers hU ω fts) run.2.1 run.2.2)
    (fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ q)
    ?_).trans ?_
  · rintro fts result hr ⟨hlen, f, g, hfg, hf, hg⟩
    obtain ⟨hp, hgs⟩ := worldGame_tracking hU ω fts adversary result hr
    refine ⟨?_, hp.trans hlen⟩
    have hsub : ({f, g} : Finset FtsCoord) ⊆ result.2.guesses := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hgs _ hf
      · exact hgs _ hg
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hfg] at this
  · have h := lazyRun_pair_le env (worldGame hU ω adversary) PUnit.unit q
    rw [card_digest] at h
    exact h

/-- **One guessed secret** within `q` recorded entries. -/
theorem fts_one_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun x => x.2.2.2.length ≤ q ∧ OneGuessIn (Omega.answers hU ω x.1) x.2.2.1 x.2.2.2 | ftsRun hU ω adversary] ≤
      guessTerm q := by
  refine (fts_event_le_world hU ω adversary
    (fun fts run => run.2.2.length ≤ q ∧ OneGuessIn (Omega.answers hU ω fts) run.2.1 run.2.2)
    (fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ q)
    ?_).trans ?_
  · rintro fts result hr ⟨hlen, f, hf⟩
    obtain ⟨hp, hgs⟩ := worldGame_tracking hU ω fts adversary result hr
    exact ⟨⟨f, hgs f hf⟩, hp.trans hlen⟩
  · have h := lazyRun_guess_le env (worldGame hU ω adversary) PUnit.unit q
    rw [card_digest] at h
    exact h

end WorldBound

end SigGolfCandidate.T3.Security.BPair
