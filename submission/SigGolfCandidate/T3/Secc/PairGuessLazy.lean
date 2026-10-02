import SigGolfCandidate.T3.Secc.PairGuessLazyEager

/-!
# B-PAIR (CC-2, 7/7): the lazy forced world for `NearBound`

* `fts_event_le_worldL`: per `ω`, a reference-run event implying a world event on the coupled eager run of the lazy
  world is bounded by the lazy observation run (`envE (digestOf ω) (nonceOf ω)`);
* **`near_chain`**: SECC's shared-law event (clean win, every `GameSplit` pinning `P` of the actual answers, log and
  final verifier's entries) is at most `(2^128 − q)⁻¹ · Σ_{slot<q} E_ω E[payoff | forcedRun envL slot (worldGameL ω)]`,
  for any payoff that is `≥ 1` on the coupled runs where `P` holds within `q` entries (those runs guess a secret);
* per-step laws of the lazy forced world (for CC's bank): `forced_birth_*`, `forced_trial_*`, `forced_nonce_*`,
  `forced_expose`, `forced_searchL` (the signer's search is SEC's lazy random-oracle search on the rows cache),
  `forced_searchL_core` (the search keeps everything but the rows cache and the trial rows).
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

/-! ## Per `ω`: the reference run against the lazy observation run of the lazy world -/

section WorldBoundL
open SecretGuessObservation (fixedRun lazyRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : (FtsCoord → Digest) → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ fts result, fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL result ≠ 0 →
      event fts result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤
      Pr[wevent | lazyRun (envE (digestOf ω) (nonceOf ω)) (worldGameL hU ω adversary) initL] := by
  rw [← SecretGuessObservation.run_erasure _ (worldGameL hU ω adversary) initL (fun _ => Finset.univ_nonempty)]
  unfold ftsRun secretsLaw
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro fts
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGameL hU ω fts adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp fts result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he

end WorldBoundL

/-! ## The chain for `NearBound` -/

section Chain

/-- **The near chain**: the shared-law event is bounded by the `ω`-averaged lazy forced world, slot by slot. -/
theorem near_chain (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω fts r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) fts
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (Omega.answers (canon_subset adversary) ω fts) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ 1 ≤ payoff r) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (publicEntries checked.events) | SeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary)
          initL] * payoff r := by
  refine (shared_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : Omega (Wots.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (Omega.answers (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun fts run => run.2.2.length ≤ q ∧ P (Omega.answers (canon_subset adversary) ω fts) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ 1 ≤ payoff r) ?_).trans ?_
    · rintro fts r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω fts r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω fts adversary r hr).1.trans hlen, hp⟩
    · have h := lazyRun_event_le_forced_of (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q
        (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ 1 ≤ payoff r) payoff (fun _ _ h => h)
      rw [card_digest] at h
      exact h
  calc (∑' ω, Pr[= ω | omegaLaw adversary] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (Omega.answers (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw adversary])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy adversary slot payoff)

end Chain

/-! ## Per-step laws of the lazy forced world -/

section Laws
open SecretGuessObservation (forcedRun forcedImpl runWith)
variable (slot : Nat)

theorem forcedRun_query (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (input : WSpecL.Domain) (s : WStateL) :
    forcedRun E slot (liftM (WSpecL.query input)) s = (forcedImpl E slot input).run s := by
  rw [forcedRun, ← bind_pure (liftM (WSpecL.query input)), SecretGuessObservation.runWith_query_bind]
  simp only [SecretGuessObservation.runWith_pure]
  exact bind_pure _

theorem forced_birth_cached (s : WStateL) (x : HashInput) (a : HashOutput) (h : s.memory.rows x = some a) :
    forcedRun envL slot (birthReq x) s = pure (a, s) := by
  rw [birthReq, forcedRun_query, envL, step_birth, rowStep_some _ _ _ _ a h, liftM_pure, map_pure, replayRow_true]

/-- A fresh digest-row read of the adversary or verifier: a uniform answer, cached and recorded as a birth. -/
theorem forced_birth_fresh (s : WStateL) (x : HashInput) (h : s.memory.rows x = none) (hx : x ∈ digestInputs) :
    forcedRun envL slot (birthReq x) s =
      (fun a => (a, { s with memory := s.memory.readRow x a true })) <$>
        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
  rw [birthReq, forcedRun_query, envL, step_birth, rowStep_in _ _ _ _ h hx, liftM_map, Functor.map_map]

theorem forced_birth_other (s : WStateL) (x : HashInput) (h : s.memory.rows x = none) (hx : x ∉ digestInputs) :
    forcedRun envL slot (birthReq x) s = pure (0, s) := by
  rw [birthReq, forcedRun_query, envL, step_birth, rowStep_out _ _ _ _ h hx, liftM_pure, map_pure, replayRow_true]

theorem forced_trial_cached (s : WStateL) (x : HashInput) (a : HashOutput) (h : s.memory.rows x = some a) :
    forcedRun envL slot (trialReq x) s =
      pure (a, { s with memory := { s.memory with trials := s.memory.trials ++ [x] } }) := by
  rw [trialReq, forcedRun_query, envL, step_trial, rowStep_some _ _ _ _ a h, liftM_pure, map_pure, replayRow_false]

/-- A fresh signer trial row: a uniform answer, cached and recorded as a trial row. -/
theorem forced_trial_fresh (s : WStateL) (x : HashInput) (h : s.memory.rows x = none) (hx : x ∈ digestInputs) :
    forcedRun envL slot (trialReq x) s =
      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
  rw [trialReq, forcedRun_query, envL, step_trial, rowStep_in _ _ _ _ h hx, liftM_map, Functor.map_map]

theorem forced_nonce_cached (s : WStateL) (m : Message) (v : Digest) (h : s.memory.nonces m = some v) :
    forcedRun envL slot (nonceReq m) s = pure (v, s) := by
  rw [nonceReq, forcedRun_query, envL, step_nonce, nonceStep_some _ _ _ v h, liftM_pure, map_pure]

/-- A fresh nonce: uniform on `Digest`, cached. -/
theorem forced_nonce_fresh (s : WStateL) (m : Message) (h : s.memory.nonces m = none) :
    forcedRun envL slot (nonceReq m) s =
      (fun v => (v, { s with memory := s.memory.drawNonce m v })) <$>
        (liftM (PMF.uniformOfFintype Digest) : SPMF Digest) := by
  rw [nonceReq, forcedRun_query, envL, step_nonce, nonceStep_none _ _ _ h, liftM_map, Functor.map_map]

theorem forced_expose (s : WStateL) (o : Option HashOutput) :
    forcedRun envL slot (exposeReq o) s = pure ((), { s with memory := s.memory.expose o }) := by
  rw [exposeReq, forcedRun_query, envL, step_expose]

theorem forcedRun_bind' {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL) :
    forcedRun E slot (first >>= next) s = forcedRun E slot first s >>= fun mid => forcedRun E slot (next mid.1) mid.2 := by
  simp only [forcedRun, SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]

theorem ro_uniform (x : HashInput) :
    𝒮[($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] = (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
  apply SPMF.ext
  intro a
  have h1 : 𝒮[($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] a =
      Pr[= a | ($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] := by
    rw [← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  have h2 := probOutput_uniformSample (α := SphincsSecurity.HashSpec.Range x) a
  have h3 : ((Fintype.card (SphincsSecurity.HashSpec.Range x) : ENNReal))⁻¹ = ((Fintype.card HashOutput : ENNReal))⁻¹ := by
    exact congrArg (fun n : ℕ => ((n : ENNReal))⁻¹)
      (Fintype.card_congr' (rfl : SphincsSecurity.HashSpec.Range x = HashOutput))
  have h4 : (PMF.uniformOfFintype HashOutput) (a : HashOutput) = ((Fintype.card HashOutput : ENNReal))⁻¹ :=
    PMF.uniformOfFintype_apply (a : HashOutput)
  exact h1.trans (h2.trans (h3.trans (h4.symm.trans (SPMF.liftM_apply _ _).symm)))

/-- **The signer's search is SEC's lazy random-oracle search on the rows cache.** -/
theorem forced_searchL (rho : Digest) (m : Message) (counter fuel : Nat) (s : WStateL) :
    (fun r => (r.1, r.2.memory.rows)) <$> forcedRun envL slot (searchL rho m counter fuel) s =
      𝒮[Sampling.roRun 0 (digestSearch rho m counter fuel) s.memory.rows] := by
  induction fuel generalizing counter s with
  | zero =>
      change (fun r => (r.1, r.2.memory.rows)) <$> forcedRun envL slot (pure none) s =
        𝒮[Sampling.roRun 0 (pure none : M (Option (BitVec 32 × HashOutput))) s.memory.rows]
      rw [Sampling.roRun_pure, evalSPMF_pure, forcedRun, SecretGuessObservation.runWith_pure, map_pure]
  | succ fuel ih =>
      have hx := digestInput_mem rho m (BitVec.ofNat 32 counter)
      rw [searchL, digestSearch, forcedRun_bind']
      rw [show digest rho m (BitVec.ofNat 32 counter) =
        Sampling.publicQuery (pad64 (digestInput rho m (BitVec.ofNat 32 counter))) from rfl]
      rw [Sampling.roRun_bind, Sampling.roRun_publicQuery, randomOracle.run_eq, map_bind]
      cases hc : s.memory.rows (pad64 (digestInput rho m (BitVec.ofNat 32 counter))) with
      | some a =>
          rw [forced_trial_cached slot s _ a hc, pure_bind]
          simp only [pure_bind]
          by_cases hadm : digestAdmissible a = true
          · simp only [hadm, ↓reduceIte, forcedRun, SecretGuessObservation.runWith_pure, map_pure,
              Sampling.roRun_pure, evalSPMF_pure]
          · simp only [hadm, ↓reduceIte, Bool.false_eq_true]
            exact ih (counter + 1) _
      | none =>
          rw [forced_trial_fresh slot s _ hc hx, bind_map_left]
          simp only [evalSPMF_bind, bind_assoc, pure_bind]
          rw [ro_uniform]
          refine bind_congr fun a => ?_
          by_cases hadm : digestAdmissible a = true
          · simp only [hadm, ↓reduceIte, forcedRun, SecretGuessObservation.runWith_pure, map_pure,
              Sampling.roRun_pure, evalSPMF_pure]
            rfl
          · simp only [hadm, ↓reduceIte, Bool.false_eq_true]
            exact ih (counter + 1) _

/-- What a signer search keeps: everything but the rows cache and the trial rows. -/
def SearchCore (s s' : WStateL) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.nonces = s.memory.nonces ∧ s'.memory.births = s.memory.births ∧
    s'.memory.exposures = s.memory.exposures

theorem SearchCore.trans {s1 s2 s3 : WStateL} (h1 : SearchCore s1 s2) (h2 : SearchCore s2 s3) : SearchCore s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

theorem SearchCore.refl (s : WStateL) : SearchCore s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The signer's search keeps the observation state, the nonces, the births and the exposures.** -/
theorem forced_searchL_core (rho : Digest) (m : Message) (counter fuel : Nat) (s : WStateL)
    (r : Option (BitVec 32 × HashOutput) × WStateL) (hr : forcedRun envL slot (searchL rho m counter fuel) s r ≠ 0) :
    SearchCore s r.2 := by
  induction fuel generalizing counter s with
  | zero =>
      change forcedRun envL slot (pure none) s r ≠ 0 at hr
      rw [forcedRun, SecretGuessObservation.runWith_pure] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact SearchCore.refl s
  | succ fuel ih =>
      have hx := digestInput_mem rho m (BitVec.ofNat 32 counter)
      rw [searchL, forcedRun_bind', RetainedObservation.bind_nonzero] at hr
      obtain ⟨mid, hm, hr⟩ := hr
      have hmid : SearchCore s mid.2 := by
        cases hc : s.memory.rows (pad64 (digestInput rho m (BitVec.ofNat 32 counter))) with
        | some a =>
            rw [forced_trial_cached slot s _ a hc] at hm
            simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hm
            rw [hm]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        | none =>
            rw [forced_trial_fresh slot s _ hc hx, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hm
            obtain ⟨a, -, hm⟩ := hm
            simp only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hm
            rw [hm, readRow_false]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      by_cases hadm : digestAdmissible mid.1 = true
      · simp only [hadm, ↓reduceIte] at hr
        rw [forcedRun, SecretGuessObservation.runWith_pure] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        exact hmid
      · simp only [hadm, ↓reduceIte, Bool.false_eq_true] at hr
        exact hmid.trans (ih (counter + 1) mid.2 hr)

end Laws

end SigGolfCandidate.T3.Security.BPair
