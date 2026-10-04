import SigGolfCandidate.T3.Secc.PairGuessLazyEager
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyFree

section

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
section Chain
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
theorem forced_trial_fresh (s : WStateL) (x : HashInput) (h : s.memory.rows x = none) (hx : x ∈ digestInputs) :
    forcedRun envL slot (trialReq x) s =
      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
  rw [trialReq, forcedRun_query, envL, step_trial, rowStep_in _ _ _ _ h hx, liftM_map, Functor.map_map]
theorem forced_nonce_cached (s : WStateL) (m : Message) (v : Digest) (h : s.memory.nonces m = some v) :
    forcedRun envL slot (nonceReq m) s = pure (v, s) := by
  rw [nonceReq, forcedRun_query, envL, step_nonce, nonceStep_some _ _ _ v h, liftM_pure, map_pure]
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
def SearchCore (s s' : WStateL) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.nonces = s.memory.nonces ∧ s'.memory.births = s.memory.births ∧
    s'.memory.exposures = s.memory.exposures
theorem SearchCore.trans {s1 s2 s3 : WStateL} (h1 : SearchCore s1 s2) (h2 : SearchCore s2 s3) : SearchCore s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩
theorem SearchCore.refl (s : WStateL) : SearchCore s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
end

section

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
section Steps
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
def Keeps (m m' : LazyMem) : Prop := m'.births = m.births ∧ m'.exposures = m.exposures ∧ m'.trials = m.trials
theorem Keeps.refl (m : LazyMem) : Keeps m m := ⟨rfl, rfl, rfl⟩
theorem Keeps.trans {m1 m2 m3 : LazyMem} (h1 : Keeps m1 m2) (h2 : Keeps m2 m3) : Keeps m1 m3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
theorem fixed_coin_state (n : Nat) (s : WStateL) (r : Fin (n + 1) × WStateL)
    (hr : fixedRun (envE D Nn) fts (coinReqL n) s r ≠ 0) : r.2 = s := by
  unfold coinReqL fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) r ≠ 0 at hr
  rw [liftM_map, Functor.map_map] at hr
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
    SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨c, _, rfl⟩ := hr
  rfl
theorem fixed_guess_state (p : FtsCoord × Digest) (s : WStateL) (r : Bool × WStateL)
    (hr : fixedRun (envE D Nn) fts (guessReq p) s r ≠ 0) : r.2.memory = s.memory := by
  unfold guessReq fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  change (pure (decide (fts p.1 = p.2), SecretGuessObservation.afterTrial (envE D Nn) s p.1 p.2
    (decide (fts p.1 = p.2))) : SPMF (Bool × WStateL)) r ≠ 0 at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  rw [hr]
  rfl
theorem fixed_disclosures_state (positions : List FtsCoord) (s : WStateL) (r : List Digest × WStateL)
    (hr : fixedRun (envE D Nn) fts (positions.mapM discloseReq) s r ≠ 0) : r.2.memory = s.memory := by
  induction positions generalizing s r with
  | nil =>
      rw [List.mapM_nil] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
  | cons first rest ih =>
      rw [List.mapM_cons] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
      rw [runL_pure_nonzero _ fts _ _ r hr]
      have hm1 : m1.2.memory = s.memory := by
        unfold discloseReq fixedRun runWith at h1
        rw [simulateQ_spec_query] at h1
        change (pure (fts first, SecretGuessObservation.afterDisclosure (envE D Nn) s first (fts first)) :
          SPMF (Digest × WStateL)) m1 ≠ 0 at h1
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h1
        rw [h1]
        rfl
      exact (ih m1.2 m2 h2).trans hm1
theorem fixed_nonce_keeps (m : Message) (s : WStateL) (r : Digest × WStateL)
    (hr : fixedRun (envE D Nn) fts (nonceReq m) s r ≠ 0) : Keeps s.memory r.2.memory := by
  cases hc : s.memory.nonces m with
  | some v =>
      rw [nonceReq, fixed_aux_single D Nn fts s (.nonce m) v s.memory (nonceStep_some _ _ _ v hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact Keeps.refl _
  | none =>
      rw [nonceReq, fixed_aux_single D Nn fts s (.nonce m) (Nn m) (s.memory.drawNonce m (Nn m))
        ((nonceStep_none _ _ _ hc).trans (map_pure _ _))] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact ⟨rfl, rfl, rfl⟩
theorem fixed_expose_mem (o : Option HashOutput) (s : WStateL) (r : Unit × WStateL)
    (hr : fixedRun (envE D Nn) fts (exposeReq o) s r ≠ 0) : r.2.memory = s.memory.expose o := by
  rw [exposeReq, fixed_aux_single D Nn fts s (.expose o) () (s.memory.expose o) rfl] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  rw [hr]
theorem fixed_birth_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) fts (birthReq x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [birthReq, fixed_aux_single D Nn fts s (.birth x) a (s.memory.replayRow x true)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [birthReq, fixed_aux_single D Nn fts s (.birth x) (rowVal D x) (s.memory.readRow x (rowVal D x) true)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_true]
      · rw [birthReq, fixed_aux_single D Nn fts s (.birth x) 0 (s.memory.replayRow x true)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]
theorem fixed_trial_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) fts (trialReq x) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials ++ [x] := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [trialReq, fixed_aux_single D Nn fts s (.trial x) a (s.memory.replayRow x false)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [trialReq, fixed_aux_single D Nn fts s (.trial x) (rowVal D x) (s.memory.readRow x (rowVal D x) false)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_false]
      · rw [trialReq, fixed_aux_single D Nn fts s (.trial x) 0 (s.memory.replayRow x false)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]
end Steps
section Programs
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCount : DecidableEq T3.Cache := Classical.decEq _
theorem queried_sign_search (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request)
    (hc : request.cache = published) (x : HashInput)
    (hx : (.inl (.inr x) : T3.Spec.Domain) ∈ SecurityExtraction.queried (Omega.answers hU ω fts)
      (digestSearch (nonceOf ω request.message) request.message 0 attemptLimit)) :
    (.inl (.inr x) : T3.Spec.Domain) ∈ SecurityExtraction.queried (Omega.answers hU ω fts)
      (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  rw [SecurityExtraction.queried_bind, if_pos hc, Correctness.signPayload_eq, SecurityExtraction.queried_bind,
    SecurityExtraction.queried_bind, eval_nonce hU ω fts request.message]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hx))
theorem queried_digestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    SecurityExtraction.queried A (digestSearch rho m counter (fuel + 1)) =
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) : T3.Spec.Domain) ::
        SecurityExtraction.queried A
          (if digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
            then pure (some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))))
            else digestSearch rho m (counter + 1) fuel) := by
  rw [digestSearch]
  exact SecurityExtraction.queried_query_bind A _ _
theorem searchL_counts (fts : FtsCoord → Digest) (rho : Digest) (m : Message) (counter fuel : Nat) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option (BitVec 32 × HashOutput) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (searchL rho m counter fuel) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (digestSearch rho m counter fuel) := by
  induction fuel generalizing counter s r with
  | zero =>
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨rfl, rfl, fun x hx => Or.inl hx⟩
  | succ fuel ih =>
      rw [searchL] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      obtain ⟨hb1, he1, ht1⟩ := fixed_trial_counts _ _ fts _ s m1 h1
      have g1 := run_good _ _ fts _ s hs m1 h1
      have hv1 : m1.1 = Omega.answers hU ω fts (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) := by
        have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ s hs.1 m1 h1
        rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (trialReq (pad64 (digestInput rho m
            (BitVec.ofNat 32 counter)))) = pure (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))
          from by simp only [trialReq, simulateQ_spec_query, inlineWith]] at h
        rw [congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h), answers_digest hU ω fts _ (digestInput_mem _ _ _)]
      rw [queried_digestSearch_succ, ← hv1]
      by_cases hadm : digestAdmissible m1.1 = true
      · simp only [hadm, ↓reduceIte] at hr ⊢
        rw [runL_pure_nonzero _ fts _ _ r hr]
        refine ⟨hb1, he1, fun x hx => ?_⟩
        rw [ht1, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_self)
      · simp only [hadm, ↓reduceIte, Bool.false_eq_true] at hr ⊢
        obtain ⟨hb2, he2, ht2⟩ := ih (counter + 1) m1.2 g1.1 r hr
        refine ⟨hb2.trans hb1, he2.trans he1, fun x hx => ?_⟩
        rcases ht2 x hx with hx | hx
        · rw [ht1, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Or.inl hx
          · exact Or.inr (List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hx)
theorem finishL_state (fts : FtsCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (finishL hU ω request rho found) s r ≠ 0) :
    r.2.memory = s.memory := by
  cases found with
  | none => rw [runL_pure_nonzero _ fts _ s r hr]
  | some found =>
      obtain ⟨c, out⟩ := found
      change fixedRun (envE (digestOf ω) (nonceOf ω)) fts (match signerLayers hU ω request out with
        | none => pure none
        | some pieces => do
            let values ← (openedPositions out).mapM discloseReq
            pure (some (Correctness.assembledSignature rho
              (openedValues (overwrite (openedPositions out) values) out,
                (signerForest hU ω out).2.1, (signerForest hU ω out).2.2) pieces))) s r ≠ 0 at hr
      cases hl : signerLayers hU ω request out with
      | none =>
          rw [hl] at hr
          rw [runL_pure_nonzero _ fts _ s r hr]
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, hm, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
          rw [runL_pure_nonzero _ fts _ _ r hr]
          exact fixed_disclosures_state _ _ fts _ s mid hm
theorem signL_counts (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (signL hU ω published request) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures.length ≤ s.memory.exposures.length + 1 ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) := by
  unfold signL at hr
  by_cases hc : request.cache = published
  · rw [if_pos hc] at hr
    obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
    obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
    obtain ⟨m3, h3, hr⟩ := runL_bind_nonzero _ fts _ _ m2.2 r hr
    have k1 := fixed_nonce_keeps _ _ fts request.message s m1 h1
    have g1 := run_good _ _ fts _ s hs m1 h1
    have hv1 : m1.1 = nonceOf ω request.message := by
      have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ s hs.1 m1 h1
      rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (nonceReq request.message) =
        pure (nonceOf ω request.message) from by simp only [nonceReq, simulateQ_spec_query, inlineWith]] at h
      exact congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h)
    obtain ⟨hb2, he2, ht2⟩ := searchL_counts hU ω fts m1.1 request.message 0 attemptLimit m1.2 g1.1 m2 h2
    have hm3 := fixed_expose_mem _ _ fts _ m2.2 m3 h3
    have hr4 := finishL_state hU ω fts request m1.1 m2.1 m3.2 r hr
    rw [hr4, hm3]
    refine ⟨hb2.trans k1.1, ?_, fun x hx => ?_⟩
    · change (m2.2.memory.exposures ++ (m2.1.map Prod.snd).toList).length ≤ s.memory.exposures.length + 1
      rw [List.length_append, he2, k1.2.1]
      cases m2.1 <;> simp
    · change x ∈ m2.2.memory.trials at hx
      rcases ht2 x hx with hx | hx
      · rw [k1.2.2] at hx
        exact Or.inl hx
      · rw [hv1] at hx
        exact Or.inr (queried_sign_search hU ω fts published request hc x hx)
  · rw [if_neg hc] at hr
    rw [runL_pure_nonzero _ fts _ s r hr]
    exact ⟨rfl, Nat.le_succ _, fun x hx => Or.inl hx⟩
theorem hashL_counts (fts : FtsCoord → Digest) (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (hashL hU ω x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  unfold hashL at hr
  cases hd : decodeProbe x with
  | some p =>
      rw [hd] at hr
      dsimp only at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      rw [runL_pure_nonzero _ fts _ _ r hr, fixed_guess_state _ _ fts p s m1 h1]
      exact ⟨Nat.le_succ _, rfl, rfl⟩
  | none =>
      rw [hd] at hr
      dsimp only at hr
      by_cases hx : x ∈ digestInputs
      · rw [if_pos hx] at hr
        exact fixed_birth_counts _ _ fts x s r hr
      · rw [if_neg hx] at hr
        rw [runL_pure_nonzero _ fts _ s r hr]
        exact ⟨Nat.le_succ _, rfl, rfl⟩
theorem interactionL_counts (fts : FtsCoord → Digest) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory)
    (r : (α × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (interactionL hU ω published program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.2.length ∧
      r.2.memory.exposures.length ≤ s.memory.exposures.length + r.1.2.1.length ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (FullGame.authenticatedSign published entry.1) := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [interactionL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨by simp, by simp, fun x hx => Or.inl hx⟩
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        have hm := fixed_coin_state _ _ fts n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [interactionL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω fts x s m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, ?_, fun y hy => ?_⟩
        · change m2.2.memory.births.length ≤ s.memory.births.length + (m2.1.2.2.length + 1)
          omega
        · rw [he1] at i2
          exact i2
        · rcases i3 y hy with hy | hy
          · rw [ht1] at hy
            exact Or.inl hy
          · exact Or.inr hy
      · rw [interactionL_request] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := signL_counts hU ω fts published request s hs m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, ?_, fun y hy => ?_⟩
        · rw [hb1] at i1
          exact i1
        · change m2.2.memory.exposures.length ≤ s.memory.exposures.length + (m2.1.2.1.length + 1)
          omega
        · rcases i3 y hy with hy | ⟨entry, he, hq⟩
          · rcases ht1 y hy with hy | hq
            · exact Or.inl hy
            · exact Or.inr ⟨⟨request, m1.1⟩, List.mem_cons_self, hq⟩
          · exact Or.inr ⟨entry, List.mem_cons_of_mem _ he, hq⟩
theorem programL_counts (fts : FtsCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (programL hU ω program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.length ∧
      r.2.memory.exposures = s.memory.exposures ∧ r.2.memory.trials = s.memory.trials := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨by simp, rfl, rfl⟩
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        have hm := fixed_coin_state _ _ fts n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω fts x s m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, i2.trans he1, i3.trans ht1⟩
        change m2.2.memory.births.length ≤ s.memory.births.length + (m2.1.2.length + 1)
        omega
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr
theorem worldGameL_counts (fts : FtsCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.memory.births.length ≤ r.1.2.2.length ∧
      (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts)
          (FullGame.authenticatedSign (evalWithAnswerFn (Omega.answers hU ω fts) keygen).2 entry.1)) ∧
      r.2.memory.exposures.length ≤ r.1.2.1.length := by
  unfold worldGameL worldGameCore at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ initL r hr
  obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
  rw [runL_pure_nonzero _ fts _ _ r hr]
  have g1 := run_good _ _ fts _ initL (good_empty _ _) m1 h1
  obtain ⟨i1, i2, i3⟩ := interactionL_counts hU ω fts _ _ initL (good_empty _ _) m1 h1
  obtain ⟨p1, p2, p3⟩ := programL_counts hU ω fts _ m1.2 g1.1 m2 h2
  have h0 : initL.memory = LazyMem.empty := rfl
  rw [h0] at i1 i2 i3
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · change m2.2.memory.births.length ≤ (m1.1.2.2 ++ m2.1.2).length
    rw [List.length_append]
    change m1.2.memory.births.length ≤ 0 + m1.1.2.2.length at i1
    omega
  · change x ∈ m2.2.memory.trials at hx
    rw [p3] at hx
    rcases i3 x hx with hx | hx
    · exact absurd hx (List.not_mem_nil)
    · rw [keygen_answers hU ω fts]
      exact hx
  · change m2.2.memory.exposures.length ≤ m1.1.2.1.length
    rw [p2]
    change m1.2.memory.exposures.length ≤ 0 + m1.1.2.1.length at i2
    omega
end Programs
section Bank
theorem worldGameL_bank (adversary : AdversaryP) (ω : Omega (Wots.referenceInputs adversary))
    (fts : FtsCoord → Digest) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) fts
      (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        signedOutput (Omega.answers (canon_subset adversary) ω fts) entry.1.message σ = some output →
          output ∈ r.2.memory.exposures) ∧
    (∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)) ∧
    (∀ f, GuessedIn (Omega.answers (canon_subset adversary) ω fts) r.1.2.1 r.1.2.2 f → f ∈ r.2.guesses) ∧
    r.2.memory.births.length ≤ r.1.2.2.length ∧
    (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
      SecurityExtraction.queried (Omega.answers (canon_subset adversary) ω fts)
        (FullGame.authenticatedSign (evalWithAnswerFn (Omega.answers (canon_subset adversary) ω fts) keygen).2
          entry.1)) ∧
    r.2.memory.exposures.length ≤ r.1.2.1.length := by
  obtain ⟨g1, g2⟩ := worldGameL_ghosts (canon_subset adversary) ω fts adversary r hr
  obtain ⟨c1, c2, c3⟩ := worldGameL_counts (canon_subset adversary) ω fts adversary r hr
  exact ⟨g1, g2, (worldGameL_tracking (canon_subset adversary) ω fts adversary r hr).2, c1, c2, c3⟩
end Bank
end SigGolfCandidate.T3.Security.BPair
end

section


namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep NotDN)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def inlineWith (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    QueryImpl WSpecL (OracleComp WSpec)
  | .inl (.coin n) => (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
  | .inl (.birth x) => pure (rowVal D x)
  | .inl (.trial x) => pure (rowVal D x)
  | .inl (.nonce m) => pure (Nn m)
  | .inl (.expose _) => pure ()
  | .inr q => liftM (WSpec.query (.inr q))
section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_g6LazyCouple : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def inlineAux (ω : CanonTable.Omega U) : QueryImpl WSpecL (OracleComp WSpec) :=
  inlineWith (digestOf ω) (nonceOf ω)
theorem inline_probeW (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (step : Guess.ChainAddr → Fin 3 → Digest → HashOutput) (top : Guess.ChainAddr → HashOutput) (miss : HashOutput)
    (a : Guess.ChainAddr) (p : Fin 3) (v : Digest) :
    simulateQ (inlineWith D Nn) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) =
      Guess.probeW (auxSpec := unifSpec) step top miss a p v := by
  unfold Guess.probeW Guess.trialQ
  rw [simulateQ_bind, simulateQ_spec_query]
  refine bind_congr fun hit => ?_
  cases hit with
  | false => simp only [Bool.false_eq_true, if_false, simulateQ_pure]
  | true =>
      simp only [if_true]
      cases Guess.succPos p with
      | none => simp only [simulateQ_pure]
      | some p' =>
          simp only
          unfold Guess.discloseQ
          rw [simulateQ_bind, simulateQ_spec_query]
          exact bind_congr fun next => by rw [simulateQ_pure]
theorem inline_discloseQ (D : digestInputs → HashOutput) (Nn : Message → Digest) (c : Guess.GCoord) :
    simulateQ (inlineWith D Nn) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) =
      Guess.discloseQ (auxSpec := unifSpec) (V := Digest) c := by
  unfold Guess.discloseQ
  rw [simulateQ_spec_query]
  rfl
theorem inline_discloseAll (D : digestInputs → HashOutput) (Nn : Message → Digest) (cs : List Guess.GCoord) :
    simulateQ (inlineWith D Nn) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) =
      Guess.discloseAll (auxSpec := unifSpec) (V := Digest) cs := by
  induction cs with
  | nil => simp [Guess.discloseAll]
  | cons c rest ih =>
      unfold Guess.discloseAll at ih ⊢
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind, inline_discloseQ]
      refine bind_congr fun v => ?_
      rw [simulateQ_bind, ih]
      exact bind_congr fun vs => by rw [simulateQ_pure]
theorem inline_hashL (ω : CanonTable.Omega U) (x : HashInput) :
    simulateQ (inlineAux ω) (hashL hU ω x) = hashW hU ω x := by
  unfold hashL hashW Guess.ChainTable.hashW
  cases hd : Guess.decodeProbe x with
  | some q => exact inline_probeW _ _ _ _ _ _ _ _
  | none =>
      simp only
      by_cases hx : x ∈ digestInputs
      · rw [if_pos hx]
        unfold birthReq
        rw [simulateQ_spec_query]
        change pure (rowVal (digestOf ω) x) = pure (wA hU ω 0 (.inl (.inr x)))
        rw [answers_digest hU ω 0 x hx]
      · rw [if_neg hx, simulateQ_pure]
        rfl
theorem eval_wctDigestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    evalWithAnswerFn A (WCT9.digestSearch rho m counter (fuel + 1)) =
      if WCT9.admissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true then
        some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))))
      else evalWithAnswerFn A (WCT9.digestSearch rho m (counter + 1) fuel) := by
  rw [WCT9.digestSearch, evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 counter)) =
    A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) from eval_query' A _]
  by_cases h : WCT9.admissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
theorem inline_searchL (ω : CanonTable.Omega U) (rho : Digest) (m : Message) (counter fuel : Nat) :
    simulateQ (inlineAux ω) (searchL rho m counter fuel) =
      pure (evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho m counter fuel)) := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
      rw [eval_wctDigestSearch_succ, answers_digest hU ω _ _ (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _)]
      simp only [searchL, trialReq, simulateQ_bind, simulateQ_spec_query, inlineAux, inlineWith, pure_bind]
      by_cases h : WCT9.admissible (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) = true
      · simp only [h, ↓reduceIte, simulateQ_pure]
      · simp only [h, ↓reduceIte, Bool.false_eq_true]
        exact ih _
theorem signerCore_neg (ω : CanonTable.Omega U) {published : SigGolfCandidate.T3.Cache} {request : Request}
    (hc : ¬request.cache = published) : signerCore hU ω published request = none := by
  unfold signerCore
  rw [if_neg hc]
theorem inline_signL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (inlineAux ω) (signL hU ω published request) = signW hU ω published request := by
  unfold signW openedFor
  simp only [sign_answers]
  unfold signL
  by_cases hc : request.cache = published
  · rw [if_pos hc]
    simp only [nonceReq, exposeReq, simulateQ_bind, simulateQ_spec_query, inline_searchL hU ω]
    simp only [inlineAux, inlineWith, pure_bind]
    rw [← eval_nonce hU ω 0 request.message]
    unfold signerCore
    rw [if_pos hc]
    generalize evalWithAnswerFn (wA hU ω 0) (privateNonce request.message) = rho
    generalize evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) = found
    rcases found with _ | ⟨c, output⟩
    · simp only [finishL, simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
    · simp only [finishL]
      unfold signerLayersW
      generalize evalWithAnswerFn (wA hU ω 0) (signLayers request.cache (output.toNat % 2 ^ 31) 4
        (WCT9.honestForest (wA hU ω 0) (output.toNat % 2 ^ 31), 0, 0)) = L
      rcases L with _ | pieces
      · simp only [simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
      · simp only [simulateQ_bind, simulateQ_pure]
        rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω))
            (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) (revealedCoords output)) =
          Guess.discloseAll (auxSpec := unifSpec) (V := Digest) (revealedCoords output) from
          inline_discloseAll _ _ _]
        exact bind_congr fun values => by rw [Option.map_some]
  · rw [if_neg hc, signerCore_neg hU ω hc]
    simp only [simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
theorem interactionL_pure (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (x : HashInput) (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signL hU ω published request >>= fun signature => interactionL hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : CanonTable.Omega U) {β : Type} (value : β) :
    programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : CanonTable.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => programL hU ω (next coin)) := rfl
theorem programL_public (ω : CanonTable.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : CanonTable.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr c)) >>= next) = programL hU ω (next 0) := rfl
theorem inline_interactionL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (inlineAux ω) (interactionL hU ω published program) = interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionL_pure, interactionW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin, interactionW_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionL_public, interactionW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionL_request, interactionW_request, simulateQ_bind, inline_signL]
        refine bind_congr fun signature => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
theorem inline_programL (ω : CanonTable.Omega U) {β : Type} (program : M β) :
    simulateQ (inlineAux ω) (programL hU ω program) = programW hU ω program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programL_pure, programW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [programL_public, programW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [programL_private]
        exact ih (0 : HashOutput)
theorem worldGame_inline (ω : CanonTable.Omega U) (adversary : AdversaryP) :
    worldGame hU ω adversary = simulateQ (inlineAux ω) (worldGameL hU ω adversary) := by
  unfold worldGameL worldGameCore worldGame
  rw [simulateQ_bind, inline_interactionL]
  refine bind_congr fun interaction => ?_
  rw [simulateQ_bind, inline_programL]
  exact bind_congr fun verdict => by rw [simulateQ_pure]
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def forget (s : WStateL) : WState := ⟨s.allowed, s.retired, s.guesses, s.probes, PUnit.unit⟩
theorem coin_spmf (n : Nat) : (liftM (liftM (coinImpl n) : PMF (Fin (n + 1))) : SPMF (Fin (n + 1))) =
    (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := evalSPMF_query (spec := unifSpec) n
theorem fixed_aux_pure {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem'))
    (next : AuxSpecL.Range input → OracleComp WSpecL α) :
    runWith (fixedImpl (envE D Nn) g) (liftM (WSpecL.query (.inl input)) >>= next) s =
      runWith (fixedImpl (envE D Nn) g) (next v) { s with memory := mem' } := by
  rw [SecretGuessObservation.runWith_query_bind]
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((envE D Nn).auxiliary s input) : SPMF _)) >>= _ = _
  rw [h, liftM_pure, map_pure, pure_bind]
theorem fixed_inline {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : SigGolfCandidate.T3.Security.BPair.Consistent D Nn s.memory) :
    (fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) g W s =
      fixedRun env g (simulateQ (inlineWith D Nn) W) (forget s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => simp only [fixedRun, SecretGuessObservation.runWith_pure, simulateQ_pure, map_pure]
  | query_bind input next ih =>
      rcases input with input | (⟨c, v⟩ | c)
      · cases input with
        | coin n =>
            rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
            change ((fun result => (result.1, { s with memory := result.2 })) <$>
              (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) >>= _ =
              fixedRun env g ((liftM (WSpec.query (.inl n)) : OracleComp WSpec _) >>= fun c =>
                simulateQ (inlineWith D Nn) (next c)) (forget s)
            rw [fixedRun, SecretGuessObservation.runWith_query_bind]
            change _ = ((fun result => (result.1, { forget s with memory := result.2 })) <$>
              (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) >>= _
            have hL : ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) =
                (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, Functor.map_map]
            have hR : ((fun result => (result.1, { forget s with memory := result.2 })) <$>
                (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) =
                (fun c => (c, forget s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, coin_spmf, Functor.map_map]
            rw [hL, hR]
            exact (bind_map_left _ _ _).trans ((bind_congr fun c => ih c s hs).trans
              (bind_map_left (fun c => (c, forget s)) _ (fun result =>
                runWith (fixedImpl env g) (simulateQ (inlineWith D Nn) (next result.1)) result.2)).symm)
        | birth x =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.rowStep_eager D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn g s (.birth x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | trial x =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.rowStep_eager D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn g s (.trial x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | nonce m =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.nonceStep_eager D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn g s (.nonce m) (Nn m) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (Nn m) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn g s (.expose o) () (s.memory.expose o) rfl, simulateQ_bind,
              simulateQ_spec_query]
            change _ = fixedRun env g (pure () >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ ⟨hs.1, hs.2⟩
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (decide (g c = v), SecretGuessObservation.afterTrial (envE D Nn) s c v (decide (g c = v))) >>= _) =
          fixedRun env g ((liftM (WSpec.query (.inr (.inl (c, v)))) : OracleComp WSpec Bool) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (decide (g c = v), SecretGuessObservation.afterTrial env (forget s) c v (decide (g c = v))) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (g c, SecretGuessObservation.afterDisclosure (envE D Nn) s c (g c)) >>= _) =
          fixedRun env g ((liftM (WSpec.query (.inr (.inr c)))  : OracleComp WSpec Digest) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (g c, SecretGuessObservation.afterDisclosure env (forget s) c (g c)) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
theorem fixed_inline_nonzero {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (g : Guess.GCoord → Digest) (W : OracleComp WSpecL α) (s : WStateL)
    (hs : SigGolfCandidate.T3.Security.BPair.Consistent D Nn s.memory)
    (r : α × WStateL) (hr : fixedRun (envE D Nn) g W s r ≠ 0) :
    fixedRun env g (simulateQ (inlineWith D Nn) W) (forget s) (r.1, forget r.2) ≠ 0 := by
  rw [← fixed_inline D Nn g W s hs]
  have hm : r ∈ support (fixedRun (envE D Nn) g W s) := by
    simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr
  have h : (r.1, forget r.2) ∈ support ((fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) g W s) := by
    rw [support_map]
    exact ⟨r, hm, rfl⟩
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using h
end Run
section LazyCouple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
open SecretGuessObservation (fixedRun)
theorem forget_initL : forget initL = init := rfl
theorem fixed_worldGameL (g : Guess.GCoord → Digest) (adversary : AdversaryP) :
    Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL =
      𝒮[pairRun (wA hU ω g) adversary] := by
  have h := congrArg (Functor.map Prod.fst)
    (fixed_inline (digestOf ω) (nonceOf ω) g (worldGameL hU ω adversary) initL
      (SigGolfCandidate.T3.Security.BPair.consistent_empty _ _))
  rw [Functor.map_map] at h
  rw [show (Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL) =
    (fun r => (r.1, forget r.2).1) <$> fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL
    from rfl, h, forget_initL, ← fixed_worldGame hU ω g adversary]
  change _ = Prod.fst <$> fixedRun env g (worldGame hU ω adversary) init
  rw [worldGame_inline]
  rfl
theorem worldGameL_tracking (g : Guess.GCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.probes ≤ r.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU ω g) r.1.2.1 r.1.2.2 c → Guess.PrefixIn r.2.guesses c.1 c.2.val := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) g _ initL
    (SigGolfCandidate.T3.Security.BPair.consistent_empty _ _) r hr
  rw [forget_initL] at h
  change fixedRun env g (simulateQ (inlineAux ω) (worldGameL hU ω adversary)) init (r.1, forget r.2) ≠ 0 at h
  rw [← worldGame_inline] at h
  exact worldGame_tracking hU ω g adversary (r.1, forget r.2) h
end LazyCouple
end ClaudeWCT.W9.T3.Security.WPair
end
