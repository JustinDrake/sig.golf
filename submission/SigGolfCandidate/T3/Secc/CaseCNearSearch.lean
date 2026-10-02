import SigGolfCandidate.T3.Secc.CaseCNearGhost

/-!
# Stream CC: the signer's digest search in the ghost lazy world is SEC's lazy random-oracle search

* `ev_aux_bind`: one auxiliary step followed by a continuation, in expectation;
* `search_law`: for any payoff of the search result and the rows cache, the expectation under the ghost lazy world
  equals the expectation under SEC's `Sampling.roRun 0 (digestSearch rho m c fuel)` on the rows cache;
* `search_frame`: the search changes only the rows cache and the trial list of the world memory.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The lazy ghost world. -/
noncomputable abbrev implG (slot : Nat) := SecretGuessObservation.forcedImpl (envG BPair.envL) slot

theorem ev_aux_bind {β : Type} (slot : Nat) (i : BPair.AuxL) (k : BPair.AuxSpecL.Range i → OracleComp BPair.WSpecL β)
    (s : GState) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (BPair.WSpecL.query (.inl i)) >>= k) s) G =
      expectedValue (BPair.envL.auxiliary (projS s) i) (fun r =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k r.1)
          { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) }) G) := by
  rw [SecretGuessObservation.runWith_query_bind, expectedValue_bind]
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
  change expectedValue ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> BPair.envL.auxiliary (projS s) i) :
      SPMF _)) _ = _
  rw [expectedValue_map, expectedValue_liftM_pmf, expectedValue_map]

theorem searchL_succ (rho : Digest) (m : Message) (c fuel : Nat) :
    BPair.searchL rho m c (fuel + 1) =
      (liftM (BPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m c)))) >>= fun output =>
        if admissible (selections output) = true then pure (some (BitVec.ofNat 32 c, output))
        else BPair.searchL rho m (c + 1) fuel) := rfl

theorem ev_uniform_eq (g : HashOutput → ENNReal) :
    expectedValue (PMF.uniformOfFintype HashOutput) g = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]

/-- **The search law.** -/
theorem search_law (slot : Nat) (rho : Digest) (m : Message)
    (F : Option (BitVec 32 × HashOutput) → Sampling.RCache → ENNReal) :
    ∀ fuel c (s : GState),
      expectedValue (SecretGuessObservation.runWith (implG slot) (BPair.searchL rho m c fuel) s)
          (fun r => F r.1 r.2.memory.1.rows) =
        expectedValue (Sampling.roRun 0 (digestSearch rho m c fuel) s.memory.1.rows) (fun r => F r.1 r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s
      change expectedValue (SecretGuessObservation.runWith (implG slot) (pure none) s) _ =
        expectedValue (Sampling.roRun 0 (digestSearch rho m c 0) s.memory.1.rows) _
      rw [Sampling.digestSearch_public]
      change _ = expectedValue (Sampling.roRun 0 (pure none) s.memory.1.rows) _
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
        expectedValue_pure]
  | succ fuel ih =>
      intro c s
      rw [searchL_succ, ev_aux_bind]
      rw [Sampling.digestSearch_public, Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery,
        expectedValue_bind, randomOracle.run_eq]
      change expectedValue (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
        (PMF.uniformOfFintype HashOutput)) _ = _
      cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
      | some a =>
          simp only [BPair.rowStep, hx]
          rw [expectedValue_pure, expectedValue_pure]
          dsimp only
          by_cases had : admissible (selections a) = true
          · have hd : Sampling.digestDecode a = some a := by simp [Sampling.digestDecode, had]
            simp only [hd, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · have hd : Sampling.digestDecode a = none := by simp [Sampling.digestDecode, had]
            simp only [hd, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1), ← Sampling.digestSearch_public]
            rfl
      | none =>
          have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
          simp only [BPair.rowStep, hx, hdi, if_true]
          rw [expectedValue_map, expectedValue_bind, ev_uniform_eq]
          apply congrArg
          funext a
          rw [expectedValue_pure]
          dsimp only
          by_cases had : admissible (selections a) = true
          · have hd : Sampling.digestDecode a = some a := by simp [Sampling.digestDecode, had]
            simp only [hd, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · have hd : Sampling.digestDecode a = none := by simp [Sampling.digestDecode, had]
            simp only [hd, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1), ← Sampling.digestSearch_public]
            rfl

/-! ## The search changes only the rows cache and the trial list -/

/-- `s'` agrees with `s` except on the rows cache and the trial list. -/
def RowsFrame (s s' : GState) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.2 = s.memory.2 ∧ s'.memory.1.nonces = s.memory.1.nonces ∧ s'.memory.1.births = s.memory.1.births ∧
    s'.memory.1.exposures = s.memory.1.exposures

theorem RowsFrame.refl (s : GState) : RowsFrame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RowsFrame.trans {s s' s'' : GState} (h : RowsFrame s s') (h' : RowsFrame s' s'') : RowsFrame s s'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2⟩

theorem runWith_bind_nonzero {β γ : Type} (slot : Nat) (W : OracleComp BPair.WSpecL β) (K : β → OracleComp BPair.WSpecL γ)
    (s : GState) (r : γ × GState) (hr : SecretGuessObservation.runWith (implG slot) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith (implG slot) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith (implG slot) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr

theorem runWith_pure_nonzero {β : Type} (slot : Nat) (b : β) (s : GState) (r : β × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr

theorem aux_nonzero (slot : Nat) (i : BPair.AuxL) (s : GState) (r : BPair.AuxSpecL.Range i × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (BPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, BPair.envL.auxiliary (projS s) i res ≠ 0 ∧
      r = (res.1, { s with memory := (res.2, ghostStep s.memory.1 i res.1 s.memory.2) }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> BPair.envL.auxiliary (projS s) i) :
      SPMF _)) r ≠ 0 at hr
  rw [liftM_map_pmf, Functor.map_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  refine ⟨res, ?_, hr⟩
  simpa [SPMF.liftM_apply] using hres

/-- **The search frame.** -/
theorem search_frame (slot : Nat) (rho : Digest) (m : Message) :
    ∀ fuel c (s : GState) r, SecretGuessObservation.runWith (implG slot) (BPair.searchL rho m c fuel) s r ≠ 0 →
      RowsFrame s r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr
      rw [runWith_pure_nonzero slot none s r hr]
      exact RowsFrame.refl s
  | succ fuel ih =>
      intro c s r hr
      rw [searchL_succ] at hr
      obtain ⟨mid, hmid, hr⟩ := runWith_bind_nonzero slot _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hf : RowsFrame s { s with memory := (res.2, ghostStep s.memory.1 (.trial (Sampling.digestTrial rho m c))
          res.1 s.memory.2) } := by
        have hres' : res ∈ (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
            (PMF.uniformOfFintype HashOutput)).support := (PMF.mem_support_iff _ _).mpr hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold BPair.rowStep at hres'
        cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨rfl, rfl, rfl⟩
        | none =>
            simp only [hx] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            exact ⟨rfl, rfl, rfl⟩
      dsimp only at hr
      split_ifs at hr
      · rw [runWith_pure_nonzero slot _ _ r hr]
        exact hf
      · exact hf.trans (ih (c + 1) _ r hr)

end SigGolfCandidate.T3.Security.CaseC
