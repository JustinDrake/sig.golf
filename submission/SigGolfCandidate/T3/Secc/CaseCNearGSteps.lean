import SigGolfCandidate.T3.Secc.CaseCNearInv

/-!
# Stream CC: the bank potential `ΦI` under the ghost lazy world's handlers

`SuperProg (implG slot) (ΦI q)` for: coins, probes, disclosures, `finishL`, public queries (`hashL`) and the signer
(`signL`, via the search law and `mem_sign_fresh` for a first signing, via replay for a repeated one), hence for the
whole world game (`worldGame_ΦI`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## SPMF expectations on the nonzero support -/

theorem spmf_ev_mono {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  rw [SPMF.probOutput_eq_apply]
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul' le_rfl (h x hx)

theorem spmf_ev_le {α : Type} (p : SPMF α) {f : α → ENNReal} {c : ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ c) :
    expectedValue p f ≤ c :=
  (spmf_ev_mono p h).trans (expectedValue_le_of_le p fun _ => le_rfl)

theorem spmf_ev_congr {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x = g x) :
    expectedValue p f = expectedValue p g :=
  le_antisymm (spmf_ev_mono p fun x hx => (h x hx).le) (spmf_ev_mono p fun x hx => (h x hx).ge)

/-- A program that keeps the memory does not change `ΦI`. -/
theorem superProg_of_memory {β : Type} (slot q : Nat) (W : OracleComp BPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implG slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg (implG slot) (ΦI q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]

/-! ## Memory-preserving requests -/

theorem coin_memory (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (BPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.coin n) s r hr
  have hres' : res ∈ (BPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl

theorem secret_memory {β : Type} (slot : Nat) (p : (BPair.FtsCoord × Digest) ⊕ BPair.FtsCoord)
    (s : GState) (r : (BPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (BPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk, map_eq_bind_pure_comp,
      RetainedObservation.bind_nonzero, Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk,
      map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl

theorem coin_ΦI (slot q n : Nat) : SuperProg (implG slot) (ΦI q) (BPair.coinReqL n) :=
  superProg_of_memory slot q _ fun s r hr => coin_memory slot n s r hr

theorem guess_ΦI (slot q : Nat) (p : BPair.FtsCoord × Digest) : SuperProg (implG slot) (ΦI q) (BPair.guessReq p) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Bool) slot (.inl p) s r hr

theorem disclose_ΦI (slot q : Nat) (f : BPair.FtsCoord) : SuperProg (implG slot) (ΦI q) (BPair.discloseReq f) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Digest) slot (.inr f) s r hr

theorem mapM_ΦI {α β : Type} (slot q : Nat) (f : α → OracleComp BPair.WSpecL β)
    (hf : ∀ a, SuperProg (implG slot) (ΦI q) (f a)) :
    ∀ l : List α, SuperProg (implG slot) (ΦI q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ (mapM_ΦI slot q f hf l) fun _ => superProg_pure _ _ _

theorem finishL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : BPair.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    SuperProg (implG slot) (ΦI q) (BPair.finishL hU ω request rho found) := by
  rcases found with _ | ⟨c, output⟩
  · exact superProg_pure _ _ _
  · simp only [BPair.finishL]
    generalize BPair.signerForest hU ω output = sf
    generalize BPair.signerLayers hU ω request output = g
    cases g with
    | none => exact superProg_pure _ _ _
    | some pieces =>
        refine superProg_bind _ _ (mapM_ΦI slot q _ (disclose_ΦI slot q) _) ?_
        intro values
        exact superProg_pure _ _ _

/-! ## Public queries -/

theorem ev_uniform_digest (g : Digest → ENNReal) :
    expectedValue (PMF.uniformOfFintype Digest) g = expectedValue ($ᵗ Digest : ProbComp Digest) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]

theorem ev_single_aux (slot : Nat) (i : BPair.AuxL) (s : GState) (G : BPair.AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (BPair.WSpecL.query (.inl i))) s) G =
      expectedValue (BPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) })) := by
  have h := ev_aux_bind slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]

/-- **A digest-row read by the adversary/verifier** keeps the invariant and is a supermartingale step. -/
theorem birth_ΦI (slot q : Nat) (x : HashInput) : SuperProg (implG slot) (ΦI q) (BPair.birthReq x) := by
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold BPair.birthReq
  rw [ev_single_aux]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq]
        have hpt : ∀ a : HashOutput, ΦI q { s with memory := (s.memory.1.readRow x a true,
            ghostStep s.memory.1 (.birth x) a s.memory.2) } =
            nearMemPotential q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : InvM (s.memory.1.readRow x a true, ghostStep s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact mem_birth q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl

/-- **Every public query.** -/
theorem hashL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : BPair.Omega U)
    (x : HashInput) : SuperProg (implG slot) (ΦI q) (BPair.hashL hU ω x) := by
  unfold BPair.hashL
  cases BPair.decodeProbe x with
  | some p => exact superProg_bind _ _ (guess_ΦI slot q p) fun _ => superProg_pure _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_ΦI slot q x
      · exact superProg_pure _ _ _

end SigGolfCandidate.T3.Security.CaseC
