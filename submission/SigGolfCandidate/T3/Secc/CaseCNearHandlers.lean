import SigGolfCandidate.T3.Secc.CaseCNearWorld

/-!
# Stream CC: the near potential under the lazy forced world's handlers (coin and public-hash queries)

`worldPot q expo flag s` is the memory near potential of a lazy-world state (targets = births, rows, nonces; the
fresh exposures and the reuse flag are read off the memory by `expo` / `flag`, which public-row reads leave alone).
Under `forcedImpl envL slot`:

* `coin_super`: an adversary coin leaves the memory unchanged;
* `guess_super`: a probe (secret trial) leaves the memory unchanged;
* `birth_super`: a digest-row read by the adversary/verifier is replayed if cached and otherwise uniform, cached
  and appended to the births (`mem_birth`);
* `hashL_super`: every public query of the adversary/verifier.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **The near potential of a lazy-world state.** -/
noncomputable def worldPot (q : Nat) (expo : BPair.LazyMem → List HashOutput) (flag : BPair.LazyMem → Bool)
    (s : BPair.WStateL) : ENNReal :=
  nearMemPotential q s.memory.births (expo s.memory) (flag s.memory) s.memory.rows s.memory.nonces

theorem expectedValue_liftM_pmf {α : Type} (p : PMF α) (g : α → ENNReal) :
    expectedValue (liftM p : SPMF α) g = expectedValue p g := by
  unfold expectedValue
  simp [SPMF.probOutput_eq_apply, PMF.probOutput_eq_apply]

theorem expectedValue_uniformOfFintype {α : Type} [Fintype α] [Nonempty α] (g : α → ENNReal) :
    expectedValue (PMF.uniformOfFintype α) g = BPORS.finiteAverage g := by
  unfold expectedValue BPORS.finiteAverage
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem runWith_aux (slot : Nat) (i : BPair.AuxL) (s : BPair.WStateL) :
    SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl BPair.envL slot)
        (liftM (BPair.WSpecL.query (.inl i))) s =
      (fun result => (result.1, { s with memory := result.2 })) <$> (liftM (BPair.envL.auxiliary s i) : SPMF _) := by
  simp only [SecretGuessObservation.runWith, simulateQ_spec_query]
  rfl

theorem expectedValue_aux (slot : Nat) (i : BPair.AuxL) (s : BPair.WStateL) (Φ : BPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl BPair.envL slot)
        (liftM (BPair.WSpecL.query (.inl i))) s) (fun r => Φ r.2) =
      expectedValue (BPair.envL.auxiliary s i) (fun result => Φ { s with memory := result.2 }) := by
  rw [runWith_aux, expectedValue_map, expectedValue_liftM_pmf]

section Handlers
variable (slot q : Nat) (expo : BPair.LazyMem → List HashOutput) (flag : BPair.LazyMem → Bool)

/-- An adversary coin leaves the memory unchanged. -/
theorem coin_super (n : Nat) :
    SuperProg (SecretGuessObservation.forcedImpl BPair.envL slot) (worldPot q expo flag) (BPair.coinReqL n) := by
  intro s
  unfold BPair.coinReqL
  refine (le_of_eq (expectedValue_aux slot (.coin n) s _)).trans ?_
  change expectedValue ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) _ ≤ _
  rw [expectedValue_map]
  exact expectedValue_le_of_le _ fun _ => le_rfl

/-- A probe leaves the memory unchanged (the lazy environment's trial keeps it). -/
theorem guess_super (p : BPair.FtsCoord × Digest) :
    SuperProg (SecretGuessObservation.forcedImpl BPair.envL slot) (worldPot q expo flag) (BPair.guessReq p) := by
  intro s
  unfold BPair.guessReq
  simp only [SecretGuessObservation.runWith, simulateQ_spec_query]
  change expectedValue ((fun hit => (hit, SecretGuessObservation.afterTrial BPair.envL s p.1 p.2 hit)) <$>
    SecretGuessObservation.forcedTrial slot s p.1 p.2) _ ≤ _
  rw [expectedValue_map]
  exact expectedValue_le_of_le _ fun _ => le_rfl

/-- **A digest-row read by the adversary/verifier.** -/
theorem birth_super (hexpo : ∀ mem x a, expo (mem.readRow x a true) = expo mem)
    (hflag : ∀ mem x a, flag (mem.readRow x a true) = flag mem) (x : HashInput) :
    SuperProg (SecretGuessObservation.forcedImpl BPair.envL slot) (worldPot q expo flag) (BPair.birthReq x) := by
  intro s
  unfold BPair.birthReq
  refine (le_of_eq (expectedValue_aux slot (.birth x) s _)).trans ?_
  change expectedValue (BPair.rowStep s.memory x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, expectedValue_uniformOfFintype,
          ← BPORS.expected_uniform_eq_finiteAverage]
        unfold worldPot
        simp only [hexpo, hflag]
        simp only [BPair.LazyMem.readRow, if_true]
        exact mem_birth q s.memory.births (expo s.memory) (flag s.memory) s.memory.rows s.memory.nonces x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl

/-- **Every public query of the adversary/verifier.** -/
theorem hashL_super {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (hexpo : ∀ mem x a, expo (mem.readRow x a true) = expo mem)
    (hflag : ∀ mem x a, flag (mem.readRow x a true) = flag mem) (x : HashInput) :
    SuperProg (SecretGuessObservation.forcedImpl BPair.envL slot) (worldPot q expo flag) (BPair.hashL hU ω x) := by
  unfold BPair.hashL
  cases BPair.decodeProbe x with
  | some p =>
      exact superProg_bind _ _ (guess_super slot q expo flag p) fun _ => superProg_pure _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_super slot q expo flag hexpo hflag x
      · exact superProg_pure _ _ _

end Handlers

end SigGolfCandidate.T3.Security.CaseC
