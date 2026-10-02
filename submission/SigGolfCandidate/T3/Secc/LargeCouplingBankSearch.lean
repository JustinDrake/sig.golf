import SigGolfCandidate.T3.Secc.LargeCouplingBankStep

/-!
# LR-34 (bank, signer search): the lazy router's digest search is SEC's `roRun` search

**`bank_search`**: if the lazy world's rows agree with a random-oracle cache on the trial rows of `(rho, m)`, the
router's digest search (`simulateQ (readImpl U a) (digestSearch …)`, uncharged residual reads) and SEC's
`Sampling.roRun secret (digestSearch …) cache` (CC's `core_sign` search) have the same law of the selected output,
and the lazy search changes only the trial rows it read (`SearchFrame`: counters `c ≤ k ≤` the selected counter).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)

/-- What the lazy search from counter `c` with fuel `fuel` and result `found` keeps. -/
def SearchFrame (c fuel : Nat) (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  s'.candidates = s.candidates ∧ s'.counters = s.counters ∧
    (∀ k' out, found = some (k', out) → c ≤ k'.toNat ∧ k'.toNat < c + fuel) ∧
    ∀ row : Cell U, s'.rows row ≠ s.rows row → ∃ k, c ≤ k ∧ k < c + fuel ∧
      row.1 = pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∧ ∀ k' out, found = some (k', out) → k ≤ k'.toNat

theorem trial_ne {k c : Nat} (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) (hne : k ≠ c) :
    pad64 (digestInput rho m (BitVec.ofNat 32 k)) ≠ pad64 (digestInput rho m (BitVec.ofNat 32 c)) := by
  intro h
  obtain ⟨-, h2, -⟩ := BPB.digestInput_injective h
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hc] at this
  exact hne this

theorem readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) :
    simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) =
      readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
  change simulateQ (readImpl U a) (liftM (Spec.query (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))))) = _
  rw [simulateQ_spec_query]
  simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]

theorem lazy_readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) {β : Type}
    (k : HashOutput → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) >>= k) s =
      (reply s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ >>= fun y =>
        lazyRun aux q (k y) (readState q s ⟨_, hU (BitVec.ofNat 32 c)⟩ y .none)) := by
  rw [readImpl_digest]
  exact lazy_readReq U aux q _ _ k s

theorem reply_of_some {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} {u : LargeResidual.HashOutput}
    (h : rows row = some u) : reply rows row = pure u := by
  unfold reply; rw [h]

theorem reply_of_none {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} (h : rows row = none) :
    reply rows row = liftM (PMF.uniformOfFintype LargeResidual.HashOutput) := by
  unfold reply; rw [h]

theorem expectedValue_uniform_ro (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]

/-- **The lazy search is the random-oracle search** (in expectation, with the search frame). -/
theorem bank_search (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (secret : BitVec 256) :
    ∀ (fuel c : Nat), c + fuel ≤ 2 ^ 32 → ∀ (s : LargeResidual.State WCoord (Cell U)) (cache : Sampling.RCache),
      (∀ k, c ≤ k → k < 2 ^ 32 →
        s.rows ⟨_, hU (BitVec.ofNat 32 k)⟩ = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
      ∀ (G : Option (Option (BitVec 32 × LargeResidual.HashOutput)) × LargeResidual.State WCoord (Cell U) → ENNReal)
        (H : Option (BitVec 32 × LargeResidual.HashOutput) → ENNReal),
        (∀ found s', SearchFrame rho m c fuel found s s' → G (some found, s') ≤ H found) →
        expectedValue (lazyRun aux q (simulateQ (readImpl U a) (digestSearch rho m c fuel)) s) G ≤
          expectedValue (Sampling.roRun secret (digestSearch rho m c fuel) cache) (fun r => H r.1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c _ s cache _ G H hG
      simp only [digestSearch, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
      rw [lazy_pure, expectedValue_pure]
      apply hG
      refine ⟨rfl, rfl, fun k' out h => (by cases h), fun row h => absurd rfl h⟩
  | succ fuel ih =>
      intro c hc s cache hagree G H hG
      have hc32 : c < 2 ^ 32 := by omega
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩ with hXdef
      -- the router side
      simp only [BPB.digestSearch_succ, simulateQ_bind, Sampling.roRun_bind]
      rw [lazy_readImpl_digest aux q a rho m hU c]
      -- the random-oracle side
      have hro : Sampling.roRun secret (digest rho m (BitVec.ofNat 32 c)) cache =
          (randomOracle (spec := SphincsSecurity.HashSpec) (pad64 (digestInput rho m (BitVec.ofNat 32 c)))).run cache :=
        Sampling.roRun_publicQuery secret _ cache
      simp only [hro, randomOracle.run_eq]
      have hXc := hagree c le_rfl hc32
      -- after reading the trial row at `c` with answer `y`
      have hstep : ∀ (y : LargeResidual.HashOutput) (cache' : Sampling.RCache),
          (∀ k, c + 1 ≤ k → k < 2 ^ 32 →
            cache' (pad64 (digestInput rho m (BitVec.ofNat 32 k))) =
              cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
          expectedValue (lazyRun aux q (simulateQ (readImpl U a)
              (if admissible (selections y) = true then pure (some (BitVec.ofNat 32 c, y))
                else digestSearch rho m (c + 1) fuel)) (readState q s X y .none)) G ≤
            expectedValue (Sampling.roRun secret
              (if admissible (selections y) = true then pure (some (BitVec.ofNat 32 c, y))
                else digestSearch rho m (c + 1) fuel) cache') (fun r => H r.1) := by
        intro y cache' hcache'
        have hrowsX : ∀ row : Cell U, (readState q s X y .none).rows row ≠ s.rows row → row = X := by
          intro row hr
          by_contra hne
          apply hr
          simp only [readState]
          rw [Function.update_of_ne hne]
        by_cases hadm : admissible (selections y) = true
        · simp only [hadm, if_true, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
          rw [lazy_pure, expectedValue_pure]
          apply hG
          have hcn : (BitVec.ofNat 32 c).toNat = c := by
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32]
          refine ⟨rfl, rfl, fun k' out h => ?_, fun row hr => ?_⟩
          · cases h
            rw [hcn]; omega
          · have hrX := hrowsX row hr
            refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
            cases h
            rw [hcn]
        · simp only [hadm, Bool.false_eq_true, if_false]
          apply ih (c + 1) (by omega) (readState q s X y .none) cache'
          · intro k hk hk32
            have hne : (⟨_, hU (BitVec.ofNat 32 k)⟩ : Cell U) ≠ X := by
              intro he
              exact trial_ne rho m hk32 hc32 (by omega) (congrArg Subtype.val he)
            simp only [readState]
            rw [Function.update_of_ne hne, hcache' k hk hk32]
            exact hagree k (by omega) hk32
          · intro found s' hf
            apply hG
            obtain ⟨h1, h2, h3, h4⟩ := hf
            refine ⟨h1, h2, fun k' out h => ?_, fun row hr => ?_⟩
            · have := h3 k' out h; omega
            · by_cases hr1 : s'.rows row ≠ (readState q s X y .none).rows row
              · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h4 row hr1
                exact ⟨k, by omega, by omega, hk3, hk4⟩
              · push Not at hr1
                have hrX := hrowsX row (by rw [← hr1]; exact hr)
                refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
                have := (h3 k' out h).1; omega
      cases hcache : cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) with
      | some u =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = some u := hXc.trans hcache
          rw [reply_of_some hsX, pure_bind, pure_bind]
          exact hstep u cache (fun _ _ _ => rfl)
      | none =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = none := hXc.trans hcache
          rw [reply_of_none hsX, expectedValue_bind, bind_assoc, expectedValue_bind, expectedValue_uniform_ro]
          apply expectedValue_mono
          intro y
          rw [pure_bind]
          dsimp only
          have hc' : ∀ k, c + 1 ≤ k → k < 2 ^ 32 →
              (QueryCache.cacheQuery cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) y)
                (pad64 (digestInput rho m (BitVec.ofNat 32 k))) = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := by
            intro k hk hk32
            exact QueryCache.cacheQuery_of_ne _ _ (trial_ne rho m hk32 hc32 (by omega))
          exact hstep y _ hc'

end Search

end SigGolfCandidate.T3.Security.LargeCoupling
