import SigGolfCandidate.SphincsSecurity.Completeness.Digest
import SigGolfCandidate.SphincsSecurity.Completeness.Decay

set_option maxRecDepth 4096

open OracleComp OracleSpec ENNReal Finset
namespace SphincsSecurity.Completeness

/-- A pair is bad if either digest was queried already, or the two halves agree. -/
def PairBad (R : Finset Randomness) (u : HashOutput) : Prop :=
  (Seeded.splitSecrets u).1 ∈ R ∨ (Seeded.splitSecrets u).2 ∈ R ∨
    (Seeded.splitSecrets u).2 = (Seeded.splitSecrets u).1

instance (R : Finset Randomness) : DecidablePred (PairBad R) := fun u => by
  unfold PairBad
  infer_instance

private theorem high_mem_card {n w : Nat} (hw : w ≤ n) (R : Finset (BitVec (n - w))) :
    (univ.filter fun u : BitVec n => u.extractLsb' w (n - w) ∈ R).card =
      2 ^ w * R.card := by
  rw [card_filter_high hw (fun d => d ∈ R), Finset.filter_univ_mem]

private theorem high_mem (R : Finset Randomness) :
    Pr[fun u : HashOutput => (Seeded.splitSecrets u).2 ∈ R |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (R.card : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniform]
  have hc : (univ.filter fun u : HashOutput => (Seeded.splitSecrets u).2 ∈ R).card =
      2 ^ 128 * R.card := high_mem_card (n := 256) (w := 128) (by decide) R
  rw [hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) ^ hashOutputBits = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]; rfl,
    mul_comm ((2 : ℝ≥0∞) ^ 128) (R.card : ℝ≥0∞),
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

private theorem diagonal_card (α : Type) [Fintype α] [DecidableEq α] :
    (univ.filter fun p : α × α => p.2 = p.1).card = Fintype.card α := by
  symm
  change (univ : Finset α).card = _
  refine Finset.card_bij (fun r _ => (r, r)) (by intro r hr; simp) ?_ ?_
  · intro r _ s _ he
    exact congrArg Prod.fst he
  · intro p hp
    have he : p.2 = p.1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl he.symm⟩

private theorem halves_eq :
    Pr[fun u : HashOutput => (Seeded.splitSecrets u).2 = (Seeded.splitSecrets u).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (1 : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniform]
  have hc := card_filter_splitBits (n := 256) (w := 128) (by decide)
    (fun p => p.2 = p.1)
  simp only [diagonal_card, Fintype.card_bitVec] at hc
  have hc' : (univ.filter fun u : HashOutput =>
      (Seeded.splitSecrets u).2 = (Seeded.splitSecrets u).1).card = 2 ^ 128 := hc
  rw [hc',
    Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) ^ hashOutputBits = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]; rfl]
  simpa using ENNReal.mul_div_mul_right (1 : ℝ≥0∞) (2 ^ 128)
    (by simp : (2 : ℝ≥0∞) ^ 128 ≠ 0) (by simp : (2 : ℝ≥0∞) ^ 128 ≠ ⊤)

/-- Conservative bound valid for the whole cached answer, without conditional independence. -/
theorem probEvent_pairBad (R : Finset Randomness) (hcard : R.card < 2 ^ 21) :
    Pr[PairBad R | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (2 : ℝ≥0∞) ^ 22 / 2 ^ 128 := by
  have hlo := probEvent_truncateHash_mem R
  have hhi := high_mem R
  have heq := halves_eq
  have ho := probEvent_or_le ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (Seeded.splitSecrets u).1 ∈ R)
    (fun u => (Seeded.splitSecrets u).2 ∈ R ∨ (Seeded.splitSecrets u).2 = (Seeded.splitSecrets u).1)
  have hi := probEvent_or_le ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (Seeded.splitSecrets u).2 ∈ R)
    (fun u => (Seeded.splitSecrets u).2 = (Seeded.splitSecrets u).1)
  change Pr[PairBad R | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ _ at ho
  change Pr[fun u : HashOutput => (Seeded.splitSecrets u).1 ∈ R |
    ($ᵗ HashOutput : ProbComp HashOutput)] = (R.card : ℝ≥0∞) / 2 ^ 128 at hlo
  refine ho.trans ((add_le_add le_rfl hi).trans ?_)
  rw [hlo, hhi, heq]
  calc (R.card : ℝ≥0∞) / 2 ^ 128 + ((R.card : ℝ≥0∞) / 2 ^ 128 + 1 / 2 ^ 128)
      = ((2 * R.card + 1 : Nat) : ℝ≥0∞) / 2 ^ 128 := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
        ring
    _ ≤ ((2 ^ 22 : Nat) : ℝ≥0∞) / 2 ^ 128 := by
      gcongr
      omega
    _ = _ := by rw [Nat.cast_pow, Nat.cast_ofNat]

end SphincsSecurity.Completeness

namespace SphincsSecurity.Completeness

/-- A 1250-pair block halves failure even if only both halves are counted. -/
theorem pow_le_half_1706_1250 (x : ENNReal)
    (hx : x + (1706 : ENNReal)⁻¹ ≤ 1) : x ^ 1250 ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (1705 : ℝ) / 1706 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  have hrat : ((1705 : ℝ) / 1706) ^ 1250 ≤ 1 / 2 := by
    have hnat : 100 * (1705 : Nat) ^ 125 ≤ 93 * (1706 : Nat) ^ 125 := by decide
    have hreal : (100 : ℝ) * (1705 : ℝ) ^ 125 ≤ 93 * (1706 : ℝ) ^ 125 := by
      exact_mod_cast hnat
    have hblock : ((1705 : ℝ) / 1706) ^ 125 ≤ 93 / 100 := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    calc
      _ = (((1705 : ℝ) / 1706) ^ 125) ^ 10 := by rw [← pow_mul]
      _ ≤ ((93 : ℝ) / 100) ^ 10 := pow_le_pow_left₀ (by positivity) hblock 10
      _ ≤ 1 / 2 := by norm_num
  have hpow : x.toReal ^ 1250 ≤ 1 / 2 :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 1250).trans hrat
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc
    ENNReal.ofReal (x.toReal ^ 1250) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hpow
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

theorem paired_digest_room (x : ENNReal) (hx : x + (3410 : ENNReal)⁻¹ ≤ 1) :
    x ^ 2 + (2 : ENNReal) ^ 22 / (2 : ENNReal) ^ 128 + ((1706 : Nat) : ENNReal)⁻¹ ≤ 1 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (3409 : ℝ) / 3410 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, Nat.cast_ofNat, ENNReal.toReal_one]
  have hpow := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
  norm_num at hpow ⊢
  linarith

/-- The all-message union bound still meets the contractual 128-bit completeness. -/
theorem paired_closing_sum :
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 419 + 5 * (2⁻¹ : ENNReal) ^ 1741)
      ≤ ((2 ^ 128 : Nat) : ENNReal)⁻¹ := by
  have hcast : ((2 ^ 128 : Nat) : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 128 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  have ha : (2⁻¹ : ENNReal) ^ 419 ≤ (2⁻¹ : ENNReal) ^ 385 := inv_two_pow_anti (by norm_num)
  have hb : 5 * (2⁻¹ : ENNReal) ^ 1741 ≤ (2⁻¹ : ENNReal) ^ 385 := by
    have hy : (2⁻¹ : ENNReal) ^ 1741 ≤ (2⁻¹ : ENNReal) ^ 388 := inv_two_pow_anti (by norm_num)
    have h1 := inv_two_pow_succ_add 387
    have h2 := inv_two_pow_succ_add 386
    have h3 := inv_two_pow_succ_add 385
    calc 5 * (2⁻¹ : ENNReal) ^ 1741 ≤ 8 * (2⁻¹ : ENNReal) ^ 388 := mul_le_mul' (by norm_num) hy
      _ = (((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)
            + ((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388))
          + (((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)
            + ((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)) := by ring
      _ = (2⁻¹ : ENNReal) ^ 385 := by rw [h1, h2, h3]
  have hsum : (2⁻¹ : ENNReal) ^ 419 + 5 * (2⁻¹ : ENNReal) ^ 1741 ≤ (2⁻¹ : ENNReal) ^ 384 :=
    (add_le_add ha hb).trans_eq (inv_two_pow_succ_add 384)
  rw [hcast]
  calc
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 419 + 5 * (2⁻¹ : ENNReal) ^ 1741)
        ≤ (2 : ENNReal) ^ 256 * (2⁻¹ : ENNReal) ^ 384 := mul_le_mul_right hsum _
    _ = (2⁻¹ : ENNReal) ^ 128 := by
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (384 : Nat) = 256 + 128 by norm_num, two_pow_div_two_pow]

end SphincsSecurity.Completeness

/-! Both halves must reject. Collision pairs are charged separately before any digest is queried. -/

open OracleComp OracleSpec ENNReal Finset
namespace SphincsSecurity.Completeness
open Concrete

noncomputable def pairedDigestFactor : ℝ≥0∞ :=
  digestReject ^ 2 + (2 : ℝ≥0∞) ^ 22 / (2 : ℝ≥0∞) ^ 128

private theorem uniform_constant (b : ℝ≥0∞) :
    ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * b = b := by
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc]
  simp only [HashOutput, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- Querying a digest changes no other digest input and no randomizer input. -/
private theorem digest_cache (sk : Seeded.SecretKey) (message : Message)
    (c : QueryCache HashSpec) (R : Finset Randomness) (rho : Randomness) (v : HashOutput)
    (t : Nat)
    (hrand : ∀ s, t ≤ s → s < 2 ^ 20 → c (randInput sk message s) = none)
    (hmsg : ∀ r, r ∉ R → c (msgInput sk message r) = none) :
    (∀ s, t ≤ s → s < 2 ^ 20 →
      (c.cacheQuery (msgInput sk message rho) v) (randInput sk message s) = none) ∧
    (∀ r, r ∉ insert rho R →
      (c.cacheQuery (msgInput sk message rho) v) (msgInput sk message r) = none) := by
  constructor
  · intro s hs hsb
    exact (QueryCache.cacheQuery_of_ne c v (randInput_ne_msgInput sk message s rho)).trans
      (hrand s hs hsb)
  · intro r hr
    rw [Finset.mem_insert, not_or] at hr
    exact (QueryCache.cacheQuery_of_ne c v
      (fun h => hr.1 (msgInput_inj sk message h))).trans (hmsg r hr.2)

set_option maxHeartbeats 1500000 in
/-- Exhausting pairs requires rejecting both fresh halves, except on a collision pair. -/
theorem probEvent_signDigestPairs (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n t : Nat) (cache : QueryCache HashSpec) (R : Finset Randomness),
      t + n ≤ 2 ^ 20 → R.card ≤ 2 * t →
      (∀ s, t ≤ s → s < 2 ^ 20 → cache (randInput sk message s) = none) →
      (∀ r, r ∉ R → cache (msgInput sk message r) = none) →
      Pr[fun r => r.1 = none | (simulateQ randomOracle
        (Seeded.signDigestPairs sk message n t
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))).run cache]
        ≤ pairedDigestFactor ^ n := by
  intro n
  induction n with
  | zero => intro t cache R _ _ _ _; simp [Seeded.signDigestPairs]
  | succ n ih =>
    intro t cache R hbound hcard hrand hmsg
    have htail : ∀ (c : QueryCache HashSpec) (R' : Finset Randomness) (rho : Randomness),
        R'.card ≤ 2 * t + 1 →
        (∀ s, t + 1 ≤ s → s < 2 ^ 20 → c (randInput sk message s) = none) →
        (∀ r, r ∉ R' → c (msgInput sk message r) = none) →
        Pr[fun r => r.1 = none | (simulateQ randomOracle (do
          let result ← Seeded.signAttempt sk message rho
          match result with
          | some (index, leaves) => pure (some (rho, index, leaves))
          | none => Seeded.signDigestPairs sk message n (t + 1)
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))).run c]
          ≤ pairedDigestFactor ^ n := by
      intro c R' rho hcard' hrand' hmsg'
      simp only [Seeded.signAttempt, messageDigest, oracleHash, HasQuery.query,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc, pure_bind]
      cases hmc : c (msgInput sk message rho) with
      | some v =>
        rw [cached_run _ _ v hmc, pure_bind]
        by_cases hadm : Admissible (truncateMessageDigest v)
        · simp [hadm]
        · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih (t + 1) c R' (by omega) (by omega) hrand' hmsg'
      | none =>
        rw [fresh_run _ _ hmc]
        refine (ENNReal.tsum_le_tsum (g := fun _ : HashOutput =>
          (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * pairedDigestFactor ^ n)
          fun v => mul_le_mul_right ?_ _).trans_eq (uniform_constant _)
        dsimp only
        by_cases hadm : Admissible (truncateMessageDigest v)
        · simp [hadm]
        · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
          have hc := digest_cache sk message c R' rho v (t + 1) hrand' hmsg'
          exact ih (t + 1) _ (insert rho R') (by omega)
            ((Finset.card_insert_le _ _).trans (by omega)) hc.1 hc.2
    have htailFresh : ∀ (c : QueryCache HashSpec) (R' : Finset Randomness) (rho : Randomness),
        R'.card ≤ 2 * t + 1 →
        (∀ s, t + 1 ≤ s → s < 2 ^ 20 → c (randInput sk message s) = none) →
        (∀ r, r ∉ R' → c (msgInput sk message r) = none) → rho ∉ R' →
        Pr[fun r => r.1 = none | (simulateQ randomOracle (do
          let result ← Seeded.signAttempt sk message rho
          match result with
          | some (index, leaves) => pure (some (rho, index, leaves))
          | none => Seeded.signDigestPairs sk message n (t + 1)
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))).run c]
          ≤ digestReject * pairedDigestFactor ^ n := by
      intro c R' rho hcard' hrand' hmsg' hnew
      simp only [Seeded.signAttempt, messageDigest, oracleHash, HasQuery.query,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc, pure_bind]
      rw [fresh_run _ _ (hmsg' rho hnew)]
      refine (ENNReal.tsum_le_tsum (g := fun v : HashOutput =>
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
          (if Admissible (truncateMessageDigest v) then 0 else pairedDigestFactor ^ n))
        fun v => mul_le_mul_right ?_ _).trans ?_
      · dsimp only
        by_cases hadm : Admissible (truncateMessageDigest v)
        · simp [hadm]
        · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
          have hc := digest_cache sk message c R' rho v (t + 1) hrand' hmsg'
          exact ih (t + 1) _ (insert rho R') (by omega)
            ((Finset.card_insert_le _ _).trans (by omega)) hc.1 hc.2
      · rw [tsum_uniform_ite]
        simp only [zero_mul, zero_add]
        change pairedDigestFactor ^ n * digestReject ≤ _
        rw [mul_comm]
    rw [Seeded.signDigestPairs]
    simp only [Seeded.deriveRandomizerPair, Seeded.splitSecrets, Seeded.signAttempt, messageDigest, oracleHash, HasQuery.query,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc, pure_bind]
    rw [fresh_run _ cache (hrand t le_rfl (by omega))]
    refine (ENNReal.tsum_le_tsum (g := fun u => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
      (if PairBad R u then pairedDigestFactor ^ n
       else digestReject ^ 2 * pairedDigestFactor ^ n))
      fun u => mul_le_mul_right ?_ _).trans ?_
    · dsimp only
      have hwrap : (2 : Nat) ^ 20 ≤ 2 ^ 32 := by norm_num
      have hc1rand : ∀ s, t + 1 ≤ s → s < 2 ^ 20 →
          (cache.cacheQuery (randInput sk message t) u) (randInput sk message s) = none := by
        intro s hs hsb
        exact (QueryCache.cacheQuery_of_ne cache u (fun h => by
          have := randInput_inj sk message (by omega) (by omega) h
          omega)).trans (hrand s (by omega) hsb)
      have hc1msg : ∀ r, (cache.cacheQuery (randInput sk message t) u)
          (msgInput sk message r) = cache (msgInput sk message r) := fun r =>
        QueryCache.cacheQuery_of_ne cache u (fun h => randInput_ne_msgInput sk message t r h.symm)
      cases hmc : (cache.cacheQuery (randInput sk message t) u)
          (msgInput sk message (truncateHash u)) with
      | some v =>
        have hmem : truncateHash u ∈ R := by
          by_contra hnot
          have hnone := hmsg _ hnot
          rw [← hc1msg, hmc] at hnone
          simp at hnone
        have hbad : PairBad R u := Or.inl hmem
        rw [if_pos hbad, cached_run _ _ v hmc, pure_bind]
        by_cases hadm : Admissible (truncateMessageDigest v)
        · simp [hadm]
        · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
          exact htail _ R _ (by omega) hc1rand (fun r hr => (hc1msg r).trans (hmsg r hr))
      | none =>
        rw [fresh_run _ _ hmc]
        refine (ENNReal.tsum_le_tsum (g := fun v => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
          (if Admissible (truncateMessageDigest v) then 0 else
            if PairBad R u then pairedDigestFactor ^ n else digestReject * pairedDigestFactor ^ n))
          fun v => mul_le_mul_right ?_ _).trans ?_
        · dsimp only
          by_cases hadm : Admissible (truncateMessageDigest v)
          · simp [hadm]
          · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
            have hc := digest_cache sk message _ R (truncateHash u) v (t + 1) hc1rand
              (fun r hr => (hc1msg r).trans (hmsg r hr))
            by_cases hbad : PairBad R u
            · rw [if_pos hbad]
              exact htail _ (insert (truncateHash u) R) _
                ((Finset.card_insert_le _ _).trans (by omega)) hc.1 hc.2
            · rw [if_neg hbad]
              apply htailFresh _ (insert (truncateHash u) R) _
                ((Finset.card_insert_le _ _).trans (by omega)) hc.1 hc.2
              simpa only [PairBad, Seeded.splitSecrets, Finset.mem_insert, not_or] using
                (show (Seeded.splitSecrets u).2 ≠ (Seeded.splitSecrets u).1 ∧
                  (Seeded.splitSecrets u).2 ∉ R from
                    ⟨fun h => hbad (Or.inr (Or.inr h)), fun h => hbad (Or.inr (Or.inl h))⟩)
        · rw [tsum_uniform_ite]
          simp only [zero_mul, zero_add]
          change (if PairBad R u then pairedDigestFactor ^ n else
            digestReject * pairedDigestFactor ^ n) * digestReject ≤ _
          by_cases hbad : PairBad R u
          · simp only [if_pos hbad]
            exact mul_le_of_le_one_right' digestReject_le_one
          · simp only [if_neg hbad]
            exact le_of_eq (by ring)
    · rw [tsum_uniform_ite]
      have hcoll := probEvent_pairBad R (by omega)
      calc pairedDigestFactor ^ n * Pr[PairBad R | ($ᵗ HashOutput : ProbComp HashOutput)] +
            digestReject ^ 2 * pairedDigestFactor ^ n *
              Pr[fun u => ¬ PairBad R u | ($ᵗ HashOutput : ProbComp HashOutput)]
          ≤ pairedDigestFactor ^ n * ((2 : ℝ≥0∞) ^ 22 / (2 : ℝ≥0∞) ^ 128) +
            digestReject ^ 2 * pairedDigestFactor ^ n * 1 :=
            add_le_add (mul_le_mul_right hcoll _) (mul_le_mul_right probEvent_le_one _)
        _ = pairedDigestFactor ^ (n + 1) := by rw [pow_succ, pairedDigestFactor]; ring

end SphincsSecurity.Completeness
