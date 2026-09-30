import SigGolfCandidate.SphincsSecurity.Completeness.Counter
import SigGolfCandidate.SphincsSecurity.Completeness.Decay
import SigGolfCandidate.Ref.CounterPack

/-!
# Counter-cap failure before compact serialization

The search still runs with its existing trial budget. A cap rejects a returned
counter only when every trial before that cap failed. This file proves that
prefix bound directly against the lazy random oracle, including exhaustion.
-/

open OracleComp OracleSpec ENNReal Finset

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

variable {β γ : Type}

/-- The first `k` trials bound exhaustion or a result excluded by a later cap.
The remaining trials may still execute, so their probability is bounded by one. -/
theorem probEvent_searchLoop_prefix
    (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → γ) (bad : γ → Prop) (cap bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s')
    (hgood : ∀ t, t < cap → ∀ v, ¬ bad (success t v)) :
    ∀ (k n t : Nat), k ≤ n → t + k = cap → t + n ≤ bound →
      ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr[fun r => r.1.elim True bad |
          (simulateQ randomOracle
            (searchLoop inputs decode (fun c v => pure (success c v)) n t)).run cache]
        ≤ failMass decode ^ k := by
  intro k
  induction k with
  | zero =>
      intro n t _ _ _ cache _
      simpa using (probEvent_le_one (p := fun r => r.1.elim True bad)
        (oa := (simulateQ randomOracle
          (searchLoop inputs decode (fun c v => pure (success c v)) n t)).run cache))
  | succ k ih =>
      intro n t hkn hcap hbound cache hfresh
      cases n with
      | zero => omega
      | succ n =>
          rw [searchLoop]
          simp only [Concrete.oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind]
          rw [fresh_run (inputs t) cache (hfresh t (Nat.le_refl t) (by omega))]
          have hterm : ∀ u : HashOutput,
              Pr[fun r => r.1.elim True bad | (simulateQ randomOracle
                (match decode u with
                 | some v => some <$> pure (success t v)
                 | none => searchLoop inputs decode (fun c v => pure (success c v)) n (t + 1))).run
                  (cache.cacheQuery (inputs t) u)]
                ≤ (if decode u = none then failMass decode ^ k else 0) := by
            intro u
            cases hu : decode u with
            | some v =>
                simp [hgood t (by omega) v]
            | none =>
                simp only [if_true]
                refine ih n (t + 1) (by omega) (by omega) (by omega) _ (fun s hs hsb => ?_)
                have hne : inputs s ≠ inputs t := fun hcon => by
                  have hst := hinj s t hsb (by omega) hcon
                  omega
                exact (QueryCache.cacheQuery_of_ne cache u hne).trans
                  (hfresh s (Nat.le_of_succ_le hs) hsb)
          refine le_trans (ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hterm u) _)) ?_
          rw [tsum_fintype, Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero]),
            Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            pow_succ', failMass, div_eq_mul_inv, ← mul_assoc]

/-- Capping an already completed long counter search charges only its initial trials. -/
theorem probEvent_encodingSearch_cap (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (cap : Nat)
    (hcap : cap ≤ encodingAttemptLimit) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr[fun r => r.1.elim True (fun v => cap ≤ v.1.toNat) |
      (simulateQ randomOracle
        (Concrete.encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
          : OracleComp HashSpec (Option (Counter × Encoding)))).run cache]
      ≤ failMass (fun out => TargetSum.decodeDigest lay (truncateHash out)) ^ cap := by
  have hwrap : encodingAttemptLimit ≤ 2 ^ 32 := by rw [encodingAttemptLimit]; norm_num
  rw [encodingSearch_eq_searchLoop]
  apply probEvent_searchLoop_prefix _ _ _ _ cap encodingAttemptLimit
    (fun s s' hs hs' heq => encodeInput_inj parameter lay tree leaf message
      (by omega) (by omega) heq) ?_ cap encodingAttemptLimit 0 hcap (by omega) (by omega)
    cache (fun s _ hs => hfresh s hs)
  intro t ht word
  change ¬ cap ≤ (BitVec.ofNat counterBits t).toNat
  rw [BitVec.toNat_ofNat, counterBits, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Injecting valid words into accepted digests preserves their count. -/
theorem codeCount_le_card_accepting (lay : Layer) :
    codeCount (targetFor lay) ≤
      (Finset.univ.filter fun d : Digest => (TargetSum.decodeDigest lay d).isSome).card := by
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : TargetSum.Valid lay x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left hleft right hright heq
    have hl : TargetSum.Valid lay left := (Finset.mem_filter.mp hleft).2
    have hr : TargetSum.Valid lay right := (Finset.mem_filter.mp hright).2
    have := decodeDigest_pack left hl
    rw [heq, decodeDigest_pack right hr] at this
    exact (Option.some.inj this).symm

set_option maxRecDepth 100000 in
/-- The four target181 layers admit at least one in2046 digests. -/
theorem digests_le_2046_mul_codeCount (lay : Layer) (hlay : lay.val < 4) :
    2 ^ 128 ≤ 2046 * codeCount (targetFor lay) := by
  rw [codeCount_target, weight_eq]
  have h : ¬ 4 ≤ lay.val := by omega
  simp only [targetFor, targetSum, h, if_false, Nat.add_zero]
  decide

theorem failMass_encoding_add_le_share (lay : Layer) (shareSize : Nat)
    (hpos : 0 < shareSize)
    (hcount : 2 ^ 128 ≤ shareSize * codeCount (targetFor lay)) :
    failMass (fun out => TargetSum.decodeDigest lay (truncateHash out)) + (shareSize : ℝ≥0∞)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (TargetSum.decodeDigest lay d).isSome).card = n := ⟨_, rfl⟩
  have hnat : (2 : Nat) ^ 128 ≤ shareSize * accepted :=
    haccepted ▸ hcount.trans (Nat.mul_le_mul_left _ (codeCount_le_card_accepting lay))
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcompl := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (TargetSum.decodeDigest lay (truncateHash u)).isSome)
  have hreject : Pr[fun u : HashOutput => ¬ (TargetSum.decodeDigest lay (truncateHash u)).isSome = true |
      ($ᵗ HashOutput : ProbComp HashOutput)]
      = failMass (fun out => TargetSum.decodeDigest lay (truncateHash out)) := by
    rw [failMass_eq_probEvent]
    apply probEvent_congr'
    · intro u _
      cases TargetSum.decodeDigest lay (truncateHash u) <;> simp
    · rfl
  have hfail : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by simp
  rw [hreject, probEvent_accept, hfail, tsub_zero, hcard, haccepted] at hcompl
  have hshare : (shareSize : ℝ≥0∞)⁻¹ ≤ (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)),
      ENNReal.inv_mul_le_iff (by exact_mod_cast Nat.ne_of_gt hpos) (by simp)]
    exact_mod_cast hnat
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

theorem failMass_encoding_low_room (lay : Layer) (hlay : lay.val < 4) :
    failMass (fun out => TargetSum.decodeDigest lay (truncateHash out)) + (2046 : ℝ≥0∞)⁻¹ ≤ 1 :=
  failMass_encoding_add_le_share lay 2046 (by decide) (digests_le_2046_mul_codeCount lay hlay)

/-- One common envelope suffices for each of the five cap events. -/
noncomputable def capFailureBound : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ 388

open SigGolfCandidate.Ref.CounterPack in
theorem probEvent_encodingSearch_cap_uniform (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr[fun r => r.1.elim True (fun v => counterCap lay.val ≤ v.1.toNat) |
      (simulateQ randomOracle
        (Concrete.encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
          : OracleComp HashSpec (Option (Counter × Encoding)))).run cache]
      ≤ capFailureBound := by
  refine (probEvent_encodingSearch_cap parameter lay tree leaf message (counterCap lay.val)
    (by unfold counterCap; split <;> decide) cache hfresh).trans ?_
  by_cases h : 4 ≤ lay.val
  · rw [counterCap, if_pos h]
    exact (counter_cap_high_pow _ failMass_encoding_add_le).trans (inv_two_pow_anti (by decide))
  · rw [counterCap, if_neg h]
    exact counter_cap_low_pow _ (failMass_encoding_low_room lay (by omega))

/-- The uniform cap envelope, including the digest failure, meets the pinned all-message bound. -/
theorem closing_sum_caps_uniform :
    (2 : ℝ≥0∞) ^ 256 * ((2⁻¹ : ℝ≥0∞) ^ 699 + 5 * capFailureBound)
      ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  have ha : (2⁻¹ : ℝ≥0∞) ^ 699 ≤ (2⁻¹ : ℝ≥0∞) ^ 388 := inv_two_pow_anti (by decide)
  have hsum : (2⁻¹ : ℝ≥0∞) ^ 699 + 5 * capFailureBound ≤ (2⁻¹ : ℝ≥0∞) ^ 384 := by
    have h1 := inv_two_pow_succ_add 387
    have h2 := inv_two_pow_succ_add 386
    have h3 := inv_two_pow_succ_add 385
    calc _ ≤ 6 * (2⁻¹ : ℝ≥0∞) ^ 388 := by
            unfold capFailureBound
            calc _ ≤ (2⁻¹ : ℝ≥0∞) ^ 388 + 5 * (2⁻¹ : ℝ≥0∞) ^ 388 := add_le_add ha le_rfl
                 _ = _ := by ring
         _ ≤ 8 * (2⁻¹ : ℝ≥0∞) ^ 388 := mul_le_mul' (by norm_num) le_rfl
         _ = (2⁻¹ : ℝ≥0∞) ^ 385 := by
           calc _ = (((2⁻¹ : ℝ≥0∞) ^ 388 + (2⁻¹ : ℝ≥0∞) ^ 388)
                     + ((2⁻¹ : ℝ≥0∞) ^ 388 + (2⁻¹ : ℝ≥0∞) ^ 388))
                    + (((2⁻¹ : ℝ≥0∞) ^ 388 + (2⁻¹ : ℝ≥0∞) ^ 388)
                     + ((2⁻¹ : ℝ≥0∞) ^ 388 + (2⁻¹ : ℝ≥0∞) ^ 388)) := by ring
                _ = _ := by rw [h1, h2, h3]
         _ ≤ _ := inv_two_pow_anti (by decide)
  rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  calc _ ≤ (2 : ℝ≥0∞) ^ 256 * (2⁻¹ : ℝ≥0∞) ^ 384 := mul_le_mul_right hsum _
       _ = _ := by
         rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
           show (384 : Nat) = 256 + 128 by norm_num, two_pow_div_two_pow]

end SphincsSecurity.Completeness
