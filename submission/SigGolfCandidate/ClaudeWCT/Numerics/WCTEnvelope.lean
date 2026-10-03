import SigGolfCandidate.ClaudeWCT.Numerics.Covariance
import SigGolfCandidate.ClaudeWCT.Numerics.CoverW2
import SigGolfCandidate.ClaudeWCT.Numerics.CoverWF
import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept

namespace ClaudeWCT.Numerics.WCTEnvelope
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning ClaudeWCT.Numerics.Kernel ClaudeWCT.Numerics.Covariance
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage uniformWordAverage_mono
  uniformWordAverage_mul_left uniformWordAverage_sum)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex uniformWordAverage_constant uniform_marked_word_atIndex)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx CoveredP scoreP price sum_admissible)
open ClaudeWCT.WCT9 (digit)
noncomputable def rankEquiv : Fin 728 ≃ ClaudeWCT.Numerics.WCT9.Word := ClaudeWCT.WCT9.equivalence
theorem wv_rankEquiv (r : Fin 728) (t : Fin 7) :
    ClaudeWCT.Numerics.WCT9.wv (rankEquiv r) t = digit r t := rfl
theorem w1Table_digit : W1Table digit := by
  intro p
  have h : #{x : Fin 728 × (Fin p → Fin 728) | CoversT digit (digit x.1) x.2} =
      ClaudeWCT.Numerics.WCT9.coverCount p := by
    refine card_equiv (rankEquiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) rankEquiv)) fun x => ?_
    simp only [mem_filter, mem_univ, true_and]
    simp only [CoversT, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, wv_rankEquiv]
  rw [h]
  exact ClaudeWCT.Numerics.WCT9.coverCount_eq p
theorem w2Table_digit : W2Table digit := by
  intro p
  have h : #{x : Fin 728 × Fin 728 × (Fin p → Fin 728) |
      CoversT digit (digit x.1) x.2.2 ∧ CoversT digit (digit x.2.1) x.2.2} =
      ClaudeWCT.Numerics.WCT9.coverCount2 p := by
    refine card_equiv (rankEquiv.prodCongr (rankEquiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) rankEquiv)))
      fun x => ?_
    simp only [mem_filter, mem_univ, true_and]
    simp only [CoversT, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, wv_rankEquiv]
  rw [h]
  exact ClaudeWCT.Numerics.WCT9.coverCount2_eq p
abbrev Coords := ClaudeWCT.WCT9.Coord → ClaudeWCT.WCT9.Child × ClaudeWCT.WCT9.Rank
noncomputable def wctEnv (L : List Coords) : ENNReal := env digit L
theorem wctEnv_cons_le (a : Coords) (L : List Coords) : wctEnv L ≤ wctEnv (a :: L) :=
  env_cons_le digit a L
theorem wctEnv_le_one (L : List Coords) : wctEnv L ≤ 1 := env_le_one digit L
theorem wctEnv_moment (r : ℕ) :
    uniformWordAverage r wctEnv = ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) :=
  env_moment digit (by simp) (by simp) w1Table_digit r
theorem wctEnv_sq_moment (r : ℕ) :
    uniformWordAverage r (fun L => wctEnv L ^ 2) =
      ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) :=
  env_sq_moment digit (by simp) (by simp) w1Table_digit w2Table_digit r
theorem wctEnv_moment_le_one (r : ℕ) : uniformWordAverage r wctEnv ≤ 1 :=
  (uniformWordAverage_mono r wctEnv_le_one).trans (uniformWordAverage_constant r 1).le
theorem wctEnv_sq_moment_le_one (r : ℕ) : uniformWordAverage r (fun L => wctEnv L ^ 2) ≤ 1 :=
  (uniformWordAverage_mono r fun L => pow_le_one₀ zero_le (wctEnv_le_one L)).trans
    (uniformWordAverage_constant r 1).le
theorem wct_index_mean (index : Fin (2 ^ 31)) (steps : ℕ) :
    uniformWordAverage steps (fun word : List WProposal => wctEnv (atIndex index word)) =
      binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
        (fun r => ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  have h := env_index_moment (n := 9) (C := ClaudeWCT.WCT9.Child) digit index steps 1
  simp only [pow_one, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (by simp_rw [← wctEnv_moment]; rfl)
theorem wct_index_second (index : Fin (2 ^ 31)) (steps : ℕ) :
    uniformWordAverage steps (fun word : List WProposal => wctEnv (atIndex index word) ^ 2) =
      binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
        (fun r => ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  have h := env_index_moment (n := 9) (C := ClaudeWCT.WCT9.Child) digit index steps 2
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (by simp_rw [← wctEnv_sq_moment]; rfl)
theorem wct_index_negative_correlation (first second : Fin (2 ^ 31)) (hne : first ≠ second) (steps : ℕ) :
    uniformWordAverage steps (fun word : List WProposal =>
        wctEnv (atIndex first word) * wctEnv (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List WProposal => wctEnv (atIndex first word)) *
        uniformWordAverage steps (fun word : List WProposal => wctEnv (atIndex second word)) :=
  env_index_negative_correlation digit first second hne steps
theorem mem_atIndex {α β : Type} [DecidableEq α] (index : α) (e : β) (W : List (α × β)) :
    e ∈ atIndex index W ↔ (index, e) ∈ W := by
  unfold atIndex
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, e'⟩, hmem, h⟩
    by_cases hi : i = index
    · simp only [hi, if_true, Option.some.injEq] at h
      rw [← hi, ← h]
      exact hmem
    · simp [hi] at h
  · intro h
    exact ⟨(index, e), h, by simp⟩
theorem coveredP_iff (W : List WProposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListCov digit (atIndex (outIdx N) W) (proposal N).2 := by
  unfold CoveredP ClaudeWCT.Bank.WCT.SlotCoveredP ListCov
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem price_scale :
    (2 : ENNReal) ^ 128 * ((22 ^ 9 * 2 ^ 24 : ℕ) : ENNReal) * ((Q ^ 9 : ℕ) : ENNReal) * ((2 ^ 256 : ℕ) : ENNReal)⁻¹ =
      ((1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 5 := by
  rw [← div_eq_mul_inv, ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num [Q]
theorem price_eq (W : List WProposal) :
    price W = ((1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 5 * ∑ index : Fin (2 ^ 31), wctEnv (atIndex index W) := by
  classical
  set g : WProposal → ENNReal := fun p => if ListCov digit (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, scoreP W N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold scoreP
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, true_and, if_true, hg]
      exact if_congr (coveredP_iff W N) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((Q ^ 9 : ℕ) : ENNReal) * ∑ index : Fin (2 ^ 31), wctEnv (atIndex index W) := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    have hT : Fintype.card Coords = Q ^ 9 := card_table (by simp) (by simp)
    unfold wctEnv env finiteAverage
    rw [hT, ENNReal.mul_div_cancel (by simp [Q]) (by simp)]
  unfold price finiteAverage
  simp_rw [hs]
  rw [sum_admissible g, hsum, Fintype.card_bitVec, ← price_scale]
  simp only [div_eq_mul_inv]
  ring
theorem price_mean (steps : ℕ) :
    uniformWordAverage steps price =
      (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
        (fun r => ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [show price = fun W => ((1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 5 *
      ∑ index : Fin (2 ^ 31), wctEnv (atIndex index W) from funext price_eq]
  rw [uniformWordAverage_mul_left, uniformWordAverage_sum]
  simp_rw [wct_index_mean]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  congr 1
  rw [ENNReal.div_eq_inv_mul, mul_comm _ ((2 ^ 31 : ℕ) : ENNReal), ← mul_assoc]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [A, ENNReal.toReal_mul, ENNReal.toReal_inv]
theorem diag_scale : (((1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 5) ^ 2 * ((2 ^ 31 : ℕ) : ENNReal) = (A : ENNReal) ^ 2 / 2 ^ 31 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [A, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem price_secondMoment_le (steps : ℕ) :
    uniformWordAverage steps (fun W => price W ^ 2) ≤
      uniformWordAverage steps price ^ 2 +
        (A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
          (fun r => ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  set c : ENNReal := ((1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 5
  have hmean : uniformWordAverage steps price =
      c * ∑ index : Fin (2 ^ 31), uniformWordAverage steps
        (fun word : List WProposal => wctEnv (atIndex index word)) := by
    rw [show price = fun W => c * ∑ index : Fin (2 ^ 31), wctEnv (atIndex index W) from funext price_eq]
    rw [uniformWordAverage_mul_left, uniformWordAverage_sum]
  have hs := env_sum_square_le (n := 9) (C := ClaudeWCT.WCT9.Child) (α := Fin (2 ^ 31)) digit steps
  calc uniformWordAverage steps (fun W => price W ^ 2)
      = c ^ 2 * uniformWordAverage steps (fun word : List WProposal =>
          (∑ index : Fin (2 ^ 31), wctEnv (atIndex index word)) ^ 2) := by
        simp_rw [price_eq, mul_pow]
        rw [uniformWordAverage_mul_left]
    _ ≤ c ^ 2 * ((∑ index : Fin (2 ^ 31), uniformWordAverage steps
          (fun word : List WProposal => wctEnv (atIndex index word))) ^ 2 +
          ∑ index : Fin (2 ^ 31), uniformWordAverage steps
            (fun word : List WProposal => wctEnv (atIndex index word) ^ 2)) := mul_le_mul' le_rfl hs
    _ = uniformWordAverage steps price ^ 2 +
          c ^ 2 * ((2 ^ 31 : ℕ) : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
            (fun r => ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
        rw [hmean, mul_add, mul_pow]
        simp_rw [wct_index_second]
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = _ := by rw [diag_scale]
theorem wfTable_digit (i : Fin 7) : WFTable digit i := by
  intro p
  have h : #{x : Fin 728 × (Fin p → Fin 728) | CoversExcept digit i (digit x.1) x.2} =
      ClaudeWCT.Numerics.WCT9.coverCountF i p := by
    refine card_equiv (rankEquiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) rankEquiv)) fun x => ?_
    simp only [mem_filter, mem_univ, true_and]
    simp only [CoversExcept, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, wv_rankEquiv]
  rw [h]
  exact ClaudeWCT.Numerics.WCT9.coverCountF_eq i p
noncomputable def wctNearEnv (k₀ : Fin 9) (i₀ : Fin 7) (L : List Coords) : ENNReal := nearEnv digit k₀ i₀ L
theorem wctNearEnv_cons_le (k₀ : Fin 9) (i₀ : Fin 7) (a : Coords) (L : List Coords) :
    wctNearEnv k₀ i₀ L ≤ wctNearEnv k₀ i₀ (a :: L) :=
  nearEnv_cons_le digit k₀ i₀ a L
theorem wctNearEnv_le_one (k₀ : Fin 9) (i₀ : Fin 7) (L : List Coords) : wctNearEnv k₀ i₀ L ≤ 1 :=
  nearEnv_le_one digit k₀ i₀ L
theorem wctNearEnv_moment (k₀ : Fin 9) (i₀ : Fin 7) (r : ℕ) :
    uniformWordAverage r (wctNearEnv k₀ i₀) =
      ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) :=
  nearEnv_moment digit k₀ i₀ (by simp) (by simp) w1Table_digit (wfTable_digit i₀) r
theorem wctNearEnv_moment_le_one (k₀ : Fin 9) (i₀ : Fin 7) (r : ℕ) :
    uniformWordAverage r (wctNearEnv k₀ i₀) ≤ 1 :=
  (uniformWordAverage_mono r (wctNearEnv_le_one k₀ i₀)).trans (uniformWordAverage_constant r 1).le
theorem wct_near_index_mean (k₀ : Fin 9) (i₀ : Fin 7) (index : Fin (2 ^ 31)) (steps : ℕ) :
    uniformWordAverage steps (fun word : List WProposal => wctNearEnv k₀ i₀ (atIndex index word)) =
      binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
        (fun r => ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [uniform_marked_word_atIndex index steps (wctNearEnv k₀ i₀)]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [wctNearEnv_moment]
end ClaudeWCT.Numerics.WCTEnvelope
