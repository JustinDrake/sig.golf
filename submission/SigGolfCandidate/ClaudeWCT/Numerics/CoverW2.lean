import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1

namespace ClaudeWCT.Numerics.WCT9
open Finset Polynomial ClaudeWCT.Numerics ClaudeWCT.Numerics.Kernel
def coverCount2 (p : ℕ) : ℕ :=
  #{x : Word × Word × (Fin p → Word) | CoversT wv (wv x.1) x.2.2 ∧ CoversT wv (wv x.2.1) x.2.2}
def joinv (u₁ u₂ : Word) : Fin 7 → Fin 4 := fun i => max (u₁.1 i) (u₂.1 i)
theorem coversT_and_iff {p : ℕ} (u₁ u₂ : Word) (E : Fin p → Word) :
    CoversT wv (wv u₁) E ∧ CoversT wv (wv u₂) E ↔
      CoversT wv (fun i => ((joinv u₁ u₂ i : Fin 4) : ℕ)) E := by
  simp only [CoversT, joinv, Fin.coe_max, wv]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    obtain ⟨e₁, he₁⟩ := h₁ i
    obtain ⟨e₂, he₂⟩ := h₂ i
    rcases le_total ((u₁.1 i : Fin 4) : ℕ) ((u₂.1 i : Fin 4) : ℕ) with h | h
    · exact ⟨e₂, by rw [max_eq_right h]; exact he₂⟩
    · exact ⟨e₁, by rw [max_eq_left h]; exact he₁⟩
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨e, he⟩ := h i
      exact ⟨e, le_trans (le_max_left _ _) he⟩
    · obtain ⟨e, he⟩ := h i
      exact ⟨e, le_trans (le_max_right _ _) he⟩
noncomputable def pairPoly (x : Fin 4) : ℕ[X] :=
  ∑ ab ∈ univ.filter (fun ab : Fin 4 × Fin 4 => max ab.1 ab.2 = x),
    X ^ ((ab.1 : ℕ) + 32 * (ab.2 : ℕ))
set_option linter.constructorNameAsVariable false in
theorem card_join (v : Fin 7 → Fin 4) :
    #{uu : Word × Word | joinv uu.1 uu.2 = v} = (∏ i, pairPoly (v i)).coeff (6 + 32 * 6) := by
  unfold pairPoly
  rw [← card_pi_sum_eq_coeff]
  refine card_bij (fun uu _ => fun i => (uu.1.1 i, uu.2.1 i)) ?_ ?_ ?_
  · intro uu huu
    simp only [mem_filter, mem_univ, true_and] at huu
    simp only [mem_filter, Fintype.mem_piFinset, mem_univ, true_and]
    refine ⟨fun i => ?_, ?_⟩
    · rw [← huu]; rfl
    · rw [sum_add_distrib, ← mul_sum, uu.1.2, uu.2.2]
  · intro a _ b _ h
    have h1 : a.1.1 = b.1.1 := funext fun i => congrArg Prod.fst (congrFun h i)
    have h2 : a.2.1 = b.2.1 := funext fun i => congrArg Prod.snd (congrFun h i)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro y hy
    simp only [mem_filter, Fintype.mem_piFinset, mem_univ, true_and] at hy
    obtain ⟨hC, hS⟩ := hy
    have hA : ∑ i, (((y i).1 : Fin 4) : ℕ) ≤ ∑ _i : Fin 7, 3 :=
      sum_le_sum fun i _ => Nat.le_of_lt_succ (y i).1.isLt
    have hB : ∑ i, (((y i).2 : Fin 4) : ℕ) ≤ ∑ _i : Fin 7, 3 :=
      sum_le_sum fun i _ => Nat.le_of_lt_succ (y i).2.isLt
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hA hB
    rw [sum_add_distrib, ← mul_sum] at hS
    refine ⟨(⟨fun i => (y i).1, by show ∑ i, (((y i).1 : Fin 4) : ℕ) = 6; omega⟩,
      ⟨fun i => (y i).2, by show ∑ i, (((y i).2 : Fin 4) : ℕ) = 6; omega⟩), ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    funext i
    exact hC i
theorem coverCount2_join (p : ℕ) :
    (coverCount2 p : ℤ) = ∑ uu : Word × Word, ∑ s : Fin 7 → Bool,
      (-1) ^ #{i | s i = true} *
        (((∏ i, chainPoly ((joinv uu.1 uu.2 i : Fin 4) : ℕ) (s i)).coeff 6 : ℕ) : ℤ) ^ p := by
  unfold coverCount2
  rw [natCast_card_filter]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun u₁ _ => sum_congr rfl fun u₂ _ => ?_
  rw [← natCast_card_filter]
  have h : #{E : Fin p → Word | CoversT wv (wv u₁) E ∧ CoversT wv (wv u₂) E} =
      #{E : Fin p → Word | CoversT wv (fun i => ((joinv u₁ u₂ i : Fin 4) : ℕ)) E} :=
    congrArg card (filter_congr fun E _ => coversT_and_iff u₁ u₂ E)
  rw [h, card_covered_eq]
  simp_rw [card_violates]
noncomputable def psi2 (p : ℕ) (k : Fin 8 → ℕ) : ℤ :=
  (-1) ^ (∑ a, k a * (if osb a then 1 else 0)) *
    (((∏ a, pairPoly (ou a) ^ k a).coeff (6 + 32 * 6) : ℕ) : ℤ) *
    (((∏ a, cp a ^ k a).coeff 6 : ℕ) : ℤ) ^ p
theorem coverCount2_occ (p : ℕ) :
    (coverCount2 p : ℤ) = ∑ o : Fin 7 → Fin 8, psi2 p (occ o) := by
  rw [coverCount2_join]
  have hfib : ∀ H : (Fin 7 → Fin 4) → ℤ, ∑ uu : Word × Word, H (joinv uu.1 uu.2) =
      ∑ v : Fin 7 → Fin 4, ((∏ i, pairPoly (v i)).coeff (6 + 32 * 6) : ℤ) * H v := by
    intro H
    simp_rw [← card_join, natCast_card_filter, sum_mul, ite_mul, one_mul, zero_mul]
    rw [sum_comm]
    refine sum_congr rfl fun uu _ => ?_
    rw [Fintype.sum_ite_eq]
  rw [hfib (fun v => ∑ s : Fin 7 → Bool, (-1) ^ #{i | s i = true} *
    (((∏ i, chainPoly ((v i : Fin 4) : ℕ) (s i)).coeff 6 : ℕ) : ℤ) ^ p)]
  simp_rw [mul_sum]
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp optEquiv.symm]
  refine sum_congr rfl fun o _ => ?_
  have e1 : ∀ i, (optEquiv.symm o).1 i = ou (o i) := fun i => rfl
  have e2 : ∀ i, (optEquiv.symm o).2 i = osb (o i) := fun i => rfl
  simp only [e1, e2]
  unfold psi2
  have hcard : #{i | osb (o i) = true} = ∑ a, occ o a * (if osb a then 1 else 0) := by
    rw [card_filter]
    exact sum_eq_sum_mul_occ (fun a => if osb a then 1 else 0) o
  have hprod : ∏ i, chainPoly ((ou (o i) : ℕ)) (osb (o i)) = ∏ a, cp a ^ occ o a :=
    prod_eq_prod_pow_occ cp o
  have hpair : ∏ i, pairPoly (ou (o i)) = ∏ a, pairPoly (ou a) ^ occ o a :=
    prod_eq_prod_pow_occ (fun a => pairPoly (ou a)) o
  simp only [hcard, hprod, hpair]
  ring
theorem coverCount2_counts (p : ℕ) :
    (coverCount2 p : ℤ) =
      ∑ k ∈ Nat.antidiagonalTuple 8 7, (Nat.multinomial univ k : ℤ) * psi2 p k := by
  rw [coverCount2_occ, sum_occ, piAntidiag_univ_fin_eq_antidiagonalTuple]
  simp_rw [nsmul_eq_mul]
theorem optsP_fst (j : Fin 8) : (optsP.get j).1 = 0 := by fin_cases j <;> rfl
theorem optsP_inS (j : Fin 8) : (optsP.get j).2.2.2 = osb j := by fin_cases j <;> rfl
theorem optsP_fu (j : Fin 8) : (optsP.get j).2.1 = (cp j).eval PB := by
  rw [← optsU_fu j]; fin_cases j <;> rfl
theorem eval_pairPoly (x : Fin 4) (B : ℕ) :
    (pairPoly x).eval B = ∑ ab ∈ univ.filter (fun ab : Fin 4 × Fin 4 => max ab.1 ab.2 = x),
      B ^ ((ab.1 : ℕ) + 32 * (ab.2 : ℕ)) := by
  rw [pairPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
theorem optsP_fb (j : Fin 8) : (optsP.get j).2.2.1 = (pairPoly (ou j)).eval PB := by
  fin_cases j <;>
  simp only [eval_pairPoly, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_four] <;> decide
theorem eval_one_pairPoly_le (x : Fin 4) : (pairPoly x).eval 1 ≤ 16 := by
  unfold pairPoly
  rw [eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, sum_const, smul_eq_mul, mul_one]
  exact (card_filter_le _ _).trans (by simp)
theorem coeff_prod_pairPoly_lt (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 7) (n : ℕ) :
    (∏ a, pairPoly (ou a) ^ k a).coeff n < PB := by
  refine lt_of_le_of_lt (coeff_le_eval_one _ n) ?_
  rw [eval_prod]
  simp only [eval_pow]
  have hsum : ∑ a, k a = 7 := Nat.mem_antidiagonalTuple.mp hk
  calc ∏ a, (pairPoly (ou a)).eval 1 ^ k a ≤ ∏ a, 16 ^ k a :=
        prod_le_prod' fun a _ => Nat.pow_le_pow_left (eval_one_pairPoly_le (ou a)) _
    _ = 16 ^ 7 := by rw [prod_pow_eq_pow_sum, hsum]
    _ < PB := by unfold PB; norm_num
theorem w2Hist_eq (hb : ℕ) :
    w2Hist hb = histOf (Nat.antidiagonalTuple 8 7) (fun _ => True)
      (fun k => parity optsP k)
      (fun k => Nat.multinomial univ k * coeffAt (∏ j, ((pairPoly (ou j)).eval PB) ^ k j) (6 + 32 * 6))
      (fun k => coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6) hb := by
  unfold w2Hist histOf
  have h1 : enumK hb 7 (6 + 32 * 6) optsP 7 0 1 1 1 false =
      ∑ k ∈ Nat.antidiagonalTuple 8 7, term hb 7 (6 + 32 * 6) optsP k 0 1 1 1 false :=
    enumK_eq hb 7 (6 + 32 * 6) optsP 7 0 1 1 1 false
  rw [h1]
  refine sum_congr rfl fun k hk => ?_
  have hsum : ∑ a, k a = 7 := Nat.mem_antidiagonalTuple.mp hk
  have h2 : term hb 7 (6 + 32 * 6) optsP k 0 1 1 1 false =
      if ∑ j : Fin 8, k j * (optsP.get j).1 = 0 then
        signedPair (false ^^ parity optsP k)
          ((fact 7 / (1 * ∏ j : Fin 8, (k j).factorial)) *
            coeffAt (1 * ∏ j : Fin 8, (optsP.get j).2.2.1 ^ k j) (6 + 32 * 6) *
            hb ^ coeffAt (1 * ∏ j : Fin 8, (optsP.get j).2.1 ^ k j) 6)
      else 0 :=
    term_eq hb 7 (6 + 32 * 6) optsP k 0 1 1 1 false
  rw [h2]
  simp only [optsP_fst, optsP_fb, optsP_fu, mul_zero, sum_const_zero, one_mul, Bool.false_xor,
    if_true]
  have hm : fact 7 / ∏ j, (k j).factorial = Nat.multinomial univ k := by
    rw [fact_eq, Nat.multinomial, ← hsum]
  rw [hm]
theorem term_match2 (p : ℕ) (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 7) :
    (Nat.multinomial univ k : ℤ) * psi2 p k =
      if True then
        (if parity optsP k then (-1 : ℤ) else 1) *
          ((Nat.multinomial univ k *
            coeffAt (∏ j, ((pairPoly (ou j)).eval PB) ^ k j) (6 + 32 * 6) : ℕ) : ℤ) *
          ((coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6 : ℕ) : ℤ) ^ p
      else 0 := by
  unfold psi2
  have hpar : parity optsP k = ((∑ a, k a * (if osb a then 1 else 0)) % 2 == 1) := by
    have h0 : parity optsP k = ((∑ j : Fin 8, if (optsP.get j).2.2.2 then k j else 0) % 2 == 1) := rfl
    rw [h0]
    congr 2
    refine sum_congr rfl fun j _ => ?_
    rw [optsP_inS]; split <;> simp
  have hcnt : coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6 = (∏ a, cp a ^ k a).coeff 6 := by
    have he : ∏ j, ((cp j).eval PB) ^ k j = (∏ a, cp a ^ k a).eval PB := by
      rw [eval_prod]; simp only [eval_pow]
    rw [he]
    exact eval_div_pow_mod (by unfold PB; positivity) 6 _ (coeff_prod_cp_lt k hk)
  have hmul : coeffAt (∏ j, ((pairPoly (ou j)).eval PB) ^ k j) (6 + 32 * 6) =
      (∏ a, pairPoly (ou a) ^ k a).coeff (6 + 32 * 6) := by
    have he : ∏ j, ((pairPoly (ou j)).eval PB) ^ k j = (∏ a, pairPoly (ou a) ^ k a).eval PB := by
      rw [eval_prod]; simp only [eval_pow]
    rw [he]
    exact eval_div_pow_mod (by unfold PB; positivity) _ _ (coeff_prod_pairPoly_lt k hk)
  rw [hpar, hcnt, hmul, ← neg_one_pow_eq, if_pos trivial]
  push_cast
  ring
theorem coverCount2_eq (p : ℕ) :
    (coverCount2 p : ℤ) = (w2Data.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  have hEq := w2_ok
  have hMass := w2_mass
  rw [w2Hist_eq] at hEq hMass
  rw [coverCount2_counts, ← decode _ _ _ _ _ w2Data hEq hMass p]
  exact sum_congr rfl fun k hk => term_match2 p k hk
end ClaudeWCT.Numerics.WCT9
