import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1

namespace ClaudeWCT.Numerics
open Finset
section
variable {c : ℕ} {β : Type*}
def CoversExcept {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (v : Fin c → ℕ) (E : Fin p → β) :
    Prop :=
  ∀ j, j ≠ i → ∃ e, v j ≤ val (E e) j
instance {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (v : Fin c → ℕ) :
    DecidablePred (CoversExcept (p := p) val i v) :=
  fun _ => Fintype.decidableForallFintype
theorem coversExcept_iff {p : ℕ} (val : β → Fin (c + 1) → ℕ) (i : Fin (c + 1))
    (v : Fin (c + 1) → ℕ) (E : Fin p → β) :
    CoversExcept val i v E ↔
      CoversT (fun x j => val x (i.succAbove j)) (fun j => v (i.succAbove j)) E := by
  constructor
  · intro h j
    exact h _ (Fin.succAbove_ne i j)
  · intro h j hj
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact h j'
end
end ClaudeWCT.Numerics
namespace ClaudeWCT.Numerics.WCT9
open Finset Polynomial ClaudeWCT.Numerics ClaudeWCT.Numerics.Kernel
def coverCountF (i : Fin 7) (p : ℕ) : ℕ :=
  #{ue : Word × (Fin p → Word) | CoversExcept wv i (wv ue.1) ue.2}
theorem chainPoly_false (x : ℕ) : chainPoly x false = cp 0 := by
  have h0 : osb 0 = false := rfl
  simp [cp, chainPoly, h0]
theorem box_three_eq : box 3 = (cp 0).eval PB := optsU_fu 0
theorem card_violates_off (i : Fin 7) (u : Fin 7 → ℕ) (s : Fin 6 → Bool) :
    #{x : Word | Violates (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) s x} =
      (cp 0 * ∏ j, chainPoly (u (i.succAbove j)) (s j)).coeff 6 := by
  have h1 : #{x : Word | Violates (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) s x} =
      #{x : Word | Violates wv u (Fin.insertNth (α := fun _ => Bool) i false s) x} := by
    refine congrArg card (filter_congr fun x _ => ?_)
    simp only [Violates]
    rw [Fin.forall_iff_succAbove i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Bool.false_eq_true,
      false_implies, true_and]
  rw [h1, card_violates, Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, chainPoly_false]
theorem card_coversExcept (i : Fin 7) (p : ℕ) (u : Fin 7 → ℕ) :
    (#{E : Fin p → Word | CoversExcept wv i u E} : ℤ) =
      ∑ s : Fin 6 → Bool, (-1) ^ #{j | s j = true} *
        (((cp 0 * ∏ j, chainPoly (u (i.succAbove j)) (s j)).coeff 6 : ℕ) : ℤ) ^ p := by
  have h : #{E : Fin p → Word | CoversExcept wv i u E} =
      #{E : Fin p → Word | CoversT (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) E} :=
    congrArg card (filter_congr fun E _ => coversExcept_iff _ _ _ _)
  rw [h, card_covered_eq]
  simp_rw [card_violates_off]
theorem coverCountF_ie (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ u : Word, ∑ s : Fin 6 → Bool,
      (-1) ^ #{j | s j = true} *
        (((cp 0 * ∏ j, chainPoly (wv u (i.succAbove j)) (s j)).coeff 6 : ℕ) : ℤ) ^ p := by
  unfold coverCountF
  rw [natCast_card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  dsimp only
  rw [← natCast_card_filter, card_coversExcept]
def optEquivN (n : ℕ) : (Fin n → Fin 4) × (Fin n → Bool) ≃ (Fin n → Fin 8) where
  toFun ds i := optOf (ds.1 i) (ds.2 i)
  invFun o := (fun i => ou (o i), fun i => osb (o i))
  left_inv ds := by ext i <;> simp [ou_optOf, osb_optOf]
  right_inv o := by ext i; simp [optOf_ou_osb]
noncomputable def psiF (p : ℕ) (x : ℕ) (k : Fin 8 → ℕ) : ℤ :=
  if x + ∑ a, k a * ((ou a : ℕ)) = 6 then
    (-1) ^ (∑ a, k a * (if osb a then 1 else 0)) *
      (((cp 0 * ∏ a, cp a ^ k a).coeff 6 : ℕ) : ℤ) ^ p
  else 0
theorem coverCountF_occ (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ x : Fin 4, ∑ o : Fin 6 → Fin 8, psiF p x (occ o) := by
  rw [coverCountF_ie]
  have hsub : ∀ G : (Fin 7 → Fin 4) → ℤ, ∑ u : Word, G u.1 =
      ∑ d : Fin 7 → Fin 4, if ∑ i, (d i : ℕ) = 6 then G d else 0 := by
    intro G
    rw [← sum_filter, ← sum_subtype (p := fun d : Fin 7 → Fin 4 => ∑ i, (d i : ℕ) = 6)]
    intro d; simp
  simp only [wv]
  rw [hsub (fun d => ∑ s : Fin 6 → Bool, (-1) ^ #{j | s j = true} *
      (((cp 0 * ∏ j, chainPoly ((d (i.succAbove j) : ℕ)) (s j)).coeff 6 : ℕ) : ℤ) ^ p)]
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => Fin 4) i), Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  have hins : ∀ d' : Fin 6 → Fin 4, (Fin.insertNthEquiv (fun _ => Fin 4) i) (x, d') =
      Fin.insertNth (α := fun _ => Fin 4) i x d' := fun _ => rfl
  simp only [hins, Fin.insertNth_apply_succAbove]
  have hsplit : ∀ d' : Fin 6 → Fin 4,
      ∑ j, ((Fin.insertNth (α := fun _ => Fin 4) i x d' j : Fin 4) : ℕ) = (x : ℕ) + ∑ j, (d' j : ℕ) := by
    intro d'
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [hsplit]
  simp_rw [ite_sum_zero]
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (optEquivN 6).symm]
  refine sum_congr rfl fun o _ => ?_
  have e1 : ∀ j, ((optEquivN 6).symm o).1 j = ou (o j) := fun j => rfl
  have e2 : ∀ j, ((optEquivN 6).symm o).2 j = osb (o j) := fun j => rfl
  simp only [e1, e2]
  unfold psiF
  have hsum : ∑ j, ((ou (o j) : Fin 4) : ℕ) = ∑ a, occ o a * (ou a : ℕ) :=
    sum_eq_sum_mul_occ (fun a => (ou a : ℕ)) o
  have hcard : #{j | osb (o j) = true} = ∑ a, occ o a * (if osb a then 1 else 0) := by
    rw [card_filter]
    exact sum_eq_sum_mul_occ (fun a => if osb a then 1 else 0) o
  have hprod : ∏ j, chainPoly ((ou (o j) : ℕ)) (osb (o j)) = ∏ a, cp a ^ occ o a :=
    prod_eq_prod_pow_occ cp o
  simp only [hsum, hcard, hprod]
theorem coverCountF_counts (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ x : Fin 4,
      ∑ k ∈ Nat.antidiagonalTuple 8 6, (Nat.multinomial univ k : ℤ) * psiF p x k := by
  rw [coverCountF_occ]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_occ, piAntidiag_univ_fin_eq_antidiagonalTuple]
  simp_rw [nsmul_eq_mul]
theorem coeff_free_prod_cp_lt (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 6) (n : ℕ) :
    (cp 0 * ∏ a, cp a ^ k a).coeff n < PB := by
  refine lt_of_le_of_lt (coeff_le_eval_one _ n) ?_
  rw [eval_mul, eval_prod]
  simp only [eval_pow]
  have hsum : ∑ a, k a = 6 := Nat.mem_antidiagonalTuple.mp hk
  calc (cp 0).eval 1 * ∏ a, (cp a).eval 1 ^ k a ≤ 4 * ∏ a, 4 ^ k a :=
        Nat.mul_le_mul (eval_one_cp_le 0)
          (prod_le_prod' fun a _ => Nat.pow_le_pow_left (eval_one_cp_le a) _)
    _ = 4 * 4 ^ 6 := by rw [prod_pow_eq_pow_sum, hsum]
    _ < PB := by unfold PB; norm_num
theorem wfHist_sum (hb : ℕ) :
    wfHist hb = ∑ x : Fin 4, enumK hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  have c0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have c1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have c2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have c3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [Fin.sum_univ_four]
  simp only [wfHist, hr, List.foldr_cons, List.foldr_nil]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, c0, c1, c2, c3, add_zero, add_assoc]
theorem wfHist_eq (hb : ℕ) :
    wfHist hb = histOf ((univ : Finset (Fin 4)) ×ˢ Nat.antidiagonalTuple 8 6)
      (fun xk => ∑ j, xk.2 j * (ou j : ℕ) = 6 - (xk.1 : ℕ))
      (fun xk => parity optsU xk.2) (fun xk => Nat.multinomial univ xk.2)
      (fun xk => coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ xk.2 j) 6) hb := by
  rw [wfHist_sum]
  unfold histOf
  rw [sum_product]
  refine sum_congr rfl fun x _ => ?_
  have h1 : enumK hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false =
      ∑ k ∈ Nat.antidiagonalTuple 8 6, term hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false :=
    enumK_eq hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false
  rw [h1]
  refine sum_congr rfl fun k hk => ?_
  have hsum : ∑ a, k a = 6 := Nat.mem_antidiagonalTuple.mp hk
  have h2 : term hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false =
      if ∑ j : Fin 8, k j * (optsU.get j).1 = 6 - (x : ℕ) then
        signedPair (false ^^ parity optsU k)
          ((fact 6 / (1 * ∏ j : Fin 8, (k j).factorial)) *
            coeffAt (1 * ∏ j : Fin 8, (optsU.get j).2.2.1 ^ k j) 0 *
            hb ^ coeffAt (box 3 * ∏ j : Fin 8, (optsU.get j).2.1 ^ k j) 6)
      else 0 :=
    term_eq hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false
  rw [h2]
  simp only [optsU_fst, optsU_fb, optsU_fu, one_pow, prod_const_one, one_mul, Bool.false_xor]
  have hm : fact 6 / ∏ j, (k j).factorial = Nat.multinomial univ k := by
    rw [fact_eq, Nat.multinomial, ← hsum]
  have hc : coeffAt 1 0 = 1 := by unfold coeffAt PB; norm_num
  rw [hm, hc, mul_one]
theorem term_matchF (p : ℕ) (x : Fin 4) (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 6) :
    (Nat.multinomial univ k : ℤ) * psiF p x k =
      if ∑ j, k j * (ou j : ℕ) = 6 - (x : ℕ) then
        (if parity optsU k then (-1 : ℤ) else 1) * (Nat.multinomial univ k : ℕ) *
          ((coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ k j) 6 : ℕ) : ℤ) ^ p
      else 0 := by
  unfold psiF
  have hpar : parity optsU k = ((∑ a, k a * (if osb a then 1 else 0)) % 2 == 1) := by
    have h0 : parity optsU k = ((∑ j : Fin 8, if (optsU.get j).2.2.2 then k j else 0) % 2 == 1) := rfl
    rw [h0]
    congr 2
    refine sum_congr rfl fun j _ => ?_
    rw [optsU_inS]; split <;> simp
  have hcnt : coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ k j) 6 = (cp 0 * ∏ a, cp a ^ k a).coeff 6 := by
    have he : box 3 * ∏ j, ((cp j).eval PB) ^ k j = (cp 0 * ∏ a, cp a ^ k a).eval PB := by
      rw [eval_mul, eval_prod, box_three_eq]; simp only [eval_pow]
    rw [he]
    exact eval_div_pow_mod (by unfold PB; positivity) 6 _ (coeff_free_prod_cp_lt k hk)
  rw [hpar, hcnt, ← neg_one_pow_eq]
  have hx : (x : ℕ) < 4 := x.isLt
  by_cases h : ∑ j, k j * (ou j : ℕ) = 6 - (x : ℕ)
  · rw [if_pos (by omega), if_pos h]
    ring
  · rw [if_neg (by omega), if_neg h, mul_zero]
theorem coverCountF_eq (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = (wfData.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  have hEq := wf_ok
  have hMass := wf_mass
  rw [wfHist_eq] at hEq hMass
  rw [coverCountF_counts, ← decode _ _ _ _ _ wfData hEq hMass p, sum_product]
  exact sum_congr rfl fun x _ => sum_congr rfl fun k hk => term_matchF p x k hk
end ClaudeWCT.Numerics.WCT9
