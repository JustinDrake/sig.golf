import SigGolfCandidate.T3.FullCache.Primitives
import Mathlib.Data.BitVec
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
theorem macPrime_eq_mersenne : macPrime = mersenne 61 := rfl
theorem macPrime_prime : macPrime.Prime := by
  rw [macPrime_eq_mersenne]
  exact lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)
instance : Fact macPrime.Prime := ⟨macPrime_prime⟩
theorem polyMac_lt (k : Nat) (cs : List Nat) : polyMac k cs < macPrime ∨ cs = [] := by
  rcases List.eq_nil_or_concat cs with h | ⟨cs', c, rfl⟩
  · exact Or.inr h
  · left
    unfold polyMac
    rw [List.concat_eq_append, List.foldl_append]
    exact Nat.mod_lt _ (by decide)
theorem polyMac_lt' (k : Nat) (cs : List Nat) : polyMac k cs < 2 ^ 61 := by
  rcases polyMac_lt k cs with h | h
  · have : macPrime < 2 ^ 61 := by decide
    omega
  · subst h; simp [polyMac]
open Polynomial
noncomputable def macPoly (cs : List Nat) : (ZMod macPrime)[X] :=
  cs.foldl (fun q c => (q + C (c : ZMod macPrime)) * X) 0
theorem macPoly_concat (cs : List Nat) (c : Nat) :
    macPoly (cs ++ [c]) = (macPoly cs + C (c : ZMod macPrime)) * X := by
  simp [macPoly, List.foldl_append]
theorem polyMac_cast_aux (k : Nat) (cs : List Nat) (acc : Nat) (q : (ZMod macPrime)[X])
    (h : (acc : ZMod macPrime) = q.eval (k : ZMod macPrime)) :
    ((cs.foldl (fun acc c => (acc + c) * k % macPrime) acc : Nat) : ZMod macPrime) =
      (cs.foldl (fun q c => (q + C (c : ZMod macPrime)) * X) q).eval (k : ZMod macPrime) := by
  induction cs generalizing acc q with
  | nil => simpa using h
  | cons c cs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [ZMod.natCast_mod]
      simp [h]
theorem polyMac_cast (k : Nat) (cs : List Nat) :
    ((polyMac k cs : Nat) : ZMod macPrime) = (macPoly cs).eval (k : ZMod macPrime) :=
  polyMac_cast_aux k cs 0 0 (by simp)
theorem natDegree_macPoly_le (cs : List Nat) : (macPoly cs).natDegree ≤ cs.length := by
  induction cs using List.reverseRecOn with
  | nil => simp [macPoly]
  | append_singleton cs c ih =>
      rw [macPoly_concat, List.length_append, List.length_singleton]
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X]
      refine Nat.add_le_add_right ((natDegree_add_le _ _).trans ?_) 1
      rw [natDegree_C]
      omega
theorem eq_of_macPoly_sub_eq_C : ∀ (xs ys : List Nat), xs.length = ys.length →
    (∀ x ∈ xs, x < macPrime) → (∀ y ∈ ys, y < macPrime) → ∀ d : ZMod macPrime, macPoly xs - macPoly ys = C d → xs = ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
      intro ys hlen _ _ _ _
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton xs x ih =>
      intro ys hlen hx hy d h
      rcases List.eq_nil_or_concat ys with hnil | ⟨ys', y, rfl⟩
      · subst hnil; simp at hlen
      rw [List.concat_eq_append] at hlen hy h ⊢
      have hlen' : xs.length = ys'.length := by simpa using hlen
      rw [macPoly_concat, macPoly_concat, ← sub_mul] at h
      have hd : d = 0 := by
        have := congrArg (Polynomial.eval 0) h
        simpa using this.symm
      subst hd
      have hzero : macPoly xs + C (x : ZMod macPrime) - (macPoly ys' + C (y : ZMod macPrime)) = 0 := by
        have := h
        rw [C_0, mul_eq_zero] at this
        exact this.resolve_right X_ne_zero
      have hsub : macPoly xs - macPoly ys' = C ((y : ZMod macPrime) - (x : ZMod macPrime)) := by
        rw [C_sub]
        linear_combination hzero
      have hxs := ih ys' hlen' (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha])) _ hsub
      subst hxs
      rw [sub_self] at hsub
      have hc : (y : ZMod macPrime) - (x : ZMod macPrime) = 0 := by
        have := congrArg (fun q : (ZMod macPrime)[X] => q.coeff 0) hsub
        simpa using this.symm
      have hxy : (x : ZMod macPrime) = (y : ZMod macPrime) := (sub_eq_zero.mp hc).symm
      have hx' := hx x (by simp)
      have hy' := hy y (by simp)
      have : x = y := by
        have := (ZMod.natCast_eq_natCast_iff' x y macPrime).mp hxy
        rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
      rw [this]
theorem card_polyMac_diff_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (d : ZMod macPrime) :
    ((Finset.range (2 ^ 61)).filter fun k => ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d).card
      ≤ xs.length + 1 := by
  set D : (ZMod macPrime)[X] := macPoly ys - macPoly xs - C d with hD
  have hD0 : D ≠ 0 := by
    intro h0
    apply hne
    have : macPoly ys - macPoly xs = C d := by rw [hD] at h0; exact sub_eq_zero.mp h0
    exact (eq_of_macPoly_sub_eq_C ys xs hlen.symm hy hx d this).symm
  have hdeg : D.natDegree ≤ xs.length := by
    rw [hD]
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_C, max_eq_left (Nat.zero_le _)]
    refine (natDegree_sub_le _ _).trans ?_
    exact max_le (hlen ▸ natDegree_macPoly_le ys) (natDegree_macPoly_le xs)
  have hsub : ((Finset.range (2 ^ 61)).filter fun k =>
        ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d) ⊆
      insert macPrime (D.roots.toFinset.image ZMod.val) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk61, hkd⟩ := hk
    by_cases hkp : k = macPrime
    · rw [hkp]; exact Finset.mem_insert_self _ _
    · have hlt : k < macPrime := by
        have : macPrime + 1 = 2 ^ 61 := by decide
        omega
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(k : ZMod macPrime), ?_, ZMod.val_natCast_of_lt hlt⟩)
      rw [Multiset.mem_toFinset, mem_roots hD0, IsRoot.def, hD]
      simp only [eval_sub, eval_C]
      rw [← polyMac_cast, ← polyMac_cast, hkd, sub_self]
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ?_ 1
  refine Finset.card_image_le.trans ?_
  refine (Multiset.toFinset_card_le _).trans ?_
  exact (card_roots' D).trans hdeg
theorem answerOfWords_toNat (w0 w1 w2 w3 : BitVec 64) :
    (answerOfWords w0 w1 w2 w3).toNat =
      w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat := by
  change (BitVec.ofNat 256 (w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat)).toNat = _
  rw [BitVec.toNat_ofNat]
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  apply Nat.mod_eq_of_lt
  show _ < 2 ^ 256
  omega
theorem extract_answerOfWords (w0 w1 w2 w3 : BitVec 64) :
    (answerOfWords w0 w1 w2 w3).extractLsb' 0 64 = w0 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 64 64 = w1 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 128 64 = w2 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 192 64 = w3 := by
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, answerOfWords_toNat, Nat.shiftRight_eq_div_pow]
    omega
theorem answerOfWords_extract (a : HashOutput) :
    answerOfWords (a.extractLsb' 0 64) (a.extractLsb' 64 64) (a.extractLsb' 128 64) (a.extractLsb' 192 64) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [answerOfWords_toNat]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have : a.toNat < 2 ^ 256 := a.isLt
  omega
noncomputable def tagResidue (delta : BitVec 64) : ZMod macPrime :=
  if delta.toNat < 2 ^ 63 then (delta.toNat : ZMod macPrime)
  else (delta.toNat : ZMod macPrime) - ((2 ^ 64 : Nat) : ZMod macPrime)
theorem residue_of_tag_eq (ux uy : Nat) (hx : ux < 2 ^ 61) (hy : uy < 2 ^ 61) (t t' : BitVec 64)
    (h : BitVec.ofNat 64 uy + (t - BitVec.ofNat 64 ux) = t') :
    ((uy : Nat) : ZMod macPrime) - ((ux : Nat) : ZMod macPrime) = tagResidue (t' - t) := by
  have hd : BitVec.ofNat 64 uy - BitVec.ofNat 64 ux = t' - t := by rw [← h]; ring
  have hn := congrArg BitVec.toNat hd
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show ux < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show uy < 2 ^ 64 by omega)] at hn
  unfold tagResidue
  have hlt := (t' - t).isLt
  generalize (t' - t).toNat = dn at hn hlt ⊢
  split
  · have hu : uy = ux + dn := by omega
    rw [hu]; push_cast; ring
  · have hu : uy + 2 ^ 64 = ux + dn := by omega
    have h2 : ((uy + 2 ^ 64 : Nat) : ZMod macPrime) = ((ux + dn : Nat) : ZMod macPrime) := by rw [hu]
    push_cast at h2 ⊢
    linear_combination h2
theorem polyMac_lt_pow (k : Nat) (cs : List Nat) : polyMac k cs < 2 ^ 61 := polyMac_lt' k cs
theorem card_lowWords_le (B : Finset Nat) :
    (Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ B).card ≤ 8 * B.card := by
  classical
  have hsub : (Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ B) ⊆
      (B ×ˢ Finset.range 8).image fun p : Nat × Nat => BitVec.ofNat 64 (p.1 + 2 ^ 61 * p.2) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    refine Finset.mem_image.mpr ⟨(w.toNat % 2 ^ 61, w.toNat / 2 ^ 61), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range]
      have := w.isLt
      exact ⟨hw.2, by omega⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have := w.isLt
      omega
  calc _ ≤ ((B ×ˢ Finset.range 8).image fun p : Nat × Nat => BitVec.ofNat 64 (p.1 + 2 ^ 61 * p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (B ×ˢ Finset.range 8).card := Finset.card_image_le
    _ = 8 * B.card := by rw [Finset.card_product, Finset.card_range, Nat.mul_comm]
noncomputable def badKeys (xs ys : List Nat) (d : ZMod macPrime) : Finset Nat :=
  (Finset.range (2 ^ 61)).filter fun k =>
    ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d
noncomputable def badWords (xs ys : List Nat) (d : ZMod macPrime) : Finset (BitVec 64) :=
  Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ badKeys xs ys d
theorem card_badWords_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (d : ZMod macPrime) :
    (badWords xs ys d).card ≤ 8 * (xs.length + 1) :=
  (card_lowWords_le (badKeys xs ys d)).trans
    (Nat.mul_le_mul_left 8 (card_polyMac_diff_le xs ys hlen hne hx hy d))
theorem chunks32_lt (data : HashInput) : ∀ c ∈ chunks32 data, c < 2 ^ 32 := by
  induction data using chunks32.induct with
  | case1 b0 b1 b2 b3 rest ih =>
      intro c hc
      rw [chunks32] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
        omega
      · exact ih c hc
  | case2 data hne =>
      intro c hc
      rw [chunks32.eq_2 _ hne] at hc
      simp at hc
theorem chunks32_length (data : HashInput) : (chunks32 data).length = data.length / 4 := by
  induction data using chunks32.induct with
  | case1 b0 b1 b2 b3 rest ih =>
      rw [chunks32, List.length_cons, ih]
      simp only [List.length_cons]
      omega
  | case2 data hne =>
      rw [chunks32.eq_2 _ hne, List.length_nil]
      match data, hne with
      | [], _ => rfl
      | [_], _ => simp
      | [_, _], _ => simp
      | [_, _, _], _ => simp
      | a :: b :: c :: d :: r, hne => exact (hne a b c d r rfl).elim
theorem chunks32_injective : ∀ (a b : HashInput), a.length = b.length → 4 ∣ a.length →
    chunks32 a = chunks32 b → a = b := by
  intro a
  induction a using chunks32.induct with
  | case1 a0 a1 a2 a3 rest ih =>
      intro b hlen hdvd h
      match b, hlen with
      | b0 :: b1 :: b2 :: b3 :: rb, hlen =>
          rw [chunks32, chunks32, List.cons.injEq] at h
          obtain ⟨hc, hr⟩ := h
          have hrest := ih rb (by simpa using hlen) (by
            have : (a0 :: a1 :: a2 :: a3 :: rest).length = rest.length + 4 := by simp
            rw [this] at hdvd
            exact (Nat.dvd_add_left (dvd_refl 4)).mp hdvd) hr
          have h0 := a0.toNat_lt; have h1 := a1.toNat_lt; have h2 := a2.toNat_lt; have h3 := a3.toNat_lt
          have g0 := b0.toNat_lt; have g1 := b1.toNat_lt; have g2 := b2.toNat_lt; have g3 := b3.toNat_lt
          have e0 : a0 = b0 := UInt8.toNat_inj.mp (by omega)
          have e1 : a1 = b1 := UInt8.toNat_inj.mp (by omega)
          have e2 : a2 = b2 := UInt8.toNat_inj.mp (by omega)
          have e3 : a3 = b3 := UInt8.toNat_inj.mp (by omega)
          rw [e0, e1, e2, e3, hrest]
      | [], hlen => simp at hlen
      | [_], hlen => simp at hlen
      | [_, _], hlen => simp at hlen
      | [_, _, _], hlen => simp at hlen
  | case2 a hne =>
      intro b hlen hdvd _
      have ha : a = [] := by
        match a, hne, hdvd with
        | [], _, _ => rfl
        | [_], _, hd => simp at hd
        | [_, _], _, hd => simp at hd
        | [_, _, _], _, hd => simp at hd
        | x :: y :: z :: w :: r, hne, _ => exact (hne x y z w r rfl).elim
      subst ha
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
theorem chunks32_lt_macPrime (data : HashInput) : ∀ c ∈ chunks32 data, c < macPrime := fun c hc =>
  (chunks32_lt data c hc).trans (by decide)
end SphincsSecurity
