import SigGolfCandidate.T3.FullCache.Retag
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

theorem mem_badWords_of_tag_eq (xs ys : List Nat) (key : MacKey) (tag tag' : MacTag) (j : Fin 4)
    (h : macTagOf (retag key xs tag) ys j = tag' j) :
    macLowWord key j ∈ badWords xs ys (tagResidue (tag' j - tag j)) := by
  unfold macTagOf at h
  rw [macKeyWord_retag] at h
  unfold retag at h
  rw [macPadWord_mk] at h
  have hres := residue_of_tag_eq _ _ (polyMac_lt_pow _ xs) (polyMac_lt_pow _ ys) _ _ h
  unfold badWords badKeys
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, ← macKeyWord_eq]
  refine ⟨Finset.mem_univ _, ?_, hres⟩
  rw [macKeyWord_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 61)



/-- **Forgeries are rare.** Among the keys retagged to `tag` on `xs`, those whose tag on a different chunk
list `ys` of the same length is `tag'` are at most `(8 (length + 1))^4` choices of low words, times the pads. -/
theorem card_retag_bad_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (tag tag' : MacTag) :
    Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'}
      ≤ (8 * (xs.length + 1)) ^ 4 * Fintype.card MacTag := by
  let f : {key : MacKey // macTagOf (retag key xs tag) ys = tag'} →
      ((j : Fin 4) → {w : BitVec 64 // w ∈ badWords xs ys (tagResidue (tag' j - tag j))}) × MacTag :=
    fun key => (fun j => ⟨macLowWord key.1 j,
      mem_badWords_of_tag_eq xs ys key.1 tag tag' j (congrFun key.2 j)⟩, macPadWord key.1)
  have hf : Function.Injective f := by
    intro k1 k2 h
    apply Subtype.ext
    have h1 : macLowWord k1.1 = macLowWord k2.1 := by
      funext j
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) j)
    have h2 : macPadWord k1.1 = macPadWord k2.1 := congrArg Prod.snd h
    rw [← mkMacKey_words k1.1, ← mkMacKey_words k2.1, h1, h2]
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_prod, Fintype.card_pi]
  refine Nat.mul_le_mul_right _ ?_
  simp only [Fintype.card_coe]
  refine (Finset.prod_le_prod' fun j _ => card_badWords_le xs ys hlen hne hx hy _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The polynomial MAC (probability) -/

theorem card_tagWord : Fintype.card (BitVec 64) = 2 ^ 64 := Fintype.card_bitVec 64

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := Fintype.card_bitVec hashOutputBits

theorem card_macTag : Fintype.card MacTag = (2 ^ 64) ^ 4 := by
  rw [Fintype.card_fun, card_tagWord, Fintype.card_fin]

theorem card_macKey : Fintype.card MacKey = (2 ^ 256) ^ 2 := by
  rw [Fintype.card_fun, card_hashOutput, Fintype.card_fin]

/-- Actual four-word retag acceptance bound for different equal-length chunks. -/
theorem probEvent_retag_bad_le [SampleableType MacKey] (xs ys : List Nat) (hlen : xs.length = ys.length)
    (hne : xs ≠ ys) (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime)
    (hL : xs.length + 1 ≤ 2 ^ 15) (tag tag' : MacTag) :
    Pr[fun key : MacKey => macTagOf (retag key xs tag) ys = tag' | $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, card_macKey]
  have hc := card_retag_bad_le xs ys hlen hne hx hy tag tag'
  rw [card_macTag] at hc
  have hn : Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} ≤ 2 ^ 328 := by
    refine hc.trans ?_
    calc (8 * (xs.length + 1)) ^ 4 * (2 ^ 64) ^ 4 ≤ (8 * 2 ^ 15) ^ 4 * (2 ^ 64) ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hL) 4)
      _ = 2 ^ 328 := by norm_num
  have hcast : ((Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} : ℕ) : ℝ≥0∞)
      ≤ (2 ^ 328 : ℝ≥0∞) := by exact_mod_cast hn
  refine ENNReal.div_le_of_le_mul (hcast.trans (le_of_eq ?_))
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show ((2 : ENNReal) ^ 256) ^ 2 = (2 : ENNReal) ^ 184 * 2 ^ 328 by
      rw [← pow_mul, ← pow_add],
    ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

end SiggolfT3Mac4
