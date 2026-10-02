import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Inputs
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# The cache's derivations: masks and MAC answers

Key generation masks the top tree's nodes with `mask(l, j)`, a seed derivation of domain tag `13`, and
authenticates the masked bytes with a polynomial MAC whose key is three more seed derivations, of tag `14`.
Both families are derivations of the seed, like the one-time secrets and the randomizers: their inputs carry
the seed in bytes `32` through `63`, so an adversary query that hits one is a seed guess. This file adds
them to the derivation cache, the masks and the MAC key answers each as one more keygen family, and proves
what the MAC elimination needs about the polynomial MAC: the law of a retagged key and the forgery bound.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

set_option backward.isDefEq.respectTransparency false

/-! ## The inputs -/

theorem length_flatten_ofFn_eq {α : Type} {n : Nat} (f g : Fin n → List α)
    (hlen : ∀ i, (f i).length = (g i).length) (h : (List.ofFn f).flatten = (List.ofFn g).flatten) : f = g := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (hlen 0)
      have htail' := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hlen i.succ) htail
      funext i
      cases i using Fin.cases with
      | zero => exact hhead
      | succ i => exact congrFun htail' i

theorem flatMap_bytesLE_ofFn_injective {n k : Nat} {f g : Fin n → BitVec (8 * k)}
    (h : (List.ofFn f).flatMap (bytesLE k) = (List.ofFn g).flatMap (bytesLE k)) : f = g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn] at h
  have hfun := length_flatten_ofFn_eq (fun i => bytesLE k (f i)) (fun i => bytesLE k (g i))
    (fun i => by simp [bytesLE_length]) h
  funext i
  exact bytesLE_injective (congrFun hfun i)

theorem regionBytes_injective : Function.Injective regionBytes := by
  intro left right h
  unfold regionBytes at h
  have hlevels := length_flatten_ofFn_eq _ _ (fun level => by
    simp [List.length_flatMap, bytesLE_length, Function.comp_def]) h
  funext level
  exact flatMap_bytesLE_ofFn_injective (congrFun hlevels level)

/-! ## The polynomial MAC (polynomial) -/

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

/-- The polynomial whose value at `k` is `polyMac k cs`. -/
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

/-- Two chunk lists of the same length with chunks below `p` whose polynomials differ by a constant are equal. -/
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
      -- the left side vanishes at `0`
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

/-- **The differential bound.** For different chunk lists of one length, at most `length + 1` keys below
`2^61` make the two hashes differ by the residue `d`. -/
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


/-! ## The polynomial MAC (key fields) -/

/-- The low word of key slot `j` (its low 61 bits are the key). -/
def macLowWord (key : MacKey) (j : Fin 6) : BitVec 64 :=
  (key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2)) 64

/-- One answer from its four words. -/
def answerOfWords (w0 w1 w2 w3 : BitVec 64) : HashOutput :=
  BitVec.ofNat hashOutputBits (w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat)

/-- The key with the given low words and pads. -/
def mkMacKey (lows pads : Fin 6 → BitVec 64) : MacKey := fun i =>
  answerOfWords (lows ⟨2 * i.val, by omega⟩) (pads ⟨2 * i.val, by omega⟩)
    (lows ⟨2 * i.val + 1, by omega⟩) (pads ⟨2 * i.val + 1, by omega⟩)

theorem answerOfWords_toNat (w0 w1 w2 w3 : BitVec 64) :
    (answerOfWords w0 w1 w2 w3).toNat =
      w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat := by
  unfold answerOfWords
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

theorem fin6_cases (j : Fin 6) : ∃ i : Fin 3, j = ⟨2 * i.val, by omega⟩ ∨ j = ⟨2 * i.val + 1, by omega⟩ := by
  refine ⟨⟨j.val / 2, by omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · left; apply Fin.ext; simp only; omega
  · right; apply Fin.ext; simp only; omega

theorem macLowWord_mk (lows pads : Fin 6 → BitVec 64) (j : Fin 6) : macLowWord (mkMacKey lows pads) j = lows j := by
  obtain ⟨hA, _, hC, _⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macLowWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero]
    rw [hA]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hC]; congr 1; apply Fin.ext; simp only; omega

theorem macPadWord_mk (lows pads : Fin 6 → BitVec 64) (j : Fin 6) : macPadWord (mkMacKey lows pads) j = pads j := by
  obtain ⟨_, hB, _, hD⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macPadWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero, Nat.zero_add]
    rw [hB]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hD]; congr 1; apply Fin.ext; simp only; omega

theorem mkMacKey_words (key : MacKey) : mkMacKey (macLowWord key) (macPadWord key) = key := by
  funext i
  unfold mkMacKey macLowWord macPadWord
  have h0 : (2 * i.val) / 2 = i.val := by omega
  have h1 : (2 * i.val + 1) / 2 = i.val := by omega
  have m0 : (2 * i.val) % 2 = 0 := by omega
  have m1 : (2 * i.val + 1) % 2 = 1 := by omega
  simp only [h0, h1, m0, m1, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Fin.eta]
  exact answerOfWords_extract (key i)

theorem macKeyWord_eq (key : MacKey) (j : Fin 6) : macKeyWord key j = (macLowWord key j).toNat % 2 ^ 61 := by
  unfold macKeyWord macLowWord
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have : (key ⟨j.val / 2, by omega⟩).toNat < 2 ^ 256 := (key ⟨j.val / 2, by omega⟩).isLt
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp only [h, Nat.mul_zero, Nat.mul_one] <;> omega

theorem macKeyWord_mk (lows pads : Fin 6 → BitVec 64) (j : Fin 6) :
    macKeyWord (mkMacKey lows pads) j = (lows j).toNat % 2 ^ 61 := by
  rw [macKeyWord_eq, macLowWord_mk]




/-! ## The polynomial MAC (tags and the law of a retagged key) -/

/-- The tag of a chunk list. -/
def macTagOf (key : MacKey) (chunks : List Nat) : MacTag :=
  fun j => BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks) + macPadWord key j

theorem macTag_eq (key : MacKey) (data : HashInput) : macTag key data = macTagOf key (chunks32 data) := rfl

/-- The key with the low words of `key` whose tag on `chunks` is `tag`. -/
def retag (key : MacKey) (chunks : List Nat) (tag : MacTag) : MacKey :=
  mkMacKey (macLowWord key) fun j => tag j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)

theorem macLowWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macLowWord (retag key chunks tag) = macLowWord key := by
  funext j; exact macLowWord_mk _ _ j

theorem macKeyWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) (j : Fin 6) :
    macKeyWord (retag key chunks tag) j = macKeyWord key j := by
  rw [macKeyWord_eq, macKeyWord_eq, macLowWord_retag]

theorem macTagOf_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macTagOf (retag key chunks tag) chunks = tag := by
  funext j
  unfold macTagOf
  rw [macKeyWord_retag]
  unfold retag
  rw [macPadWord_mk]
  exact add_sub_cancel _ _

theorem retag_macTagOf (key : MacKey) (chunks : List Nat) : retag key chunks (macTagOf key chunks) = key := by
  unfold retag
  have hp : (fun j => macTagOf key chunks j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)) =
      macPadWord key := by
    funext j; unfold macTagOf; exact add_sub_cancel_left _ _
  rw [hp, mkMacKey_words]

/-- A key with the low words of `h` retags to `h` at `h`'s own tag. -/
theorem retag_mk_eq (h : MacKey) (chunks : List Nat) (pads : MacTag) :
    retag (mkMacKey (macLowWord h) pads) chunks (macTagOf h chunks) = h := by
  have hl : macLowWord (mkMacKey (macLowWord h) pads) = macLowWord h := by
    funext j; exact macLowWord_mk _ _ j
  have hk : ∀ j, macKeyWord (mkMacKey (macLowWord h) pads) j = macKeyWord h j := by
    intro j; rw [macKeyWord_eq, macKeyWord_eq, hl]
  have := retag_macTagOf h chunks
  unfold retag at this ⊢
  rw [hl]
  simp only [hk]
  exact this

/-- **The law of a retagged key.** A uniform key is a uniform key whose pads are replaced so that its tag on
`chunks` is an independent uniform tag: the published tag is uniform and independent of the low words. -/
theorem evalSPMF_uniformSample_bind_retag [SampleableType MacTag] [SampleableType MacKey] (chunks : List Nat) :
    𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (retag key chunks tag)] = 𝒮[$ᵗ MacKey] := by
  classical
  refine evalSPMF_ext fun h => ?_
  rw [probOutput_uniformSample MacKey h, probOutput_bind_eq_sum_fintype]
  have hinner : ∀ tag : MacTag,
      Pr[= h | (do let key ← $ᵗ MacKey; pure (retag key chunks tag))]
        = (if tag = macTagOf h chunks then
            (Fintype.card MacTag : ℝ≥0∞) * (Fintype.card MacKey : ℝ≥0∞)⁻¹ else 0) := by
    intro tag
    rw [bind_pure_comp, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample MacKey]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun key : MacKey => h = retag key chunks tag).card : ℝ≥0∞)
          = if tag = macTagOf h chunks then (Fintype.card MacTag : ℝ≥0∞) else 0 := by
      by_cases ht : tag = macTagOf h chunks
      · have hset : (Finset.univ.filter fun key : MacKey => h = retag key chunks tag)
            = Finset.univ.image (fun pads : MacTag => mkMacKey (macLowWord h) pads) := by
          ext key
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hk
            refine ⟨macPadWord key, ?_⟩
            have hl : macLowWord h = macLowWord key := by rw [hk, macLowWord_retag]
            rw [hl, mkMacKey_words]
          · rintro ⟨pads, rfl⟩
            rw [ht]
            exact (retag_mk_eq h chunks pads).symm
        rw [hset, Finset.card_image_of_injective _ (fun p q hpq => by
              funext j
              have := congrArg (fun k => macPadWord k j) hpq
              simpa only [macPadWord_mk] using this),
            Finset.card_univ, if_pos ht]
      · rw [if_neg ht, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro key - rfl
        exact ht (macTagOf_retag key chunks tag).symm
    rw [hcard, ite_mul, zero_mul]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (macTagOf h chunks), if_pos (Finset.mem_univ _),
      probOutput_uniformSample MacTag, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

/-! ## The polynomial MAC (forgeries) -/

/-- The residue a 64-bit tag difference forces on the difference of two hashes below `2^61`. -/
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

/-- The low words whose key (their low 61 bits) lies in a set of at most `n` keys: at most `8 n` words. -/
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

/-- The keys below `2^61` at which the hashes of `xs` and `ys` differ by the residue `d`. -/
noncomputable def badKeys (xs ys : List Nat) (d : ZMod macPrime) : Finset Nat :=
  (Finset.range (2 ^ 61)).filter fun k =>
    ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d

/-- The low words whose key lies in `badKeys`. -/
noncomputable def badWords (xs ys : List Nat) (d : ZMod macPrime) : Finset (BitVec 64) :=
  Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ badKeys xs ys d

theorem card_badWords_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (d : ZMod macPrime) :
    (badWords xs ys d).card ≤ 8 * (xs.length + 1) :=
  (card_lowWords_le (badKeys xs ys d)).trans
    (Nat.mul_le_mul_left 8 (card_polyMac_diff_le xs ys hlen hne hx hy d))

theorem mem_badWords_of_tag_eq (xs ys : List Nat) (key : MacKey) (tag tag' : MacTag) (j : Fin 6)
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

attribute [irreducible] badKeys badWords

/-- **Forgeries are rare.** Among the keys retagged to `tag` on `xs`, those whose tag on a different chunk
list `ys` of the same length is `tag'` are at most `(8 (length + 1))^6` choices of low words, times the pads. -/
theorem card_retag_bad_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (tag tag' : MacTag) :
    Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'}
      ≤ (8 * (xs.length + 1)) ^ 6 * Fintype.card MacTag := by
  let f : {key : MacKey // macTagOf (retag key xs tag) ys = tag'} →
      ((j : Fin 6) → {w : BitVec 64 // w ∈ badWords xs ys (tagResidue (tag' j - tag j))}) × MacTag :=
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

theorem card_macTag : Fintype.card MacTag = (2 ^ 64) ^ 6 := by
  rw [Fintype.card_fun, card_tagWord, Fintype.card_fin]

theorem card_macKey : Fintype.card MacKey = (2 ^ 256) ^ 3 := by
  rw [Fintype.card_fun, card_hashOutput, Fintype.card_fin]

/-- **A forged tag is accepted with probability at most `2^-256`.** The key is uniform; it is retagged to the
published `tag` on the published chunks `xs`; the forgery is a different chunk list `ys` of the same length
with any tag `tag'`. -/
theorem probEvent_retag_bad_le [SampleableType MacKey] (xs ys : List Nat) (hlen : xs.length = ys.length)
    (hne : xs ≠ ys) (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime)
    (hL : xs.length + 1 ≤ 2 ^ 14) (tag tag' : MacTag) :
    Pr[fun key : MacKey => macTagOf (retag key xs tag) ys = tag' | $ᵗ MacKey] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, card_macKey]
  have hc := card_retag_bad_le xs ys hlen hne hx hy tag tag'
  rw [card_macTag] at hc
  have hn : Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} ≤ (2 ^ 256) ^ 2 := by
    refine hc.trans ?_
    calc (8 * (xs.length + 1)) ^ 6 * (2 ^ 64) ^ 6 ≤ (8 * 2 ^ 14) ^ 6 * (2 ^ 64) ^ 6 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hL) 6)
      _ ≤ (2 ^ 256) ^ 2 := by norm_num
  have hcast : ((Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} : ℕ) : ℝ≥0∞)
      ≤ (((2 ^ 256) ^ 2 : ℕ) : ℝ≥0∞) := by exact_mod_cast hn
  refine ENNReal.div_le_of_le_mul (hcast.trans (le_of_eq ?_))
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show ((2 : ℝ≥0∞) ^ 256) ^ 3 = (2 ^ 256) * ((2 ^ 256) ^ 2) by ring, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ## The polynomial MAC (chunks) -/

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

/-- Byte strings of one length divisible by four with the same chunks are equal. -/
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

/-! ## The authenticated bytes -/

theorem length_flatMap_bytesLE {n k : Nat} (f : Fin n → BitVec (8 * k)) :
    ((List.ofFn f).flatMap (bytesLE k)).length = k * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.flatMap_cons, List.length_append, bytesLE_length, ih, Nat.mul_succ,
        Nat.add_comm]

theorem length_flatMap_digest {n : Nat} (f : Fin n → Digest) :
    ((List.ofFn f).flatMap (bytesLE 16)).length = 16 * n :=
  length_flatMap_bytesLE (k := 16) f

theorem regionBytes_length (region : TopRegion) : (regionBytes region).length = 65504 := by
  unfold regionBytes
  rw [List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, length_flatMap_digest]
  decide

/-- The chunks of two different regions differ. -/
theorem chunks32_regionBytes_ne {r₁ r₂ : TopRegion} (h : r₁ ≠ r₂) :
    chunks32 (regionBytes r₁) ≠ chunks32 (regionBytes r₂) := fun hc =>
  h (regionBytes_injective (chunks32_injective _ _
    ((regionBytes_length r₁).trans (regionBytes_length r₂).symm)
    (by rw [regionBytes_length]; decide) hc))

theorem chunks32_regionBytes_length (region : TopRegion) :
    (chunks32 (regionBytes region)).length = 16376 := by
  rw [chunks32_length, regionBytes_length]

theorem chunks32_lt_macPrime (data : HashInput) : ∀ c ∈ chunks32 data, c < macPrime := fun c hc =>
  (chunks32_lt data c hc).trans (by decide)

namespace Seeded

/-! ## The mask table -/

/-- A mask position: a level below the root and a node index. Positions outside the region hold masks
nothing reads. -/
abbrev MaskPosition := Fin maxLayerHeight × Fin (2 ^ maxLayerHeight)
abbrev MaskOutputs := MaskPosition → HashOutput

noncomputable opaque maskOutputsSampleableType : SampleableType MaskOutputs :=
  SampleableType.ofFintype MaskOutputs

noncomputable instance : SampleableType MaskOutputs := maskOutputsSampleableType

noncomputable def sampleMaskOutputs : ProbComp MaskOutputs := $ᵗ MaskOutputs

/-- The position `maskDomain level nodeIdx` derives. -/
def maskPosition (level nodeIdx : Nat) : MaskPosition :=
  (⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩, ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩)

def maskInputs (parameter : PublicParameter) (seed : MasterSeed) (position : MaskPosition) : HashInput :=
  keygenHashInput parameter (.mask position.1 position.2) seed

theorem maskInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (maskInputs parameter seed) := by
  intro left right h
  have hdomain := (keygenHashInput_injective h).2.1
  simp only [KeygenDomain.mask.injEq] at hdomain
  exact Prod.ext hdomain.1 hdomain.2

theorem maskSecret_input (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) :
    keygenHashInput parameter (maskDomain level nodeIdx) seed = maskInputs parameter seed (maskPosition level nodeIdx) :=
  rfl

/-- The mask the table assigns to node `(l, j)`. -/
def maskValue (masks : MaskOutputs) (level nodeIdx : Nat) : Digest :=
  truncateHash (masks (maskPosition level nodeIdx))

/-! ## The MAC key table -/

/-- The three answers that key the MAC. -/
abbrev MacOutputs := MacKey

noncomputable opaque macOutputsSampleableType : SampleableType MacOutputs :=
  SampleableType.ofFintype MacOutputs

noncomputable instance : SampleableType MacOutputs := macOutputsSampleableType

noncomputable def sampleMacOutputs : ProbComp MacOutputs := $ᵗ MacOutputs

noncomputable opaque macTagSampleableType : SampleableType MacTag :=
  SampleableType.ofFintype MacTag

noncomputable instance : SampleableType MacTag := macTagSampleableType

def macInputs (parameter : PublicParameter) (seed : MasterSeed) (index : Fin 3) : HashInput :=
  keygenHashInput parameter (.mackey index) seed

theorem macInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (macInputs parameter seed) := by
  intro left right h
  have hdomain := (keygenHashInput_injective h).2.1
  simpa only [KeygenDomain.mackey.injEq] using hdomain

/-! ## The full derivation cache -/

/-- The secrets, the randomizers and the masks. -/
noncomputable def maskedDerivationCache (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) : QueryCache HashSpec :=
  cacheTable (signingDerivationCache seed outputs randomizers) (maskInputs 0 seed) masks

/-- Every derivation of the seed: secrets, randomizers, masks and MAC answers. -/
noncomputable def cachedDerivationCache (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) : QueryCache HashSpec :=
  cacheTable (maskedDerivationCache seed outputs randomizers masks) (macInputs 0 seed) macs

theorem signingDerivationCache_mask_fresh (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (position : MaskPosition) :
    signingDerivationCache seed outputs randomizers (maskInputs 0 seed position) = none := by
  unfold signingDerivationCache derivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · rfl
  · intro secret h
    have := (keygenHashInput_injective h).2.1
    cases secret <;> simp [secretDomain] at this
  · intro randomizer h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h.symm

theorem maskedDerivationCache_mac_fresh (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (index : Fin 3) :
    maskedDerivationCache seed outputs randomizers masks (macInputs 0 seed index) = none := by
  unfold maskedDerivationCache signingDerivationCache derivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · rfl
  · intro secret h
    have := (keygenHashInput_injective h).2.1
    cases secret <;> simp [secretDomain] at this
  · intro randomizer h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h.symm
  · intro position h
    have := (keygenHashInput_injective h).2.1
    simp at this

theorem cachedDerivationCache_mac (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (index : Fin 3) :
    cachedDerivationCache seed outputs randomizers masks macs (macInputs 0 seed index) = some (macs index) :=
  cacheTable_apply _ _ (macInputs_injective _ _) _ _

theorem cachedDerivationCache_mask (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : MaskPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (maskInputs 0 seed position) =
      some (masks position) := by
  unfold cachedDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · exact cacheTable_apply _ _ (maskInputs_injective _ _) _ _
  · intro index h
    have := (keygenHashInput_injective h).2.1
    simp at this

theorem cachedDerivationCache_randomizer (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : RandomizerPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (randomizerInputs 0 seed position) =
      some (randomizers position) := by
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_randomizer _ _ _ _
  · intro mask h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h
  · intro index h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h

theorem cachedDerivationCache_secret (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : SecretPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (secretInputs 0 seed position) =
      some (outputs position) := by
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_secret _ _ _ _
  · intro mask h
    have := (keygenHashInput_injective h).2.1
    cases position <;> simp [secretDomain] at this
  · intro index h
    have := (keygenHashInput_injective h).2.1
    cases position <;> simp [secretDomain] at this

theorem cachedDerivationCache_agreeOutside (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) :
    AgreeOutside (fun input => SeedHit input seed) (cachedDerivationCache seed outputs randomizers masks macs) ∅ := by
  intro input hinput
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_agreeOutside seed outputs randomizers input hinput
  · intro position heq
    exact hinput (heq.symm ▸ derivationSeedHit_keygen 0 _ seed)
  · intro index heq
    exact hinput (heq.symm ▸ derivationSeedHit_keygen 0 _ seed)

noncomputable def prepareMasks (seed : MasterSeed) : OracleComp HashSpec MaskOutputs :=
  queryTable (maskInputs 0 seed)

theorem evalDist_prepareMasks (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    𝒮[(simulateQ randomOracle (prepareMasks seed)).run (signingDerivationCache seed outputs randomizers)] =
        𝒮[(fun masks => (masks, maskedDerivationCache seed outputs randomizers masks)) <$> sampleMaskOutputs] :=
  evalDist_queryTable_fresh _ (maskInputs_injective _ seed) _
    (signingDerivationCache_mask_fresh seed outputs randomizers)

noncomputable def prepareMacs (seed : MasterSeed) : OracleComp HashSpec MacOutputs :=
  queryTable (macInputs 0 seed)

theorem evalDist_prepareMacs (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (masks : MaskOutputs) :
    𝒮[(simulateQ randomOracle (prepareMacs seed)).run (maskedDerivationCache seed outputs randomizers masks)] =
        𝒮[(fun macs => (macs, cachedDerivationCache seed outputs randomizers masks macs)) <$> sampleMacOutputs] :=
  evalDist_queryTable_fresh _ (macInputs_injective _ seed) _
    (maskedDerivationCache_mac_fresh seed outputs randomizers masks)

end Seeded

end SphincsSecurity
