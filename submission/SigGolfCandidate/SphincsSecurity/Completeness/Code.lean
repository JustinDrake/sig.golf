import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# How many digests the target-sum code accepts

The signer's counter search succeeds on a digest whose 42 three-bit digits sum to `T = 181` and
whose two padding bits are clear, so the search's failure probability is governed by how many of
the `2^128` digests that is. The count is the coefficient of `z^181` in `(1 + z + ... + z^7)^42`,
about `2^117.002`: at least one digest in `codeShare = 2397`.

Counting it is one identity and one division. Packing the polynomial into a single natural number
in base `2^128`, which is above every coefficient, turns the product of the `42` factors into a
`Nat` power and the coefficient into one of its digits, so the kernel evaluates the whole count as
ordinary arithmetic on one large numeral.
-/

open Finset

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

open TargetSum


/-- A base above every coefficient, so the coefficients are the digits. -/
def base : Nat := 2 ^ 128

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem weight_pow (B : Nat) :
    (∑ d : Digit, B ^ d.val) ^ numChains = ∑ x : Encoding, B ^ (TargetSum.sum x) := by
  have hcard : (Finset.univ : Finset ChainIndex).card = numChains := by
    simp [Finset.card_univ]
  have h1 : (∑ d : Digit, B ^ d.val) ^ numChains
      = ∏ _i : ChainIndex, ∑ d : Digit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl


/-- The number of codewords of digit sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => TargetSum.sum x = s)).card

theorem sum_lt_295 (x : Encoding) : TargetSum.sum x < 295 := by
  have : TargetSum.sum x ≤ ∑ _i : ChainIndex, 7 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  have hcard : Fintype.card ChainIndex = 42 := by simp [numChains]
  rw [hcard] at this
  omega

theorem sum_encoding_pow (B : Nat) :
    ∑ x : Encoding, B ^ (TargetSum.sum x) = ∑ s ∈ range 295, codeCount s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := TargetSum.sum) (t := range 295)
    (fun x _ => Finset.mem_range.mpr (sum_lt_295 x)) (fun x => B ^ (TargetSum.sum x))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, codeCount, smul_eq_mul]

theorem codeCount_lt_base (s : Nat) : codeCount s < base := by
  have h : codeCount s ≤ Fintype.card Encoding := Finset.card_filter_le _ _
  have hcard : Fintype.card Encoding = 8 ^ 42 := by
    simp [numChains, chainLength, winternitzBits]
  rw [hcard] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem weight_eq : (∑ d : Digit, base ^ d.val) = (base ^ 8 - 1) / (base - 1) := by decide

theorem codeCount_target :
    codeCount targetSum = (∑ d : Digit, base ^ d.val) ^ numChains / base ^ targetSum % base := by
  rw [weight_pow, sum_encoding_pow]
  exact (digit_of_sum base (by decide) codeCount codeCount_lt_base 295 targetSum (by decide)).symm

/-- One digest in `codeShare` or more is a codeword. -/
def codeShare : Nat := 2397

theorem digests_le_codeShare_mul_codeCount : 2 ^ 128 ≤ codeShare * codeCount targetSum := by
  rw [codeCount_target, weight_eq]
  decide


/-- A bounded-digit sum stays below the next power. -/
theorem sum_digits_lt (B : Nat) (hB : 0 < B) (v : Nat → Nat) (hv : ∀ j, v j < B) :
    ∀ n, ∑ j ∈ range n, v j * B ^ j < B ^ n := by
  intro n
  induction n with
  | zero => simpa using hB
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hle : v n * B ^ n ≤ (B - 1) * B ^ n :=
        Nat.mul_le_mul_right _ (by have := hv n; omega)
      have : B ^ n * B = (B - 1) * B ^ n + B ^ n := by
        cases B with
        | zero => omega
        | succ b => simp [Nat.succ_sub_one]; ring
      omega

def packHalf (v : Nat → Nat) : Nat := ∑ j ∈ range 21, v j * 8 ^ j

def lowDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < 21 then (x ⟨j, by simp only [numChains]; omega⟩).val else 0

def highDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < 21 then (x ⟨21 + j, by simp only [numChains]; omega⟩).val else 0

theorem lowDigit_lt (x : Encoding) (j : Nat) : lowDigit x j < 8 := by
  unfold lowDigit
  split
  · exact (x _).isLt
  · decide

theorem highDigit_lt (x : Encoding) (j : Nat) : highDigit x j < 8 := by
  unfold highDigit
  split
  · exact (x _).isLt
  · decide

theorem packHalf_lt (v : Nat → Nat) (hv : ∀ j, v j < 8) : packHalf v < 2 ^ 63 := by
  have h := sum_digits_lt 8 (by decide) v hv 21
  simpa [packHalf, show (8 : Nat) ^ 21 = 2 ^ 63 by norm_num] using h

theorem packHalf_digit (v : Nat → Nat) (hv : ∀ j, v j < 8) (k : Nat) (hk : k < 21) :
    packHalf v / 8 ^ k % 8 = v k :=
  digit_of_sum 8 (by decide) v hv 21 k hk

def packNat (x : Encoding) : Nat := packHalf (lowDigit x) + 2 ^ 64 * packHalf (highDigit x)

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hhigh := packHalf_lt _ (highDigit_lt x)
  have hmul : 2 ^ 64 * packHalf (highDigit x) ≤ 2 ^ 64 * 2 ^ 63 :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hhigh)
  have hpow : (2 : Nat) ^ 64 * 2 ^ 63 = 2 ^ 127 := by rw [← pow_add]
  have hbound : (2 : Nat) ^ 127 + 2 ^ 63 < 2 ^ 128 := by norm_num
  rw [hpow] at hmul
  unfold packNat
  omega

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [digestBits] using packNat_lt x)]

theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 8 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

theorem low_field (A B k : Nat) (hk : k < 21) :
    (A + 2 ^ 64 * B) / 2 ^ (3 * k) % 8 = A / 2 ^ (3 * k) % 8 := by
  have hsplit : 2 ^ 64 * B = 2 ^ (3 * k) * (8 * (2 ^ (61 - 3 * k) * B)) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (3 * k)), Nat.mul_comm 8,
    Nat.add_mul_mod_self_right]

theorem high_field (A B k : Nat) (hA : A < 2 ^ 64) :
    (A + 2 ^ 64 * B) / 2 ^ (64 + 3 * k) % 8 = B / 2 ^ (3 * k) % 8 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 64),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hA, Nat.zero_add]

theorem digitOffset_low (i : ChainIndex) (h : i.val < 21) : digitOffset i = 3 * i.val := by
  simp [digitOffset, digitsPerHalf, numChains, winternitzBits, h]

theorem digitOffset_high (i : ChainIndex) (h : ¬ i.val < 21) :
    digitOffset i = 64 + 3 * (i.val - 21) := by
  have hi : i.val < 42 := by simpa [numChains] using i.isLt
  simp only [digitOffset, digitsPerHalf, numChains, winternitzBits,
    show ¬ i.val < 42 / 2 from by omega, if_false]
  omega

theorem packNat_lt_two_pow_127 (x : Encoding) : packNat x < 2 ^ 127 := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hhigh := packHalf_lt _ (highDigit_lt x)
  have hmul : 2 ^ 64 * packHalf (highDigit x) ≤ 2 ^ 64 * (2 ^ 63 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpow : (2 : Nat) ^ 64 * (2 ^ 63 - 1) = 2 ^ 127 - 2 ^ 64 := by
    rw [Nat.mul_sub, ← pow_add]
    norm_num
  have hb : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  rw [hpow] at hmul
  have hle : (2 : Nat) ^ 64 ≤ 2 ^ 127 := by norm_num
  unfold packNat
  omega

theorem pack_padding_low (x : Encoding) : (pack x).getLsbD 63 = false := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hsplit : packNat x / 2 ^ 63 = 2 * packHalf (highDigit x) := by
    unfold packNat
    rw [show (2 : Nat) ^ 64 * packHalf (highDigit x) = 2 ^ 63 * (2 * packHalf (highDigit x)) by
      rw [← Nat.mul_assoc, show (2 : Nat) ^ 63 * 2 = 2 ^ 64 by norm_num]]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 63), Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hbit : (pack x).toNat.testBit 63 = false := by
    rw [toNat_pack, Nat.testBit_eq_decide_div_mod_eq, hsplit]
    simp [Nat.mul_mod_right]
  simpa [BitVec.getLsbD] using hbit

theorem pack_padding_high (x : Encoding) : (pack x).getLsbD 127 = false := by
  have hbit : (pack x).toNat.testBit 127 = false := by
    rw [toNat_pack]
    exact Nat.testBit_lt_two_pow (packNat_lt_two_pow_127 x)
  simpa [BitVec.getLsbD] using hbit

theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [encoding_val, toNat_pack]
  have hi42 : i.val < 42 := by simpa [numChains] using i.isLt
  by_cases hi : i.val < 21
  · rw [digitOffset_low i hi]
    unfold packNat
    rw [low_field _ _ _ hi,
      show (2 : Nat) ^ (3 * i.val) = 8 ^ i.val by rw [pow_mul]; norm_num,
      packHalf_digit _ (lowDigit_lt x) i.val hi, lowDigit, dif_pos hi]
  · have hlow := packHalf_lt _ (lowDigit_lt x)
    have hstep : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
    rw [digitOffset_high i hi]
    unfold packNat
    rw [high_field _ _ _ (by omega),
      show (2 : Nat) ^ (3 * (i.val - 21)) = 8 ^ (i.val - 21) by rw [pow_mul]; norm_num,
      packHalf_digit _ (highDigit_lt x) (i.val - 21) (by omega),
      highDigit, dif_pos (show i.val - 21 < 21 by omega)]
    congr 1
    exact congrArg x (Fin.ext (show 21 + (i.val - 21) = i.val by omega))

theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, if_pos ⟨pack_padding_low x, pack_padding_high x, by rw [digestEncoding_pack]; exact hx⟩,
    digestEncoding_pack]

/-- The signer's counter search accepts at least one in `codeShare` of the `2^128` digests. -/
theorem digests_le_codeShare_mul_card_accepting :
    2 ^ 128 ≤ codeShare * (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans digests_le_codeShare_mul_codeCount (Nat.mul_le_mul_left _ ?_)
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left hleft right hright heq
    have hl : Valid left := (Finset.mem_filter.mp hleft).2
    have hr : Valid right := (Finset.mem_filter.mp hright).2
    have := decodeDigest_pack left hl
    rw [heq, decodeDigest_pack right hr] at this
    exact (Option.some.inj this).symm

end SphincsSecurity.Completeness

/-!
## Alternate four-layer construction: radix-four code

This namespace is preparation for a different construction, not a change to the
certificate's production parameters.  It counts the actual antichain before
spending the signing budget on a machine implementation.  The proposed code has
62 digits in `Fin 4`; its 124 payload bits leave four zero padding bits in the
128-bit encoding output.  Four layers and a 17-tree, height-nine FORS forest would
use 7232 signature bytes.  No cycle estimate here is an execution measurement.
-/

namespace SigGolfCandidate.Base4Candidate

open Finset

abbrev Index := Fin 62
abbrev Digit := Fin 4
abbrev Word := Index → Digit

def weight (x : Word) : Nat := ∑ i, (x i).val
def Valid (x : Word) : Prop := weight x = 110
def count (s : Nat) : Nat := (univ.filter (fun x : Word => weight x = s)).card
def radix : Nat := 2 ^ 128

/-- The new code retains the componentwise antichain property. -/
theorem eq_of_le_of_valid {x y : Word} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  have hsum : weight x = weight y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : weight x < weight y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

theorem weight_lt (x : Word) : weight x < 187 := by
  have h : weight x ≤ ∑ _i : Index, 3 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem weighted_words (B : Nat) :
    (∑ d : Digit, B ^ d.val) ^ 62 = ∑ x : Word, B ^ weight x := by
  have hcard : (univ : Finset Index).card = 62 := by simp
  have h : (∑ d : Digit, B ^ d.val) ^ 62 =
      ∏ _i : Index, ∑ d : Digit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem collect_weights (B : Nat) :
    ∑ x : Word, B ^ weight x = ∑ s ∈ range 187, count s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := weight) (t := range 187)
    (fun x _ => Finset.mem_range.mpr (weight_lt x)) (fun x => B ^ weight x)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, count, smul_eq_mul]

theorem count_lt_radix (s : Nat) : count s < radix := by
  have h : count s ≤ Fintype.card Word := Finset.card_filter_le _ _
  have hc : Fintype.card Word = 4 ^ 62 := by simp [Word, Index, Digit]
  rw [hc] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem digit_weight : (∑ d : Digit, radix ^ d.val) =
    (radix ^ 4 - 1) / (radix - 1) := by decide

theorem count_coefficient (s : Nat) (hs : s < 187) :
    count s = ((radix ^ 4 - 1) / (radix - 1)) ^ 62 / radix ^ s % radix := by
  rw [← digit_weight, weighted_words, collect_weights]
  exact (SphincsSecurity.Completeness.digit_of_sum radix (by decide)
    count count_lt_radix 187 s hs).symm

/-- Exact accepted-code count; this is a finite combinatorial identity. -/
theorem count_110 : count 110 =
    150115833895609872634682265795824424 := by
  rw [count_coefficient 110 (by decide)]
  decide

/-- A conservative reciprocal share for the proposed counter search. -/
theorem counter_share : 2 ^ 128 ≤ 2267 * count 110 := by
  rw [count_110]
  decide

theorem signature_size : 16 * (1 + 4 * 62 + 33 + 17 * (9 + 1)) = 7232 := by decide

/-- Arithmetic costs assume the same paired PRF and internal-node cache strategy.
They are not yet refinements of alternate RISC-V images. -/
theorem keygen_arithmetic : 4096 * 234 - 1 + 4094 + 1025 = 963582 := by decide
theorem keygen_room : 963582 < 2 ^ 20 := by decide
theorem sign_arithmetic :
    3 * (128 * 234 - 1) + 17 * (512 * 5 / 2 - 1) + 5 +
      1025 + 31 + 110 + 233 + 11 = 113011 := by decide

end SigGolfCandidate.Base4Candidate
