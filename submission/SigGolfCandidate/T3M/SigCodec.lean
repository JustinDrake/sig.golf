import SigGolfCandidate.T3M.Bytes

/-!
# The signature codec (stream E)

Core's signature `T3.Signature` is 357 digests (`rho`, 21 secrets, 117 proof slots, then for each layer
its chain values and Merkle path); `serialize` writes them as 5,712 little-endian bytes. The organizer's
signature object is `Legacy.Bytes 5712`. This module is the bijection between the two:

* `sigDigests s` : the 357 digests in `serialize` order, `serialize_eq : serialize s = (sigDigests s).flatMap (bytesLE 16)`;
* `sigB s : Bytes 5712` (the little-endian value of `serialize s`) and `sigDec b : Signature` (digest `k`
  of the signature is `sigDig b k = b.extractLsb' (128 k) 128`);
* `sigDec_sigB : sigDec (sigB s) = s` and `sigB_sigDec : sigB (sigDec b) = b` (every 5,712-byte string
  decodes); `sigB_injective`, `sigDec_injective`;
* the digest index of each field: `rho` 0, secret `i` at `1 + i`, proof slot `j` at `22 + j`, layer `lay`'s
  chain value `i` at `layIdx lay + i` and Merkle sibling `j` at `layIdx lay + chainCount lay + j`
  (`layIdx` = 139, 209, 259, 308, i.e. byte offsets 2224, 3344, 4144, 4928);
* the doubleword view `sigDig_lo/hi` used by the machine proofs (the signature buffer at `0x7000`
  holds `b.extractLsb' (64 j) 64` at `0x7000 + 8 j`).
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Digest lists as numbers -/

/-- The little-endian value of a list of digests (`readLE` of their bytes). -/
def digNat (ds : List Digest) : Nat := readLE (ds.flatMap (bytesLE 16))

theorem digNat_nil : digNat [] = 0 := rfl

theorem digNat_cons (d : Digest) (ds : List Digest) :
    digNat (d :: ds) = d.toNat + 2 ^ 128 * digNat ds := by
  unfold digNat
  rw [List.flatMap_cons, readLE_append, readLE_bytesLE, bytesLE_length]
  norm_num

theorem digNat_lt (ds : List Digest) : digNat ds < 2 ^ (128 * ds.length) := by
  induction ds with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    rw [digNat_cons, List.length_cons, show 128 * (ds.length + 1) = 128 + 128 * ds.length by ring,
      pow_add]
    have := d.isLt
    nlinarith

/-- Digit `k` (base `2^128`) of `digNat ds` is the `k`-th digest (zero past the end). -/
theorem digNat_digit (ds : List Digest) (k : Nat) :
    digNat ds / 2 ^ (128 * k) % 2 ^ 128 = (ds.getD k 0).toNat := by
  induction ds generalizing k with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    have hd := d.isLt
    rcases k with _ | k
    · rw [digNat_cons]; simp; omega
    · rw [digNat_cons, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
        show (d.toNat + 2 ^ 128 * digNat ds) / 2 ^ 128 = digNat ds by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hd, Nat.zero_add], ih]
      simp

/-- A number below `2^(128 n)` whose base-`2^128` digits are the digests of `ds` is `digNat ds`. -/
theorem digNat_eq_of_digits : ∀ (ds : List Digest) (B : Nat), B < 2 ^ (128 * ds.length) →
    (∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ (128 * k) % 2 ^ 128) → digNat ds = B
  | [], B, hB, _ => by simp at hB; simp [digNat_nil, hB]
  | d :: ds, B, hB, h => by
    rw [digNat_cons]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hB' : B / 2 ^ 128 < 2 ^ (128 * ds.length) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      simpa [show 128 * (ds.length + 1) = 128 * ds.length + 128 by ring] using hB
    have hrest : ∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ 128 / 2 ^ (128 * k) % 2 ^ 128 := by
      intro k hk
      have := h (k + 1) (by simp; omega)
      rw [List.getD_cons_succ] at this
      rw [this, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, Nat.div_div_eq_div_mul]
    rw [digNat_eq_of_digits ds (B / 2 ^ 128) hB' hrest]
    omega

/-! ## The digests of a signature -/

/-- The 357 digests of a signature in `serialize` order. -/
def sigDigests (s : Signature) : List Digest :=
  [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
    (List.ofFn fun lay : Layer => List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path).flatten

theorem ofFn_four {α : Type} (f : Fin 4 → α) : List.ofFn f = [f 0, f 1, f 2, f 3] := by
  simp [List.ofFn_succ]

/-- The layer pieces, expanded. -/
theorem sigDigests_eq (s : Signature) : sigDigests s =
    [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
      ((List.ofFn (s.layers 0).values ++ List.ofFn (s.layers 0).path) ++
      ((List.ofFn (s.layers 1).values ++ List.ofFn (s.layers 1).path) ++
      ((List.ofFn (s.layers 2).values ++ List.ofFn (s.layers 2).path) ++
      (List.ofFn (s.layers 3).values ++ List.ofFn (s.layers 3).path)))) := by
  unfold sigDigests
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem serialize_eq (s : Signature) : serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  rw [sigDigests_eq]
  unfold serialize serializeLayer
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil]

theorem length_sigDigests (s : Signature) : (sigDigests s).length = 357 := by
  rw [sigDigests_eq]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rfl

/-- First digest index of layer `lay`'s piece (`16 * layIdx lay` = 2224, 3344, 4144, 4928). -/
def layIdx (lay : Layer) : Nat := (![139, 209, 259, 308] : Layer → Nat) lay

section getD

theorem getD_append_left' {l₁ l₂ : List Digest} {k : Nat} (h : k < l₁.length) :
    (l₁ ++ l₂).getD k 0 = l₁.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {l₁ l₂ : List Digest} {k : Nat} (h : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k 0 = l₂.getD (k - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_ofFn' {n : Nat} (f : Fin n → Digest) (i : Nat) (hi : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem chainCount_0 : chainCount 0 = 58 := rfl
theorem chainCount_1 : chainCount 1 = 43 := rfl
theorem chainCount_2 : chainCount 2 = 43 := rfl
theorem chainCount_3 : chainCount 3 = 43 := rfl
theorem height_0 : height 0 = 12 := rfl
theorem height_1 : height 1 = 7 := rfl
theorem height_2 : height 2 = 6 := rfl
theorem height_3 : height 3 = 6 := rfl

/-- Layer `lay`'s piece of the digest list: its chain values, then its Merkle path. -/
def layerList (s : Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path

variable (s : Signature)

theorem length_layerList (lay : Layer) : (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]

theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  rw [sigDigests_eq]; rfl

theorem sigDigests_secret (i : Nat) (hi : i < 21) : (sigDigests s).getD (1 + i) 0 = s.secrets ⟨i, hi⟩ := by
  have h1 : 1 + i < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : 1 + i < ([s.rho] ++ List.ofFn s.secrets).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_left' h2,
    getD_append_right' (by simp only [List.length_singleton]; omega), List.length_singleton,
    Nat.add_sub_cancel_left, getD_ofFn']

theorem sigDigests_proof (j : Nat) (hj : j < 117) : (sigDigests s).getD (22 + j) 0 = s.proof ⟨j, hj⟩ := by
  have h1 : 22 + j < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : ([s.rho] ++ List.ofFn s.secrets).length ≤ 22 + j := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_right' h2]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rw [show 22 + j - (1 + 21) = j by omega, getD_ofFn']

/-- The layer part of the digest list, from index 139. -/
theorem sigDigests_tail (k : Nat) (hk : 139 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 139) 0 := by
  have h1 : ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length ≤ k := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_right' h1]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rfl

/-- Digest `layIdx lay + i` is entry `i` of layer `lay`'s piece. -/
theorem sigDigests_layer (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := length_layerList s 0
  have l1 := length_layerList s 1
  have l2 := length_layerList s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (139 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 70 := hi
    rw [sigDigests_tail s _ (by omega), show 139 + i - 139 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (209 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 209 + i - 139 - 70 = i by omega]
  · show (sigDigests s).getD (259 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 259 + i - 139 - 70 - 50 = i by omega]
  · show (sigDigests s).getD (308 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 308 + i - 139 - 70 - 50 - 49 = i by omega]

theorem sigDigests_value (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']

theorem sigDigests_path (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']

end getD

/-! ## The codec -/

/-- Digest `k` (bytes `16 k .. 16 k + 16`) of a 5,712-byte signature string. -/
def sigDig (b : Bytes 5712) (k : Nat) : Digest := b.extractLsb' (128 * k) 128

/-- Decode a 5,712-byte string as a signature (every string decodes). -/
def sigDec (b : Bytes 5712) : Signature where
  rho := sigDig b 0
  secrets := fun i => sigDig b (1 + i.val)
  proof := fun j => sigDig b (22 + j.val)
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩

theorem pow_5728 : (2 : Nat) ^ (8 * 5712) = 2 ^ (128 * 357) := congrArg (fun n => 2 ^ n) rfl

/-- A signature as the organizer's 5,712-byte object (`serialize`, little endian). -/
def sigB (s : Signature) : Bytes 5712 := BitVec.ofNat _ (readLE (serialize s))

set_option exponentiation.threshold 50000 in
theorem sigB_toNat (s : Signature) : (sigB s).toNat = digNat (sigDigests s) := by
  have hlt := digNat_lt (sigDigests s)
  rw [length_sigDigests] at hlt
  rw [sigB, BitVec.toNat_ofNat, serialize_eq, ← digNat, Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt pow_5728.symm)]

theorem sigDig_toNat (b : Bytes 5712) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem sigDig_sigB (s : Signature) (k : Nat) : sigDig (sigB s) k = (sigDigests s).getD k 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [sigDig_toNat, sigB_toNat, digNat_digit]

theorem sigDec_sigB (s : Signature) : sigDec (sigB s) = s := by
  have hd := sigDig_sigB s
  have hr := sigDigests_rho s
  have hs := sigDigests_secret s
  have hp := sigDigests_proof s
  have hv := sigDigests_value s
  have hpa := sigDigests_path s
  rcases s with ⟨rho, secrets, proof, layers⟩
  generalize sigB ⟨rho, secrets, proof, layers⟩ = b at hd ⊢
  unfold sigDec
  congr 1
  · rw [hd]; exact hr
  · funext i; rw [hd]; exact hs i.val i.isLt
  · funext j; rw [hd]; exact hp j.val j.isLt
  · funext lay
    have hv' := hv lay
    have hpa' := hpa lay
    simp only at hv' hpa'
    rcases hl : layers lay with ⟨vals, path⟩
    rw [hl] at hv' hpa'
    congr 1
    · funext i; rw [hd]; exact hv' i.val i.isLt
    · funext j; rw [hd]; exact hpa' j.val j.isLt

/-- Entry `i` of layer `lay`'s piece of a decoded signature. -/
theorem layerList_sigDec (b : Bytes 5712) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (layerList (sigDec b) lay).getD i 0 = sigDig b (layIdx lay + i) := by
  unfold layerList
  by_cases hc : i < chainCount lay
  · rw [getD_append_left' (by simpa using hc), getD_ofFn' _ i hc]; rfl
  · rw [getD_append_right' (by simp; omega), List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega)]
    show sigDig b (layIdx lay + (chainCount lay + (i - chainCount lay))) = _
    rw [show chainCount lay + (i - chainCount lay) = i by omega]

theorem sigDigests_sigDec (b : Bytes 5712) (k : Nat) (hk : k < 357) :
    (sigDigests (sigDec b)).getD k 0 = sigDig b k := by
  by_cases h0 : k = 0
  · subst h0; exact sigDigests_rho _
  by_cases h1 : k < 22
  · have := sigDigests_secret (sigDec b) (k - 1) (by omega)
    rw [show 1 + (k - 1) = k by omega] at this
    rw [this]; show sigDig b (1 + (k - 1)) = _; rw [show 1 + (k - 1) = k by omega]
  by_cases h2 : k < 139
  · have := sigDigests_proof (sigDec b) (k - 22) (by omega)
    rw [show 22 + (k - 22) = k by omega] at this
    rw [this]; show sigDig b (22 + (k - 22)) = _; rw [show 22 + (k - 22) = k by omega]
  have key : ∀ (lay : Layer) (i : Nat), i < chainCount lay + height lay → layIdx lay + i = k →
      (sigDigests (sigDec b)).getD k 0 = sigDig b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi, layerList_sigDec b lay i hi]
  by_cases h3 : k < 209
  · exact key 0 (k - 139) (by rw [chainCount_0, height_0]; omega) (by simp [layIdx]; omega)
  by_cases h4 : k < 259
  · exact key 1 (k - 209) (by rw [chainCount_1, height_1]; omega) (by simp [layIdx]; omega)
  by_cases h5 : k < 308
  · exact key 2 (k - 259) (by rw [chainCount_2, height_2]; omega) (by simp [layIdx]; omega)
  · exact key 3 (k - 308) (by rw [chainCount_3, height_3]; omega) (by simp [layIdx]; omega)

set_option exponentiation.threshold 50000 in
theorem sigB_sigDec (b : Bytes 5712) : sigB (sigDec b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigB_toNat]
  apply digNat_eq_of_digits
  · rw [length_sigDigests]; exact lt_of_lt_of_eq b.isLt pow_5728
  · intro k hk
    rw [length_sigDigests] at hk
    rw [sigDigests_sigDec b k hk, sigDig_toNat]

theorem sigB_injective : Function.Injective sigB := fun s t h => by
  rw [← sigDec_sigB s, ← sigDec_sigB t, h]

theorem sigDec_injective : Function.Injective sigDec := fun a b h => by
  rw [← sigB_sigDec a, ← sigB_sigDec b, h]

/-! ## Doublewords -/

/-- The low doubleword of digest `k` is doubleword `2 k` of the string. -/
theorem sigDig_lo (b : Bytes 5712) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]

/-- The high doubleword of digest `k` is doubleword `2 k + 1` of the string. -/
theorem sigDig_hi (b : Bytes 5712) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]

end SigGolfCandidate.T3M
