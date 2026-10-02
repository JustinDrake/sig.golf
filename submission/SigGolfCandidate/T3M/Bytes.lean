import SigGolfCandidate.T3.Core
import SigGolfCandidate.Rv.Hash

/-!
# T3M bytes: Core's byte lists as organizer queries and as machine doublewords

Core (`T3/Core.lean`) hashes byte lists (`HashInput := List UInt8`); the organizer's oracle takes
`Legacy.Query := (n : Nat) × Bytes (64 * (n + 1))` and the machine reads doublewords. This module
is the whole relabeling layer between the two (MACH-PLAN §1.2–1.3):

* `toQ l` : the little-endian value of `l` as an `(l.length / 64)`-block query (junk on
  unaligned lists); `Aligned`, `toQ_injOn` (injective on aligned lists), `ofQ`, `toQ_ofQ`,
  `ofQ_toQ`, `blocks_toQ`;
* `wordsOf l` : the little-endian doublewords of `l`, with `wordsOf_append`, `wordsOf_bytesLE16`,
  `wordsOf_header`, `wordsOf_zero16`, the private inputs (`wordsOf_privateInput_tweak`,
  `privateInput_mac_eq`) and `pad64` (`pad64_of_aligned`);
* `hashInput_toQ` : the machine's HASH input is `toQ l` when its buffer holds `wordsOf l`;
* `readBuffer_of_words` : an output buffer holding `wordsOf l` reads back as `l`;
* the cache codec `cacheB` / `cacheDec` (`cacheDec_cacheB`, `cacheB_cacheDec`).

`readLE` is Core's own little-endian reading (`T3.readLE`).
-/

set_option maxRecDepth 20000

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (readLE pad64 zero16 header privateInput Cache cacheBytes Region)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Little-endian values of byte lists -/

@[simp] theorem readLE_nil : readLE [] = 0 := rfl

theorem readLE_cons (b : UInt8) (l : List UInt8) : readLE (b :: l) = b.toNat + 256 * readLE l := rfl

theorem readLE_append (l₁ l₂ : List UInt8) :
    readLE (l₁ ++ l₂) = readLE l₁ + 256 ^ l₁.length * readLE l₂ := by
  induction l₁ with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, readLE_cons, ih, List.length_cons, pow_succ]
    ring

theorem readLE_lt (l : List UInt8) : readLE l < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [readLE_cons, List.length_cons, pow_succ]
    have hb : b.toNat < 256 := b.toNat_lt
    nlinarith

theorem readLE_inj : ∀ {l₁ l₂ : List UInt8}, l₁.length = l₂.length → readLE l₁ = readLE l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    simp only [readLE_cons, List.length_cons, Nat.add_right_cancel_iff] at hl h
    have h1 : b₁.toNat < 256 := b₁.toNat_lt
    have h2 : b₂.toNat < 256 := b₂.toNat_lt
    have hb : b₁.toNat = b₂.toNat := by omega
    have hr : readLE l₁ = readLE l₂ := by omega
    rw [UInt8.toNat_inj.mp hb, readLE_inj hl hr]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

@[simp] theorem readLE_replicate_zero (n : Nat) : readLE (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, readLE_cons, ih]; rfl

theorem readLE_ofFn_digits : ∀ (n N : Nat),
    readLE (List.ofFn fun i : Fin n => UInt8.ofNat (N / 256 ^ i.val % 256)) = N % 256 ^ n
  | 0, N => by simp [Nat.mod_one]
  | n + 1, N => by
    rw [List.ofFn_succ, readLE_cons]
    have e : (fun i : Fin n => UInt8.ofNat (N / 256 ^ (i.succ : Fin (n + 1)).val % 256)) =
        fun i : Fin n => UInt8.ofNat (N / 256 / 256 ^ i.val % 256) := by
      funext i
      rw [Fin.val_succ, pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    rw [e, readLE_ofFn_digits n (N / 256), pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp

/-- `bytesLE n x` reads back as `x`. -/
theorem readLE_bytesLE (n : Nat) (x : BitVec (8 * n)) : readLE (bytesLE n x) = x.toNat := by
  have e : bytesLE n x = List.ofFn fun i : Fin n => UInt8.ofNat (x.toNat / 256 ^ i.val % 256) := by
    unfold bytesLE
    congr 1; funext i
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt8.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [show 256 ^ i.val = 2 ^ (8 * i.val) by rw [Nat.pow_mul]]
    omega
  rw [e, readLE_ofFn_digits, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this

theorem readLE_div_mod (l : List UInt8) (i : Nat) : readLE l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rcases i with _ | i
    · have := b.toNat_lt
      simp only [readLE_cons, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · rw [readLE_cons, pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul,
        show (b.toNat + 256 * readLE l) / 256 = readLE l by have := b.toNat_lt; omega, ih]
      simp

/-! ## Organizer queries -/

/-- Core's byte lists as organizer queries: the little-endian value as a query of
`l.length / 64` blocks (a junk value on unaligned lists, which never occur). -/
def toQ (l : List UInt8) : Query := ⟨l.length / 64 - 1, BitVec.ofNat _ (readLE l)⟩

/-- Nonempty whole 64-byte blocks: every Core query has this shape (`pad64`). -/
def Aligned (l : List UInt8) : Prop := 0 < l.length ∧ l.length % 64 = 0

/-- The byte list of an organizer query (little endian). -/
def ofQ (q : Query) : List UInt8 := bytesLE (64 * (q.1 + 1)) q.2

theorem aligned_len {l : List UInt8} (h : Aligned l) : 64 * (l.length / 64 - 1 + 1) = l.length := by
  obtain ⟨h0, h64⟩ := h
  have : 1 ≤ l.length / 64 := by omega
  rw [Nat.sub_add_cancel this]
  omega

/-- `toQ` is injective on aligned lists. -/
theorem toQ_injOn : Set.InjOn toQ {l | Aligned l} := by
  intro l₁ h₁ l₂ h₂ h
  have hn : l₁.length / 64 - 1 = l₂.length / 64 - 1 := congrArg (fun q : Query => q.1) h
  have ht : (toQ l₁).2.toNat = (toQ l₂).2.toNat := congrArg (fun q : Query => q.2.toNat) h
  have e₁ := aligned_len h₁
  have e₂ := aligned_len h₂
  have hlen : l₁.length = l₂.length := by omega
  simp only [toQ, BitVec.toNat_ofNat] at ht
  rw [e₁, e₂] at ht
  have hp : ∀ l : List UInt8, (2 : Nat) ^ (8 * l.length) = 256 ^ l.length := fun l => by
    rw [pow_mul]; norm_num
  rw [hp, hp, Nat.mod_eq_of_lt (readLE_lt l₁), Nat.mod_eq_of_lt (readLE_lt l₂)] at ht
  exact readLE_inj hlen ht

/-- A query of `n + 1` blocks has `n + 1` blocks. -/
theorem blocks_toQ {l : List UInt8} (h : Aligned l) : (toQ l).blocks = l.length / 64 := by
  have := aligned_len h
  unfold toQ Query.blocks
  dsimp only
  omega

theorem ofQ_length (q : Query) : (ofQ q).length = 64 * (q.1 + 1) := bytesLE_length _ _

/-- `toQ` of a list of `n + 1` blocks. -/
theorem toQ_eq (l : List UInt8) (n : Nat) (hl : l.length = 64 * (n + 1)) :
    toQ l = ⟨n, BitVec.ofNat _ (readLE l)⟩ := by
  have hn : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn]

theorem toQ_ofQ (q : Query) : toQ (ofQ q) = q := by
  obtain ⟨n, v⟩ := q
  rw [toQ_eq _ n (ofQ_length _), ofQ, readLE_bytesLE]
  simp

theorem ofQ_toQ {l : List UInt8} (h : Aligned l) : ofQ (toQ l) = l := by
  have e := aligned_len h
  apply readLE_inj
  · rw [ofQ_length]; exact e
  · unfold ofQ toQ
    rw [readLE_bytesLE]
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hl := readLE_lt l
    rw [show (2 : Nat) ^ (8 * (64 * (l.length / 64 - 1 + 1))) = 256 ^ l.length by
      rw [e, pow_mul]; norm_num]
    exact hl

/-! ## Doublewords of byte lists -/

/-- The little-endian doublewords of a byte list (a trailing partial word is dropped). -/
def wordsOf : List UInt8 → List Word
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      BitVec.ofNat 64 (readLE [b0, b1, b2, b3, b4, b5, b6, b7]) :: wordsOf rest
  | _ => []

@[simp] theorem wordsOf_nil : wordsOf [] = [] := rfl

theorem wordsOf_append8 (l rest : List UInt8) (hl : l.length = 8) :
    wordsOf (l ++ rest) = BitVec.ofNat 64 (readLE l) :: wordsOf rest := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem wordsOf_append (l₁ l₂ : List UInt8) (h : l₁.length % 8 = 0) :
    wordsOf (l₁ ++ l₂) = wordsOf l₁ ++ wordsOf l₂ := by
  obtain ⟨n, hn⟩ : ∃ n, l₁.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing l₁ with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [List.length_eq_zero_iff] at hn
      subst hn; rfl
    · have ht : (l₁.take 8).length = 8 := by simp; omega
      rw [← List.take_append_drop 8 l₁, List.append_assoc,
        wordsOf_append8 (l₁.take 8) (l₁.drop 8 ++ l₂) ht, wordsOf_append8 (l₁.take 8) (l₁.drop 8) ht,
        ih (n - 8) (by omega) (l₁.drop 8) (by simp; omega) (by simp; omega)]
      rfl

theorem wordsOf_eq_range : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsOf l = (List.range m).map fun j => BitVec.ofNat 64 (readLE l / 2 ^ (64 * j))
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hr : readLE l = readLE (l.take 8) + 2 ^ 64 * readLE (l.drop 8) := by
      conv_lhs => rw [hl]
      rw [readLE_append, ht]; norm_num
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, ← hl, wordsOf_eq_range m _ hd, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.mul_zero, pow_zero, Nat.div_one, hr]
      omega
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp, hr]
      congr 1
      rw [show 64 * (j + 1) = 64 + 64 * j by ring, pow_add, ← Nat.div_div_eq_div_mul]
      congr 1
      omega

theorem length_wordsOf (m : Nat) (l : List UInt8) (h : l.length = 8 * m) : (wordsOf l).length = m := by
  rw [wordsOf_eq_range m l h]; simp

theorem wordsToNat_wordsOf : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsToNat (wordsOf l) = readLE l
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, wordsToNat, wordsToNat_wordsOf m _ hd, readLE_append, ht,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    norm_num

/-- The doublewords of an `8 m`-byte value. -/
theorem wordsOf_bytesLE (m : Nat) (x : BitVec (8 * (8 * m))) :
    wordsOf (bytesLE (8 * m) x) = (List.range m).map fun j => x.extractLsb' (64 * j) 64 := by
  rw [wordsOf_eq_range m _ (bytesLE_length _ _), readLE_bytesLE]
  apply List.map_congr_left
  intro j _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem wordsOf_bytesLE16 (x : BitVec 128) :
    wordsOf (bytesLE 16 x) = [x.extractLsb' 0 64, x.extractLsb' 64 64] :=
  wordsOf_bytesLE 2 x

theorem wordsOf_bytesLE32 (x : BitVec 256) :
    wordsOf (bytesLE 32 x) =
      [x.extractLsb' 0 64, x.extractLsb' 64 64, x.extractLsb' 128 64, x.extractLsb' 192 64] :=
  wordsOf_bytesLE 4 x

@[simp] theorem wordsOf_zero16 : wordsOf zero16 = [0, 0] := rfl

theorem wordsOf_replicate_zero (m : Nat) : wordsOf (List.replicate (8 * m) 0) = List.replicate m 0 := by
  rw [wordsOf_eq_range m _ (by simp), readLE_replicate_zero]
  apply List.ext_getElem (by simp)
  intro i _ _
  simp

/-- The doublewords of a list of 16-byte digests. -/
theorem wordsOf_flatMap16 (ds : List (BitVec 128)) :
    wordsOf (ds.flatMap (bytesLE 16)) = ds.flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [bytesLE_length]),
      wordsOf_bytesLE16, ih]

/-! ## Core's headers -/

/-- Doubleword 0 of Core's header: `1 | tag << 8 | lay << 16 | (tree >> 32) << 24 | position << 32`. -/
def hdr0 (tag lay tree position : Nat) : Nat :=
  1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + tree / 2 ^ 32 % 256 * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32

/-- Doubleword 1 of Core's header: `tree | index << 32` (low 32 bits each). -/
def hdr1 (tree index : Nat) : Nat := tree % 2 ^ 32 + index % 2 ^ 32 * 2 ^ 32

theorem hdr0_lt (tag lay tree position : Nat) : hdr0 tag lay tree position < 2 ^ 64 := by
  unfold hdr0
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  have := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  omega

theorem hdr1_lt (tree index : Nat) : hdr1 tree index < 2 ^ 64 := by
  unfold hdr1
  have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  omega

theorem header_toNat (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat = hdr0 tag lay tree position + 2 ^ 64 * hdr1 tree index := by
  unfold header hdr0 hdr1
  rw [BitVec.toNat_ofNat]
  have ht := Nat.mod_lt tag (by decide : 0 < 256)
  have hl := Nat.mod_lt lay (by decide : 0 < 256)
  have hth := Nat.mod_lt (tree / 2 ^ 32) (by decide : 0 < 256)
  have hp := Nat.mod_lt position (by decide : 0 < 2 ^ 32)
  have htl := Nat.mod_lt tree (by decide : 0 < 2 ^ 32)
  have hi := Nat.mod_lt index (by decide : 0 < 2 ^ 32)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem header_lo (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 tag lay tree position) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have h1 := hdr1_lt tree index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  generalize hdr0 tag lay tree position = a at *
  generalize hdr1 tree index = b at *
  omega

theorem header_hi (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (hdr1 tree index) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have h1 := hdr1_lt tree index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  generalize hdr0 tag lay tree position = a at *
  generalize hdr1 tree index = b at *
  omega

theorem wordsOf_header (tag lay tree position index : Nat) :
    wordsOf (bytesLE 16 (header tag lay tree position index)) =
      [BitVec.ofNat 64 (hdr0 tag lay tree position), BitVec.ofNat 64 (hdr1 tree index)] := by
  rw [wordsOf_bytesLE16, header_lo, header_hi]

/-- `hdr0` without the overflow guards (`tag, lay < 256`, `tree, position < 2^32`). -/
theorem hdr0_eq (tag lay tree position : Nat) (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 32)
    (hp : position < 2 ^ 32) :
    hdr0 tag lay tree position = 1 + 256 * tag + 65536 * lay + 2 ^ 32 * position := by
  unfold hdr0
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp, Nat.div_eq_of_lt htr]
  omega

theorem hdr1_eq (tree index : Nat) (htr : tree < 2 ^ 32) (hi : index < 2 ^ 32) :
    hdr1 tree index = tree + 2 ^ 32 * index := by
  unfold hdr1
  rw [Nat.mod_eq_of_lt htr, Nat.mod_eq_of_lt hi]
  omega

/-! ## `pad64` and the private inputs -/

theorem pad64_of_aligned (l : List UInt8) (h : l.length % 64 = 0) : pad64 l = l := by
  unfold pad64; rw [h]; simp

theorem pad64_length (l : List UInt8) : (pad64 l).length = l.length + (64 - l.length % 64) % 64 := by
  simp [pad64]

theorem pad64_aligned (l : List UInt8) (h : 0 < l.length) : Aligned (pad64 l) := by
  rw [Aligned, pad64_length]; omega

/-- The two secret halves `S0 = sk[0, 16)`, `S1 = sk[16, 32)` as doublewords. -/
theorem sk_words (sk : BitVec 256) :
    (sk.extractLsb' 0 128).extractLsb' 0 64 = sk.extractLsb' 0 64 ∧
    (sk.extractLsb' 0 128).extractLsb' 64 64 = sk.extractLsb' 64 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 0 64 = sk.extractLsb' 128 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 64 64 = sk.extractLsb' 192 64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] <;>
    norm_num <;> omega

/-- The private input of a 16-byte tweak (`privatePair`, `mask`): one block. -/
theorem privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    privateInput sk (.inl tw) = bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 := by
  show pad64 (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++ []) = _
  rw [List.append_nil, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length]; rfl)]

theorem wordsOf_privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    wordsOf (privateInput sk (.inl tw)) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, tw.extractLsb' 0 64, tw.extractLsb' 64 64,
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  rw [privateInput_tweak, wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16, h1, h2, h3, h4]
  rfl

theorem privateInput_tweak_length (sk : BitVec 256) (tw : BitVec 128) :
    (privateInput sk (.inl tw)).length = 64 := by
  rw [privateInput_tweak]; simp [bytesLE_length, zero16]

/-- The MAC input: `S0 | T14 | S1 | 0^16 | region | 0^32` (513 blocks). -/
theorem privateInput_mac_eq (sk : BitVec 256) (region : Region) :
    privateInput sk (.inr (.inr region)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 14 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      List.ofFn region ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate,
    List.length_ofFn]

theorem privateInput_mac_length (sk : BitVec 256) (region : Region) :
    (privateInput sk (.inr (.inr region))).length = 32832 := by
  rw [privateInput_mac_eq]
  simp only [List.length_append, bytesLE_length, List.length_ofFn, List.length_replicate, zero16]

/-- The nonce input: `S0 | T7 | S1 | 0^16 | m | 0^32` (2 blocks). -/
theorem privateInput_nonce_eq (sk : BitVec 256) (m : T3.Message) :
    privateInput sk (.inr (.inl m)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 7 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      bytesLE 32 m ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate]

theorem privateInput_aligned (sk : BitVec 256) (c : T3.Coordinate) : Aligned (privateInput sk c) := by
  rcases c with tw | m | region
  · rw [Aligned, privateInput_tweak_length]; omega
  · rw [Aligned, privateInput_nonce_eq]
    simp only [List.length_append, bytesLE_length, List.length_replicate, zero16]; decide
  · rw [Aligned, privateInput_mac_length]; omega

/-! ## Machine buffers -/

/-- **The HASH input of a buffer holding `wordsOf l`** is `toQ l`. -/
theorem hashInput_toQ (t : MachineState) (l : List UInt8) (n A : Nat)
    (hl : l.length = 64 * (n + 1)) (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A < 2 ^ 64) (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hn : 64 * (n + 1) < 2 ^ 64)
    (hw : t.readWords (BitVec.ofNat 64 A) (8 * (n + 1)) = wordsOf l) : hashInput t = toQ l := by
  rw [hashInput_eq_words t n h11 hn (by rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']; exact hA),
    h10, hw, queryOfWords, wordsToNat_wordsOf (8 * (n + 1)) l (by rw [hl]; ring)]
  have hn' : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn']

theorem readWords_add (t : MachineState) (A m₁ m₂ : Nat) :
    t.readWords (BitVec.ofNat 64 A) (m₁ + m₂) =
      t.readWords (BitVec.ofNat 64 A) m₁ ++ t.readWords (BitVec.ofNat 64 (A + 8 * m₁)) m₂ := by
  induction m₁ generalizing A with
  | zero => simp
  | succ m ih =>
    have e : BitVec.ofNat 64 A + 8 = BitVec.ofNat 64 (A + 8) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [show m + 1 + m₂ = (m + m₂) + 1 by omega, MachineState.readWords_succ,
      MachineState.readWords_succ, e, ih]
    simp only [List.cons_append]
    rw [show A + 8 + 8 * m = A + 8 * (m + 1) by ring]

theorem readWords_one (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 1 = [t.getMem (BitVec.ofNat 64 A)] := rfl

theorem readWords_two (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 2 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8))] := by
  have := readWords_add t A 1 1
  rw [readWords_one, readWords_one] at this
  simpa using this

private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl

private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega

private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega

private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring

/-- Bytes of an aligned buffer as the little-endian value of its doublewords. -/
theorem foldl_bytes_eq_words (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0) :
    ∀ m, 8 * m < 2 ^ 64 →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
    simp only [foldl_range_succ]
    rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
      byte_term t src hal m 0 (8 * m) (by omega) (by omega) (by omega),
      byte_term t src hal m 1 (8 * m + 1) (by omega) (by omega) (by omega),
      byte_term t src hal m 2 (8 * m + 2) (by omega) (by omega) (by omega),
      byte_term t src hal m 3 (8 * m + 3) (by omega) (by omega) (by omega),
      byte_term t src hal m 4 (8 * m + 4) (by omega) (by omega) (by omega),
      byte_term t src hal m 5 (8 * m + 5) (by omega) (by omega) (by omega),
      byte_term t src hal m 6 (8 * m + 6) (by omega) (by omega) (by omega),
      byte_term t src hal m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
    generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
    conv_rhs => rw [← word_bytes w.toNat w.isLt]
    ring

/-- **An output buffer holding `wordsOf l`** reads back as `l` (`readBuffer`). -/
theorem readBuffer_of_words (t : MachineState) (A m : Nat) (l : List UInt8) (hA : A % 8 = 0)
    (hA' : A + 8 * m < 2 ^ 64) (hl : l.length = 8 * m)
    (hw : t.readWords (BitVec.ofNat 64 A) m = wordsOf l) :
    readBuffer t A (8 * m) = BitVec.ofNat _ (readLE l) := by
  unfold readBuffer
  have e : ∀ i, BitVec.ofNat 64 (A + i) = BitVec.ofNat 64 A + BitVec.ofNat 64 i := fun i => by
    apply BitVec.eq_of_toNat_eq; simp
  simp only [e]
  rw [foldl_bytes_eq_words t _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega)]; exact hA) m
    (by omega), hw, wordsToNat_wordsOf m l hl]

/-! ## The cache codec -/

/-- The cache as the organizer's 32,768-byte object (`cacheBytes`, little endian). -/
def cacheB (c : Cache) : Bytes 32768 := BitVec.ofNat _ (readLE (cacheBytes c))

/-- The inverse of `cacheB`: tag = bytes `[0, 32)`, region = bytes `[32, 32768)`. -/
def cacheDec (b : Bytes 32768) : Cache :=
  ⟨b.extractLsb' 0 256, fun i => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)⟩

theorem cacheBytes_length (c : Cache) : (cacheBytes c).length = 32768 := by
  simp only [cacheBytes, List.length_append, bytesLE_length, List.length_ofFn]

theorem two_pow_eight_mul (n : Nat) : (2 : Nat) ^ (8 * n) = 256 ^ n := by
  rw [pow_mul]; norm_num

theorem readLE_cacheBytes_lt (c : Cache) : readLE (cacheBytes c) < 2 ^ (8 * 32768) := by
  have := readLE_lt (cacheBytes c)
  rwa [cacheBytes_length, ← two_pow_eight_mul] at this

theorem cacheDec_cacheB (c : Cache) : cacheDec (cacheB c) = c := by
  obtain ⟨tag, region⟩ := c
  have hlt := readLE_cacheBytes_lt ⟨tag, region⟩
  have hr : readLE (cacheBytes ⟨tag, region⟩) = tag.toNat + 256 ^ 32 * readLE (List.ofFn region) := by
    rw [cacheBytes, readLE_append, readLE_bytesLE, bytesLE_length]
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have htag : tag.toNat < 256 ^ 32 := by have := tag.isLt; rwa [h256] at this
  unfold cacheDec cacheB
  refine congrArg₂ Cache.mk ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.shiftRight_zero, hr,
      h256, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htag]
  · funext i
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, pow_add, ← Nat.div_div_eq_div_mul,
      hr, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt htag, Nat.zero_add, readLE_div_mod]
    have hi := (region i).toNat_lt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    simp

theorem cacheB_cacheDec (b : Bytes 32768) : cacheB (cacheDec b) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have e2 : (256 : Nat) ^ 32768 = 256 ^ 32736 * 256 ^ 32 := (pow_add 256 32736 32 : _)
  have hb' : b.toNat < 256 ^ 32736 * 256 ^ 32 := by
    have h := hb
    rw [two_pow_eight_mul, e2] at h; exact h
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have h3 : b.toNat / 256 ^ 32 < 256 ^ 32736 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb'
  unfold cacheB cacheDec cacheBytes
  rw [BitVec.toNat_ofNat, readLE_append, readLE_bytesLE, bytesLE_length]
  have e : List.ofFn (fun i : Fin 32736 => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)) =
      List.ofFn fun i : Fin 32736 => UInt8.ofNat (b.toNat / 256 ^ 32 / 256 ^ i.val % 256) := by
    exact congrArg List.ofFn (funext fun i => by rw [pow_add, Nat.div_div_eq_div_mul])
  rw [e, readLE_ofFn_digits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, h256, Nat.mod_eq_of_lt h3,
    Nat.mod_add_div]
  exact Nat.mod_eq_of_lt hb

end SigGolfCandidate.T3M
