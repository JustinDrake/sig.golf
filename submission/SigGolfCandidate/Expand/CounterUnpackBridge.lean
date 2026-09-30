import SigGolfCandidate.Expand.Init
import SigGolfCandidate.Sign.Bytes
import SigGolfCandidate.Ref.Lemmas
import SigGolfCandidate.Expand.CounterUnpackLayout
import SigGolfCandidate.Expand.CounterUnpackRun
import SigGolfCandidate.Keygen.State
import SigGolfCandidate.Expand.Run
import SigGolfCandidate.Expand.SchedBase

set_option maxRecDepth 4096

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Sign SigGolfCandidate.Ref RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem sigOK_region (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061)
    (off n : Nat) (hrange : off + n ≤ 6061) :
    bytesAt u (0x3300 + off) n = (sig.drop off).take n := by
  apply List.ext_getElem (by simp [hlen]; omega)
  intro j hj1 hj2
  have hj : j < n := by simpa using hj1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  have he := h (off + j) (by omega)
  rw [List.getD_eq_getElem _ _ (by omega)] at he
  simpa only [List.getElem_take, List.getElem_drop, Nat.add_assoc] using he

theorem lwu_first4 (u : MachineState) (a : Nat)
    (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64) :
    (LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 a)) 0).toNat =
      leNat (bytesAt u a 4) := by
  have h8 := Ref.leNat_lt (bytesAt u a 8)
  have h4 := Ref.leNat_lt (bytesAt u a 4)
  simp only [Sign.length_bytesAt] at h8 h4
  have h8' : leNat (bytesAt u a 8) < 2 ^ 64 := by norm_num at h8 ⊢; exact h8
  have h4' : leNat (bytesAt u a 4) < 2 ^ 32 := by norm_num at h4 ⊢; exact h4
  change (Sign.lwuW (u.getMem (BitVec.ofNat 64 a)) 0).toNat = _
  rw [Sign.lwuW_toNat, getMem_of_bytes u a ha hb]
  simp only [BitVec.toNat_ofNat]
  change leNat (bytesAt u a 8) % 2 ^ 64 / 2 ^ (32 * (0 / 4)) % 2 ^ 32 = _
  rw [Nat.mod_eq_of_lt h8']
  have hs := Sign.bytesAt_add u a 4 4
  rw [hs, Ref.leNat_append]
  simp only [Sign.length_bytesAt]
  norm_num at h4' ⊢
  omega

theorem hu_high2_toNat (w : Word) :
    (LoadKind.fromWord .bu w 4).toNat = w.toNat / 2 ^ 32 % 2 ^ 8 := by
  simp only [LoadKind.fromWord, extractByte, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem lhu_last2 (u : MachineState) (a : Nat)
    (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64) :
    (LoadKind.fromWord .bu (u.getMem (BitVec.ofNat 64 a)) 4).toNat =
      leNat (bytesAt u (a + 4) 1) := by
  have he := Sign.getByte_aligned' u a 4 ha (by decide) hb
  simp only [LoadKind.fromWord, BitVec.toNat_setWidth, bytesAt, List.range_one,
    List.map_cons, List.map_nil, Nat.add_zero, leNat, Nat.mul_zero, Nat.add_zero]
  rw [he]
  have hlt := (extractByte (u.getMem (BitVec.ofNat 64 a)) 4).isLt
  omega

theorem tail_split14 (tail : List Byte) (hlen : tail.length = 13) :
    leNat tail = leNat (tail.take 8) + 2 ^ 64 *
      (leNat ((tail.drop 8).take 4) + 2 ^ 32 * leNat (tail.drop 12)) := by
  have h8 : 8 ≤ tail.length := by omega
  have h4 : 4 ≤ (tail.drop 8).length := by simp [hlen]
  rw [Ref.leNat_split8 tail h8]
  conv_lhs => rw [← List.take_append_drop 4 (tail.drop 8)]
  rw [Ref.leNat_append]
  simp only [List.length_take, Nat.min_eq_left h4, List.drop_drop]
  norm_num

theorem sigOK_tail_ld (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061) :
    u.getMem (BitVec.ofNat 64 0x4aa0) =
      BitVec.ofNat 64 (leNat ((sig.drop 6048).take 8)) := by
  rw [getMem_of_bytes u 0x4aa0 (by decide) (by decide)]
  have hb := congrArg (List.take 8) (sigOK_region u sig h hlen 6048 13 (by decide))
  have hdrop : (sig.drop 6048).take 13 = sig.drop 6048 := by simp [hlen]
  rw [hdrop] at hb
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left (by decide : 8 ≤ 13)] at hb
  simpa only [bytesAt, show (13056 : Nat) + 6048 = 19104 by decide] using
    congrArg (fun x => BitVec.ofNat 64 (leNat x)) hb

theorem sigOK_tail_lwu (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061) :
    (LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0).toNat =
      leNat ((sig.drop 6056).take 4) := by
  rw [lwu_first4 u 0x4aa8 (by decide) (by decide)]
  have hr := sigOK_region u sig h hlen 6056 4 (by decide)
  simpa only [show (0x3300 : Nat) + 6056 = 0x4aa8 by decide] using congrArg leNat hr

theorem sigOK_tail_lhu (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061) :
    (LoadKind.fromWord .bu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4).toNat =
      leNat ((sig.drop 6060).take 1) := by
  rw [lhu_last2 u 0x4aa8 (by decide) (by decide)]
  have hr := sigOK_region u sig h hlen 6060 1 (by decide)
  simpa only [show (0x3300 : Nat) + 6060 = 0x4aac by decide,
    show (0x4aa8 : Nat) + 4 = 0x4aac by decide] using congrArg leNat hr

theorem leNat_two (l : List Byte) (hlen : l.length = 2) :
    leNat l = (l.getD 0 0).toNat + 256 * (l.getD 1 0).toNat := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => simp [leNat]
      | cons c l => simp at hlen

theorem tail_hi_two (tail : List Byte) (hlen : tail.length = 13) :
    leNat ((tail.drop 12).take 1) = (tail.getD 12 0).toNat := by
  have h1 : ((tail.drop 12).take 1).length = 1 := by simp [hlen]
  have hone : ∀ l : List Byte, l.length = 1 → leNat l = (l.getD 0 0).toNat := by
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      have he : l = [] := by simpa using hl
      subst l
      simp [leNat]
  rw [hone _ h1]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem shift14_zero_iff (w : Word) : w >>> 4 = 0 ↔ w.toNat / 2 ^ 4 = 0 := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using hh
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h

theorem sigOK_tail_canonical (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061) :
    (LoadKind.fromWord .bu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4 >>> 4 = 0) ↔
      CounterPack.canonicalTail (sig.drop 6048) = true := by
  have htlen : (sig.drop 6048).length = CounterPack.tailBytes := by
    simp [hlen, CounterPack.tailBytes]
  rw [shift14_zero_iff, sigOK_tail_lhu u sig h hlen]
  have he : (sig.drop 6060).take 1 = ((sig.drop 6048).drop 12).take 1 := by
    simp only [List.drop_drop, show 6048 + 12 = 6060 by decide]
  rw [he, tail_hi_two _ (by simpa [CounterPack.tailBytes] using htlen)]
  exact (CounterUnpackLayout.canonicalTail_iff_highHalfword (sig.drop 6048) htlen).symm

theorem sigOK_tail_value (u : MachineState) (sig : List Byte)
    (h : SigOK u sig) (hlen : sig.length = 6061) :
    CounterPack.tailValue (sig.drop 6048) =
      (u.getMem (BitVec.ofNat 64 0x4aa0)).toNat + 2 ^ 64 *
        ((LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0).toNat +
          2 ^ 32 * (LoadKind.fromWord .bu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4).toNat) := by
  have htail := tail_split14 (sig.drop 6048) (by simp [hlen])
  have hlo := congrArg BitVec.toNat (sigOK_tail_ld u sig h hlen)
  have hlt := Ref.leNat_lt ((sig.drop 6048).take 8)
  have hlen8 : ((sig.drop 6048).take 8).length = 8 := by simp [hlen]
  rw [hlen8] at hlt
  have hlt' : leNat ((sig.drop 6048).take 8) < 2 ^ 64 := by norm_num at hlt ⊢; exact hlt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt'] at hlo
  have h8 : ((sig.drop 6048).drop 8).take 4 = (sig.drop 6056).take 4 := by
    simp only [List.drop_drop, show 6048 + 8 = 6056 by decide]
  have h12 : (sig.drop 6048).drop 12 = sig.drop 6060 := by
    simp only [List.drop_drop, show 6048 + 12 = 6060 by decide]
  have h2 : sig.drop 6060 = (sig.drop 6060).take 1 := by simp [hlen]
  unfold CounterPack.tailValue
  rw [htail, h8, h12, h2, ← hlo, ← sigOK_tail_lwu u sig h hlen,
    ← sigOK_tail_lhu u sig h hlen]

theorem sigCounterTail_eq_drop (sig : List Byte) (hlen : sig.length = 6061) :
    sigCounterTail sig = sig.drop 6048 := by
  unfold sigCounterTail slice
  rw [CounterPack.tailOffset_eq]
  have hdrop : (sig.drop 6048).length = 13 := by simp [hlen]
  rw [List.take_of_length_le (by rw [hdrop]; decide)]

/-- The five shift and mask expressions in the decoder recover five radix-2^20 digits. -/
theorem digit0_word (lo : Word) :
    ((lo <<< 44 >>> 44).truncate 32).toNat = lo.toNat % 2 ^ 20 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem digit1_word (lo : Word) :
    ((lo >>> 20 <<< 44 >>> 44).truncate 32).toNat =
      lo.toNat / 2 ^ 20 % 2 ^ 20 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem hi_word (a b : Word) (ha : a.toNat < 2 ^ 32)
    (hb : b.toNat < 2 ^ 16) :
    (a ||| b <<< 32).toNat = a.toNat + 2 ^ 32 * b.toNat := by
  have hrepA : BitVec.ofNat 64 a.toNat = a := by
    simpa using BitVec.ofNat_toNat 64 a
  have hrepB : BitVec.ofNat 64 b.toNat = b := by
    simpa using BitVec.ofNat_toNat 64 b
  calc
    (a ||| b <<< 32).toNat =
        ((BitVec.ofNat 64 a.toNat) ||| (BitVec.ofNat 64 b.toNat <<< 32)).toNat := by
          rw [hrepA, hrepB]
    _ = (BitVec.ofNat 64 (b.toNat * 2 ^ 32 + a.toNat)).toNat := by
          rw [Keygen.ofNat_shl, BitVec.or_comm,
            Keygen.ofNat_or_add _ _ 32 ha]
    _ = a.toNat + 2 ^ 32 * b.toNat := by
          rw [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : b.toNat * 2 ^ 32 + a.toNat < 2 ^ 64)]
          omega

theorem shr_word (w : Word) (k : Nat) :
    w >>> k = BitVec.ofNat 64 (w.toNat / 2 ^ k) := by
  have hrep : BitVec.ofNat 64 w.toNat = w := by
    simpa using BitVec.ofNat_toNat 64 w
  calc
    w >>> k = BitVec.ofNat 64 w.toNat >>> k := by rw [hrep]
    _ = _ := Keygen.ofNat_shr w.toNat k w.isLt

theorem and3_word (w : Word) :
    w &&& 3#64 = BitVec.ofNat 64 (w.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h3 : (3#64 : Word).toNat = 2 ^ 2 - 1 := by decide
  rw [h3, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem digit2_word (lo : Word) :
    ((lo >>> 40 <<< 44 >>> 44).truncate 32).toNat =
      lo.toNat / 2 ^ 40 % 2 ^ 20 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem digit3_word (lo hi : Word) :
    ((lo >>> 60 ||| (hi <<< 48 >>> 44)).truncate 32).toNat =
      lo.toNat / 2 ^ 60 + (hi.toNat % 2 ^ 16) * 2 ^ 4 := by
  have hlo : lo.toNat / 2 ^ 60 < 2 ^ 4 := by have := lo.isLt; omega
  have hm : hi <<< 48 >>> 44 = BitVec.ofNat 64 ((hi.toNat % 2 ^ 16) * 2 ^ 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  rw [shr_word lo 60, hm, BitVec.or_comm,
    Keygen.ofNat_or_add _ _ 4 hlo]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hhi : hi.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have hv : (hi.toNat % 2 ^ 16) * 2 ^ 4 + lo.toNat / 2 ^ 60 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt hv]
  omega

theorem digit4_word (hi : Word) (hhi : hi.toNat < 2 ^ 36) :
    ((hi >>> 16).truncate 32).toNat = hi.toNat / 2 ^ 16 % 2 ^ 20 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have hquot : hi.toNat / 2 ^ 16 < 2 ^ 20 := by omega
  rw [Nat.mod_eq_of_lt (by omega : hi.toNat / 2 ^ 16 < 2 ^ 32),
    Nat.mod_eq_of_lt hquot]

/-- The five decoder stores are exactly the reference digits of the loaded
low 64 and high 36 bits, when the canonicality branch accepts. -/
theorem packedBody_values (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8)
    (h12 : (u.getReg .x12).toNat < 2 ^ 32)
    (h13 : (u.getReg .x13).toNat < 2 ^ 16)
    (hhi : (u.getReg .x12).toNat + 2 ^ 32 * (u.getReg .x13).toNat < 2 ^ 36) :
    let v := blk231PackedBody.res.toState u
    [ (lo32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat,
      (hi32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat,
      (lo32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat,
      (hi32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat,
      (lo32 (v.getMem (BitVec.ofNat 64 0x20c8))).toNat] =
      CounterUnpackLayout.unpackWords (u.getReg .x11).toNat
        ((u.getReg .x12).toNat + 2 ^ 32 * (u.getReg .x13).toNat) := by
  have hh := hi_word (u.getReg .x12) (u.getReg .x13) h12 h13
  have hword : (u.getReg .x12 ||| u.getReg .x13 <<< 32).toNat < 2 ^ 36 := by
    rw [hh]
    exact hhi
  have hmid : (u.getReg .x11).toNat / 2 ^ 60 +
      ((u.getReg .x12 ||| u.getReg .x13 <<< 32).toNat % 2 ^ 16) * 2 ^ 4 < 2 ^ 20 := by
    have hlo := (u.getReg .x11).isLt
    have hmod := Nat.mod_lt (u.getReg .x12 ||| u.getReg .x13 <<< 32).toNat (by decide : 0 < 2 ^ 16)
    omega
  obtain ⟨h0, h1, h2, h3, h4⟩ := packedBody_halves u h7
  dsimp only
  rw [h0, h1, h2, h3, h4]
  rw [digit0_word, digit1_word, digit2_word, digit3_word,
    digit4_word _ hword]
  simp only [CounterUnpackLayout.unpackWords]
  rw [← hh]
  simp only [Nat.mod_eq_of_lt hmid]

/-- Under signature loading and an accepted canonical branch, the five
machine stores decode the same counters as the reference tail parser. -/
theorem packedBody_sig_values (orig u : MachineState) (sig : List Byte)
    (hs : SigOK orig sig) (hlen : sig.length = 6061)
    (h11 : u.getReg .x11 = orig.getMem (BitVec.ofNat 64 0x4aa0))
    (h12 : u.getReg .x12 =
      LoadKind.fromWord .wu (orig.getMem (BitVec.ofNat 64 0x4aa8)) 0)
    (h13 : u.getReg .x13 =
      LoadKind.fromWord .bu (orig.getMem (BitVec.ofNat 64 0x4aa8)) 4)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8)
    (hcanon : (u.getReg .x13).toNat < 2 ^ 4) :
    let v := blk231PackedBody.res.toState u
    [ (lo32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat,
      (hi32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat,
      (lo32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat,
      (hi32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat,
      (lo32 (v.getMem (BitVec.ofNat 64 0x20c8))).toNat] =
      CounterPack.unpackTail (sig.drop 6048) := by
  have h12b : (u.getReg .x12).toNat < 2 ^ 32 := by
    rw [h12]
    change (Sign.lwuW (orig.getMem (BitVec.ofNat 64 0x4aa8)) 0).toNat < _
    rw [Sign.lwuW_toNat]
    omega
  have h13b : (u.getReg .x13).toNat < 2 ^ 16 := by
    rw [h13, hu_high2_toNat]
    omega
  have hhib : (u.getReg .x12).toNat + 2 ^ 32 * (u.getReg .x13).toNat < 2 ^ 36 := by
    omega
  have hval := sigOK_tail_value orig sig hs hlen
  rw [← h11, ← h12, ← h13] at hval
  let lo := (u.getReg .x11).toNat
  let hi := (u.getReg .x12).toNat + 2 ^ 32 * (u.getReg .x13).toNat
  have hlo : lo < 2 ^ 64 := (u.getReg .x11).isLt
  have hsplit0 : CounterPack.tailValue (sig.drop 6048) % 2 ^ 64 = lo := by
    rw [hval]
    dsimp only [lo, hi]
    omega
  have hsplit1 : CounterPack.tailValue (sig.drop 6048) / 2 ^ 64 = hi := by
    rw [hval]
    dsimp only [lo, hi]
    omega
  calc
    _ = CounterUnpackLayout.unpackWords lo hi := packedBody_values u h7 h12b h13b hhib
    _ = CounterUnpackLayout.unpackWords
        (CounterPack.tailValue (sig.drop 6048) % 2 ^ 64)
        (CounterPack.tailValue (sig.drop 6048) / 2 ^ 64) := by rw [hsplit0, hsplit1]
    _ = CounterPack.unpackTail (sig.drop 6048) := by
          exact CounterUnpackLayout.unpackWords_value _

/-- Four bytes from either half of an aligned dword equal the little-endian
encoding of that half's 32-bit value. -/
theorem bytesAt_half (t : MachineState) (a k c : Nat)
    (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64) (hk : k < 2) (hc : c < 2 ^ 32)
    (hh : (t.getMem (BitVec.ofNat 64 a)).extractLsb' (32 * k) 32 = BitVec.ofNat 32 c) :
    Sign.bytesAt t (a + 4 * k) 4 = le32 c := by
  apply List.ext_getElem (by simp [Sign.bytesAt, le32])
  intro i h1 h2
  have hi : i < 4 := by simpa [Sign.bytesAt] using h1
  simp only [Sign.bytesAt, List.getElem_map, List.getElem_range, le32, leBytes]
  rw [show a + 4 * k + i = a + (4 * k + i) by omega,
    Sign.getByte_aligned' t a (4 * k + i) ha (by omega) hb]
  apply BitVec.eq_of_toNat_eq
  rw [Sign.extractByte_toNat', byte_toNat]
  have hn := congrArg BitVec.toNat hh
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt hc] at hn
  interval_cases k <;> interval_cases i <;>
    norm_num at hn ⊢ <;> omega

theorem counterArea_bytes (t : MachineState) (c0 c1 c2 c3 c4 : Nat)
    (hc0 : c0 < 2 ^ 32) (hc1 : c1 < 2 ^ 32) (hc2 : c2 < 2 ^ 32)
    (hc3 : c3 < 2 ^ 32) (hc4 : c4 < 2 ^ 32)
    (h0 : lo32 (t.getMem (BitVec.ofNat 64 0x20b8)) = BitVec.ofNat 32 c0)
    (h1 : hi32 (t.getMem (BitVec.ofNat 64 0x20b8)) = BitVec.ofNat 32 c1)
    (h2 : lo32 (t.getMem (BitVec.ofNat 64 0x20c0)) = BitVec.ofNat 32 c2)
    (h3 : hi32 (t.getMem (BitVec.ofNat 64 0x20c0)) = BitVec.ofNat 32 c3)
    (h4 : lo32 (t.getMem (BitVec.ofNat 64 0x20c8)) = BitVec.ofNat 32 c4) :
    Sign.bytesAt t 0x20b8 20 = le32 c0 ++ le32 c1 ++ le32 c2 ++ le32 c3 ++ le32 c4 := by
  have e0 := bytesAt_half t 0x20b8 0 c0 (by decide) (by decide) (by decide) hc0 h0
  have e1 := bytesAt_half t 0x20b8 1 c1 (by decide) (by decide) (by decide) hc1 h1
  have e2 := bytesAt_half t 0x20c0 0 c2 (by decide) (by decide) (by decide) hc2 h2
  have e3 := bytesAt_half t 0x20c0 1 c3 (by decide) (by decide) (by decide) hc3 h3
  have e4 := bytesAt_half t 0x20c8 0 c4 (by decide) (by decide) (by decide) hc4 h4
  rw [show (20 : Nat) = 4 + (4 + (4 + (4 + 4))) by decide]
  repeat rw [Sign.bytesAt_add]
  norm_num at e0 e1 e2 e3 e4 ⊢
  rw [e0, e1, e2, e3, e4]

theorem packedBody_sig_bytes (orig u : MachineState) (sig : List Byte)
    (hs : SigOK orig sig) (hlen : sig.length = 6061)
    (h11 : u.getReg .x11 = orig.getMem (BitVec.ofNat 64 0x4aa0))
    (h12 : u.getReg .x12 =
      LoadKind.fromWord .wu (orig.getMem (BitVec.ofNat 64 0x4aa8)) 0)
    (h13 : u.getReg .x13 =
      LoadKind.fromWord .bu (orig.getMem (BitVec.ofNat 64 0x4aa8)) 4)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8)
    (hcanon : (u.getReg .x13).toNat < 2 ^ 4) :
    Sign.bytesAt (blk231PackedBody.res.toState u) 0x20b8 20 =
      ((List.range nLayers).map (sigCounterBytes sig)).flatten := by
  let v := blk231PackedBody.res.toState u
  let c0 := (lo32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat
  let c1 := (hi32 (v.getMem (BitVec.ofNat 64 0x20b8))).toNat
  let c2 := (lo32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat
  let c3 := (hi32 (v.getMem (BitVec.ofNat 64 0x20c0))).toNat
  let c4 := (lo32 (v.getMem (BitVec.ofNat 64 0x20c8))).toNat
  have hc0 : c0 < 2 ^ 32 := (lo32 (v.getMem (BitVec.ofNat 64 0x20b8))).isLt
  have hc1 : c1 < 2 ^ 32 := (hi32 (v.getMem (BitVec.ofNat 64 0x20b8))).isLt
  have hc2 : c2 < 2 ^ 32 := (lo32 (v.getMem (BitVec.ofNat 64 0x20c0))).isLt
  have hc3 : c3 < 2 ^ 32 := (hi32 (v.getMem (BitVec.ofNat 64 0x20c0))).isLt
  have hc4 : c4 < 2 ^ 32 := (lo32 (v.getMem (BitVec.ofNat 64 0x20c8))).isLt
  have h0 : lo32 (v.getMem (BitVec.ofNat 64 0x20b8)) = BitVec.ofNat 32 c0 := by
    simpa [c0] using (BitVec.ofNat_toNat 32 (lo32 (v.getMem (BitVec.ofNat 64 0x20b8)))).symm
  have h1 : hi32 (v.getMem (BitVec.ofNat 64 0x20b8)) = BitVec.ofNat 32 c1 := by
    simpa [c1] using (BitVec.ofNat_toNat 32 (hi32 (v.getMem (BitVec.ofNat 64 0x20b8)))).symm
  have h2 : lo32 (v.getMem (BitVec.ofNat 64 0x20c0)) = BitVec.ofNat 32 c2 := by
    simpa [c2] using (BitVec.ofNat_toNat 32 (lo32 (v.getMem (BitVec.ofNat 64 0x20c0)))).symm
  have h3 : hi32 (v.getMem (BitVec.ofNat 64 0x20c0)) = BitVec.ofNat 32 c3 := by
    simpa [c3] using (BitVec.ofNat_toNat 32 (hi32 (v.getMem (BitVec.ofNat 64 0x20c0)))).symm
  have h4 : lo32 (v.getMem (BitVec.ofNat 64 0x20c8)) = BitVec.ofNat 32 c4 := by
    simpa [c4] using (BitVec.ofNat_toNat 32 (lo32 (v.getMem (BitVec.ofNat 64 0x20c8)))).symm
  have hbytes := counterArea_bytes v c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 h0 h1 h2 h3 h4
  have hvals := packedBody_sig_values orig u sig hs hlen h11 h12 h13 h7 hcanon
  change [c0, c1, c2, c3, c4] = CounterPack.unpackTail (sig.drop 6048) at hvals
  have hflat : ((List.range nLayers).map (sigCounterBytes sig)).flatten =
      le32 c0 ++ le32 c1 ++ le32 c2 ++ le32 c3 ++ le32 c4 := by
    unfold sigCounterBytes CounterPack.unpackCounter
    rw [sigCounterTail_eq_drop sig hlen]
    rw [← hvals]
    rfl
  exact hbytes.trans hflat.symm

/-- Only three aligned counter dwords change. Within the 6,348-byte witness,
their first twenty bytes are exactly the reconstructed counter area. -/
theorem witness_putCounters_bytes (t u : MachineState) (sig : List Byte) (f : Nat → Byte)
    (ht : BytesEq t f)
    (hf : Frame t u (fun a => a = 0x20b8 ∨ a = 0x20c0 ∨ a = 0x20c8))
    (harea : Sign.bytesAt u 0x20b8 20 =
      ((List.range nLayers).map (sigCounterBytes sig)).flatten) :
    ∀ i < 6348,
      u.getByte (BitVec.ofNat 64 (0x800 + i)) = putCounters sig f (0x800 + i) := by
  intro i hi
  let x := 0x800 + i
  unfold putCounters
  by_cases hc : 0x20b8 ≤ x ∧ x < 0x20b8 + 20
  · rw [if_pos hc]
    have hj : x - 0x20b8 < 20 := by omega
    have hget : (Sign.bytesAt u 0x20b8 20).getD (x - 0x20b8) 0 =
        u.getByte (BitVec.ofNat 64 x) := by
      rw [List.getD_eq_getElem _ _ (by simp [Sign.bytesAt]; omega)]
      simp only [Sign.bytesAt, List.getElem_map, List.getElem_range]
      rw [show 0x20b8 + (x - 0x20b8) = x by omega]
    rw [harea] at hget
    exact hget.symm
  · rw [if_neg hc]
    have hx : x < 0x20b8 := by omega
    rw [getByte_ofNat u x (by omega), hf (x / 8 * 8) (by omega)
      (by intro h; rcases h with h | h | h <;> omega),
      ← getByte_ofNat t x (by omega)]
    exact ht x (by omega)

/-- The existing two-instruction success epilogue consumes the byte witness. -/
theorem run_success (s : MachineState) (w : List Byte)
    (hpc : s.pc = pcOf 281)
    (hb : ∀ i < 6348, s.getByte (BitVec.ofNat 64 (0x800 + i)) = w.getD i 0) :
    Run s 2 (Final (some w)) := by
  have hst := symRun_sound blk281 codeAt_281 s hpc (by simp only [blk281.res, rv_simp])
  refine Run.of hst (le_refl _) ⟨symRun_ecall blk281 codeAt_281 s (by simp only [blk281.res, rv_simp]) rfl,
    by simp only [blk281.res, rv_simp], ?_, ?_⟩
  · simp only [blk281.res, rv_simp]
  · intro i hi
    rw [getByte_ofNat _ _ (by omega), toState_getMem_nil (r := blk281.res) rfl s,
      ← getByte_ofNat _ _ (by omega)]
    exact hb i hi

/-- From the packed tail, canonical signatures reach the witness epilogue;
noncanonical signatures reach the existing rejection epilogue. -/
theorem packedFinish (u : MachineState) (sig w : List Byte)
    (hpc : u.pc = pcOf 226)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8)
    (hs : SigOK u sig) (hlen : sig.length = 6061)
    (hb : CounterPack.canonicalTail (sig.drop 6048) = true → ∀ i < 6348,
      (blk231PackedBody.res.toState
        (blk230PackedBranch.res.toState (blk226PackedPrelude.res.toState u))).getByte
          (BitVec.ofNat 64 (0x800 + i)) = w.getD i 0) :
    Run u 28 (fun v => if CounterPack.canonicalTail (sig.drop 6048) = true
      then Final (some w) v else Final none v) := by
  let t1 := blk226PackedPrelude.res.toState u
  let t2 := blk230PackedBranch.res.toState t1
  let t3 := blk231PackedBody.res.toState t2
  have hpre := packedPrelude_run u hpc h6
  have hbr := packedBranch_run t1 hpre.2.1
  have h14 := (packedPrelude_words u h6).2.2.2
  have hcan := sigOK_tail_canonical u sig hs hlen
  have h7pre : t1.getReg .x7 = BitVec.ofNat 64 0x20b8 := by
    simp only [t1, Result.toState_getReg, blk226PackedPrelude.res, rv_simp, h7]
  have h7br : t2.getReg .x7 = BitVec.ofNat 64 0x20b8 := by
    rw [hbr.2.2.2.1 .x7, h7pre]
  by_cases hc : CounterPack.canonicalTail (sig.drop 6048) = true
  · have hz : t1.getReg .x14 = 0 := by rw [h14]; exact hcan.mpr hc
    have hbody := packedBody_run t2 (hbr.2.1 hz) h7br
    have hbytes : ∀ i < 6348, t3.getByte (BitVec.ofNat 64 (0x800 + i)) = w.getD i 0 := hb hc
    have hfinish := run_success t3 w hbody.2 hbytes
    have hrun := Run.steps ((hpre.1.trans hbr.1).trans hbody.1) hfinish
    simpa [hc] using hrun
  · have hnz : t1.getReg .x14 ≠ 0 := by
      rw [h14]
      intro hz
      exact hc (hcan.mp hz)
    have hfinish := run_fail t2 (hbr.2.2.1 hnz)
    have hrun := Run.steps (hpre.1.trans hbr.1) hfinish
    exact hrun.mono (by norm_num) (fun _ h => by simpa [hc] using h)

/-- The complete packed decoder consumes the modeled witness. The input model
already includes the body copies; this theorem adds exactly the five counters. -/
theorem packedFinish_of_model (u : MachineState) (sig w : List Byte)
    (f : Nat → Byte)
    (hpc : u.pc = pcOf 226)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8)
    (hs : SigOK u sig) (hlen : sig.length = 6061)
    (hf : BytesEq u f)
    (hmodel : ∀ i < 6348, putCounters sig f (0x800 + i) = w.getD i 0) :
    Run u 28 (fun v => if CounterPack.canonicalTail (sig.drop 6048) = true
      then Final (some w) v else Final none v) := by
  refine packedFinish u sig w hpc h6 h7 hs hlen ?_
  intro hc i hi
  let t1 := blk226PackedPrelude.res.toState u
  let t2 := blk230PackedBranch.res.toState t1
  let t3 := blk231PackedBody.res.toState t2
  have hpre := packedPrelude_run u hpc h6
  have hbr := packedBranch_run t1 hpre.2.1
  have hword := packedPrelude_words u h6
  have h11 : t2.getReg .x11 = u.getMem (BitVec.ofNat 64 0x4aa0) := by
    rw [hbr.2.2.2.1 .x11]
    exact hword.1
  have h12 : t2.getReg .x12 =
      LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0 := by
    rw [hbr.2.2.2.1 .x12]
    exact hword.2.1
  have h13 : t2.getReg .x13 =
      LoadKind.fromWord .bu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4 := by
    rw [hbr.2.2.2.1 .x13]
    exact hword.2.2.1
  have h7b : t2.getReg .x7 = BitVec.ofNat 64 0x20b8 := by
    rw [hbr.2.2.2.1 .x7]
    simp only [t1, Result.toState_getReg, blk226PackedPrelude.res, rv_simp, h7]
  have h13lt : (t2.getReg .x13).toNat < 2 ^ 4 := by
    have hz : t1.getReg .x14 = 0 := by
      rw [hword.2.2.2]
      exact (sigOK_tail_canonical u sig hs hlen).mpr hc
    have hshift : t2.getReg .x13 >>> 4 = 0 := by
      rw [h13]
      rw [hword.2.2.2] at hz
      exact hz
    have := (shift14_zero_iff (t2.getReg .x13)).mp hshift
    omega
  have harea := packedBody_sig_bytes u t2 sig hs hlen h11 h12 h13 h7b h13lt
  have hbytes2 : BytesEq t2 f := by
    intro a ha
    rw [getByte_ofNat t2 a ha, hbr.2.2.2.2, hpre.2.2,
      ← getByte_ofNat u a ha]
    exact hf a ha
  have hcounter := witness_putCounters_bytes t2 t3 sig f hbytes2
    (packedBody_frame t2 h7b) harea
  exact (hcounter i hi).trans (hmodel i hi)

end SigGolfCandidate.Expand
