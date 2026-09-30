import SigGolfCandidate.Sign.CounterPackRun
import SigGolfCandidate.Ref.Lemmas
import SigGolfCandidate.Keygen.State

/-!
# Byte seam for the aligned packed-counter stores

The appended signer code stores two aligned 64-bit words at `0x4aa0` and
`0x4aa8`. The signature exposes only the first fourteen bytes. These lemmas
turn the two machine words into the reference little-endian counter tail;
the instruction-level proof supplies the word hypotheses separately.
-/

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- A bounded staged counter survives the tail block's unsigned 32-bit load. -/
theorem lwuW_counter (c : Nat) (hc : c < CounterPack.radix) :
    lwuW (BitVec.ofNat 64 c) 0 = BitVec.ofNat 64 c := by
  have h32 : c < 2 ^ 32 := by
    have := hc
    norm_num [CounterPack.radix, CounterPack.counterBits] at this ⊢
    omega
  have h64 : c < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [lwuW_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_div, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]

/-- A tail block that only writes at or above 0x4aa0 leaves the signature
head and all 3,904 aligned body bytes intact. -/
theorem bytesAt_frame_before (t u : MachineState) (B : Nat)
    (hf : Frame t u (fun a => B ≤ a))
    (a n : Nat) (hbound : a + n ≤ B) (hB : B < 2 ^ 64) :
    bytesAt u a n = bytesAt t a n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Expand.getByte_ofNat u _ (by omega), Expand.getByte_ofNat t _ (by omega)]
  rw [hf ((a + i) / 8 * 8) (by omega) (by omega)]

/-- The tail block's shift/OR network computes the low machine word. The
second OR is modular: the upper two bits of `c2 << 44` may overflow 64 bits. -/
theorem lowWord_bitwise (c0 c1 c2 : Nat)
    (h0 : c0 < CounterPack.radix) (h1 : c1 < CounterPack.radix) :
    (BitVec.ofNat 64 c0 ||| (BitVec.ofNat 64 c1 <<< 22)) |||
        (BitVec.ofNat 64 c2 <<< 44) =
      CounterPackLayout.lowWord c0 c1 c2 := by
  have h01 : c0 + 2 ^ 22 * c1 < 2 ^ 44 := by
    norm_num [CounterPack.radix, CounterPack.counterBits] at h0 h1 ⊢
    omega
  have hp1 : BitVec.ofNat 64 c0 ||| (BitVec.ofNat 64 c1 <<< 22) =
      BitVec.ofNat 64 (c0 + 2 ^ 22 * c1) := by
    rw [Keygen.ofNat_shl, BitVec.or_comm,
      Keygen.ofNat_or_add c0 c1 22 (by
        simpa [CounterPack.radix, CounterPack.counterBits] using h0)]
    congr 1
    ring
  rw [hp1, Keygen.ofNat_shl, BitVec.or_comm,
    Keygen.ofNat_or_add (c0 + 2 ^ 22 * c1) c2 44 h01]
  unfold CounterPackLayout.lowWord
  congr 1
  ring

/-- The high-word shift/OR network computes the upper 46 useful bits. -/
theorem highWord_bitwise (c2 c3 c4 : Nat)
    (h2 : c2 < CounterPack.radix) (h3 : c3 < CounterPack.radix) :
    ((BitVec.ofNat 64 c2 >>> 20) ||| (BitVec.ofNat 64 c3 <<< 2)) |||
        (BitVec.ofNat 64 c4 <<< 24) =
      CounterPackLayout.highWord c2 c3 c4 := by
  have h2wide : c2 < 2 ^ 64 := by
    have := h2
    norm_num [CounterPack.radix, CounterPack.counterBits] at this ⊢
    omega
  have h2small : c2 / 2 ^ 20 < 2 ^ 2 := by
    have := h2
    norm_num [CounterPack.radix, CounterPack.counterBits] at this ⊢
    omega
  have h23 : c2 / 2 ^ 20 + 4 * c3 < 2 ^ 24 := by
    have := h3
    norm_num [CounterPack.radix, CounterPack.counterBits] at this ⊢
    omega
  have hp1 : (BitVec.ofNat 64 c2 >>> 20) ||| (BitVec.ofNat 64 c3 <<< 2) =
      BitVec.ofNat 64 (c2 / 2 ^ 20 + 4 * c3) := by
    rw [Keygen.ofNat_shr c2 20 h2wide, Keygen.ofNat_shl,
      BitVec.or_comm, Keygen.ofNat_or_add (c2 / 2 ^ 20) c3 2 h2small]
    congr 1
    ring
  rw [hp1, Keygen.ofNat_shl, BitVec.or_comm,
    Keygen.ofNat_or_add (c2 / 2 ^ 20 + 4 * c3) c4 24 h23]
  unfold CounterPackLayout.highWord
  congr 1
  ring

/-- Sixteen little-endian bytes split into the two aligned machine words. -/
theorem wordsOf_leBytes16 (v : Nat) :
    wordsOf (leBytes 16 v) =
      [BitVec.ofNat 64 (v % 2 ^ 64),
       BitVec.ofNat 64 ((v / 2 ^ 64) % 2 ^ 64)] := by
  rw [show (16 : Nat) = 8 + 8 from rfl, Ref.leBytes_append,
    wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
    wordsOf_eight _ (by simp), leNat_leBytes, leNat_leBytes]
  norm_num

/-- The first fourteen bytes of two aligned words are the exact tail encoding. -/
theorem bytesAt_tail_of_words (t : MachineState) (a v : Nat)
    (ha : a % 8 = 0) (hb : a + 24 < 2 ^ 64)
    (hlo : t.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 (v % 2 ^ 64))
    (hhi : t.getMem (BitVec.ofNat 64 (a + 8)) =
      BitVec.ofNat 64 ((v / 2 ^ 64) % 2 ^ 64)) :
    bytesAt t a 14 = leBytes 14 v := by
  have hwords : t.readWords (BitVec.ofNat 64 a) 2 = wordsOf (leBytes 16 v) := by
    rw [readWords_ofNat_two, wordsOf_leBytes16, hlo, hhi]
  have h16 := bytesAt_of_readWords t 2 a (leBytes 16 v) ha hb
    (by simp) hwords
  calc
    bytesAt t a 14 = (bytesAt t a 16).take 14 :=
      (bytesAt_take t a 14 16 (by omega)).symm
    _ = (leBytes 16 v).take 14 := by rw [h16]
    _ = leBytes 14 v := Ref.leBytes_take 14 16 v (by omega)

/-- The machine store seam, stated directly for the five-counter value. -/
theorem bytesAt_packedTail (t : MachineState) (cs : List Nat)
    (hlo : t.getMem (BitVec.ofNat 64 0x4aa0) =
      BitVec.ofNat 64 (CounterPack.packDigits cs % 2 ^ 64))
    (hhi : t.getMem (BitVec.ofNat 64 0x4aa8) =
      BitVec.ofNat 64 ((CounterPack.packDigits cs / 2 ^ 64) % 2 ^ 64)) :
    bytesAt t 0x4aa0 14 = CounterPack.packTail cs := by
  rw [Ref.packTail_eq_leBytes]
  exact bytesAt_tail_of_words t 0x4aa0 (CounterPack.packDigits cs)
    (by norm_num) (by norm_num) hlo hhi

/-- The form used after the symbolic tail block has identified its two store
values as the low and high five-counter words. -/
theorem bytesAt_packedTail_five (t : MachineState)
    (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < CounterPack.radix)
    (h1 : c1 < CounterPack.radix)
    (h2 : c2 < CounterPack.radix)
    (hlo : t.getMem (BitVec.ofNat 64 0x4aa0) =
      CounterPackLayout.lowWord c0 c1 c2)
    (hhi : t.getMem (BitVec.ofNat 64 0x4aa8) =
      CounterPackLayout.highWord c2 c3 c4) :
    bytesAt t 0x4aa0 14 =
      CounterPack.packTail [c0, c1, c2, c3, c4] := by
  apply bytesAt_packedTail t [c0, c1, c2, c3, c4]
  · exact hlo.trans (CounterPackLayout.lowWord_eq_packDigits c0 c1 c2 c3 c4)
  · exact hhi.trans (CounterPackLayout.highWord_eq_packDigits c0 c1 c2 c3 c4 h0 h1 h2)

/-- The tail appendix's two aligned stores have these exact shift/OR values. -/
theorem tail_low_expr (t : MachineState) :
    (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa0) =
      ((lwuW (t.getMem (BitVec.ofNat 64 0x900)) 0 |||
        (lwuW (t.getMem (BitVec.ofNat 64 0xc58)) 0 <<< 22)) |||
        (lwuW (t.getMem (BitVec.ofNat 64 0xfb0)) 0 <<< 44)) := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [show (19104#64 : BitVec 64) ≠ 19112#64 from by decide,
    lwuW, LoadKind.fromWord, BitVec.or_comm, BitVec.or_assoc]

theorem tail_high_expr (t : MachineState) :
    (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa8) =
      ((lwuW (t.getMem (BitVec.ofNat 64 0xfb0)) 0 >>> 20 |||
        (lwuW (t.getMem (BitVec.ofNat 64 0x1308)) 0 <<< 2)) |||
        (lwuW (t.getMem (BitVec.ofNat 64 0x1660)) 0 <<< 24)) := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [show (19104#64 : BitVec 64) ≠ 19112#64 from by decide,
    lwuW, LoadKind.fromWord, BitVec.or_comm, BitVec.or_assoc]

theorem tail_mem_frame (t : MachineState) (a : Word)
    (hlo : a ≠ BitVec.ofNat 64 0x4aa0)
    (hhi : a ≠ BitVec.ofNat 64 0x4aa8) :
    (blk2942PackedTail.res.toState t).getMem a = t.getMem a := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [hlo, hhi]

theorem tail_steps (t : MachineState) (hpc : t.pc = pcOf 2942) :
    Steps image t 24 24 (blk2942PackedTail.res.toState t) ∧
    (blk2942PackedTail.res.toState t).pc = pcOf 2966 ∧
    (blk2942PackedTail.res.toState t).getReg .x5 = 1 ∧
    (blk2942PackedTail.res.toState t).getReg .x10 = 0 := by
  have hs := symRun_sound blk2942PackedTail codeAt_2942 t hpc
    (by simp only [blk2942PackedTail.res, rv_simp])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [show blk2942PackedTail.res.steps = 24 from rfl,
      show blk2942PackedTail.res.cycles = 24 from rfl] using hs
  · simp only [blk2942PackedTail.res, rv_simp]
  · simp only [Result.toState_getReg, blk2942PackedTail.res, rv_simp]
  · simp only [Result.toState_getReg, blk2942PackedTail.res, rv_simp]

theorem tail_frame (t : MachineState) :
    Frame t (blk2942PackedTail.res.toState t) (fun a => 0x4aa0 ≤ a) := by
  intro a ha hW
  apply tail_mem_frame t (BitVec.ofNat 64 a)
  · intro heq
    have hae := congrArg BitVec.toNat heq
    norm_num [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hae
    omega
  · intro heq
    have hae := congrArg BitVec.toNat heq
    norm_num [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hae
    omega

/-- Given the five staged counter words, the final two stores encode their
canonical compact tail. -/
theorem tail_bytes_from_staged (t : MachineState) (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < CounterPack.radix) (h1 : c1 < CounterPack.radix)
    (h2 : c2 < CounterPack.radix) (h3 : c3 < CounterPack.radix)
    (h4 : c4 < CounterPack.radix)
    (hm0 : t.getMem (BitVec.ofNat 64 0x900) = BitVec.ofNat 64 c0)
    (hm1 : t.getMem (BitVec.ofNat 64 0xc58) = BitVec.ofNat 64 c1)
    (hm2 : t.getMem (BitVec.ofNat 64 0xfb0) = BitVec.ofNat 64 c2)
    (hm3 : t.getMem (BitVec.ofNat 64 0x1308) = BitVec.ofNat 64 c3)
    (hm4 : t.getMem (BitVec.ofNat 64 0x1660) = BitVec.ofNat 64 c4) :
    bytesAt (blk2942PackedTail.res.toState t) 0x4aa0 14 =
      CounterPack.packTail [c0, c1, c2, c3, c4] := by
  have hlo : (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa0) =
      CounterPackLayout.lowWord c0 c1 c2 := by
    rw [tail_low_expr, hm0, hm1, hm2,
      lwuW_counter c0 h0, lwuW_counter c1 h1, lwuW_counter c2 h2]
    exact lowWord_bitwise c0 c1 c2 h0 h1
  have hhi : (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa8) =
      CounterPackLayout.highWord c2 c3 c4 := by
    rw [tail_high_expr, hm2, hm3, hm4,
      lwuW_counter c2 h2, lwuW_counter c3 h3, lwuW_counter c4 h4]
    exact highWord_bitwise c2 c3 c4 h2 h3
  exact bytesAt_packedTail_five _ c0 c1 c2 c3 c4 h0 h1 h2 hlo hhi

theorem layerSig_list_five (lays : List LayerSig) (h : lays.length = 5) :
    lays = [lays[0], lays[1], lays[2], lays[3], lays[4]] := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  have hi : i < 5 := by omega
  interval_cases i <;> simp

theorem fst_list_five (lays : List LayerSig) (h : lays.length = 5) :
    lays.map Prod.fst =
      [lays[0].1, lays[1].1, lays[2].1, lays[3].1, lays[4].1] := by
  conv_lhs => rw [layerSig_list_five lays h]
  simp

theorem tail_bytes_of_stages (t : MachineState) (lays : List LayerSig)
    (hll : lays.length = 5)
    (hst : ∀ l (hl : l < lays.length), StageAt t l lays[l]) :
    bytesAt (blk2942PackedTail.res.toState t) 0x4aa0 14 =
      CounterPack.packTail (lays.map Prod.fst) := by
  have s0 := hst 0 (by omega)
  have s1 := hst 1 (by omega)
  have s2 := hst 2 (by omega)
  have s3 := hst 3 (by omega)
  have s4 := hst 4 (by omega)
  rw [fst_list_five lays hll]
  apply tail_bytes_from_staged t _ _ _ _ _
    s0.2.1 s1.2.1 s2.2.1 s3.2.1 s4.2.1
  · simpa only [Nat.reduceMul, Nat.reduceAdd] using s0.1
  · simpa only [Nat.reduceMul, Nat.reduceAdd] using s1.1
  · simpa only [Nat.reduceMul, Nat.reduceAdd] using s2.1
  · simpa only [Nat.reduceMul, Nat.reduceAdd] using s3.1
  · simpa only [Nat.reduceMul, Nat.reduceAdd] using s4.1

end SigGolfCandidate.Sign
