import SigGolfCandidate.Sign.CounterPackRun
import SigGolfCandidate.Ref.Lemmas
import SigGolfCandidate.Keygen.State
import SigGolfCandidate.Sign.CounterMixWords

/-!
# Byte seam for the aligned packed-counter stores

The appended signer code stores two aligned 64-bit words at `0x4aa0` and
`0x4aa8`. The signature exposes only the first twelve bytes. These lemmas
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

/-- Sixteen little-endian bytes split into the two aligned machine words. -/
theorem wordsOf_leBytes16 (v : Nat) :
    wordsOf (leBytes 16 v) =
      [BitVec.ofNat 64 (v % 2 ^ 64),
       BitVec.ofNat 64 ((v / 2 ^ 64) % 2 ^ 64)] := by
  rw [show (16 : Nat) = 8 + 8 from rfl, Ref.leBytes_append,
    wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
    wordsOf_eight _ (by simp), leNat_leBytes, leNat_leBytes]
  norm_num

/-- The first twelve bytes of two aligned words are the exact tail encoding. -/
theorem bytesAt_tail_of_words (t : MachineState) (a v : Nat)
    (ha : a % 8 = 0) (hb : a + 24 < 2 ^ 64)
    (hlo : t.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 (v % 2 ^ 64))
    (hhi : t.getMem (BitVec.ofNat 64 (a + 8)) =
      BitVec.ofNat 64 ((v / 2 ^ 64) % 2 ^ 64)) :
    bytesAt t a 12 = leBytes 12 v := by
  have hwords : t.readWords (BitVec.ofNat 64 a) 2 = wordsOf (leBytes 16 v) := by
    rw [readWords_ofNat_two, wordsOf_leBytes16, hlo, hhi]
  have h16 := bytesAt_of_readWords t 2 a (leBytes 16 v) ha hb
    (by simp) hwords
  calc
    bytesAt t a 12 = (bytesAt t a 16).take 12 :=
      (bytesAt_take t a 12 16 (by omega)).symm
    _ = (leBytes 16 v).take 12 := by rw [h16]
    _ = leBytes 12 v := Ref.leBytes_take 12 16 v (by omega)

/-- The machine store seam, stated directly for the five-counter value. -/
theorem bytesAt_packedTail (t : MachineState) (cs : List Nat)
    (hlo : t.getMem (BitVec.ofNat 64 0x4aa0) =
      BitVec.ofNat 64 (CounterPack.packDigits cs % 2 ^ 64))
    (hhi : t.getMem (BitVec.ofNat 64 0x4aa8) =
      BitVec.ofNat 64 ((CounterPack.packDigits cs / 2 ^ 64) % 2 ^ 64)) :
    bytesAt t 0x4aa0 12 = CounterPack.packTail cs := by
  rw [Ref.packTail_eq_leBytes]
  exact bytesAt_tail_of_words t 0x4aa0 (CounterPack.packDigits cs)
    (by norm_num) (by norm_num) hlo hhi

theorem bytesAt_packedTail_five (t : MachineState) (c0 c1 c2 c3 c4 : Nat)
    (hlo : t.getMem (BitVec.ofNat 64 0x4aa0) = CounterPackLayout.lowWord c0 c1 c2 c3 c4)
    (hhi : t.getMem (BitVec.ofNat 64 0x4aa8) = CounterPackLayout.highWord c0 c1 c2 c3 c4) :
    bytesAt t 0x4aa0 12 = CounterPack.packTail [c0,c1,c2,c3,c4] :=
  bytesAt_packedTail t _ hlo hhi

/-- The tail appendix's two aligned stores have these exact shift/OR values. -/
theorem tail_low_expr (t : MachineState) :
    (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa0) =
      CounterMixWords.outLow
        (lwuW (t.getMem (BitVec.ofNat 64 0x900)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0xc58)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0xfb0)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0x1308)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0x1660)) 0) := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [show (19104#64 : BitVec 64) ≠ 19112#64 from by decide,
    lwuW, LoadKind.fromWord, CounterMixWords.outLow, CounterMixWords.lowW,
    CounterMixWords.highW, CounterMixWords.rankW, CounterMixWords.okW, BitVec.ult]

theorem tail_high_expr (t : MachineState) :
    (blk2942PackedTail.res.toState t).getMem (BitVec.ofNat 64 0x4aa8) =
      CounterMixWords.outHigh
        (lwuW (t.getMem (BitVec.ofNat 64 0x900)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0xc58)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0xfb0)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0x1308)) 0)
        (lwuW (t.getMem (BitVec.ofNat 64 0x1660)) 0) := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [show (19104#64 : BitVec 64) ≠ 19112#64 from by decide,
    lwuW, LoadKind.fromWord, CounterMixWords.outHigh, CounterMixWords.lowW,
    CounterMixWords.highW, CounterMixWords.rankW, CounterMixWords.okW, BitVec.ult]

theorem tail_mem_frame (t : MachineState) (a : Word)
    (hlo : a ≠ BitVec.ofNat 64 0x4aa0)
    (hhi : a ≠ BitVec.ofNat 64 0x4aa8) :
    (blk2942PackedTail.res.toState t).getMem a = t.getMem a := by
  simp only [Result.toState_getMem, blk2942PackedTail.res, rv_simp]
  simp [hlo, hhi]

theorem tail_steps (t : MachineState) (hpc : t.pc = pcOf 2942) :
    Steps image t 66 78 (blk2942PackedTail.res.toState t) ∧
    (blk2942PackedTail.res.toState t).pc = pcOf 3037 ∧
    (blk2942PackedTail.res.toState t).getReg .x5 = 1 ∧
    (blk2942PackedTail.res.toState t).getReg .x10 = 0 := by
  let j := blk2942TailJump.res.toState t
  have hj := symRun_sound blk2942TailJump codeAt_2942 t hpc
    (by simp only [blk2942TailJump.res, rv_simp])
  have hjpc : j.pc = pcOf 2972 := by simp only [j, blk2942TailJump.res, rv_simp]
  have hs := symRun_sound blk2942PackedTail codeAt_2972 j hjpc
    (by simp only [blk2942PackedTail.res, rv_simp])
  have hjstate : j = { t with pc := pcOf 2972 } := by
    apply MachineState.ext' <;> try rfl
    funext r
    cases r <;> rfl
  have he : blk2942PackedTail.res.toState j = blk2942PackedTail.res.toState t := by
    rw [hjstate]
    apply MachineState.ext' <;> try rfl
    · funext r
      cases r <;> rfl
  rw [he] at hs
  have hsteps := hj.trans hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [show blk2942PackedTail.res.steps = 65 from rfl,
      show blk2942PackedTail.res.cycles = 77 from rfl, show blk2942TailJump.res.steps = 1 from rfl,
      show blk2942TailJump.res.cycles = 1 from rfl, Nat.reduceAdd] using hsteps
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
    bytesAt (blk2942PackedTail.res.toState t) 0x4aa0 12 =
      CounterPack.packTail [c0, c1, c2, c3, c4] := by
  have hwide : ∀ c : Nat, c < CounterPack.radix → c < 2^64 := by
    intro c hc
    norm_num [CounterPack.radix, CounterPack.counterBits] at hc ⊢
    omega
  apply bytesAt_packedTail_five
  · rw [tail_low_expr, hm0, hm1, hm2, hm3, hm4,
      lwuW_counter c0 h0, lwuW_counter c1 h1, lwuW_counter c2 h2,
      lwuW_counter c3 h3, lwuW_counter c4 h4]
    exact CounterMixWords.outLow_eq _ _ _ _ _ (hwide _ h0) (hwide _ h1)
      (hwide _ h2) (hwide _ h3) (hwide _ h4)
  · rw [tail_high_expr, hm0, hm1, hm2, hm3, hm4,
      lwuW_counter c0 h0, lwuW_counter c1 h1, lwuW_counter c2 h2,
      lwuW_counter c3 h3, lwuW_counter c4 h4]
    exact CounterMixWords.outHigh_eq _ _ _ _ _ (hwide _ h0) (hwide _ h1)
      (hwide _ h2) (hwide _ h3) (hwide _ h4)

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
    bytesAt (blk2942PackedTail.res.toState t) 0x4aa0 12 =
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
