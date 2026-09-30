import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Mac
/-! Machine effects of the one-block randomizer setup tail. -/
namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
theorem blk2844_cycles : blk2844.res.cycles = 43 := by rfl
theorem blk2844_steps : blk2844.res.steps = 43 := by rfl
theorem blk2844_pc (t : MachineState) : (blk2844.res.toState t).pc = pcOf 65 := by
  simp only [blk2844.res, rv_simp]
theorem blk2844_x6 (t : MachineState) : (blk2844.res.toState t).getReg .x6 = 0 := by
  simp only [blk2844.res, rv_simp]
theorem blk2844_word0 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x780) =
      rndW0 (t.getMem (BitVec.ofNat 64 0x640)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW0, ↓reduceIte]
  norm_num
theorem blk2844_word1 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x788) = rndW1 (t.getMem (BitVec.ofNat 64 0x640)) (t.getMem (BitVec.ofNat 64 0x648)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW1, ↓reduceIte]
  norm_num
theorem blk2844_word2 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x790) = rndW1 (t.getMem (BitVec.ofNat 64 0x648)) (t.getMem (BitVec.ofNat 64 0x650)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW1, ↓reduceIte]
  norm_num
theorem blk2844_word3 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x798) = rndW3 (t.getMem (BitVec.ofNat 64 0x650)) (t.getMem (BitVec.ofNat 64 0x658)) (t.getMem (BitVec.ofNat 64 0x660)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW3, ↓reduceIte]
  norm_num
theorem blk2844_word4 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x7a0) = rndW4 (t.getMem (BitVec.ofNat 64 0x660)) (t.getMem (BitVec.ofNat 64 0x668)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW4, ↓reduceIte]
  norm_num
theorem blk2844_word5 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x7a8) = rndW4 (t.getMem (BitVec.ofNat 64 0x668)) (t.getMem (BitVec.ofNat 64 0x670)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW4, ↓reduceIte]
  norm_num
theorem blk2844_word6 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x7b0) = rndW4 (t.getMem (BitVec.ofNat 64 0x670)) (t.getMem (BitVec.ofNat 64 0x678)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW4, ↓reduceIte]
  norm_num
theorem blk2844_word7 (t : MachineState) :
    (blk2844.res.toState t).getMem (BitVec.ofNat 64 0x7b8) = rndW7 (t.getMem (BitVec.ofNat 64 0x678)) := by
  simp (config := { decide := true }) only [blk2844.res, rv_simp, rndW7, ↓reduceIte]
  norm_num
theorem blk2844_words (t : MachineState) :
    (blk2844.res.toState t).readWords (BitVec.ofNat 64 0x780) 8 =
      rndPackWords (t.getMem (BitVec.ofNat 64 0x640)) (t.getMem (BitVec.ofNat 64 0x648))
        (t.getMem (BitVec.ofNat 64 0x650)) (t.getMem (BitVec.ofNat 64 0x658))
        (t.getMem (BitVec.ofNat 64 0x660)) (t.getMem (BitVec.ofNat 64 0x668))
        (t.getMem (BitVec.ofNat 64 0x670)) (t.getMem (BitVec.ofNat 64 0x678)) := by
  rw [readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ,
    readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ,
    readWords_ofNat_succ, readWords_ofNat_succ]
  simp only [rndPackWords]
  rw [blk2844_word0, blk2844_word1, blk2844_word2, blk2844_word3, blk2844_word4, blk2844_word5, blk2844_word6, blk2844_word7]
  rfl

theorem blk2844_frame (t : MachineState) :
    Frame t (blk2844.res.toState t) (fun a => 0x780 ≤ a ∧ a < 0x7c0) := by
  apply frame_toState
  intro x hx hW
  simp only [blk2844.res, rv_simp, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, ne_eq, ofNat_eq_iff]
  omega

theorem blk2844_regs (t : MachineState) :
    RegsEq t (blk2844.res.toState t)
      [.x1, .x2, .x3, .x4, .x6, .x8, .x9, .x10, .x11, .x12, .x13] := by
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl
theorem blk2844_rnd (t : MachineState) (S m : List Byte)
    (hS : S.length = 32) (hm : m.length = 32)
    (rs : t.readWords (BitVec.ofNat 64 0x640) 4 = wordsOf S)
    (rm : t.readWords (BitVec.ofNat 64 0x660) 4 = wordsOf m) :
    (blk2844.res.toState t).readWords (BitVec.ofNat 64 0x780) 8 =
      wordsOf (rndInput S m 0) := by
  let s0 := t.getMem (BitVec.ofNat 64 0x640)
  let s1 := t.getMem (BitVec.ofNat 64 0x648)
  let s2 := t.getMem (BitVec.ofNat 64 0x650)
  let s3 := t.getMem (BitVec.ofNat 64 0x658)
  let m0 := t.getMem (BitVec.ofNat 64 0x660)
  let m1 := t.getMem (BitVec.ofNat 64 0x668)
  let m2 := t.getMem (BitVec.ofNat 64 0x670)
  let m3 := t.getMem (BitVec.ofNat 64 0x678)
  have hsw : wordsOf S = [s0, s1, s2, s3] := by
    rw [← rs]
    rw [readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ]
    rfl
  have hmw : wordsOf m = [m0, m1, m2, m3] := by
    rw [← rm]
    rw [readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ, readWords_ofNat_succ]
    rfl
  have hsbytes := eq_of_words4 S hS s0 s1 s2 s3 hsw
  have hmbytes := eq_of_words4 m hm m0 m1 m2 m3 hmw
  rw [blk2844_words]
  simpa [hsbytes, hmbytes] using (words_rndInput_packed s0 s1 s2 s3 m0 m1 m2 m3).symm

theorem rndW7a_replace1 (w m3 : Word) (a : Nat)
    (h : lo32 w = lo32 (rndW7 m3)) :
    replaceWord32 w 1 (BitVec.ofNat 32 a) = rndW7a m3 a := by
  have hlo : lo32 (rndW7 m3) = hi32 m3 := by
    unfold rndW7
    rw [BitVec.ushiftRight_eq_extractLsb'_of_lt (n := 32) (by decide)]
    change BitVec.extractLsb' 0 32 (0#32 ++ hi32 m3) = hi32 m3
    exact BitVec.extractLsb'_append_eq_right
  have hrep : replaceWord32 w 1 (BitVec.ofNat 32 a) = BitVec.ofNat 32 a ++ lo32 w := by
    calc
      replaceWord32 w 1 (BitVec.ofNat 32 a) =
          hi32 (replaceWord32 w 1 (BitVec.ofNat 32 a)) ++
            lo32 (replaceWord32 w 1 (BitVec.ofNat 32 a)) := by
              simpa [hi32, lo32] using
                (BitVec.extractLsb'_append_extractLsb'
                  (w := 32) (len := 32) (x := replaceWord32 w 1 (BitVec.ofNat 32 a))).symm
      _ = BitVec.ofNat 32 a ++ lo32 w := by simp
  have hpack : rndW7a m3 a = BitVec.ofNat 32 a ++ hi32 m3 := by
    unfold rndW7a
    rw [BitVec.ushiftRight_eq_extractLsb'_of_lt (by omega)]
    rw [BitVec.shiftLeft_eq_concat_of_lt (by omega)]
    change (0#32 ++ hi32 m3) ||| (lo32 (BitVec.ofNat 64 a) ++ 0#32) =
      BitVec.ofNat 32 a ++ hi32 m3
    rw [BitVec.or_append]
    simp
  rw [hrep, hpack]
  simpa [hlo] using congrArg (fun q => BitVec.ofNat 32 a ++ q) h

theorem blk65_word7 (t : MachineState) :
    (blk65.res.toState t).getMem (BitVec.ofNat 64 0x7b8) =
      replaceWord32 (t.getMem (BitVec.ofNat 64 0x7b8)) 1 (lo32 (t.getReg .x6)) := by
  simp (config := { decide := true }) only [blk65.res, rv_simp, lo32, ↓reduceIte]
  rfl

theorem blk65_lo32 (t : MachineState) :
    lo32 ((blk65.res.toState t).getMem (BitVec.ofNat 64 0x7b8)) =
      lo32 (t.getMem (BitVec.ofNat 64 0x7b8)) := by
  rw [blk65_word7, lo32_replace1]

theorem blk65_rndW7a (t : MachineState) (m3 : Word) (a : Nat)
    (h6 : t.getReg .x6 = BitVec.ofNat 64 a)
    (hlo : lo32 (t.getMem (BitVec.ofNat 64 0x7b8)) = lo32 (rndW7 m3)) :
    (blk65.res.toState t).getMem (BitVec.ofNat 64 0x7b8) = rndW7a m3 a := by
  rw [blk65_word7, h6, lo32_ofNat]
  exact rndW7a_replace1 _ _ _ hlo

theorem readRndWords_append7 (t : MachineState) :
    t.readWords (BitVec.ofNat 64 0x780) 8 =
      t.readWords (BitVec.ofNat 64 0x780) 7 ++ [t.getMem (BitVec.ofNat 64 0x7b8)] := by
  rw [show (8 : Nat) = 7 + 1 from rfl, readWords_ofNat_add]
  simp only [Nat.reduceMul, Nat.reduceAdd, readWords_ofNat_one]

theorem rndPackWords_trial (u t1 : MachineState) (s0 s1 s2 s3 m0 m1 m2 m3 : Word) (a : Nat)
    (hbase : u.readWords (BitVec.ofNat 64 0x780) 8 = rndPackWords s0 s1 s2 s3 m0 m1 m2 m3)
    (hpre : t1.readWords (BitVec.ofNat 64 0x780) 7 = u.readWords (BitVec.ofNat 64 0x780) 7)
    (hlast : t1.getMem (BitVec.ofNat 64 0x7b8) = rndW7a m3 a) :
    t1.readWords (BitVec.ofNat 64 0x780) 8 = rndPackWordsAt s0 s1 s2 s3 m0 m1 m2 m3 a := by
  have hp := congrArg (List.take 7) hbase
  rw [readRndWords_append7] at hp
  have hlen : (u.readWords (BitVec.ofNat 64 0x780) 7).length = 7 := by
    simp [MachineState.readWords]
  rw [List.take_append_of_le_length (show 7 ≤ (u.readWords (BitVec.ofNat 64 0x780) 7).length by omega),
    List.take_of_length_le (show (u.readWords (BitVec.ofNat 64 0x780) 7).length ≤ 7 by omega)] at hp
  simp only [rndPackWords] at hp
  rw [readRndWords_append7, hpre, hp, hlast]
  rfl
end SigGolfCandidate.Sign
