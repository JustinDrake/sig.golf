import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv
import SigGolfCandidate.Verify.Swar

/-!
# `sign`, the counter search of a layer (`enc_loop`, instructions 294 .. 329)

`encLoop_sim` : from `enc_loop` with counter `c`, the machine refines
`searchCounter lay tau e M c (2^22 - c)`.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The selector uses only the otherwise forbidden padding bit of the low half. -/
theorem encoding_bit63 (a : BitVec 256) :
    (a.extractLsb' 0 64 >>> 63) =
      if a.getLsbD 63 then (1 : Word) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hz : i = 0
  · subst i
    cases h : a.getLsbD 63 <;>
      simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, h]
    · simpa only [← BitVec.getLsbD_eq_getElem] using h
  · have hlt : ¬ 63 + i < 64 := by omega
    cases h : a.getLsbD 63 <;>
      simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, h, hz, hlt]

/-- The encoding selector checks both otherwise forbidden low-half padding bits. -/
theorem encoding_paddingSelector (a : BitVec 256) :
    ((a.extractLsb' 0 64 ||| a.extractLsb' 64 64) >>> 63) =
      if a.getLsbD 63 || a.getLsbD 127 then (1 : Word) else 0 := by
  have h0 := encoding_bit63 a
  have h1 := encoding_bit63 (a >>> 64)
  have he : (a >>> 64).extractLsb' 0 64 = a.extractLsb' 64 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi]
  rw [he] at h1
  simp only [BitVec.getLsbD_ushiftRight, show (64 + 63 : Nat) = 127 from rfl] at h1
  rw [BitVec.ushiftRight_or_distrib, h0, h1]
  cases h63 : a.getLsbD 63 <;> cases h127 : a.getLsbD 127 <;> simp [h63, h127]

/-- The gate reads exactly the two most significant bits of the first word. -/
theorem encoding_top2 (a : BitVec 256) :
    (a.extractLsb' 0 64 >>> 62) =
      (if a.getLsbD 62 then (1 : Word) else 0) +
      (if a.getLsbD 63 then (2 : Word) else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i = 0
  · subst i
    cases h62 : a.getLsbD 62 <;> cases h63 : a.getLsbD 63 <;>
      simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, h62, h63]
    all_goals simpa only [← BitVec.getLsbD_eq_getElem] using h62
  by_cases h1 : i = 1
  · subst i
    cases h62 : a.getLsbD 62 <;> cases h63 : a.getLsbD 63 <;>
      simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, h62, h63]
    all_goals simpa only [← BitVec.getLsbD_eq_getElem] using h63
  have hlt : ¬62 + i < 64 := by omega
  cases h62 : a.getLsbD 62 <;> cases h63 : a.getLsbD 63 <;>
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, h62, h63, h0, h1, hlt]
  all_goals interval_cases i <;> simp_all

theorem encoding_gateZero (a : BitVec 256) :
    ((a.extractLsb' 0 64 >>> 62) == 0#64) = !(a.getLsbD 62 || a.getLsbD 63) := by
  rw [encoding_top2]
  cases h62 : a.getLsbD 62 <;> cases h63 : a.getLsbD 63 <;> simp [h62,h63]

/-- The selected pair is AB, BC, or CD, with the explicit padding gate. -/
theorem encoding_word (a : BitVec 256) (i : Nat) (hi : i < 2) :
    (encodingAnswer a).extractLsb' (64 * i) 64 =
      if a.getLsbD 127 then
        if a.getLsbD 62 || a.getLsbD 63 then a.extractLsb' (128 + 64 * i) 64
        else a.extractLsb' (64 * i) 64
      else if a.getLsbD 63 then a.extractLsb' (64 + 64 * i) 64
      else a.extractLsb' (64 * i) 64 := by
  have hs (k : Nat) (hk : k ≤ 128) :
      (a >>> k).extractLsb' (64 * i) 64 = a.extractLsb' (k + 64 * i) 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hraw : 64 * i + j < 256 := by omega
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
      hj, hraw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold encodingAnswer
  split_ifs <;> first | exact hs _ (by omega) | rfl

theorem encoding_highBit (a : BitVec 256) :
    (a.extractLsb' 64 64 >>> 63) = if a.getLsbD 127 then (1 : Word) else 0 := by
  have h := encoding_bit63 (a >>> 64)
  have he : (a >>> 64).extractLsb' 0 64 = a.extractLsb' 64 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi]
  rw [he] at h
  simpa only [BitVec.getLsbD_ushiftRight, show (64 + 63 : Nat) = 127 from rfl] using h

def encodingOffset (a : BitVec 256) : Word :=
  let t := a.extractLsb' 0 64 >>> 62
  let b := a.extractLsb' 64 64 >>> 63
  ((((if (0#64).ult t then (1 : Word) else 0) * b) <<< 1) |||
    ((t >>> 1) * (b ^^^ 1))) <<< 3

theorem encodingOffset_eq (a : BitVec 256) :
    encodingOffset a = if a.getLsbD 127 then
      (if a.getLsbD 62 || a.getLsbD 63 then 16 else 0)
      else if a.getLsbD 63 then 8 else 0 := by
  unfold encodingOffset
  rw [encoding_top2, encoding_highBit]
  cases h62 : a.getLsbD 62 <;> cases h63 : a.getLsbD 63 <;> cases h127 : a.getLsbD 127 <;>
    simp [h62,h63,h127]

/-- Fixed branchless selector: sixteen instructions and twenty-two cycles, including caller. -/
theorem encodingSelect_steps {img : Image}
    (hc351 : CodeAt img (pcOf 351) seg351)
    (hc1800 : CodeAt img (pcOf 1800) seg1800)
    (s : MachineState) (a : BitVec 256) (hpc : s.pc = pcOf 351)
    (w0 : s.getMem 320 = a.extractLsb' 0 64)
    (w1 : s.getMem 328 = a.extractLsb' 64 64)
    (w2 : s.getMem 336 = a.extractLsb' 128 64)
    (w3 : s.getMem 344 = a.extractLsb' 192 64) :
    ∃ t, Steps img s 16 22 t ∧ t.pc = pcOf 353 ∧
      t.getReg .x1 = (encodingAnswer a).extractLsb' 0 64 ∧
      t.getReg .x2 = (encodingAnswer a).extractLsb' 64 64 ∧
      RegsEq s t [.x1, .x2, .x3] ∧ Frame s t (fun _ => False) := by
  have hjump := symRun_sound blk351 hc351 s hpc (by simp only [blk351.res, rv_simp])
  let u := blk351.res.toState s
  have hpcu : u.pc = pcOf 1800 := by simp only [u, blk351.res, rv_simp]
  have h0 : u.getMem (320#64) = a.extractLsb' 0 64 := by simpa [u, blk351.res, rv_simp] using w0
  have h1 : u.getMem (328#64) = a.extractLsb' 64 64 := by simpa [u, blk351.res, rv_simp] using w1
  have h2 : u.getMem (336#64) = a.extractLsb' 128 64 := by simpa [u, blk351.res, rv_simp] using w2
  have h3 : u.getMem (344#64) = a.extractLsb' 192 64 := by simpa [u, blk351.res, rv_simp] using w3
  have hstub := symRun_sound blk1800 hc1800 u hpcu (by
    simp only [blk1800.res, rv_simp]
    simp only [h0,h1]
    change accessValid (encodingOffset a + 328#64) 8 = true ∧
      accessValid (encodingOffset a + 320#64) 8 = true
    rw [encodingOffset_eq]
    cases h127 : a.getLsbD 127 <;> cases h63 : a.getLsbD 63 <;> cases h62 : a.getLsbD 62 <;>
      simp [h127,h63,h62,accessValid,rangeValid,MEMORY_BYTES])
  refine ⟨blk1800.res.toState u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hjump.trans hstub).of_eq rfl rfl
  · simp only [blk1800.res, rv_simp]
  · have hw := encoding_word a 0 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at hw
    rw [hw]
    simp only [blk1800.res,rv_simp]
    simp only [h0,h1]
    change u.getMem (encodingOffset a + 320#64) = _
    rw [encodingOffset_eq]
    cases h127 : a.getLsbD 127 <;> cases h63 : a.getLsbD 63 <;> cases h62 : a.getLsbD 62 <;>
      simp [h127,h63,h62,h0,h1,h2,h3]
  · have hw := encoding_word a 1 (by decide)
    simp only [Nat.mul_one,Nat.reduceAdd] at hw
    rw [hw]
    simp only [blk1800.res,rv_simp]
    simp only [h0,h1]
    change u.getMem (encodingOffset a + 328#64) = _
    rw [encodingOffset_eq]
    cases h127 : a.getLsbD 127 <;> cases h63 : a.getLsbD 63 <;> cases h62 : a.getLsbD 62 <;>
      simp [h127,h63,h62,h0,h1,h2,h3]
  · intro r hr
    simp only [Result.toState_getReg,u]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · intro x hx hW
    simp only [Result.toState_getMem,blk1800.res,blk351.res,u,rv_simp]


theorem slice_valOfWords_0 (w0 w1 : Word) : slice (valOfWords w0 w1) 0 8 = bytesOfWord w0 := by
  simp [slice, valOfWords]

theorem slice_valOfWords_8 (w0 w1 : Word) : slice (valOfWords w0 w1) 8 8 = bytesOfWord w1 := by
  simp [slice, valOfWords, List.drop_append_of_le_length]

/-- `decodeDigits` of a hash answer, in terms of its first two dwords. -/
theorem decodeDigits_answer (lay : Nat) (a : BitVec 256) :
    decodeDigits lay (answerBytes 16 a) =
      if (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63 then
        (if (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
            = targetFor lay then
          some (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat)
        else none)
      else none := by
  rw [answerBytes_16]
  unfold decodeDigits
  rw [slice_valOfWords_0, slice_valOfWords_8, leNat_bytesOfWord, leNat_bytesOfWord]

theorem slt_zero_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 d) (BitVec.ofNat 64 0) = decide (2 ^ 63 ≤ d) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

theorem land7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3

/-! ## The SWAR digit sum (shared with verify: `Verify.swar_nat`) -/

/-- The digit-sum masks `M1 = 0x71C7..` (3-bit digits, even positions of 6-bit lanes) and
`M2 = 0xF03F..` (6-bit lanes, even positions of 12-bit lanes). -/
abbrev swM1 : Word := BitVec.ofNat 64 8198552921648689607
abbrev swM2 : Word := BitVec.ofNat 64 17311559823019733055

/-- The four masked digit lanes. -/
def swS1 (a b m1 : Word) : Word := ((a >>> 3) &&& m1) + (a &&& m1) + ((b >>> 3) &&& m1) + (b &&& m1)

/-- One folding step `x + (x >> k)`. -/
def swF (x : Word) (k : Nat) : Word := x + (x >>> k)

/-- The machine's SWAR digit sum of `(d0, d1)` (instructions 309 .. 327). -/
def swarW (a b m1 m2 : Word) : Word :=
  swF (swF (swF (swF (swS1 a b m1) 6 &&& m2) 12) 24) 48 &&& 2047

/-- The SWAR sum, layer-target thunk, and existing equality branch. -/
def swarState (t : MachineState) : MachineState :=
  blk375.res.toState (blk1816.res.toState (blk355.res.toState t))

theorem swarState_pc_raw (t : MachineState) : (swarState t).pc =
    if (swarW (t.getReg .x1) (t.getReg .x2) (t.getReg .x26) (t.getReg .x27) +
        BitVec.ofNat 64 (2 ^ 64 - 185) +
        (if (t.getReg .x8).ult 1 then (1 : Word) else 0) != 0#64) = true then pcOf 377 else pcOf 376 := by
  simp only [swarState, blk375.res, blk1816.res, blk355.res, rv_simp,
    swarW, swF, swS1, BitVec.sub_eq_add_neg]
  rfl

theorem swF_toNat (x : Word) (k : Nat) : (swF x k).toNat = (x.toNat + x.toNat / 2 ^ k) % 2 ^ 64 := by
  rw [swF, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem swM1_toNat : swM1.toNat = 8198552921648689607 := rfl
theorem swM2_toNat : swM2.toNat = 17311559823019733055 := rfl

theorem swS1_toNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1).toNat = Verify.sw1 a b := by
  have ea : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have eb : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  rw [swS1, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and,
    BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, ea, eb,
    swM1_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 3 = 8 from rfl,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  unfold Verify.sw1
  rfl

theorem digitsOfWord_sum_le (d : Nat) : (digitsOfWord d).sum ≤ 147 := by
  have := List.sum_le_card_nsmul (digitsOfWord d) 7 (fun x hx => by
    simp only [digitsOfWord, List.mem_map, List.mem_range] at hx
    obtain ⟨r, _, rfl⟩ := hx; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)))
  simpa [digitsOfWord] using this

theorem digits_sum_le (a b : Nat) : (digitsOfWord a ++ digitsOfWord b).sum ≤ 294 := by
  rw [List.sum_append]; have := digitsOfWord_sum_le a; have := digitsOfWord_sum_le b; omega

theorem swarW_toNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (digitsOfWord a ++ digitsOfWord b).sum := by
  have key := Verify.swar_nat a b ha hb
  have hle := digits_sum_le a b
  have h1 : (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2).toNat =
      Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616) := by
    rw [BitVec.toNat_and, swF_toNat, swS1_toNat a b (by omega) (by omega), swM2_toNat,
      show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m3; rfl
  have h2 : ∀ (Y : Word) (y : Nat), Y.toNat = y → (swF (swF (swF Y 12) 24) 48).toNat = Verify.m6 y := by
    intro Y y hY
    rw [swF_toNat, swF_toNat, swF_toNat, hY, show (2 : Nat) ^ 12 = 4096 from rfl,
      show (2 : Nat) ^ 24 = 16777216 from rfl, show (2 : Nat) ^ 48 = 281474976710656 from rfl,
      show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m6 Verify.m6' Verify.m5 Verify.m4; rfl
  have h3 := h2 _ _ h1
  have h4 : (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (swF (swF (swF (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2) 12) 24) 48).toNat
        % 2048 := by
    unfold swarW
    rw [BitVec.toNat_and, show (2047 : Word).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [h4, h3]
  generalize Verify.m6 (Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616)) = X at key ⊢
  rw [← Nat.mod_mod_of_dvd X (show 2048 ∣ 4096 by norm_num), key]
  omega

theorem swar_check (lay a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 + BitVec.ofNat 64 (2 ^ 64 - targetFor lay)
      != 0#64) = !decide ((digitsOfWord a ++ digitsOfWord b).sum = targetFor lay) := by
  have h := swarW_toNat a b ha hb
  have hle := digits_sum_le a b
  generalize swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 = w at h
  have ht : targetFor lay = 184 ∨ targetFor lay = 185 := by
    unfold targetFor targetSum; split_ifs <;> omega
  have hc : (BitVec.ofNat 64 (2 ^ 64 - targetFor lay)).toNat = 2 ^ 64 - targetFor lay := by
    rcases ht with h | h <;> rw [h] <;> rfl
  by_cases hs : (digitsOfWord a ++ digitsOfWord b).sum = targetFor lay
  · have : w + BitVec.ofNat 64 (2 ^ 64 - targetFor lay) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, h, hs, hc]
      rcases ht with hh | hh <;> rw [hh] <;> rfl
    rw [this, decide_eq_true hs]; rfl
  · have : w + BitVec.ofNat 64 (2 ^ 64 - targetFor lay) ≠ 0#64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_add, h, hc] at this
      have h0 : (0#64).toNat = 0 := rfl
      rw [h0] at this
      omega
    rw [bne_iff_ne.mpr this, decide_eq_false hs]; rfl

/-- The sign test `(d0 | d1) < 0` (bit 63 of either word). -/
theorem slt_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) (BitVec.ofNat 64 0) =
      decide (2 ^ 63 ≤ a ∨ 2 ^ 63 ≤ b) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or,
    BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h1 : 2 ^ 63 ≤ a <;> by_cases h2 : 2 ^ 63 ≤ b <;> simp [h1, h2]

structure EncMem (lay tau e : Nat) (M : Val) (u : MachineState) : Prop where
  hlay : lay < 6
  htau : tau < 2 ^ 30
  he : e < 2048
  hM : M.length = 16
  eb0 : u.getMem (BitVec.ofNat 64 0x100) = twWord0 4 lay tau 0
  eb8 : u.getMem (BitVec.ofNat 64 0x108) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  ebP : u.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  ebM : u.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  eb56 : u.getMem (BitVec.ofNat 64 0x138) = 0
  x5 : u.getReg .x5 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x26 : u.getReg .x26 = swM1
  x27 : u.getReg .x27 = swM2
  x8 : u.getReg .x8 = BitVec.ofNat 64 lay

def encW (a : Nat) : Prop := a = 0x130 ∨ (0x140 ≤ a ∧ a < 0x160)

def encRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12, .x28, .x29]

def EncInv (u : MachineState) (c : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 346 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧ RegsEq u t encRegs ∧ Frame u t encW

def EncPost (lay : Nat) (u : MachineState) : Option (Nat × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 381 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (c, x), t => t.pc = pcOf 382 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧
      (∃ d0 d1, d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 ∧ x = digitsOfWord d0 ++ digitsOfWord d1 ∧ x.sum = targetFor lay ∧
        t.getReg .x1 = BitVec.ofNat 64 d0 ∧ t.getReg .x2 = BitVec.ofNat 64 d1) ∧
      RegsEq u t encRegs ∧ Frame u t encW

/-- The code of the counter search (instructions 346 .. 381) inside an image: the sign image, and the
expand image (which carries the sign's words 316 .. 381 verbatim). -/
structure EncCode (img : Image) : Prop where
  c346 : CodeAt img (pcOf 346) seg346
  c351 : CodeAt img (pcOf 351) seg351
  c353 : CodeAt img (pcOf 353) seg353
  c1800 : CodeAt img (pcOf 1800) seg1800
  c355 : CodeAt img (pcOf 355) seg355
  c375 : CodeAt img (pcOf 375) seg375
  c1816 : CodeAt img (pcOf 1816) seg1816
  c376 : CodeAt img (pcOf 376) seg376
  c377 : CodeAt img (pcOf 377) seg377
  c379 : CodeAt img (pcOf 379) seg379

/-- The sign image's counter-search code. -/
theorem encCode : EncCode image := ⟨codeAt_346, codeAt_351, codeAt_353, codeAt_1800, codeAt_355, codeAt_375, codeAt_1816, codeAt_376, codeAt_377, codeAt_379⟩

theorem searchCounter_succ (lay tau e : Nat) (M : Val) (c f : Nat) :
    searchCounter lay tau e M c (f + 1) = (encodingHash (encInput lay tau e M c) >>= fun d =>
      match decodeDigits lay d with
      | some x => pure (some (c, x))
      | none => searchCounter lay tau e M (c + 1) f) := rfl

theorem encTrial {img : Image} (hcode : EncCode img) (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u)
    (c : Nat) (t : MachineState) (hinv : EncInv u c t) (rest : OracleComp HashSpec (Option (Nat × List Nat)))
    (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 377 → t'.getReg .x6 = BitVec.ofNat 64 c → RegsEq u t' encRegs →
      Frame u t' encW → Sim img t' Wr rest (EncPost lay u)) :
    Sim img t (62 + Wr) (encodingHash (encInput lay tau e M c) >>= fun d =>
      match decodeDigits lay d with
      | some x => pure (some (c, x))
      | none => rest) (EncPost lay u) := by
  obtain ⟨tpc, t6, hc, tregs, tframe⟩ := hinv
  have hl := hmem.hlay
  have htau := hmem.htau
  have he := hmem.he
  -- block 294
  have hs1 := symRun_sound blk346 hcode.c346 t tpc (by simp only [blk346.res, rv_simp])
  have hc1 : blk346.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk346.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x130) := by
    apply frame_toState; intro x hx hW
    simp only [blk346.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk346 hcode.c346 t (by simp only [blk346.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x100 := by simp only [ht1, blk346.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk346.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk346.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hmem.x5]
  have pc1 : t1.pc = pcOf 350 := by simp only [ht1, blk346.res, rv_simp]
  have hq : hashInput t1 = pad64 (encInput lay tau e M c) := by
    obtain ⟨hn, hw⟩ := words_encInput lay tau e M hmem.hM c
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 1 + 1 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one,
      f1.getMem (a := 0x100) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x100) (by norm_num) (by simp only [encW]; omega),
      hmem.eb0, f1.getMem (a := 0x108) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x108) (by norm_num) (by simp only [encW]; omega), hmem.eb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebP,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebM,
      f1.getMem (a := 0x138) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x138) (by norm_num) (by simp only [encW]; omega), hmem.eb56]
    simp only [ht1, blk346.res, rv_simp, t6]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and, and_true]
    refine ⟨?_, ?_⟩
    · congr 1; rw [Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : e < 2 ^ 32)]
    · rw [if_pos trivial, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  have hb : (pad64 (encInput lay tau e M c)).blocks = 1 :=
    congrArg (· + 1) (words_encInput lay tau e M hmem.hM c).1
  refine (Sim.steps hs1 (Sim.encodingHash_bind (W := 50 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (addrFmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]; omega) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 351 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  have w2 : t2.getMem (BitVec.ofNat 64 0x150) = a.extractLsb' 128 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x150 x12 (by norm_num) (by norm_num)]; simp
  have w3 : t2.getMem (BitVec.ofNat 64 0x158) = a.extractLsb' 192 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x158 x12 (by norm_num) (by norm_num)]; simp
  obtain ⟨tsel, hsel, pcsel, sel0, sel1, rsel, fsel⟩ :=
    encodingSelect_steps hcode.c351 hcode.c1800 t2 a pc2 w0 w1 w2 w3
  set d0 := ((encodingAnswer a).extractLsb' 0 64).toNat with hd0
  set d1 := ((encodingAnswer a).extractLsb' 64 64).toNat with hd1
  have hd0' : (encodingAnswer a).extractLsb' 0 64 = BitVec.ofNat 64 d0 := by
    rw [hd0, BitVec.ofNat_toNat]; rfl
  have hd1' : (encodingAnswer a).extractLsb' 64 64 = BitVec.ofNat 64 d1 := by
    rw [hd1, BitVec.ofNat_toNat]; rfl
  have hd0l : d0 < 2 ^ 64 := BitVec.isLt _
  have hd1l : d1 < 2 ^ 64 := BitVec.isLt _
  rw [encodingBytes, decodeDigits_answer]
  have hsB := symRun_sound blk353 hcode.c353 tsel pcsel (by simp only [blk353.res, rv_simp])
  set t3 := blk353.res.toState tsel with ht3
  have hs3 : Steps img t2 18 24 t3 := (hsel.trans hsB).of_eq rfl rfl
  have fB : Frame tsel t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk353.res]
  have f3 : Frame t2 t3 (fun _ => False) := (fsel.trans fB).mono (by simp)
  have rB : RegsEq tsel t3 [.x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have r3 : RegsEq t2 t3 [.x1, .x2, .x3] := (rsel.trans rB).mono (by decide)
  have y1 : t3.getReg .x1 = BitVec.ofNat 64 d0 := by
    simp only [ht3, blk353.res, rv_simp]; rw [sel0, hd0']
  have y2 : t3.getReg .x2 = BitVec.ofNat 64 d1 := by
    simp only [ht3, blk353.res, rv_simp]; rw [sel1, hd1']
  have fu3 : Frame u t3 encW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [encW] at hx ⊢; rcases hx with ((h | h) | h) | h
    · exact h
    · omega
    · omega
    · exact h.elim)
  have ru3 : RegsEq u t3 encRegs := ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono
    (by decide)
  have x36 : t3.getReg .x6 = BitVec.ofNat 64 c := by
    rw [r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
  have pc3 : t3.pc = if 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1 then pcOf 377 else pcOf 355 := by
    simp only [ht3, blk353.res, rv_simp, CmpOp.eval, sel0, sel1, hd0', hd1',
      slt_or_ofNat _ _ hd0l hd1l]
    by_cases h : 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  by_cases h01 : d0 < 2 ^ 63 ∧ d1 < 2 ^ 63
  swap
  · rw [if_neg h01]
    exact (Sim.steps hs3 (hrest t3 (by rw [pc3, if_pos (by omega)]) x36 ru3 fu3)).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨h0, h1⟩ := h01
  rw [if_pos ⟨h0, h1⟩]
  have hs50 := symRun_sound blk355 hcode.c355 t3 (by rw [pc3, if_neg (by omega)])
    (by simp only [blk355.res, rv_simp])
  have hs51 := symRun_sound blk1816 hcode.c1816 (blk355.res.toState t3)
    (by simp only [blk355.res, rv_simp]) (by simp only [blk1816.res, rv_simp])
  have hs52 := symRun_sound blk375 hcode.c375 (blk1816.res.toState (blk355.res.toState t3))
    (by simp only [blk1816.res, rv_simp]) (by simp only [blk375.res, rv_simp])
  have hs5 : Steps img t3 25 25 (swarState t3) := hs50.trans (hs51.trans hs52)
  set t5 := swarState t3 with ht5
  have f50 : Frame t3 (blk355.res.toState t3) (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk355.res]
  have f51 : Frame (blk355.res.toState t3)
      (blk1816.res.toState (blk355.res.toState t3)) (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk1816.res]
  have f52 : Frame (blk1816.res.toState (blk355.res.toState t3)) t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk375.res]
  have f5 : Frame t3 t5 (fun _ => False) :=
    ((f50.trans f51).trans f52).mono (by tauto)
  have r5 : RegsEq t3 t5 [.x28, .x29] := by
    intro r hr
    unfold t5 swarState
    simp only [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fu5 : Frame u t5 encW := (fu3.trans f5).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have ru5 : RegsEq u t5 encRegs := (ru3.trans r5).mono (by decide)
  have pc5 : t5.pc = if (digitsOfWord d0 ++ digitsOfWord d1).sum = targetFor lay then pcOf 376 else pcOf 377 := by
    have hx8 : t3.getReg .x8 = BitVec.ofNat 64 lay := by rw [ru3.get .x8, hmem.x8]
    have htarget : BitVec.ofNat 64 (2 ^ 64 - 185) +
        (if (BitVec.ofNat 64 lay).ult 1 then (1 : Word) else 0) =
        BitVec.ofNat 64 (2 ^ 64 - targetFor lay) := by
      have hl := hmem.hlay
      interval_cases lay <;> decide
    rw [ht5, swarState_pc_raw, y1, y2, ru3.get .x26, hmem.x26, ru3.get .x27, hmem.x27, hx8]
    simp only [BitVec.add_assoc] at htarget ⊢
    rw [htarget, swar_check lay d0 d1 h0 h1]
    by_cases h : (digitsOfWord d0 ++ digitsOfWord d1).sum = targetFor lay
    · rw [if_pos h, if_neg (by rw [decide_eq_true h]; decide)]
    · rw [if_neg h, if_pos (by rw [decide_eq_false h]; rfl)]
  by_cases hsum : (digitsOfWord d0 ++ digitsOfWord d1).sum = targetFor lay
  · rw [if_pos hsum]
    have hs6 := symRun_sound blk376 hcode.c376 t5 (by rw [pc5, if_pos hsum])
      (by simp only [blk376.res, rv_simp])
    have hc6 : blk376.res.cycles = 1 := rfl
    rw [hc6] at hs6
    set t6 := blk376.res.toState t5 with ht6
    have f6 : Frame t5 t6 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk376.res]
    have r6 : RegsEq t5 t6 [] := by
      intro r hr; rw [ht6, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    refine (Sim.steps hs3 (Sim.steps hs5 (Sim.pure_steps hs6 ?_))).mono
      (by omega) (fun _ _ h => h)
    refine ⟨by simp only [ht6, blk376.res, rv_simp], ?_, hc, ⟨d0, d1, h0, h1, rfl, hsum, ?_, ?_⟩,
      (ru5.trans r6).mono (by decide), (fu5.trans f6).mono (by
        intro x hx; rcases hx with h | h; exact h; exact h.elim)⟩
    · rw [r6.get .x6, r5.get .x6, x36]
    · rw [r6.get .x1, r5.get .x1, y1]
    · rw [r6.get .x2, r5.get .x2, y2]
  · rw [if_neg hsum]
    exact (Sim.steps hs3 (Sim.steps hs5 (hrest t5 (by rw [pc5, if_neg hsum])
      (by rw [r5.get .x6, x36]) ru5 fu5))).mono (by omega) (fun _ _ h => h)

/-- After a failing trial (instruction 325): `c += 1`, back to the loop or fail. -/
theorem encNext {img : Image} (hcode : EncCode img) (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)) (c : Nat)
    (hc : c < 2 ^ 22) (t : MachineState) (tpc : t.pc = pcOf 377) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (tregs : RegsEq u t encRegs) (tframe : Frame u t encW) :
    ∃ t', Steps img t 2 2 t' ∧ (c + 1 < 2 ^ 22 → EncInv u (c + 1) t') ∧
      (c + 1 = 2 ^ 22 → t'.pc = pcOf 379) := by
  have hs := symRun_sound blk377 hcode.c377 t tpc (by simp only [blk377.res, rv_simp])
  have r1 : RegsEq t (blk377.res.toState t) [.x6] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22) := by rw [tregs.get .x7, hx7]
  refine ⟨_, hs, ?_, ?_⟩
  · intro h
    refine ⟨?_, ?_, h, (tregs.trans r1).mono (by decide), ?_⟩
    · simp only [blk377.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
      rw [if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · simp only [blk377.res, rv_simp, t6, ofNat_add_ofNat]
    · intro x hx hW
      rw [Result.toState_getMem, show blk377.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
  · intro h
    simp only [blk377.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
    rw [if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]

/-- **Counter search** of a layer, from counter `c` with `fuel + 1` trials left. -/
theorem encLoop_sim {img : Image} (hcode : EncCode img) (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u) :
    ∀ fuel c t, c + (fuel + 1) = 2 ^ 22 → EncInv u c t →
      Sim img t ((fuel + 1) * 64 + 2) (searchCounter lay tau e M c (fuel + 1)) (EncPost lay u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial hcode lay tau e M u hmem c t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, -, hfail⟩ := encNext hcode u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    have hs67 := symRun_sound blk379 hcode.c379 t'' (hfail (by omega)) (by simp only [blk379.res, rv_simp])
    have hc67 : blk379.res.cycles = 2 := rfl
    rw [hc67] at hs67
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Nat × List Nat))) (Q := EncPost lay u) hs67
      ⟨by simp only [blk379.res, rv_simp], by simp only [blk379.res, rv_simp],
       by simp only [blk379.res, rv_simp]⟩)
    simpa [searchCounter] using this
  | succ f ih =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial hcode lay tau e M u hmem c t hinv _ (2 + ((f + 1) * 64 + 2)) ?_).mono
      (by ring_nf; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, hinv', -⟩ := encNext hcode u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    exact Sim.steps hs (ih (c + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Sign
