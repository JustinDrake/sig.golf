import SigGolfCandidate.T3M.Verify.Common
import SigGolfCandidate.T3M.Submission

/-!
# The initial state of the verify phase (T3M)

`init_ok` : the initial state of `T3M.submission`'s verify phase on `(m, pk, w)` has all registers zero except
`sp` (`KnownOK k0`), `pc = 0x1000`, the message doublewords at `0x40`, the public key at `0xA0`, the witness
doublewords from `0x800` **and zero memory after the witness** (`WitAll w`: `wword w j`, zero past `W`), and zero
memory everywhere else below the witness.

The loader lemma: `bytesToWordLE` of eight consecutive bytes of `Legacy.bytes x` is the corresponding doubleword
of `x` (`bytes_word`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

/-! ## Bytes to doublewords -/

/-- Little-endian value of a byte list. -/
def leNat8 : List (BitVec 8) → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leNat8 l

theorem shl_or (X y k : Nat) (hX : X < 2 ^ k) : X ||| y * 2 ^ k = X + 2 ^ k * y := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring

theorem zext_shl_toNat (b : BitVec 8) (k : Nat) (hk : k ≤ 56) :
    ((b.zeroExtend 64 : Word) <<< (BitVec.ofNat 64 k)).toNat = b.toNat * 2 ^ k := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ (8 + k) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)

theorem leNat8_lt : ∀ l : List (BitVec 8), leNat8 l < 256 ^ l.length
  | [] => by simp [leNat8]
  | b :: l => by
    have := leNat8_lt l
    have hb := b.isLt
    simp only [leNat8, List.length_cons, pow_succ]
    have : b.toNat < 256 := by simpa using hb
    nlinarith

theorem bytesToWordLE8_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]).toNat =
      leNat8 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [bytesToWordLE, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BitVec.toNat_or, leNat8]
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
    show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
    show (40 : Word) = BitVec.ofNat 64 40 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    show (56 : Word) = BitVec.ofNat 64 56 from rfl]
  rw [zext_shl_toNat _ _ (by decide), zext_shl_toNat _ _ (by decide), zext_shl_toNat _ _ (by decide),
    zext_shl_toNat _ _ (by decide), zext_shl_toNat _ _ (by decide), zext_shl_toNat _ _ (by decide),
    zext_shl_toNat _ _ (by decide)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  generalize b0.toNat = x0 at *; generalize b1.toNat = x1 at *; generalize b2.toNat = x2 at *
  generalize b3.toNat = x3 at *; generalize b4.toNat = x4 at *; generalize b5.toNat = x5 at *
  generalize b6.toNat = x6 at *; generalize b7.toNat = x7 at *
  rw [Nat.mod_eq_of_lt (show x0 < 2 ^ 64 by omega), shl_or x0 x1 8 (by omega),
    shl_or _ x2 16 (by omega), shl_or _ x3 24 (by omega), shl_or _ x4 32 (by omega),
    shl_or _ x5 40 (by omega), shl_or _ x6 48 (by omega), shl_or _ x7 56 (by omega)]
  norm_num
  omega

theorem bytesToWordLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7] =
      BitVec.ofNat 64 (leNat8 [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := leNat8_lt [b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [List.length_cons, List.length_nil] at hlt
  rw [bytesToWordLE8_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; exact hlt)]

theorem bytesToWordLE_len8 (l : List (BitVec 8)) (hl : l.length = 8) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact bytesToWordLE8 b0 b1 b2 b3 b4 b5 b6 b7

theorem length_bytes {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]

/-- Consecutive bytes of `bytes x` as a little-endian value. -/
theorem leNat8_slice {n : Nat} (x : Bytes n) : ∀ k a, a + k ≤ n →
    leNat8 (((bytes x).drop a).take k) = x.toNat / 2 ^ (8 * a) % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro a _; simp only [List.take_zero, leNat8, Nat.mul_zero, pow_zero, Nat.mod_one]
  | succ k ih =>
    intro a h
    have ha : a < (bytes x).length := by rw [length_bytes]; omega
    rw [List.drop_eq_getElem_cons ha, List.take_succ_cons, leNat8, ih (a + 1) (by omega)]
    have hb : ((bytes x)[a]'ha).toNat = x.toNat / 2 ^ (8 * a) % 2 ^ 8 := by
      simp only [bytes, List.getElem_map, List.getElem_range, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow]
    rw [hb, show 8 * (a + 1) = 8 * a + 8 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add 2 8 (8 * k), Nat.mod_mul]

/-- **The loader**: eight consecutive bytes of `bytes x` form the doubleword `x[64 j, 64 j + 64)`. -/
theorem bytes_word {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rw [bytesToWordLE_len8 _ (by simp [length_bytes]; omega), leNat8_slice x 8 (8 * j) h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring, show 8 * 8 = 64 by rfl, Nat.mod_mod]

/-! ## The initial state -/

/-- All registers except `x2` are zero in the initial state. -/
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]

/-- The initial verify state on `(m, pk, w)`. -/
structure InitOK (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (0x40 + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0x40 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  /-- The embedded data words at `DATA` (T3K). -/
  data : DataOK s

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem verifyData_length : (submission.image .verify).data.length = 16480 := rfl

theorem dataBase_verify : dataBase (submission.image .verify) = HDATA := by
  unfold dataBase; rw [verifyData_length]; decide

/-- Expected doubleword at a physical index in the image data. -/
def physicalWord (k : Nat) : Nat := if k < 2048 then headerWord k else dataWords.getD (k - 2048) 0

/-- A linear-time, kernel-reduced check of all image doublewords. -/
def imageWordsCheck : List (BitVec 8) → Nat → Bool
  | [], _ => true
  | a :: b :: c :: d :: e :: f :: g :: h :: tail, k =>
      (bytesToWordLE [a,b,c,d,e,f,g,h] == BitVec.ofNat 64 (physicalWord k)) && imageWordsCheck tail (k + 1)
  | _, _ => false

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem verifyData_checked : imageWordsCheck (submission.image .verify).data 0 = true := by decide +kernel

/-- A successful word check certifies every aligned eight-byte slice. -/
theorem imageWordsCheck_word (j : Nat) : ∀ (l : List (BitVec 8)) (k : Nat),
    imageWordsCheck l k = true → 8 * j + 8 ≤ l.length →
    bytesToWordLE ((l.drop (8 * j)).take 8) = BitVec.ofNat 64 (physicalWord (k + j)) := by
  induction j with
  | zero =>
    intro l k h hl
    match l with
    | a :: b :: c :: d :: e :: f :: g :: h' :: tail =>
      simp only [imageWordsCheck, Bool.and_eq_true] at h
      have H := h.1
      simpa only [Nat.mul_zero, List.drop_zero, List.take_succ_cons, List.take_zero,
        Nat.add_zero, beq_iff_eq] using H
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] =>
      simp_all
  | succ j ih =>
    intro l k h hl
    match l with
    | a :: b :: c :: d :: e :: f :: g :: h' :: tail =>
      simp only [imageWordsCheck, Bool.and_eq_true] at h
      have H := h.2
      have ht : 8 * j + 8 ≤ tail.length := by simp only [List.length_cons] at hl; omega
      have H' := ih tail (k + 1) H ht
      rw [show 8 * (j + 1) = 8 * j + 8 by omega]
      simpa only [List.drop_succ_cons, Nat.add_succ, Nat.add_zero,
        show k + 1 + j = k + (j + 1) by omega] using H'
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] =>
      simp_all
    | [_,_,_,_] => simp_all

/-- Every logical data index reads its exact image value. -/
theorem verifyData_word (k : Nat) (hk : k < 2060) :
    bytesToWordLE ((((submission.image .verify).data).drop (dataOffset k)).take 8) =
      BitVec.ofNat 64 (dataValue k) := by
  by_cases h : k < 12
  · have H := imageWordsCheck_word (2048 + k) _ 0 verifyData_checked (by rw [verifyData_length]; omega)
    simpa only [dataOffset, dataValue, if_pos h, Nat.zero_add, physicalWord,
      if_neg (by omega : ¬ 2048 + k < 2048), show 2048 + k - 2048 = k by omega,
      show 8 * (2048 + k) = 16384 + 8 * k by ring] using H
  · have H := imageWordsCheck_word (k - 12) _ 0 verifyData_checked (by rw [verifyData_length]; omega)
    simpa only [dataOffset, dataValue, if_neg h, Nat.zero_add, physicalWord,
      if_pos (by omega : k - 12 < 2048)] using H

theorem init_ok (m : Legacy.Message) (pk : PublicKey) (w : Bytes 25240) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : InitOK m pk w s := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(0x40, bytes m), (0xA0, bytes pk), (0x800, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 25240 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 0x40) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x800) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if HDATA ≤ A ∧ A < HDATA + 8 * ((16480 + 7) / 8) ∧ (A - HDATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - HDATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold HDATA; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < HDATA → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold HDATA at hA; omega), if_neg (by omega)]
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if 0x40 ≤ A ∧ A < 0x40 + 8 * ((32 + 7) / 8) ∧ (A - 0x40) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x40)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 0x40 A (by rw [lm]; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((25240 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x800)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x800 A (by rw [lw]; omega) hA, lw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hr1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).regs = st.regs := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    have hr : s3.regs = blank.regs := by simp only [s3, s2, s1, s0, hr1]
    simp only [k0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MachineState.setReg, MachineState.getReg, hr, blank]
  · have hp1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).pc = st.pc := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    simp only [MachineState.pc_setReg, s3, s2, s1, s0, hp1, blank]
    rfl
  · intro k hk
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_pos (by omega), show 0x40 + 8 * k - 0x40 = 8 * k by omega, bytes_word m k (by omega)]
  · refine ⟨?_, ?_⟩
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA0) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA0 : Nat) - 0xA0 = 8 * 0 by rfl, bytes_word pk 0 (by omega)]
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA8) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA8 : Nat) - 0xA0 = 8 * 1 by rfl, bytes_word pk 1 (by omega)]
  · intro j hj
    unfold WX at hj
    rw [gm, g3 _ (by unfold WIT; omega)]
    by_cases hw : 8 * j < 25240
    · rw [if_pos (by unfold WIT; omega), show WIT + 8 * j - 0x800 = 8 * j by unfold WIT; omega,
        bytes_word w j (by omega)]
      rfl
    · rw [if_neg (by unfold WIT; omega), g2 _ (by unfold WIT; omega), if_neg (by unfold WIT; omega),
        g1 _ (by unfold WIT; omega), if_neg (by unfold WIT; omega), g0z _ (by unfold WIT HDATA; omega),
        wword_zero w j (by omega)]
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by omega), g0z A (by unfold HDATA; omega)]
  · intro k hk
    obtain ⟨hk1, hk2⟩ := DATA_ge k hk
    have he : dataAddr k - HDATA = dataOffset k := by
      unfold dataAddr dataOffset DATA HDATA; split_ifs <;> omega
    have ha : HDATA ≤ dataAddr k ∧ dataAddr k < HDATA + 8 * ((16480 + 7) / 8) ∧
        (dataAddr k - HDATA) % 8 = 0 := by
      unfold dataAddr HDATA DATA; split_ifs <;> omega
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by omega), g0 _ (by omega), if_pos ha, he, verifyData_word k hk]

end SigGolfCandidate.T3M.Verify
