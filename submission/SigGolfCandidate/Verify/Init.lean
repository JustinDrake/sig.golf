import SigGolfCandidate.Verify.PorsRuns
import SigGolfCandidate.Verify.Common

/-! # The initial state of the verify phase -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem wbw_regs : ∀ (n : Nat) (bytes : List (BitVec 8)) (s : MachineState) (base : Word),
    bytes.length ≤ n → (s.writeBytesAsWords base bytes).regs = s.regs := by
  intro n
  induction n with
  | zero => intro bytes s base h; rw [List.eq_nil_of_length_eq_zero (l := bytes) (by omega)]; simp
  | succ n ih =>
    intro bytes s base h
    cases bytes with
    | nil => simp
    | cons b bs =>
      unfold MachineState.writeBytesAsWords
      rw [ih _ _ _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega)]
      rfl

theorem wbw_mem : ∀ (n : Nat) (bytes : List (BitVec 8)) (s : MachineState) (base : Nat),
    bytes.length ≤ 8 * n → base + 8 * n < 2 ^ 64 → ∀ A, A < 2 ^ 64 →
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bytes).getMem (BitVec.ofNat 64 A) =
      if base ≤ A ∧ A < base + 8 * ((bytes.length + 7) / 8) ∧ (A - base) % 8 = 0 then
        bytesToWordLE ((bytes.drop (A - base)).take 8)
      else s.getMem (BitVec.ofNat 64 A) := by
  intro n
  induction n with
  | zero =>
    intro bytes s base h _ A _
    rw [List.eq_nil_of_length_eq_zero (l := bytes) (by omega)]
    simp only [List.length_nil, MachineState.writeBytesAsWords_nil]
    rw [if_neg (by omega)]
  | succ n ih =>
    intro bytes s base h hb A hA
    cases bytes with
    | nil =>
      simp only [List.length_nil, MachineState.writeBytesAsWords_nil]
      rw [if_neg (by omega)]
    | cons b bs =>
      unfold MachineState.writeBytesAsWords
      simp only []
      rw [show BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base + 8) by
        rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]]
      rw [ih _ _ _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega) (by omega) A hA]
      simp only [List.length_drop, List.length_cons]
      by_cases h1 : base + 8 ≤ A ∧ A < base + 8 + 8 * (((bs.length + 1 - 8) + 7) / 8) ∧ (A - (base + 8)) % 8 = 0
      · rw [if_pos h1, if_pos (by omega)]
        rw [List.drop_drop, show 8 + (A - (base + 8)) = A - base by omega]
      · rw [if_neg h1]
        rw [getMem_setMem]
        by_cases h2 : A = base
        · subst h2
          rw [if_pos rfl, if_pos (by omega)]
          simp
        · rw [if_neg (by rw [ofNat_eq_iff hA (by omega)]; exact h2)]
          rw [if_neg]
          intro ⟨h3, h4, h5⟩
          apply h1
          refine ⟨by omega, by omega, by omega⟩

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

theorem bytesToWordLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7] = w64 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  apply BitVec.eq_of_toNat_eq
  rw [w64_toNat _ (by simp)]
  simp only [bytesToWordLE, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BitVec.toNat_or, leNat]
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

theorem bytesToWordLE_pad (bs : List (BitVec 8)) (k : Nat) :
    bytesToWordLE (bs ++ zeros k) = bytesToWordLE bs := by
  have h : ∀ i : Nat, (bs ++ zeros k)[i]?.getD (0 : BitVec 8) = bs[i]?.getD 0 := by
    intro i
    by_cases hi : i < bs.length
    · rw [List.getElem?_append_left hi]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := bs) (by omega)]
      simp only [zeros, List.getElem?_replicate]
      split <;> rfl
  simp only [bytesToWordLE, h]

theorem bytesToWordLE_eq (bs : List (BitVec 8)) (hb : bs.length ≤ 8) : bytesToWordLE bs = w64 bs := by
  rw [← bytesToWordLE_pad bs (8 - bs.length)]
  have hw : w64 bs = w64 (bs ++ zeros (8 - bs.length)) := by
    simp only [w64, leNat_append, leNat_zeros]; simp
  rw [hw]
  have hl : (bs ++ zeros (8 - bs.length)).length = 8 := by simp; omega
  generalize bs ++ zeros (8 - bs.length) = l at hl ⊢
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact bytesToWordLE8 b0 b1 b2 b3 b4 b5 b6 b7

theorem wbw_word (bytes : List (BitVec 8)) (s : MachineState) (base : Nat) (hb : base + bytes.length + 8 < 2 ^ 64)
    (j : Nat) (hj : 8 * j < bytes.length) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bytes).getMem (BitVec.ofNat 64 (base + 8 * j)) =
      w64 (slice bytes (8 * j) 8) := by
  rw [wbw_mem ((bytes.length + 7) / 8) bytes s base (by omega) (by omega) _ (by omega), if_pos (by omega),
    show base + 8 * j - base = 8 * j by omega, bytesToWordLE_eq _ (by simp)]
  rfl

theorem wbw_frame (bytes : List (BitVec 8)) (s : MachineState) (base : Nat) (hb : base + bytes.length + 8 < 2 ^ 64)
    (A : Nat) (hA : A < 2 ^ 64) (h : A < base ∨ base + 8 * ((bytes.length + 7) / 8) ≤ A) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bytes).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [wbw_mem ((bytes.length + 7) / 8) bytes s base (by omega) (by omega) _ hA, if_neg (by omega)]

/-! ## The verifier's data: the leaf header table, the root tag, the masks -/

theorem flatMap8_length {α : Type} (f : Nat → List α) (hf : ∀ n, (f n).length = 8) :
    ∀ N, ((List.range N).flatMap f).length = 8 * N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf]
    omega

theorem flatMap8_slice {α : Type} (f : Nat → List α) (hf : ∀ n, (f n).length = 8) :
    ∀ N n, n < N → (((List.range N).flatMap f).drop (8 * n)).take 8 = f n := by
  intro N
  induction N with
  | zero => intro n h; omega
  | succ N ih =>
    intro n hn
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases h : n < N
    · rw [List.drop_append_of_le_length (by rw [flatMap8_length f hf]; omega),
        List.take_append_of_le_length (by rw [List.length_drop, flatMap8_length f hf]; omega), ih n h]
    · have e : n = N := by omega
      subst e
      rw [List.drop_left' (flatMap8_length f hf n), List.take_of_length_le (Nat.le_of_eq (hf n))]

/-- The 8 little-endian bytes of leaf header `n`. -/
def rtBlk (n : Nat) : List (BitVec 8) :=
  (List.range 8).map fun k => BitVec.ofNat 8 ((Ref.Rev.revWord (2 ^ 14 ||| n)).toNat / 256 ^ k)

/-- The data after the leaf header table: the root tag and the two mask words. -/
def vdTail : List (BitVec 8) :=
  [1, 4, 4, 0, 0, 0, 0, 0,
   0xc7, 0x71, 0x1c, 0xc7, 0x71, 0x1c, 0xc7, 0x71, 0x3f, 0xf0, 0x03, 0x3f, 0xf0, 0x03, 0x3f, 0xf0]

/-- The duplicated masks and tag are close to the preserved initial stack pointer. -/
def vdHead : List (BitVec 8) :=
  [0xc7,0x71,0x1c,0xc7,0x71,0x1c,0xc7,0x71,
   0x3f,0xf0,0x03,0x3f,0xf0,0x03,0x3f,0xf0,
   1,4,4,0,0,0,0,0, 0,0,0,0,0,0,0,0]

def vdBody : List (BitVec 8) := (List.range 16385).flatMap rtBlk ++ vdTail

theorem vd_eq : Images.verifyData = vdHead ++ vdBody := rfl

theorem rtBlk_length (n : Nat) : (rtBlk n).length = 8 := by simp [rtBlk]

theorem vdHead_length : vdHead.length = 32 := rfl

theorem vdBody_length : vdBody.length = 131104 := by
  rw [vdBody, List.length_append, flatMap8_length rtBlk rtBlk_length]
  simp [vdTail]

theorem vd_length : Images.verifyData.length = 131136 := by
  rw [vd_eq, List.length_append, vdBody_length, vdHead_length]

theorem vd_after_head (off len : Nat) :
    slice Images.verifyData (32 + off) len = slice vdBody off len := by
  unfold slice
  rw [vd_eq, List.drop_append, List.drop_eq_nil_of_le (by rw [vdHead_length]; omega),
    List.nil_append, vdHead_length, Nat.add_sub_cancel_left]

theorem vd_slice_head (j : Nat) (hj : j < 4) :
    slice Images.verifyData (8 * j) 8 = slice vdHead (8 * j) 8 := by
  unfold slice
  rw [vd_eq, List.drop_append_of_le_length (by rw [vdHead_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, vdHead_length]; omega)]

theorem vd_slice (n : Nat) (hn : n < 16385) :
    slice Images.verifyData (32 + 8 * n) 8 = rtBlk n := by
  rw [vd_after_head]
  unfold slice vdBody
  rw [List.drop_append_of_le_length (by rw [flatMap8_length rtBlk rtBlk_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, flatMap8_length rtBlk rtBlk_length]; omega),
    flatMap8_slice rtBlk rtBlk_length 16385 n hn]

theorem vd_slice_hi (j : Nat) (hj : 16385 ≤ j) :
    slice Images.verifyData (32 + 8 * j) 8 = slice vdTail (8 * j - 8 * 16385) 8 := by
  rw [vd_after_head]
  unfold slice vdBody
  rw [List.drop_append, List.drop_eq_nil_of_le (by rw [flatMap8_length rtBlk rtBlk_length]; omega),
    List.nil_append, flatMap8_length rtBlk rtBlk_length]

theorem w64_rtBlk (n : Nat) : w64 (rtBlk n) = Ref.Rev.revWord (2 ^ 14 ||| n) := by
  apply BitVec.eq_of_toNat_eq
  rw [w64_toNat _ (Nat.le_of_eq (rtBlk_length n))]
  have h : leNat (rtBlk n) = (Ref.Rev.revWord (2 ^ 14 ||| n)).toNat % 256 ^ 8 :=
    leNat_map_range 8 (Ref.Rev.revWord (2 ^ 14 ||| n)).toNat
  rw [h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_eq (BitVec.isLt _) (by norm_num))

/-! ## The initial state -/

def InitOK (ml pkl wl : List Byte) (s : MachineState) : Prop :=
  MaskData s ∧ KnownOK k0 s ∧ s.pc = pcOf 0 ∧ WitAll wl s ∧ PkOK pkl s ∧
  (∀ j, j < 4 → s.getMem (BitVec.ofNat 64 (0x40 + 8 * j)) = w64 (slice ml (8 * j) 8)) ∧
  (∀ A, A < 0x800 → (A < 0x40 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0) ∧
  RtabData s

/-- The view's zero lead (`0x800 .. 0x900`). -/
theorem slice_extW_lo (l : List Byte) (j : Nat) (hj : j < 32) : slice (extW l) (8 * j) 8 = zeros 8 := by
  unfold slice extW
  rw [List.drop_append_of_le_length (by rw [length_zeros]; unfold witLead; omega)]
  unfold zeros
  rw [List.drop_replicate, List.take_append_of_le_length (by rw [List.length_replicate]; unfold witLead; omega),
    List.take_replicate]
  congr 1; unfold witLead; omega

/-- The witness words (`0x900 ..`). -/
theorem slice_extW_hi (l : List Byte) (j : Nat) (hj : 32 ≤ j) :
    slice (extW l) (8 * j) 8 = slice l (8 * (j - 32)) 8 := by
  unfold slice extW
  rw [show 8 * j = (zeros witLead).length + 8 * (j - 32) by rw [length_zeros]; unfold witLead; omega,
    List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

/-- The initial state (W1: the witness at `0x900`; the view `extW` of `0x800 .. 0x4800`). -/
theorem init_ok (m : Message) (pk : PublicKey) (w : Bytes 16128) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) :
    InitOK (toList m) (toList pk) (extW (toList w)) s := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have e1 : (submission.image .verify).data = Images.verifyData := rfl
  have vdl : Images.verifyData.length = 131136 := vd_length
  have eb : dataBase (submission.image .verify) = 0xFDFFC0 := by
    unfold dataBase
    rw [e1, vdl] <;> decide
  rw [e1, eb]
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(0x40, toList m), (0xA0, toList pk), (0x900, toList w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (toList m).length = 32 := length_toList m
  have lp : (toList pk).length = 16 := length_toList pk
  have lw : (toList w).length = 16128 := length_toList w
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set withData := blank.writeBytesAsWords (BitVec.ofNat 64 0xFDFFC0) Images.verifyData
  have dataRegs : withData.regs = blank.regs := wbw_regs 131136 _ _ _ (Nat.le_of_eq vdl)
  have dataLow : ∀ A, A < 0xFDFFC0 → withData.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [wbw_frame Images.verifyData blank 0xFDFFC0 (by omega) A (by omega) (Or.inl hA)]
    rfl
  have dataMasks : MaskData withData := by
    refine ⟨?_, ?_, ?_⟩
    · change withData.getMem (BitVec.ofNat 64 (0xFDFFC0 + 8 * 0)) = M1w
      rw [wbw_word Images.verifyData blank 0xFDFFC0 (by omega) 0 (by omega), vd_slice_head 0 (by omega)]
      decide +kernel
    · change withData.getMem (BitVec.ofNat 64 (0xFDFFC0 + 8 * 1)) = M2w
      rw [wbw_word Images.verifyData blank 0xFDFFC0 (by omega) 1 (by omega), vd_slice_head 1 (by omega)]
      decide +kernel
    · change withData.getMem (BitVec.ofNat 64 (0xFDFFC0 + 8 * 2)) = 0x40401
      rw [wbw_word Images.verifyData blank 0xFDFFC0 (by omega) 2 (by omega), vd_slice_head 2 (by omega)]
      decide +kernel
  have dataRt : RtabData withData := by
    intro n hn
    rw [show RTAB + 8 * n = 0xFDFFC0 + 8 * (n + 4) by unfold RTAB; omega,
      wbw_word Images.verifyData blank 0xFDFFC0 (by omega) (n + 4) (by omega),
      show 8 * (n + 4) = 32 + 8 * n by omega, vd_slice n (by omega)]
    exact w64_rtBlk n
  set s1 := withData.writeBytesAsWords (BitVec.ofNat 64 0x40) (toList m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (toList pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x900) (toList w)
  have hr3 : s3.regs = fun _ => 0 := by
    rw [wbw_regs 20000 _ _ _ (by omega), wbw_regs 20000 _ _ _ (by omega), wbw_regs 20000 _ _ _ (by omega), dataRegs]
  have hpc3 : s3.pc = 0x1000 := by
    simp only [s3, s2, s1, withData, MachineState.pc_writeBytesAsWords]
    rfl
  have hreg : ∀ r : Reg, r ≠ .x2 → (s3.setReg .x2 (BitVec.ofNat 64 0xFDFFC0)).getReg r = 0 := by
    intro r hr2
    rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr2)]
    cases r <;> first | rfl | (show s3.regs _ = 0; rw [hr3])
  have hpcT : (s3.setReg .x2 (BitVec.ofNat 64 0xFDFFC0)).pc = 0x1000 := by
    rw [MachineState.pc_setReg, hpc3]
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 0xFDFFC0)).getMem A = s3.getMem A :=
    fun A => by simp [MachineState.setReg, MachineState.getMem]
  have fr : ∀ A, A < 2 ^ 64 → 0x4800 ≤ A →
      (s3.setReg .x2 (BitVec.ofNat 64 0xFDFFC0)).getMem (BitVec.ofNat 64 A) =
        withData.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    rw [gm, wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
      wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
      wbw_frame _ _ _ (by omega) _ (by omega) (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(fr 0xFDFFC0 (by decide) (by decide)).trans dataMasks.1,
      (fr 0xFDFFC8 (by decide) (by decide)).trans dataMasks.2.1,
      (fr 0xFDFFD0 (by decide) (by decide)).trans dataMasks.2.2⟩
  · intro p hp
    have hx2 : (s3.setReg .x2 (BitVec.ofNat 64 0xFDFFC0)).getReg .x2 = BitVec.ofNat 64 0xFDFFC0 :=
      MachineState.getReg_setReg_eq (by decide)
    simp only [k0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hx2 | exact hreg _ (by decide)
  · rw [hpcT]
    rfl
  · intro j hj
    by_cases hj32 : j < 32
    · rw [gm, slice_extW_lo _ j hj32, wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
        wbw_frame _ _ _ (by omega) _ (by omega) (by omega), wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
        dataLow _ (by omega)]
      rfl
    · rw [gm, slice_extW_hi _ j (by omega), show 0x800 + 8 * j = 0x900 + 8 * (j - 32) by omega,
        wbw_word _ _ _ (by omega) (j - 32) (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [gm, show (0xA0 : Word) = BitVec.ofNat 64 0xA0 from rfl, wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
        show 0xA0 = 0xA0 + 8 * 0 from rfl, wbw_word _ _ _ (by omega) 0 (by omega)]
      rfl
    · rw [gm, show (0xA8 : Word) = BitVec.ofNat 64 0xA8 from rfl, wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
        show 0xA8 = 0xA0 + 8 * 1 from rfl, wbw_word _ _ _ (by omega) 1 (by omega)]
      simp only [slice]
      rw [List.take_of_length_le (by simp; omega)]
  · intro j hj
    rw [gm, wbw_frame _ _ _ (by omega) _ (by omega) (by omega), wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
      wbw_word _ _ _ (by omega) j (by omega)]
  · intro A hA hz
    rw [gm, wbw_frame _ _ _ (by omega) _ (by omega) (by omega), wbw_frame _ _ _ (by omega) _ (by omega) (by omega),
      wbw_frame _ _ _ (by omega) _ (by omega) (by omega)]
    exact dataLow _ (by omega)
  · intro n hn
    have hR : RTAB = 0xFDFFE0 := rfl
    rw [fr (RTAB + 8 * n) (by omega) (by omega)]
    exact dataRt n hn

end SigGolfCandidate.Verify
