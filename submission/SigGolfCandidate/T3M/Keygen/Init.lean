import SigGolfCandidate.T3M.Keygen.MainBlocks

/-!
# The keygen initial state and the `start` block

`kinit sk` is the loaded state (zero registers and memory, the secret key bytes at `0x80`,
`sp = 2^24`); `kstart` runs `start` (words 0..26) to a state satisfying `KStart`: the leaf
registers, the private prefix at `PRIV`, the secret key still at `0x80`, zero elsewhere.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-! ## Bytes of a doubleword -/

theorem extractByte_toNat' (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

theorem word_ext_bytes {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat'] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega

theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)

theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl

/-- Doubleword `j` of the loaded secret key. -/
theorem bytesToWordLE_sk (sk : SecretKey) (j : Nat) (hj : j < 4) :
    bytesToWordLE (((bytes sk).drop (8 * j)).take 8) = sk.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes
  intro i hi
  rw [extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < 32 by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := sk.isLt
  interval_cases j <;> interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega

/-! ## The loaded state -/

/-- The keygen initial state: zero registers and memory, the secret key at `0x80`, `sp = 2^24`. -/
def kinit (sk : SecretKey) : MachineState :=
  (({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).setReg .x2 (BitVec.ofNat 64 (2 ^ 24))

theorem kinit_pc (sk : SecretKey) : (kinit sk).pc = pcOf 0 := by
  unfold kinit; rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords]; rfl

theorem bytes_length (sk : SecretKey) : (bytes sk).length = 32 := by simp [bytes]

theorem kinit_getMem (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) :
    (kinit sk).getMem (BitVec.ofNat 64 A) =
      if 0x80 ≤ A ∧ A < 0xA0 ∧ (A - 0x80) % 8 = 0 then bytesToWordLE (((bytes sk).drop (A - 0x80)).take 8)
      else 0 := by
  unfold kinit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x80 A (by rw [bytes_length]; decide) hA,
    bytes_length]
  rfl

theorem kinit_sk (sk : SecretKey) (j : Nat) (hj : j < 4) :
    (kinit sk).getMem (BitVec.ofNat 64 (0x80 + 8 * j)) = sk.extractLsb' (64 * j) 64 := by
  rw [kinit_getMem sk _ (by omega), if_pos (by omega), show 0x80 + 8 * j - 0x80 = 8 * j by omega,
    bytesToWordLE_sk sk j hj]

theorem kinit_zero (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) (h : A < 0x80 ∨ 0xA0 ≤ A) :
    (kinit sk).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [kinit_getMem sk _ hA, if_neg (by omega)]

/-! ## After `start` -/

/-- The state after `start` (word 26): the leaf registers, the private prefix at `PRIV`, the secret
key at `0x80`, zero elsewhere. -/
structure KStart (sk : SecretKey) (s : MachineState) : Prop where
  pc : s.pc = pcOf 26
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x18 : s.getReg .x18 = BitVec.ofNat 64 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 ZDIG
  x26 : s.getReg .x26 = BitVec.ofNat 64 54
  x27 : s.getReg .x27 = BitVec.ofNat 64 51
  x31 : s.getReg .x31 = BitVec.ofNat 64 0
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  k0 : s.getMem (BitVec.ofNat 64 0x80) = sk.extractLsb' 0 64
  k8 : s.getMem (BitVec.ofNat 64 0x88) = sk.extractLsb' 64 64
  k16 : s.getMem (BitVec.ofNat 64 0x90) = sk.extractLsb' 128 64
  k24 : s.getMem (BitVec.ofNat 64 0x98) = sk.extractLsb' 192 64
  zero : ∀ A < 2 ^ 64, (A < 0x80 ∨ 0xA0 ≤ A) → (A < PRIV ∨ PRIV + 64 ≤ A) →
    s.getMem (BitVec.ofNat 64 A) = 0

/-- `start` from the loaded state. -/
theorem kstart (sk : SecretKey) : ∃ s, Steps image (kinit sk) 26 26 s ∧ KStart sk s := by
  obtain ⟨t, st, tpc, t2, t5, t8, t9, t18, t22, t26, t27, t31, tp0, tp8, tp32, tp40, tp48, tp56, -, tf⟩ :=
    blk0_spec (kinit sk) (kinit_pc sk)
  have k : ∀ j < 4, t.getMem (BitVec.ofNat 64 (0x80 + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj =>
    (tf.get (by omega) (by simp only [PRIV]; omega)).trans (kinit_sk sk j hj)
  refine ⟨t, st, tpc, t2, t5, t8, t9, t18, t22, t26, t27, t31, ?_, ?_, ?_, ?_, tp48, tp56, k 0 (by decide),
    k 1 (by decide), k 2 (by decide), k 3 (by decide), ?_⟩
  · rw [tp0]; exact kinit_sk sk 0 (by decide)
  · rw [tp8]; exact kinit_sk sk 1 (by decide)
  · rw [tp32]; exact kinit_sk sk 2 (by decide)
  · rw [tp40]; exact kinit_sk sk 3 (by decide)
  · intro A hA h1 h2
    rw [tf.get hA (by simp only [PRIV] at *; omega), kinit_zero sk A hA h1]

end SigGolfCandidate.T3M.Keygen
