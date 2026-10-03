import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.T3M.Search.TopData

/-!
# The expand initial state (stream E)

`einit m pk σ` is the loaded state (zero registers and memory, the message at `0x40`, the public key at `0xA0`,
the signature bytes at `0x7000`, `sp = 2^24`; `initialState_expand` is in `Expand/Main`). Doubleword views:
`einit_msg`, `einit_pk`, `einit_sig` (digest `k` of the signature at `0x7000 + 16 k`), `einit_zero`.
(The byte-word lemmas are local copies of K's `Keygen/Init` / S's `Sign/Basic` ones.)
-/

namespace SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (TOP_DATA TableOK expandData_length expandData_table)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

set_option autoImplicit false

/-! ## Bytes of a doubleword -/

theorem extractByte_toNat_e (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

theorem word_ext_bytes_e {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat_e] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega

theorem extractByte_or8_e (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)

theorem extractByte_bytesToWordLE_e (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8_e _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl

/-- Doubleword `j` of a loaded input buffer (`writeBytesAsWords` of `bytes x`; S's `bytesToWordLE_bytes`). -/
theorem bytesToWordLE_bytes_e {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega

theorem bytes_length_e {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]

/-! ## The loaded state -/

/-- Immutable decoder bytes loaded before input buffers. -/
def edata : MachineState :=
  ({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 TOP_DATA) Images.expandData

theorem edata_getMem (A : Nat) (hA : A < 2 ^ 64) :
    edata.getMem (BitVec.ofNat 64 A) =
      if TOP_DATA ≤ A ∧ A < TOP_DATA + 4096 ∧ (A - TOP_DATA) % 8 = 0 then
        bytesToWordLE ((Images.expandData.drop (A - TOP_DATA)).take 8) else 0 := by
  unfold edata
  rw [getMem_writeBytesAsWords _ _ TOP_DATA A (by rw [expandData_length]; decide) hA, expandData_length]
  rfl

theorem edata_zero (A : Nat) (hA : A < TOP_DATA) : edata.getMem (BitVec.ofNat 64 A) = 0 := by
  rw [edata_getMem A (by unfold TOP_DATA at hA; omega), if_neg (by omega)]

/-- The expand initial state: zero registers and memory, the message at `0x40`, the public key at `0xA0`, the
signature at `0x7000`, `sp = 2^24`. -/
def einit (m : Message) (pk : PublicKey) (σ : Bytes 5664) : MachineState :=
  (((edata.writeBytesAsWords
    (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords
    (BitVec.ofNat 64 0x7000) (bytes σ)).setReg .x2 (BitVec.ofNat 64 TOP_DATA)

theorem einit_pc (m : Message) (pk : PublicKey) (σ : Bytes 5664) : (einit m pk σ).pc = pcOf 0 := by
  unfold einit
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords]
  simp [edata, MachineState.pc_writeBytesAsWords]

theorem einit_getMem (m : Message) (pk : PublicKey) (σ : Bytes 5664) (A : Nat) (hA : A < 2 ^ 64) :
    (einit m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5664 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x40 ≤ A ∧ A < 0x60 ∧ (A - 0x40) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x40)).take 8)
      else edata.getMem (BitVec.ofNat 64 A) := by
  unfold einit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x40 A (by rw [bytes_length_e]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e]

theorem einit_msg (m : Message) (pk : PublicKey) (σ : Bytes 5664) (j : Nat) (hj : j < 4) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0x40 + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 0x40 + 8 * j - 0x40 = 8 * j by omega, bytesToWordLE_bytes_e m j (by omega)]

theorem einit_pk (m : Message) (pk : PublicKey) (σ : Bytes 5664) (j : Nat) (hj : j < 2) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_neg (by omega), if_pos (by omega),
    show 0xA0 + 8 * j - 0xA0 = 8 * j by omega, bytesToWordLE_bytes_e pk j (by omega)]

theorem einit_sigw (m : Message) (pk : PublicKey) (σ : Bytes 5664) (j : Nat) (hj : j < 708) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = σ.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega,
    bytesToWordLE_bytes_e σ j (by omega)]

/-- Digest `k` of the signature bytes at `0x7000 + 16 k`. -/
theorem einit_sig (m : Message) (pk : PublicKey) (σ : Bytes 5664) (k : Nat) (hk : k < 354) :
    DigAt (einit m pk σ) (0x7000 + 16 * k) (sigDig σ k) := by
  constructor
  · rw [show 0x7000 + 16 * k = 0x7000 + 8 * (2 * k) by ring, einit_sigw _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [sigDig, BitVec.getLsbD_extractLsb', hi, show i < 128 by omega]; ring_nf
  · rw [show 0x7000 + 16 * k + 8 = 0x7000 + 8 * (2 * k + 1) by ring, einit_sigw _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [sigDig, BitVec.getLsbD_extractLsb', hi, show 64 + i < 128 by omega]; ring_nf

theorem einit_zero (m : Message) (pk : PublicKey) (σ : Bytes 5664) (A : Nat) (hA : A < TOP_DATA)
    (h : (A < 0x7000 ∨ 0x7000 + 5664 ≤ A) ∧ (A < 0xA0 ∨ 0xB0 ≤ A) ∧ (A < 0x40 ∨ 0x60 ≤ A)) :
    (einit m pk σ).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [einit_getMem _ _ _ _ (by unfold TOP_DATA at hA; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), edata_zero A hA]

theorem einit_x5 (m : Message) (pk : PublicKey) (σ : Bytes 5664) : (einit m pk σ).getReg .x5 = 0 := by
  unfold einit
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  unfold edata
  rw [MachineState.getReg_writeBytesAsWords]
  rfl

theorem einit_table (m : Message) (pk : PublicKey) (σ : Bytes 5664) : TableOK (einit m pk σ) := by
  intro i hi
  rw [getByte_eq_word _ _ (by unfold TOP_DATA; omega),
    einit_getMem _ _ _ _ (by unfold TOP_DATA; omega),
    if_neg (by unfold TOP_DATA; omega), if_neg (by unfold TOP_DATA; omega), if_neg (by unfold TOP_DATA; omega),
    edata_getMem _ (by unfold TOP_DATA; omega), if_pos (by unfold TOP_DATA; omega),
    extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - TOP_DATA + (TOP_DATA + i) % 8 = i := by unfold TOP_DATA; omega
  rw [hidx]
  exact expandData_table i hi

end SigGolfCandidate.T3M.Expand
