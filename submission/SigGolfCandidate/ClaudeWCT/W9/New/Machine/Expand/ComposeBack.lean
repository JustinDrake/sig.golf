import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.T3M.Search.TopData
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.NewCode
import SigGolfCandidate.T3M.Expand.Layers
import SigGolfCandidate.T3M.Witness.Roundtrip

section




namespace SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (TOP_DATA TableOK expandData_length expandData_table)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
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
def EXPAND_DATA : Nat := 16768512
def edata : MachineState :=
  ({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 EXPAND_DATA) Images.expandData
theorem edata_getMem (A : Nat) (hA : A < 2 ^ 64) :
    edata.getMem (BitVec.ofNat 64 A) =
      if EXPAND_DATA ≤ A ∧ A < EXPAND_DATA + 8704 ∧ (A - EXPAND_DATA) % 8 = 0 then
        bytesToWordLE ((Images.expandData.drop (A - EXPAND_DATA)).take 8) else 0 := by
  unfold edata
  rw [getMem_writeBytesAsWords _ _ EXPAND_DATA A (by rw [expandData_length]; decide) hA, expandData_length]
  rfl
theorem edata_zero (A : Nat) (hA : A < EXPAND_DATA) : edata.getMem (BitVec.ofNat 64 A) = 0 := by
  rw [edata_getMem A (by unfold EXPAND_DATA at hA; omega), if_neg (by omega)]
def einit (m : Message) (pk : PublicKey) (σ : Bytes 5456) : MachineState :=
  (((edata.writeBytesAsWords
    (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords
    (BitVec.ofNat 64 0x7000) (bytes σ)).setReg .x2 (BitVec.ofNat 64 EXPAND_DATA)
theorem einit_pc (m : Message) (pk : PublicKey) (σ : Bytes 5456) : (einit m pk σ).pc = pcOf 0 := by
  unfold einit
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords]
  simp [edata, MachineState.pc_writeBytesAsWords]
theorem einit_getMem (m : Message) (pk : PublicKey) (σ : Bytes 5456) (A : Nat) (hA : A < 2 ^ 64) :
    (einit m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5456 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x40 ≤ A ∧ A < 0x60 ∧ (A - 0x40) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x40)).take 8)
      else edata.getMem (BitVec.ofNat 64 A) := by
  unfold einit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x40 A (by rw [bytes_length_e]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e]
theorem einit_msg (m : Message) (pk : PublicKey) (σ : Bytes 5456) (j : Nat) (hj : j < 4) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0x40 + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 0x40 + 8 * j - 0x40 = 8 * j by omega, bytesToWordLE_bytes_e m j (by omega)]
theorem einit_pk (m : Message) (pk : PublicKey) (σ : Bytes 5456) (j : Nat) (hj : j < 2) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_neg (by omega), if_pos (by omega),
    show 0xA0 + 8 * j - 0xA0 = 8 * j by omega, bytesToWordLE_bytes_e pk j (by omega)]
theorem einit_sigw (m : Message) (pk : PublicKey) (σ : Bytes 5456) (j : Nat) (hj : j < 682) :
    (einit m pk σ).getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = σ.extractLsb' (64 * j) 64 := by
  rw [einit_getMem _ _ _ _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega,
    bytesToWordLE_bytes_e σ j (by omega)]
theorem einit_sig (m : Message) (pk : PublicKey) (σ : Bytes 5456) (k : Nat) (hk : k < 341) :
    DigAt (einit m pk σ) (0x7000 + 16 * k) (σ.extractLsb' (128 * k) 128) := by
  constructor
  · rw [show 0x7000 + 16 * k = 0x7000 + 8 * (2 * k) by ring, einit_sigw _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi, show i < 128 by omega]; ring_nf
  · rw [show 0x7000 + 16 * k + 8 = 0x7000 + 8 * (2 * k + 1) by ring, einit_sigw _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi, show 64 + i < 128 by omega]; ring_nf
theorem einit_zero (m : Message) (pk : PublicKey) (σ : Bytes 5456) (A : Nat) (hA : A < EXPAND_DATA)
    (h : (A < 0x7000 ∨ 0x7000 + 5456 ≤ A) ∧ (A < 0xA0 ∨ 0xB0 ≤ A) ∧ (A < 0x40 ∨ 0x60 ≤ A)) :
    (einit m pk σ).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [einit_getMem _ _ _ _ (by unfold EXPAND_DATA at hA; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), edata_zero A hA]
theorem einit_x5 (m : Message) (pk : PublicKey) (σ : Bytes 5456) : (einit m pk σ).getReg .x5 = 0 := by
  unfold einit
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  unfold edata
  rw [MachineState.getReg_writeBytesAsWords]
  rfl
theorem einit_table (m : Message) (pk : PublicKey) (σ : Bytes 5456) : TableOK (einit m pk σ) := by
  intro i hi
  rw [getByte_eq_word _ _ (by simp only [TOP_DATA]; omega),
    einit_getMem _ _ _ _ (by simp only [TOP_DATA]; omega),
    if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega),
    edata_getMem _ (by simp only [TOP_DATA]; omega), if_pos (by simp only [TOP_DATA, EXPAND_DATA]; omega),
    extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - EXPAND_DATA + (TOP_DATA + i) % 8 = 4608 + i := by simp only [TOP_DATA, EXPAND_DATA]; omega
  rw [hidx]
  exact expandData_table i hi
end SigGolfCandidate.T3M.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec)
set_option linter.unusedSimpArgs false
theorem codeAt_appL {im : Image} {pc : Word} {a b : List (BitVec 32)} (h : CodeAt im pc (a ++ b)) : CodeAt im pc a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_append] at h3
  exact ⟨h1, h2, by omega, (List.prefix_append a b).trans h4⟩
theorem codeAt_appR {im : Image} {n : Nat} {a b : List (BitVec 32)} (h : CodeAt im (pcOf n) (a ++ b))
    (hn : 0x1000 + 4 * n + 4 * (a.length + b.length) < 2 ^ 64) : CodeAt im (pcOf (n + a.length)) b := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : (pcOf n).toNat = 0x1000 + 4 * n := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (pcOf (n + a.length)).toNat = 0x1000 + 4 * (n + a.length) := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [e2, show (0x1000 + 4 * (n + a.length) - 0x1000) / 4 = (0x1000 + 4 * n - 0x1000) / 4 + a.length by omega,
    ← List.drop_drop]
  rw [e1] at h4
  obtain ⟨t, ht⟩ := h4
  refine ⟨t, ?_⟩
  rw [← ht, List.append_assoc, List.drop_left]
def w9init (im : Image) (m : Message) (pk : PublicKey) (σ : Bytes 5456) : MachineState :=
  (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords (BitVec.ofNat 64 0x7000) (bytes σ))).setReg .x2
    (BitVec.ofNat 64 (dataBase im))
set_option maxRecDepth 100000 in
theorem initialState_w9 (imgs : Phase → Image) (hv : (imgs .expand).Valid (w9Sub imgs).sizes (w9Sub imgs).layout)
    (m : Message) (pk : PublicKey) (σ : Bytes 5456) :
    initialState (w9Sub imgs) .expand (m, pk, σ) = some (w9init (imgs .expand) m pk σ) := by
  unfold initialState
  simp only [show (w9Sub imgs).image .expand = imgs .expand from rfl]
  rw [if_pos hv]
  simp only [inputBuffers, List.foldl_cons, List.foldl_nil]
  rfl
theorem hdrBankBytes_length : hdrBankBytes.length = 4608 := by decide +kernel
theorem data_length {im : Image} (hd : ExpandDataOK im) : im.data.length = 8704 := by
  rw [hd, List.length_append, hdrBankBytes_length, Search.expandLegacyData_length]
theorem dataBase_eq {im : Image} (hd : ExpandDataOK im) : dataBase im = HB0 := by
  unfold dataBase
  rw [data_length hd]
  rfl
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5456)
include hd
theorem w9init_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5456 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x40 ≤ A ∧ A < 0x60 ∧ (A - 0x40) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x40)).take 8)
      else if HB0 ≤ A ∧ A < HB0 + 8704 ∧ (A - HB0) % 8 = 0 then bytesToWordLE ((im.data.drop (A - HB0)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x40 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ HB0 A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9init_msg (j : Nat) (hj : j < 4) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 (0x40 + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 0x40 + 8 * j - 0x40 = 8 * j by omega, bytesToWordLE_bytes_e m j (by omega)]
theorem w9init_pk (j : Nat) (hj : j < 2) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_pos (by omega),
    show 0xA0 + 8 * j - 0xA0 = 8 * j by omega, bytesToWordLE_bytes_e pk j (by omega)]
theorem w9init_sigw (j : Nat) (hj : j < 682) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = σ.extractLsb' (64 * j) 64 := by
  rw [w9init_getMem hd _ _ _ _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega,
    bytesToWordLE_bytes_e σ j (by omega)]
theorem w9init_sig (k : Nat) (hk : k < 341) : DigAt (w9init im m pk σ) (0x7000 + 16 * k) (sigDig σ k) := by
  constructor
  · rw [show 0x7000 + 16 * k = 0x7000 + 8 * (2 * k) by ring, w9init_sigw hd _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [ClaudeWCT.W9.T3M.sigDig, BitVec.getLsbD_extractLsb', hi, show i < 128 by omega]; ring_nf
  · rw [show 0x7000 + 16 * k + 8 = 0x7000 + 8 * (2 * k + 1) by ring, w9init_sigw hd _ _ _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [ClaudeWCT.W9.T3M.sigDig, BitVec.getLsbD_extractLsb', hi, show 64 + i < 128 by omega]; ring_nf
theorem w9init_zero (A : Nat) (hA : A < HB0)
    (h : (A < 0x7000 ∨ 0x7000 + 5456 ≤ A) ∧ (A < 0xA0 ∨ 0xB0 ≤ A) ∧ (A < 0x40 ∨ 0x60 ≤ A)) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) = 0 := by
  unfold HB0 at hA
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by unfold HB0; omega)]
theorem w9init_data (A : Nat) (h1 : HB0 ≤ A) (h2 : A < HB0 + 8704) (h3 : (A - HB0) % 8 = 0) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) = bytesToWordLE ((im.data.drop (A - HB0)).take 8) := by
  unfold HB0 at h1 h2 h3
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by unfold HB0; omega)]
omit hd in
theorem w9init_x5 : (w9init im m pk σ).getReg .x5 = 0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  rfl
omit hd in
theorem w9init_pc : (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl
end init
def bankB : Bool :=
  (List.range 9).all fun k =>
    bytesToWordLE ((hdrBankBytes.drop (512 * k + 448)).take 8) == BitVec.ofNat 64 (hdr0 3 (4 + k) 0 0) &&
    bytesToWordLE ((hdrBankBytes.drop (512 * k + 456)).take 8) == BitVec.ofNat 64 (hdr0 6 k 0 0)
set_option maxRecDepth 100000 in
theorem bankB_ok : bankB = true := by decide +kernel
theorem data_word {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 4608) :
    (im.data.drop o).take 8 = (hdrBankBytes.drop o).take 8 := by
  rw [hd, List.drop_append_of_le_length (by rw [hdrBankBytes_length]; omega),
    List.take_append_of_le_length (by simp [hdrBankBytes_length]; omega)]
theorem w9init_bank {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5456) :
    HdrBankOK (w9init im m pk σ) := by
  intro k hk
  have hb := List.all_eq_true.mp bankB_ok k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨h2, h3⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [w9init_data hd _ _ _ _ (by omega) (by unfold HB0; omega) (by omega),
      show HB0 + 512 * k + 448 - HB0 = 512 * k + 448 by omega, data_word hd _ (by omega)]
    exact h2
  · rw [w9init_data hd _ _ _ _ (by omega) (by unfold HB0; omega) (by omega),
      show HB0 + 512 * k + 456 - HB0 = 512 * k + 456 by omega, data_word hd _ (by omega)]
    exact h3
theorem w9init_table {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5456) :
    TableOK (w9init im m pk σ) := by
  intro i hi
  have hT : TOP_DATA = HB0 + 4608 := rfl
  rw [getByte_eq_word _ _ (by unfold TOP_DATA; omega),
    w9init_data hd _ _ _ _ (by unfold TOP_DATA HB0; omega) (by unfold TOP_DATA HB0; omega)
      (by unfold TOP_DATA HB0; omega),
    extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  have e : (TOP_DATA + i) / 8 * 8 - HB0 = 4608 + ((TOP_DATA + i) / 8 * 8 - TOP_DATA) := by unfold TOP_DATA HB0; omega
  rw [e, hd, ← List.drop_drop, List.drop_append_of_le_length (by rw [hdrBankBytes_length]),
    show hdrBankBytes.drop 4608 = [] from List.drop_eq_nil_of_le (by rw [hdrBankBytes_length]), List.nil_append]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - TOP_DATA + (TOP_DATA + i) % 8 = i := by unfold TOP_DATA; omega
  rw [hidx]
  exact Search.expandLegacyData_table i hi
theorem front_spec {im : Image} (hF : CodeAt im (pcOf 0) SigGolfCandidate.T3M.Expand.seg_0) (s : MachineState)
    (hpc : s.pc = pcOf 0) :
    ∃ t, Steps im s 30 30 t ∧ t.pc = pcOf 30 ∧ t.getReg .x5 = 0 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x40) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x48) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x50) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x58) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound SigGolfCandidate.T3M.Expand.eblk_0 hF s hpc
    (by simp [SigGolfCandidate.T3M.Expand.eblk_0.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, SigGolfCandidate.T3M.Expand.eblk_0.res, E.eval]
  · simp [SigGolfCandidate.T3M.Expand.eblk_0.res, rv_simp]
  · simp [SigGolfCandidate.T3M.Expand.eblk_0.res, rv_simp]
  iterate 8
    · simp only [Result.toState_getMem, SigGolfCandidate.T3M.Expand.eblk_0.res, DIG]
      t3n []
  · ex_regs SigGolfCandidate.T3M.Expand.eblk_0.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, SigGolfCandidate.T3M.Expand.eblk_0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem front_pre30 {im : Image} (hF : FrontAt im) (hd : ExpandDataOK im) (m : Message) (pk : PublicKey)
    (σ : Bytes 5456) :
    ∃ t, Steps im (w9init im m pk σ) 30 30 t ∧ Pre30 m (sigDec σ) t ∧
      t.getMem (BitVec.ofNat 64 0x800) = (sigDec σ).rho.extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 0x808) = (sigDec σ).rho.extractLsb' 64 64 ∧
      Frame (w9init im m pk σ) t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
        A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56) := by
  set s := w9init im m pk σ
  obtain ⟨t, st, p, x5, x19, w800, w808, d0, d8, d32, d40, d48, d56, r, f⟩ :=
    front_spec (codeAt_appL hF) s (w9init_pc m pk σ)
  have hrho : DigAt s 0x7000 (sigDec σ).rho := w9init_sig hd m pk σ 0 (by decide)
  have hsd : ∀ k, k < 341 → DigAt t (0x7000 + 16 * k) ((sigDigests (sigDec σ)).getD k 0) := by
    intro k hk
    have := w9init_sig hd m pk σ k hk
    rw [sigDigests_sigDec σ k hk]
    exact ⟨(f _ (by omega) (by simp only [DIG]; omega)).trans this.1,
      (f _ (by omega) (by simp only [DIG]; omega)).trans this.2⟩
  refine ⟨t, st, ⟨p, x5, x19, ⟨d0.trans hrho.1, d8.trans hrho.2⟩, fun k hk => ?_, hsd, fun A h1 h2 => ?_,
    hdrBank_frame (w9init_bank hd m pk σ) f (fun A h1 h2 h => by simp only [DIG] at h; unfold HB0 at h1; omega)⟩,
    w800.trans hrho.1, w808.trans hrho.2, f⟩
  · interval_cases k
    · rw [show DIG + 32 + 8 * 0 = DIG + 32 by rfl, d32]; simpa using w9init_msg hd m pk σ 0 (by decide)
    · rw [show DIG + 32 + 8 * 1 = DIG + 40 by rfl, d40]; simpa using w9init_msg hd m pk σ 1 (by decide)
    · rw [show DIG + 32 + 8 * 2 = DIG + 48 by rfl, d48]; simpa using w9init_msg hd m pk σ 2 (by decide)
    · rw [show DIG + 32 + 8 * 3 = DIG + 56 by rfl, d56]; simpa using w9init_msg hd m pk σ 3 (by decide)
  · rw [f A (by omega) (by simp only [DIG]; omega)]
    exact w9init_zero hd m pk σ A (by unfold HB0; omega) ⟨by omega, by omega, by omega⟩
end ClaudeWCT.W9.Machine.Expand
end

section



namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput Layer LayerSignature height chainCount)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit sideOff height_le)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (bcTopBlock layerBytesBC bcTopBlock_length)
set_option linter.unusedSimpArgs false
theorem readWords_blocks (t : MachineState) : ∀ (bs : List (List Word)) (A : Nat),
    (∀ b ∈ bs, b.length = 8) → (∀ k < bs.length, t.readWords (BitVec.ofNat 64 (A + 64 * k)) 8 = bs.getD k []) →
    t.readWords (BitVec.ofNat 64 A) (8 * bs.length) = bs.flatten
  | [], _, _, _ => rfl
  | b :: bs, A, hl, h => by
    rw [List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, readWords_add,
      show A + 8 * 8 = A + 64 by ring, List.flatten_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine readWords_blocks t bs (A + 64) (fun x hx => hl x (by simp [hx])) (fun k hk => ?_)
      have := h (k + 1) (by simp; omega)
      rw [show A + 64 * (k + 1) = A + 64 + 64 * k by ring] at this
      simpa using this
theorem wordsOf_flatMap64 {α : Type} (f : α → List UInt8) (hf : ∀ x, (f x).length = 64) :
    ∀ (xs : List α), wordsOf (xs.flatMap f) = xs.flatMap (fun x => wordsOf (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [hf]), wordsOf_flatMap64 f hf xs]
theorem wordsOf_dig_zeros48 (d : Digest) :
    wordsOf (bytesLE 16 d ++ SigGolfCandidate.T3M.zeros 48) =
      [d.extractLsb' 0 64, d.extractLsb' 64 64, 0, 0, 0, 0, 0, 0] := by
  rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
theorem wordsOf_zeros48_dig (d : Digest) :
    wordsOf (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 d) =
      [0, 0, 0, 0, 0, 0, d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by rfl), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
def lBase (lay : Layer) : Nat := ![0x3148, 0x41C8, 0x4E48, 0x5A88] lay
theorem lBase_eq (lay : Layer) : lWM lay = lBase lay + 64 * (height lay - 1) ∧
    lWC lay = lBase lay + 64 * height lay + 64 * (chainCount lay - 1) := by
  fin_cases lay <;> decide
def mkWords (leaf j : Nat) (p : Digest) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, 0, 0, 0, 0]
  else [0, 0, 0, 0, 0, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
def chWords (v : Digest) : List Word := [0, 0, 0, 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64]
def layBlocks (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List (List Word) :=
  (List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i))
theorem length_flatMap_const {α : Type} (f : α → List UInt8) (c : Nat) (hf : ∀ x, (f x).length = c) :
    ∀ (xs : List α), (xs.flatMap f).length = c * xs.length
  | [] => by simp
  | x :: xs => by rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f c hf xs]; simp; ring
theorem flatMap_eq_flatten {α β : Type} (f : α → List β) (g : α → List β) (h : ∀ x, f x = g x) :
    ∀ (xs : List α), xs.flatMap f = (xs.map g).flatten
  | [] => rfl
  | x :: xs => by rw [List.flatMap_cons, List.map_cons, List.flatten_cons, h, flatMap_eq_flatten f g h xs]
theorem layerBytes_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (SigGolfCandidate.T3M.layerBytes lay leaf ls) = (layBlocks lay leaf ls).flatten := by
  unfold SigGolfCandidate.T3M.layerBytes layBlocks
  have hm : ∀ j : Fin (height lay), ((if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++
      SigGolfCandidate.T3M.zeros 48 else SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.path j))).length = 64 := by
    intro j; split_ifs <;> simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  have hc : ∀ i : Fin (chainCount lay), (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.values i)).length = 64 := by
    intro i; simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  rw [wordsOf_append _ _ (by rw [length_flatMap_const _ 64 hm]; omega),
    wordsOf_flatMap64 _ hm, wordsOf_flatMap64 _ hc, List.flatten_append]
  rw [flatMap_eq_flatten _ (fun j => mkWords leaf j.val (ls.path j)) (fun j => by
      unfold mkWords
      split_ifs
      · exact wordsOf_dig_zeros48 _
      · exact wordsOf_zeros48_dig _),
    flatMap_eq_flatten _ (fun i => chWords (ls.values i)) (fun i => wordsOf_zeros48_dig _)]
theorem mk_block (t : MachineState) (B leaf j : Nat) (p : Digest) (hp : DigAt t (B + sideOff leaf j) p)
    (hz : ∀ r < 8, 8 * r ≠ sideOff leaf j → 8 * r ≠ sideOff leaf j + 8 →
      t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = mkWords leaf j p := by
  rw [readWords_eight]
  unfold mkWords
  unfold sideOff at hp hz
  split_ifs at hp hz ⊢ with hb
  · simp only [Nat.add_zero] at hp
    rw [hp.1, hp.2, show B + 16 = B + 8 * 2 by ring, hz 2 (by omega) (by omega) (by omega),
      show B + 24 = B + 8 * 3 by ring, hz 3 (by omega) (by omega) (by omega),
      show B + 32 = B + 8 * 4 by ring, hz 4 (by omega) (by omega) (by omega),
      show B + 40 = B + 8 * 5 by ring, hz 5 (by omega) (by omega) (by omega),
      show B + 48 = B + 8 * 6 by ring, hz 6 (by omega) (by omega) (by omega),
      show B + 56 = B + 8 * 7 by ring, hz 7 (by omega) (by omega) (by omega)]
  · have h0 := hz 0 (by omega) (by omega) (by omega)
    have h1 := hz 1 (by omega) (by omega) (by omega)
    have h2 := hz 2 (by omega) (by omega) (by omega)
    have h3 := hz 3 (by omega) (by omega) (by omega)
    have h4 := hz 4 (by omega) (by omega) (by omega)
    have h5 := hz 5 (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
      show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hp.1,
      show B + 56 = B + 48 + 8 by ring, hp.2]
theorem ch_block (t : MachineState) (B : Nat) (v : Digest) (hv : DigAt t (B + 48) v)
    (hz : ∀ r < 6, t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = chWords v := by
  rw [readWords_eight]
  have h0 := hz 0 (by omega); have h1 := hz 1 (by omega); have h2 := hz 2 (by omega)
  have h3 := hz 3 (by omega); have h4 := hz 4 (by omega); have h5 := hz 5 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
    show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hv.1,
    show B + 56 = B + 48 + 8 by ring, hv.2]
  rfl
theorem getD_rev_finRange_map {β : Type} (n : Nat) (f : Fin n → β) (d : β) (k : Nat) (hk : k < n) :
    ((List.finRange n).reverse.map f).getD k d = f ⟨n - 1 - k, by omega⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp [show n - 1 - k < n by omega]
theorem layer_words (t : MachineState) (lay : Layer) (leaf : Nat) (ls : LayerSignature lay)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainCount lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (SigGolfCandidate.T3M.layerBytes lay leaf ls) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hH := height_le lay
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  rw [layerBytes_words]
  have hlen : (layBlocks lay leaf ls).length = height lay + chainCount lay := by simp [layBlocks]
  have hl8 : ∀ b ∈ layBlocks lay leaf ls, b.length = 8 := by
    intro b hb
    simp only [layBlocks, List.mem_append, List.mem_map] at hb
    rcases hb with ⟨j, _, rfl⟩ | ⟨i, _, rfl⟩
    · unfold mkWords; split_ifs <;> rfl
    · rfl
  have key := readWords_blocks t (layBlocks lay leaf ls) (lBase lay) hl8 (fun k hk => by
    rw [hlen] at hk
    by_cases hkH : k < height lay
    · rw [layBlocks, List.getD_append _ _ _ _ (by simp; omega), getD_rev_finRange_map _ _ _ _ hkH]
      obtain ⟨j, hj⟩ : ∃ j, j = height lay - 1 - k := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWM lay - 64 * j := by omega
      have e : (⟨height lay - 1 - k, by omega⟩ : Fin (height lay)) = ⟨j, by omega⟩ := Fin.ext hj.symm
      rw [hB, e]
      refine mk_block t _ leaf j _ (hp j (by omega)) (fun r hr h1 h2 => hz _ (by omega) (by omega) ?_)
      rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rw [layBlocks, List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_reverse,
        List.length_finRange, getD_rev_finRange_map _ _ _ _ (by omega)]
      obtain ⟨i, hi⟩ : ∃ i, i = chainCount lay - 1 - (k - height lay) := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWC lay - 64 * i := by omega
      have e : (⟨chainCount lay - 1 - (k - height lay), by omega⟩ : Fin (chainCount lay)) = ⟨i, by omega⟩ :=
        Fin.ext hi.symm
      rw [hB, e]
      refine ch_block t _ _ (hv i (by omega)) (fun r hr => hz _ (by omega) (by omega) ?_)
      rintro (⟨i', hi', h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases hso j' with h4 | h4 <;> omega
      · rcases hso j' with h4 | h4 <;> omega)
  rw [hlen] at key
  exact key
theorem readWords_zero (t : MachineState) (B n : Nat) (hB : B + 8 * n < 2 ^ 64)
    (hz : ∀ j < n, t.getMem (BitVec.ofNat 64 (B + 8 * j)) = 0) :
    t.readWords (BitVec.ofNat 64 B) n = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 = n + 1 from rfl, readWords_add, ih (by omega) (fun j hj => hz j (by omega)),
      readWords_one, hz n (by omega)]
    simp [List.replicate_add]
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
theorem ctr_words (c : BitVec 32) (m : Nat) :
    wordsOf (bytesLE 4 c ++ SigGolfCandidate.T3M.zeros (4 + 8 * m)) = BitVec.ofNat 64 c.toNat :: List.replicate m 0 := by
  have hc : SigGolfCandidate.T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [SigGolfCandidate.T3M.readLE_append, SigGolfCandidate.T3M.readLE_bytesLE,
      SigGolfCandidate.T3M.readLE_replicate_zero]
    simp
  rw [show SigGolfCandidate.T3M.zeros (4 + 8 * m) = List.replicate 4 0 ++ List.replicate (8 * m) 0 by
      simp [SigGolfCandidate.T3M.zeros, List.replicate_add],
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc, wordsOf_replicate_zero]
theorem headerW_words (w : WCT9.Witness) :
    wordsOf (ClaudeWCT.W9.T3M.headerBytes w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64, BitVec.ofNat 64 w.digestCounter.toNat,
        0, BitVec.ofNat 64 (w.counters 3).toNat, 0, 0, 0] := by
  unfold ClaudeWCT.W9.T3M.headerBytes
  simp only [List.append_assoc]
  rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl,
    show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
  rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, ← List.append_assoc (bytesLE 4 _),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words, ctr_words]
  rfl
def bcWords (leaf j : Nat) (p : Digest) (c : BitVec 32) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, BitVec.ofNat 64 c.toNat, 0, 0, 0]
  else [0, 0, 0, 0, BitVec.ofNat 64 c.toNat, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
theorem bcTop_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (bcTopBlock lay leaf ls c) = bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c := by
  unfold bcTopBlock bcWords
  split_ifs with hb
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
    rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16,
      wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 16 = List.replicate (8 * 2) 0 from rfl, wordsOf_replicate_zero, ctr_words]
    rfl
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl]
    rw [wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 32 = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero,
      ← List.append_assoc (bytesLE 4 _), wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words,
      wordsOf_bytesLE16]
    rfl
theorem wordsOf_drop64 (l : List UInt8) (h : 64 ≤ l.length) :
    wordsOf (l.drop 64) = (wordsOf l).drop 8 := by
  conv_rhs => rw [← List.take_append_drop 64 l]
  rw [wordsOf_append _ _ (by simp; omega), List.drop_left' (length_wordsOf 8 _ (by simp; omega))]
theorem layerBytesBC_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (layerBytesBC lay leaf ls c) =
      bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c ++ (layBlocks lay leaf ls).flatten.drop 8 := by
  unfold layerBytesBC
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  rw [wordsOf_append _ _ (by rw [bcTopBlock_length]), bcTop_words,
    wordsOf_drop64 _ (by rw [SigGolfCandidate.T3M.layerBytes_length]; omega), layerBytes_words]
theorem layerBC_words (t : MachineState) (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hc : t.getMem (BitVec.ofNat 64 (lBase lay + 32)) = BitVec.ofNat 64 c.toNat)
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainCount lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (layerBytesBC lay leaf ls c) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hlB : lBase lay + 64 * (height lay + chainCount lay) < 2 ^ 64 := by fin_cases lay <;> decide
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  have hRne : ∀ A, RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 := by
    rintro A (⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩) he
    · omega
    · omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
  set t' := t.setMem (BitVec.ofNat 64 (lBase lay + 32)) 0 with ht'
  have g' : ∀ A, A < 2 ^ 64 → A ≠ lBase lay + 32 → t'.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA hne
    have hne' : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (lBase lay + 32) := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show lBase lay + 32 < 2 ^ 64 by omega)]
        at this
      exact hne this
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_iff_eq, hne', if_false]
  have g0 : t'.getMem (BitVec.ofNat 64 (lBase lay + 32)) = 0 := by
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_self_eq_true, if_true]
  have dig' : ∀ A d, A + 16 ≤ 2 ^ 64 → A ≠ lBase lay + 32 → A + 8 ≠ lBase lay + 32 → DigAt t A d → DigAt t' A d :=
    fun A d h1 h2 h3 hd => ⟨(g' A (by omega) h2).trans hd.1, (g' (A + 8) (by omega) h3).trans hd.2⟩
  have hW' := layer_words t' lay leaf ls
    (fun i h => dig' _ _ (by omega) (hRne _ (Or.inl ⟨i, h, Or.inl rfl⟩)) (hRne _ (Or.inl ⟨i, h, Or.inr rfl⟩))
      (hv i h))
    (fun j h => dig' _ _ (by rcases hso j with h4 | h4 <;> omega) (hRne _ (Or.inr ⟨j, h, Or.inl rfl⟩))
      (hRne _ (Or.inr ⟨j, h, Or.inr rfl⟩)) (hp j h))
    (fun A h1 h2 hn => by
      by_cases he : A = lBase lay + 32
      · rw [he, g0]
      · rw [g' A (by omega) he]; exact hz A h1 h2 hn he)
  rw [layerBytes_words] at hW'
  rw [layerBytesBC_words]
  have eM : 8 * (height lay + chainCount lay) = 8 + (8 * (height lay + chainCount lay) - 8) := by omega
  rw [eM, readWords_add] at hW' ⊢
  have hlow : t.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) =
      t'.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) := by
    have F : Frame t' t (fun A => A = lBase lay + 32) := fun A hA hn => (g' A hA hn).symm
    exact frame_readWords F _ _ (by omega) (fun i _ h => by omega)
  have hl8 : (t'.readWords (BitVec.ofNat 64 (lBase lay)) 8).length = 8 := SigGolfCandidate.Rv.readWords_length _ _ _
  rw [hlow, ← hW', List.drop_left' hl8]
  congr 1
  have hp1 := hp (height lay - 1) (by omega)
  rw [show lWM lay - 64 * (height lay - 1) = lBase lay by omega] at hp1
  have hzt : ∀ r < 8, 8 * r ≠ sideOff leaf (height lay - 1) → 8 * r ≠ sideOff leaf (height lay - 1) + 8 → r ≠ 4 →
      t.getMem (BitVec.ofNat 64 (lBase lay + 8 * r)) = 0 := by
    intro r hr h1 h2 h4
    refine hz _ (by omega) (by omega) ?_ (by omega)
    rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
    · omega
    · omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
  rw [readWords_eight]
  unfold bcWords
  unfold sideOff at hp1 hzt
  have htl : ls.path (WCT9.topLevel lay) = ls.path ⟨height lay - 1, by omega⟩ := rfl
  rw [htl]
  split_ifs at hp1 hzt ⊢ with hb
  · simp only [Nat.add_zero] at hp1
    rw [hp1.1, hp1.2, show lBase lay + 16 = lBase lay + 8 * 2 by ring, hzt 2 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 24 = lBase lay + 8 * 3 by ring, hzt 3 (by omega) (by omega) (by omega) (by omega), hc,
      show lBase lay + 40 = lBase lay + 8 * 5 by ring, hzt 5 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 48 = lBase lay + 8 * 6 by ring, hzt 6 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 56 = lBase lay + 8 * 7 by ring, hzt 7 (by omega) (by omega) (by omega) (by omega)]
  · have h0 := hzt 0 (by omega) (by omega) (by omega) (by omega)
    have h1 := hzt 1 (by omega) (by omega) (by omega) (by omega)
    have h2 := hzt 2 (by omega) (by omega) (by omega) (by omega)
    have h3 := hzt 3 (by omega) (by omega) (by omega) (by omega)
    have h5 := hzt 5 (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show lBase lay + 16 = lBase lay + 8 * 2 by ring, h2, show lBase lay + 24 = lBase lay + 8 * 3 by ring,
      h3, hc, show lBase lay + 40 = lBase lay + 8 * 5 by ring, h5, hp1.1,
      show lBase lay + 56 = lBase lay + 48 + 8 by ring, hp1.2]
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open SigGolfCandidate.T3M (window window_flatMap_const zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (regionBytes regionBytes_length wctBytes)
set_option linter.unusedSimpArgs false
section compare
variable {im : Image} (hC : CodeAt im (pcOf 342) compareCode)
include hC
theorem codeAt_342W : CodeAt im (pcOf 342) SigGolfCandidate.T3M.Expand.seg_342 :=
  codeAt_appL (codeAt_appL (codeAt_appL hC))
theorem codeAt_348W : CodeAt im (pcOf 348) SigGolfCandidate.T3M.Expand.seg_348 :=
  codeAt_appR (n := 342) (a := SigGolfCandidate.T3M.Expand.seg_342) (codeAt_appL (codeAt_appL hC)) (by decide)
theorem codeAt_351W : CodeAt im (pcOf 351) SigGolfCandidate.T3M.Expand.seg_351 :=
  codeAt_appR (n := 342) (a := SigGolfCandidate.T3M.Expand.seg_342 ++ SigGolfCandidate.T3M.Expand.seg_348)
    (codeAt_appL hC) (by decide)
theorem codeAt_353W : CodeAt im (pcOf 353) SigGolfCandidate.T3M.Expand.seg_353 :=
  codeAt_appR (n := 342) (a := SigGolfCandidate.T3M.Expand.seg_342 ++ SigGolfCandidate.T3M.Expand.seg_348 ++
    SigGolfCandidate.T3M.Expand.seg_351) hC (by decide)
variable (s : MachineState)
theorem c342W (hpc : s.pc = pcOf 342) :
    ∃ t, Steps im s 6 6 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 0xA0) then pcOf 348 else pcOf 354) ∧
      t.getReg .x28 = BitVec.ofNat 64 ENC ∧ t.getReg .x29 = BitVec.ofNat 64 0xA0 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound SigGolfCandidate.T3M.Expand.eblk_342 (codeAt_342W hC) s hpc
    (by simp [SigGolfCandidate.T3M.Expand.eblk_342.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SigGolfCandidate.T3M.Expand.eblk_342.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [SigGolfCandidate.T3M.Expand.eblk_342.res, rv_simp]
  · simp [SigGolfCandidate.T3M.Expand.eblk_342.res, rv_simp]
  · ex_regs SigGolfCandidate.T3M.Expand.eblk_342.res
  · intro A _ _; simp [SigGolfCandidate.T3M.Expand.eblk_342.res, rv_simp]
theorem c348W (hpc : s.pc = pcOf 348) (h28 : s.getReg .x28 = BitVec.ofNat 64 ENC)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 0xA0) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 0xA8) then pcOf 351 else pcOf 354) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound SigGolfCandidate.T3M.Expand.eblk_348 (codeAt_348W hC) s hpc
    (by simp [SigGolfCandidate.T3M.Expand.eblk_348.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, h29, ENC]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SigGolfCandidate.T3M.Expand.eblk_348.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC,
      h28, h29]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs SigGolfCandidate.T3M.Expand.eblk_348.res
  · intro A _ _; simp [SigGolfCandidate.T3M.Expand.eblk_348.res, rv_simp]
theorem c351W (hpc : s.pc = pcOf 351) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 353 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ fetch im t = some (.base .ECALL) ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound SigGolfCandidate.T3M.Expand.eblk_351 (codeAt_351W hC) s hpc
    (by simp [SigGolfCandidate.T3M.Expand.eblk_351.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, SigGolfCandidate.T3M.Expand.eblk_351.res, E.eval]
  · simp [SigGolfCandidate.T3M.Expand.eblk_351.res, rv_simp]
  · simp [SigGolfCandidate.T3M.Expand.eblk_351.res, rv_simp]
  · rw [(codeAt_353W hC).fetch _ (by simp [Result.toState_pc, SigGolfCandidate.T3M.Expand.eblk_351.res, E.eval])]; rfl
  · ex_regs SigGolfCandidate.T3M.Expand.eblk_351.res
  · intro A _ _; simp [SigGolfCandidate.T3M.Expand.eblk_351.res, rv_simp]
end compare
theorem codeAt_1420 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf 1420) [0x00000073] :=
  codeAt_of_window hc (by decide) (by decide +kernel)
theorem readWords_ext (t : MachineState) : ∀ (L : List Word) (A : Nat),
    (∀ i, i < L.length → t.getMem (BitVec.ofNat 64 (A + 8 * i)) = L.getD i 0) →
    t.readWords (BitVec.ofNat 64 A) L.length = L
  | [], _, _ => rfl
  | w :: L, A, h => by
    rw [List.length_cons, show L.length + 1 = 1 + L.length by ring, readWords_add, readWords_one]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, readWords_ext t L (A + 8 * 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show A + 8 * (i + 1) = A + 8 * 1 + 8 * i by ring] at this
      simpa using this)]
    rfl
theorem wctBytes_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytes N sig).length = 9216 :=
  ClaudeWCT.W9.T3M.wctBytes_length N sig
theorem placed_words {N : HashOutput} {sig : WCT9.Signature} {t : MachineState} (hp : Placed N sig t) :
    t.readWords (BitVec.ofNat 64 0x840) 1152 = wordsOf (wctBytes N sig) := by
  have hl : (wordsOf (wctBytes N sig)).length = 1152 := length_wordsOf 1152 _ (by rw [wctBytes_length])
  rw [← hl]
  refine readWords_ext t _ 0x840 (fun i hi => ?_)
  rw [hl] at hi
  have hk : i / 128 < 9 := by omega
  rw [wordsOf_getD _ 1152 (wctBytes_length N sig) i hi]
  have hw : window (wctBytes N sig) (8 * i) 8 =
      window (regionBytes (WCT9.child N ⟨i / 128, hk⟩).val (sig.openings ⟨i / 128, hk⟩)) (8 * (i % 128)) 8 := by
    unfold wctBytes
    rw [show 8 * i = 1024 * (i / 128) + 8 * (i % 128) by omega,
      window_flatMap_const _ _ 1024 (fun k => regionBytes_length _ _) (i / 128) (by simp; omega) _ 8 (by omega)]
    simp
  rw [hw, show 0x840 + 8 * i = regBase (i / 128) + 8 * (i % 128) by unfold regBase; omega,
    hp (i / 128) (i % 128) hk (by omega), regionWord]
  have hk' : (⟨i / 128 % 9, Nat.mod_lt _ (by decide)⟩ : WCT9.Coord) = ⟨i / 128, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
  rw [hk', wordsOf_getD _ 128 (regionBytes_length _ _) _ (by omega)]
theorem witListW_words (t : MachineState) (N : HashOutput) (w : WCT9.Witness)
    (hh : t.readWords (BitVec.ofNat 64 0x800) 8 = wordsOf (ClaudeWCT.W9.T3M.headerBytes w))
    (hwct : t.readWords (BitVec.ofNat 64 0x840) 1152 = wordsOf (wctBytes N w.signature))
    (hgap : t.readWords (BitVec.ofNat 64 0x2c40) 161 = List.replicate 161 0)
    (hlay : ∀ lay : Layer, t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (ClaudeWCT.W9.T3M.layerRegion N w lay)) :
    t.readWords (BitVec.ofNat 64 0x800) 3033 = wordsOf (ClaudeWCT.W9.T3M.witList N w) := by
  have l1 : (ClaudeWCT.W9.T3M.headerBytes w).length = 64 := ClaudeWCT.W9.T3M.headerBytes_length w
  have hf : (List.finRange 4).flatMap (ClaudeWCT.W9.T3M.layerRegion N w) =
      ClaudeWCT.W9.T3M.layerRegion N w 0 ++ ClaudeWCT.W9.T3M.layerRegion N w 1 ++
      ClaudeWCT.W9.T3M.layerRegion N w 2 ++ ClaudeWCT.W9.T3M.layerRegion N w 3 := by
    simp only [List.finRange_succ, List.finRange_zero, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, List.append_assoc]
    rfl
  unfold ClaudeWCT.W9.T3M.witList
  rw [hf]
  simp only [List.append_assoc]
  rw [wordsOf_append _ _ (by rw [l1]), wordsOf_append _ _ (by rw [wctBytes_length]),
    wordsOf_append _ _ (by rw [show (SigGolfCandidate.T3M.zeros 1288).length = 1288 from List.length_replicate]),
    wordsOf_append _ _ (by rw [ClaudeWCT.W9.T3M.layerRegion_length]; decide),
    wordsOf_append _ _ (by rw [ClaudeWCT.W9.T3M.layerRegion_length]; decide),
    wordsOf_append _ _ (by rw [ClaudeWCT.W9.T3M.layerRegion_length]; decide), ← hh, ← hwct]
  have hz : wordsOf (SigGolfCandidate.T3M.zeros 1288) = List.replicate 161 0 := by
    rw [show SigGolfCandidate.T3M.zeros 1288 = List.replicate (8 * 161) 0 from rfl, wordsOf_replicate_zero]
  rw [hz, ← hgap]
  have h0 := hlay 0; have h1 := hlay 1; have h2 := hlay 2; have h3 := hlay 3
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [lBase, height, chainCount]
  rw [show (3033 : Nat) = 8 + (1152 + (161 + (528 + (400 + (392 + 392))))) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_add, readWords_add, readWords_add]
  rfl
def tailProg (pk : PublicKey) (sig : WCT9.Signature) :
    Option (BitVec 32 × HashOutput × Digest) → M (Option (HashOutput × WCT9.Witness))
  | none => pure none
  | some (counter, N, root) => do
    let some (root, counters) ← WCT9.expandLayersBC sig (N.toNat % 2 ^ 31) 4 (.forest root) | pure none
    if root ≠ pk then return none
    pure (some (N, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
theorem expandN_split (m : Message) (pk : PublicKey) (sig : WCT9.Signature) :
    ClaudeWCT.W9.T3M.expandN m pk sig = newProg m sig >>= tailProg pk sig := by
  unfold ClaudeWCT.W9.T3M.expandN newProg
  rw [bind_assoc]
  congr 1
  funext r
  rcases r with _ | ⟨counter, N⟩
  · simp only [pure_bind]; rfl
  · simp only [bind_assoc, pure_bind]; rfl
end ClaudeWCT.W9.Machine.Expand
end
