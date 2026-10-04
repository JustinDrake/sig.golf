import SigGolfCandidate.T3M.Verify.Common
import SigGolfCandidate.T3M.Submission
import SigGolfCandidate.T3M.Search.TopData
import SigGolfCandidate.Rv
import SigGolfCandidate.T3.Core
import SigGolfCandidate.T3M.Verify.MerkleRuns
import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3.Rev
import SigGolfCandidate.T3M.Verify.LayerGood
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.ClaudeWCT.WCT9.Core
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Verify.Nonbinary (PAIR_DATA TAIL_DATA)
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
theorem bytes_word {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rw [bytesToWordLE_len8 _ (by simp [length_bytes]; omega), leNat8_slice x 8 (8 * j) h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring, show 8 * 8 = 64 by rfl, Nat.mod_mod]
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
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]
def VERIFY_DATA : Nat := 16705024
structure InitOK (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (0x40 + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0x40 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem verifyData_length : (submission.image .verify).data.length = 72192 := Search.verifyData_length
theorem dataBase_verify : dataBase (submission.image .verify) = VERIFY_DATA := by
  unfold dataBase; rw [verifyData_length]; decide
def le8 (v : Nat) : List (BitVec 8) := (List.range 8).map fun k => BitVec.ofNat 8 (v / 256 ^ k)
theorem le8_length (v : Nat) : (le8 v).length = 8 := by simp [le8]
def tabData : List (BitVec 8) := (List.range 2048).flatMap fun j => le8 (Images.verifyTabWord j)
theorem verifyData_split : ∃ rest, Images.verifyLegacyData = tabData ++ rest := ⟨_, rfl⟩
theorem flatMap8_length (f : Nat → List (BitVec 8)) (hf : ∀ x, (f x).length = 8) :
    ∀ l : List Nat, (l.flatMap f).length = 8 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hf a, flatMap8_length f hf l, List.length_cons]; ring
theorem tabData_length : tabData.length = 16384 := by
  unfold tabData
  rw [flatMap8_length (fun j => le8 (Images.verifyTabWord j)) (fun x => le8_length _), List.length_range]
theorem flatMap8_slice (f : Nat → List (BitVec 8)) (hf : ∀ x, (f x).length = 8) :
    ∀ (l : List Nat) (j : Nat) (hj : j < l.length), ((l.flatMap f).drop (8 * j)).take 8 = f l[j]
  | [], j, hj => by simp at hj
  | a :: l, 0, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.take_append_of_le_length (hf a).symm.le,
      List.take_of_length_le (hf a).le] <;> rfl
  | a :: l, j + 1, hj => by
    rw [List.flatMap_cons, show 8 * (j + 1) = (f a).length + 8 * j by have := hf a; omega,
      List.drop_length_add_append]
    exact flatMap8_slice f hf l j (by simp at hj; omega)
theorem leNat8_le8 (v : Nat) : leNat8 (le8 v) = v % 2 ^ 64 := by
  simp only [le8, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons, List.map_nil, leNat8,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.div_one]
  omega
theorem tabRev_eq' : ∀ n v, Images.tabRev n v = T3.Rev.revBits n v
  | 0, _ => rfl
  | n + 1, v => by simp only [Images.tabRev, T3.Rev.revBits, tabRev_eq' n (v / 2)]
theorem verifyData_tab (j : Nat) (hj : j < 2048) :
    bytesToWordLE ((((submission.image .verify).data).drop (4608 + 8 * j)).take 8) =
      BitVec.ofNat 64 (T3.Rev.revBits 64 (2048 + j)) := by
  show bytesToWordLE ((Images.verifyData.drop (4608 + 8 * j)).take 8) = _
  rw [Images.verifyData, show 4608 + 8 * j = Images.verifyPrefixData.length + 8 * j by rw [Images.verifyPrefixData_length], List.drop_length_add_append]
  obtain ⟨rest, hr⟩ := verifyData_split
  rw [hr, List.drop_append_of_le_length (by rw [tabData_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, tabData_length]; omega)]
  unfold tabData
  rw [flatMap8_slice (fun j => le8 (Images.verifyTabWord j)) (fun x => le8_length _) (List.range 2048) j
    (by rw [List.length_range]; exact hj)]
  beta_reduce
  rw [List.getElem_range, bytesToWordLE_len8 _ (le8_length _), leNat8_le8, Images.verifyTabWord, tabRev_eq',
    Nat.mod_eq_of_lt (T3.Rev.revBits_lt 64 _)]
theorem verifyData_word (k : Nat) (hk : k < 12) :
    bytesToWordLE ((((submission.image .verify).data).drop (72096 + 8 * k)).take 8) =
      BitVec.ofNat 64 (dataWords.getD k 0) := by
  interval_cases k <;> decide +kernel
def headerWord (k : Nat) : Nat :=
  if k < 4 then 128 + 193 * 2 ^ 56 + k * 2 ^ 48
  else 0x101 + 65536 * (k / 512) + 2 ^ 40 * (k % 512 / 8) + 2 ^ 32 * (k % 8)
def headerWordsCheck : List (BitVec 8) → Nat → Bool
  | [], _ => true
  | a :: b :: c :: d :: e :: f :: g :: h :: tail, k =>
      (bytesToWordLE [a,b,c,d,e,f,g,h] == BitVec.ofNat 64 (headerWord k)) && headerWordsCheck tail (k + 1)
  | _, _ => false
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem verifyHeader_checked :
    headerWordsCheck ((((submission.image .verify).data).drop 20992).take 16384) 0 = true := by decide +kernel
theorem headerWordsCheck_word (j : Nat) : ∀ (l : List (BitVec 8)) (k : Nat),
    headerWordsCheck l k = true → 8 * j + 8 ≤ l.length →
    bytesToWordLE ((l.drop (8 * j)).take 8) = BitVec.ofNat 64 (headerWord (k + j)) := by
  induction j with
  | zero =>
    intro l k h hl
    match l with
    | a :: b :: c :: d :: e :: f :: g :: h' :: tail =>
      simp only [headerWordsCheck, Bool.and_eq_true] at h
      have H := h.1
      simpa only [Nat.mul_zero, List.drop_zero, List.take_succ_cons, List.take_zero,
        Nat.add_zero, beq_iff_eq] using H
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] =>
      simp_all
  | succ j ih =>
    intro l k h hl
    match l with
    | a :: b :: c :: d :: e :: f :: g :: h' :: tail =>
      simp only [headerWordsCheck, Bool.and_eq_true] at h
      have H := h.2
      have ht : 8 * j + 8 ≤ tail.length := by simp only [List.length_cons] at hl; omega
      have H' := ih tail (k + 1) H ht
      rw [show 8 * (j + 1) = 8 * j + 8 by omega]
      simpa only [List.drop_succ_cons, Nat.add_succ, Nat.add_zero,
        show k + 1 + j = k + (j + 1) by omega] using H'
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] =>
      simp_all
    | [_,_,_,_] => simp_all
theorem verifyData_header (k : Nat) (hk : k < 2048) :
    bytesToWordLE ((((submission.image .verify).data).drop (20992 + 8 * k)).take 8) =
      BitVec.ofNat 64 (headerWord k) := by
  have hl : ((((submission.image .verify).data).drop 20992).take 16384).length = 16384 := by
    rw [List.length_take, List.length_drop, verifyData_length]; decide
  have H := headerWordsCheck_word k _ 0 verifyHeader_checked (by rw [hl]; omega)
  rw [Nat.zero_add, List.drop_take, List.take_take, List.drop_drop] at H
  rw [← H]
  congr 2
  omega
set_option maxRecDepth 200000 in
theorem init_ok (m : Legacy.Message) (pk : PublicKey) (w : Bytes 24264) (s : MachineState)
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
  have lw : (bytes w).length = 24264 := length_bytes w
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
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((72192 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < VERIFY_DATA → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold VERIFY_DATA at hA; omega), if_neg (by omega)]
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
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((24264 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x800)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x800 A (by rw [lw]; omega) hA, lw]
  have gb : ∀ A, VERIFY_DATA ≤ A → A < 2 ^ 24 →
      (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getByte
        (BitVec.ofNat 64 A) = (submission.image .verify).data.getD (A - VERIFY_DATA) 0 := by
    intro A hA hA'
    rw [T3M.getByte_eq_word _ _ (by omega), gm,
      g3 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g2 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g1 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g0 _ (by omega), if_pos (by unfold VERIFY_DATA at *; omega),
      extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos (Nat.mod_lt A (show 0 < 8 by decide))]
    have hidx : A / 8 * 8 - VERIFY_DATA + A % 8 = A - VERIFY_DATA := by
      unfold VERIFY_DATA at hA ⊢
      omega
    rw [hidx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    by_cases hw : 8 * j < 24264
    · rw [if_pos (by unfold WIT; omega), show WIT + 8 * j - 0x800 = 8 * j by unfold WIT; omega,
        bytes_word w j (by omega)]
      rfl
    · rw [if_neg (by unfold WIT; omega), g2 _ (by unfold WIT; omega), if_neg (by unfold WIT; omega),
        g1 _ (by unfold WIT; omega), if_neg (by unfold WIT; omega), g0z _ (by unfold WIT VERIFY_DATA; omega),
        wword_zero w j (by omega)]
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by omega), g0z A (by unfold VERIFY_DATA; omega)]
  · refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro k hk
      obtain ⟨hk1, hk2⟩ := DATA_ge k hk
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
        if_neg (by omega), g0 _ (by omega), if_pos (by unfold DATA VERIFY_DATA; omega),
        show DATA + 8 * k - VERIFY_DATA = 72096 + 8 * k by unfold DATA VERIFY_DATA; omega,
        verifyData_word k hk]
    · intro i hi
      rw [gb _ (by unfold Search.TOP_DATA VERIFY_DATA; omega) (by unfold Search.TOP_DATA; omega)]
      have hidx : Search.TOP_DATA + i - VERIFY_DATA = 68096 + i := by
        unfold Search.TOP_DATA VERIFY_DATA; omega
      rw [hidx]
      exact Search.verifyData_sum i hi
    · intro i hi
      rw [gb _ (by unfold PAIR_DATA VERIFY_DATA; omega) (by unfold PAIR_DATA; omega)]
      have hidx : PAIR_DATA + i - VERIFY_DATA = 39424 + i := by
        unfold PAIR_DATA VERIFY_DATA; omega
      rw [hidx]
      exact Search.verifyData_pair i hi
    · intro i hi
      rw [gb _ (by unfold TAIL_DATA VERIFY_DATA; omega) (by unfold TAIL_DATA; omega)]
      have hidx : TAIL_DATA + i - VERIFY_DATA = 55808 + i := by
        unfold TAIL_DATA VERIFY_DATA; omega
      rw [hidx]
      exact Search.verifyData_tail i hi
    · intro j hj
      rw [gm, g3 _ (by simp only [TAB, VERIFY_DATA]; omega), if_neg (by simp only [TAB, VERIFY_DATA]; omega), g2 _ (by simp only [TAB, VERIFY_DATA]; omega),
        if_neg (by simp only [TAB, VERIFY_DATA]; omega), g1 _ (by simp only [TAB, VERIFY_DATA]; omega), if_neg (by simp only [TAB, VERIFY_DATA]; omega),
        g0 _ (by simp only [TAB, VERIFY_DATA]; omega), if_pos (by simp only [TAB, VERIFY_DATA]; omega),
        show TAB + 8 * j - VERIFY_DATA = 4608 + 8 * j by simp only [TAB, VERIFY_DATA]; omega, verifyData_tab j hj]
    ·
      intro lay i d hl hi hd
      have hb : 2 ^ 23 + 4096 ≤ HDATA + 4096 * lay + 64 * i + 8 * d ∧
          HDATA + 4096 * lay + 64 * i + 8 * d + 8 ≤ 2 ^ 24 := by unfold HDATA; omega
      obtain ⟨hb1, hb2⟩ := hb
      have e1 : (512 * lay + 8 * i + d) / 512 = lay := by omega
      have e2 : (512 * lay + 8 * i + d) % 512 / 8 = i := by omega
      have e3 : (512 * lay + 8 * i + d) % 8 = d := by omega
      have ew : headerWord (512 * lay + 8 * i + d) =
          (if lay = 0 ∧ i = 0 ∧ d < 4 then 128 + 193 * 2 ^ 56 + d * 2 ^ 48
           else 0x101 + 65536 * lay + 2 ^ 40 * i + 2 ^ 32 * d) := by
        unfold headerWord
        by_cases hsmall : lay = 0 ∧ i = 0 ∧ d < 4
        · rcases hsmall with ⟨rfl, rfl, hd4⟩; simp [hd4]
        · rw [if_neg (by omega), if_neg hsmall, e1, e2, e3]
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
        if_neg (by omega), g0 _ (by omega), if_pos (by simp only [TAB, VERIFY_DATA, HDATA]; omega),
        show HDATA + 4096 * lay + 64 * i + 8 * d - VERIFY_DATA = 20992 + 8 * (512 * lay + 8 * i + d) by
          simp only [TAB, VERIFY_DATA, HDATA]; omega,
        verifyData_header _ (by omega), ew]
  · simp [MachineState.setReg, MachineState.getReg]
    exact congrArg (BitVec.ofNat 64) eD
end SigGolfCandidate.T3M.Verify
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open RiscvZkvm.Rv64 SigGolfCandidate.Rv
theorem srl_toNat (x : Word) (k : Nat) (hk : k < 64) :
    (BinOp.eval .srl x (BitVec.ofNat 64 k)).toNat = x.toNat / 2 ^ k := by
  simp only [BinOp.eval, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem sll_toNat (x : Word) (k : Nat) (hk : k < 64) :
    (BinOp.eval .sll x (BitVec.ofNat 64 k)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  simp only [BinOp.eval, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem andMask_toNat (x : Word) (k : Nat) (hk : k ≤ 64) :
    (BinOp.eval .and x (BitVec.ofNat 64 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
  simp only [BinOp.eval, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
    omega
  rw [Nat.mod_eq_of_lt this, Nat.and_two_pow_sub_one_eq_mod]
theorem or_toNat (x y : Word) : (BinOp.eval .or x y).toNat = x.toNat ||| y.toNat := by
  simp only [BinOp.eval, BitVec.toNat_or]
theorem mod_div_mod (x n k m : Nat) (h : k + m ≤ n) : x % 2 ^ n / 2 ^ k % 2 ^ m = x / 2 ^ k % 2 ^ m := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self x, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]
theorem or_add_shift (X y k : Nat) (hX : X < 2 ^ k) : X ||| 2 ^ k * y = X + 2 ^ k * y := by
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring
theorem gp_single (N : Nat) (W : Word) (w o : Nat) (hW : W.toNat = N / 2 ^ (64 * w) % 2 ^ 64)
    (ho : o + 25 ≤ 64) :
    (BinOp.eval .srl W (BitVec.ofNat 64 o)).toNat % 2 ^ 25 = N / 2 ^ (64 * w + o) % 2 ^ 25 := by
  rw [srl_toNat W o (by omega), hW, mod_div_mod _ 64 o 25 ho, Nat.div_div_eq_div_mul, ← Nat.pow_add]
theorem gp_double (N : Nat) (W W' : Word) (w o : Nat) (hW : W.toNat = N / 2 ^ (64 * w) % 2 ^ 64)
    (hW' : W'.toNat = N / 2 ^ (64 * (w + 1)) % 2 ^ 64) (ho : 0 < o) (ho' : o < 64) :
    (BinOp.eval .or (BinOp.eval .srl W (BitVec.ofNat 64 o))
        (BinOp.eval .sll W' (BitVec.ofNat 64 (64 - o)))).toNat % 2 ^ 25 =
      N / 2 ^ (64 * w + o) % 2 ^ 25 := by
  rw [or_toNat, srl_toNat W o ho', sll_toNat W' (64 - o) (by omega), hW, hW']
  have hN : N / 2 ^ (64 * w + o) = N / 2 ^ (64 * w) / 2 ^ o := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hN' : N / 2 ^ (64 * (w + 1)) = N / 2 ^ (64 * w) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2
  rw [hN, hN']
  generalize N / 2 ^ (64 * w) = A
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - o) * 2 ^ o := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hlo : A % 2 ^ 64 / 2 ^ o < 2 ^ (64 - o) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e]
    exact Nat.mod_lt _ (by positivity)
  have hhi : A / 2 ^ 64 % 2 ^ 64 * 2 ^ (64 - o) % 2 ^ 64 = 2 ^ (64 - o) * (A / 2 ^ 64 % 2 ^ o) := by
    generalize A / 2 ^ 64 = B
    rw [e, Nat.mul_comm (B % _), Nat.mul_mod_mul_left,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left _ _)]
  rw [hhi, or_add_shift _ _ _ hlo]
  have h1 : A / 2 ^ o % 2 ^ (64 - o) = A % 2 ^ 64 / 2 ^ o := by
    rw [e, Nat.mul_comm (2 ^ (64 - o)), Nat.mod_mul_right_div_self]
  have h2 : A / 2 ^ o / 2 ^ (64 - o) = A / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  have hsum : A % 2 ^ 64 / 2 ^ o + 2 ^ (64 - o) * (A / 2 ^ 64 % 2 ^ o) = A / 2 ^ o % 2 ^ 64 := by
    conv_rhs => rw [e, Nat.mod_mul]
    rw [h1, h2]
  rw [hsum, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem andMask_toNat' (x : Word) (m k : Nat) (hm : m = 2 ^ k - 1) (hk : k ≤ 64) :
    (BinOp.eval .and x (BitVec.ofNat 64 m)).toNat = x.toNat % 2 ^ k := by
  subst hm; exact andMask_toNat x k hk
theorem xval_eq (g : Word) (G j : Nat) (hj : j < 3) (hg : g.toNat % 2 ^ 25 = G % 2 ^ 25) :
    BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl g (BitVec.ofNat 64 (4 + 7 * j))) (BitVec.ofNat 64 127))
        (BinOp.eval .sll (BinOp.eval .or (BinOp.eval .and g (BitVec.ofNat 64 15)) (BitVec.ofNat 64 16))
          (BitVec.ofNat 64 7)) =
      BitVec.ofNat 64 (2048 + 128 * (G % 16) + G / 2 ^ (4 + 7 * j) % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [or_toNat, andMask_toNat' _ 127 7 rfl (by decide), srl_toNat _ _ (by omega),
    sll_toNat _ 7 (by decide), or_toNat, andMask_toNat' _ 15 4 rfl (by decide)]
  have h8 : (BitVec.ofNat 64 16).toNat = 2 ^ 4 * 1 := rfl
  rw [h8, or_add_shift _ _ _ (Nat.mod_lt _ (by decide))]
  have hlt : (g.toNat % 2 ^ 4 + 2 ^ 4 * 1) * 2 ^ 7 < 2 ^ 64 := by
    have := Nat.mod_lt g.toNat (show 0 < 2 ^ 4 by decide); omega
  rw [Nat.mod_eq_of_lt hlt, show (g.toNat % 2 ^ 4 + 2 ^ 4 * 1) * 2 ^ 7 = 2 ^ 7 * (g.toNat % 2 ^ 4 + 2 ^ 4 * 1)
    by ring, or_add_shift _ _ _ (Nat.mod_lt _ (by decide))]
  have e1 : g.toNat % 2 ^ 4 = G % 16 := by
    rw [← Nat.mod_mod_of_dvd g.toNat (show 2 ^ 4 ∣ 2 ^ 25 by norm_num), hg,
      Nat.mod_mod_of_dvd _ (show 2 ^ 4 ∣ 2 ^ 25 by norm_num)]; rfl
  have e2 : g.toNat / 2 ^ (4 + 7 * j) % 2 ^ 7 = G / 2 ^ (4 + 7 * j) % 128 := by
    rw [← mod_div_mod g.toNat 25 (4 + 7 * j) 7 (by omega), hg, mod_div_mod G 25 (4 + 7 * j) 7 (by omega)]; rfl
  rw [e1, e2, BitVec.toNat_ofNat]
  have hb : 2048 + 128 * (G % 16) + G / 2 ^ (4 + 7 * j) % 128 < 2 ^ 64 := by
    have := Nat.mod_lt G (show 0 < 16 by decide)
    have := Nat.mod_lt (G / 2 ^ (4 + 7 * j)) (show 0 < 128 by decide)
    omega
  rw [Nat.mod_eq_of_lt hb]
  omega
theorem land8 (n : Nat) : n &&& 1016 = 8 * (n / 8 % 2 ^ 7) := by
  rw [show (1016 : Nat) = 8 * (2 ^ 7 - 1) by norm_num]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ j
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h, Bool.and_comm]
  · simp [h]
theorem xaddr_eq (g X : Word) (G T j : Nat) (hj : j < 3) (hg : g.toNat % 2 ^ 25 = G % 2 ^ 25)
    (hX : X = BitVec.ofNat 64 T) (hT : T < 2 ^ 32) :
    BinOp.eval .add (BinOp.eval .add (BinOp.eval .and (BinOp.eval .srl g (BitVec.ofNat 64 (1 + 7 * j)))
        (BitVec.ofNat 64 1016)) (BinOp.eval .sll (BinOp.eval .and g (BitVec.ofNat 64 15)) (BitVec.ofNat 64 10))) X =
      BitVec.ofNat 64 (T + 8 * (128 * (G % 16) + G / 2 ^ (4 + 7 * j) % 128)) := by
  subst hX
  have e1 : g.toNat % 2 ^ 4 = G % 16 := by
    rw [← Nat.mod_mod_of_dvd g.toNat (show 2 ^ 4 ∣ 2 ^ 25 by norm_num), hg,
      Nat.mod_mod_of_dvd _ (show 2 ^ 4 ∣ 2 ^ 25 by norm_num)]; rfl
  have e2 : g.toNat / 2 ^ (1 + 7 * j) / 8 % 2 ^ 7 = G / 2 ^ (4 + 7 * j) % 128 := by
    rw [Nat.div_div_eq_div_mul, show 2 ^ (1 + 7 * j) * 8 = 2 ^ (4 + 7 * j) by
        rw [show 4 + 7 * j = (1 + 7 * j) + 3 by ring, Nat.pow_add (m := 1 + 7 * j)],
      ← mod_div_mod g.toNat 25 (4 + 7 * j) 7 (by omega), hg, mod_div_mod G 25 (4 + 7 * j) 7 (by omega)]; rfl
  have hA : (BinOp.eval .and (BinOp.eval .srl g (BitVec.ofNat 64 (1 + 7 * j))) (BitVec.ofNat 64 1016)).toNat =
      8 * (G / 2 ^ (4 + 7 * j) % 128) := by
    have hs := srl_toNat g (1 + 7 * j) (by omega)
    show ((BinOp.eval .srl g (BitVec.ofNat 64 (1 + 7 * j))) &&& BitVec.ofNat 64 1016).toNat = _
    rw [BitVec.toNat_and, hs, show (BitVec.ofNat 64 1016).toNat = 1016 from rfl, land8, e2]
  have hB : (BinOp.eval .sll (BinOp.eval .and g (BitVec.ofNat 64 15)) (BitVec.ofNat 64 10)).toNat =
      1024 * (G % 16) := by
    rw [sll_toNat _ 10 (by decide), andMask_toNat' g 15 4 rfl (by decide), e1]
    have := Nat.mod_lt G (show 0 < 16 by decide)
    rw [Nat.mod_eq_of_lt (by omega)]; ring
  apply BitVec.eq_of_toNat_eq
  show (BinOp.eval .and (BinOp.eval .srl g (BitVec.ofNat 64 (1 + 7 * j))) (BitVec.ofNat 64 1016) +
    BinOp.eval .sll (BinOp.eval .and g (BitVec.ofNat 64 15)) (BitVec.ofNat 64 10) + BitVec.ofNat 64 T).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_add, hA, hB, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mod_lt G (show 0 < 16 by decide)
  have := Nat.mod_lt (G / 2 ^ (4 + 7 * j)) (show 0 < 128 by decide)
  rw [Nat.mod_eq_of_lt (show T < 2 ^ 64 by omega)]
  omega
theorem mergeSort3 (x0 x1 x2 a b c : Nat) (hp : [a, b, c].Perm [x0, x1, x2]) (hab : a ≤ b) (hbc : b ≤ c) :
    [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = [a, b, c] := by
  apply List.Perm.eq_of_sortedLE
  · rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_mergeSort (le := fun x y => decide (x ≤ y))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      (fun h => by simpa using h)
  · rw [List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, forall_eq_or_imp,
      forall_eq, or_false, List.Pairwise.nil, and_true, forall_const, IsEmpty.forall_iff, implies_true]
    omega
  · exact (List.mergeSort_perm _ _).trans hp.symm
theorem perm3_0 (x0 x1 x2 : Nat) : [x0, x1, x2].Perm [x0, x1, x2] := List.Perm.refl _
theorem perm3_1 (x0 x1 x2 : Nat) : [x0, x2, x1].Perm [x0, x1, x2] := List.Perm.cons x0 (List.Perm.swap x1 x2 [])
theorem perm3_2 (x0 x1 x2 : Nat) : [x2, x0, x1].Perm [x0, x1, x2] :=
  (List.Perm.swap x0 x2 [x1]).trans (perm3_1 x0 x1 x2)
theorem perm3_3 (x0 x1 x2 : Nat) : [x1, x0, x2].Perm [x0, x1, x2] := List.Perm.swap x0 x1 [x2]
theorem perm3_4 (x0 x1 x2 : Nat) : [x1, x2, x0].Perm [x0, x1, x2] :=
  (List.Perm.cons x1 (List.Perm.swap x0 x2 [])).trans (perm3_3 x0 x1 x2)
theorem perm3_5 (x0 x1 x2 : Nat) : [x2, x1, x0].Perm [x0, x1, x2] :=
  (List.Perm.swap x1 x2 [x0]).trans (perm3_4 x0 x1 x2)
def selNum (N : Nat) (c : Nat) : Nat := N / 2 ^ (31 + 25 * c)
def selX (N c j : Nat) : Nat := selNum N c / 2 ^ (4 + 7 * j) % 128
theorem selections_getD (N : T3.HashOutput) (c : Nat) (hc : c < 7) :
    (T3.selections N).getD c ⟨0, []⟩ =
      ⟨selNum N.toNat c % 16, [selX N.toNat c 0, selX N.toNat c 1, selX N.toNat c 2].mergeSort
        (fun x y => decide (x ≤ y))⟩ := by
  simp only [T3.selections, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some, selNum, selX]
  rfl
theorem selections_length (N : T3.HashOutput) : (T3.selections N).length = 7 := by
  simp [T3.selections]
end SigGolfCandidate.T3M.Verify
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
set_option maxRecDepth 100000
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel
theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.Verify.FtsRev
open RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3.Rev
def rv (E : Nat) : BitVec 64 := BitVec.ofNat 64 (revBits 64 E)
theorem rv_toNat (E : Nat) : (rv E).toNat = revBits 64 E := by
  unfold rv; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (revBits_lt 64 E)]
theorem rv_sll1 (E : Nat) (hE : E < 2 ^ 64) : BinOp.eval .sll (rv E) (BitVec.ofNat 64 1) = rv (E / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.toNat_shiftLeft, rv_toNat, Nat.shiftLeft_eq]
  rw [revBits_succ_div 63 E hE]
  norm_num
  ring_nf
theorem revBits_top64 (E : Nat) : revBits 64 E / 2 ^ 63 = E % 2 := revBits_top 63 E
theorem rv_slt (E : Nat) : BitVec.slt (rv E) 0 = decide (E % 2 = 1) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide, rv_toNat]
  have h := revBits_top64 E
  have hl := revBits_lt 64 E
  rcases Nat.mod_two_eq_zero_or_one E with he | he <;> rw [he] at h <;> simp only [he]
  · have : revBits 64 E < 2 ^ 63 := by
      by_contra hc; have : 1 ≤ revBits 64 E / 2 ^ 63 := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
      omega
    simp; omega
  · have : 2 ^ 63 ≤ revBits 64 E := by
      by_contra hc; have : revBits 64 E / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    simp; omega
theorem xor_two_pow (x k : Nat) : x ^^^ 2 ^ k = 2 ^ k * (x / 2 ^ k ^^^ 1) + x % 2 ^ k := by
  have h1 : (x ^^^ 2 ^ k) / 2 ^ k = x / 2 ^ k ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (by positivity)]
  have h2 : (x ^^^ 2 ^ k) % 2 ^ k = x % 2 ^ k := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  rw [← h1, ← h2, Nat.div_add_mod]
theorem xor_2048 (g : Nat) (hg : g < 2048) : g ^^^ 2048 = 2048 + g := by
  have := xor_two_pow g 11
  rw [Nat.div_eq_of_lt (by norm_num; omega), Nat.mod_eq_of_lt (by norm_num; omega)] at this
  rw [show (2048 : Nat) = 2 ^ 11 by norm_num, this]; rfl
theorem xor_top (x : Nat) (hx : x < 2 ^ 64) : x ^^^ 2 ^ 63 = (x + 2 ^ 63) % 2 ^ 64 := by
  rw [xor_two_pow]
  by_cases h : x < 2 ^ 63
  · rw [Nat.div_eq_of_lt h, show (0 : Nat) ^^^ 1 = 1 from rfl, Nat.mod_eq_of_lt h]; omega
  · have h1 : x / 2 ^ 63 = 1 := by omega
    rw [h1, show (1 : Nat) ^^^ 1 = 0 from rfl]; omega
theorem rv_xor (E : Nat) : rv E ^^^ BitVec.ofNat 64 (2 ^ 63) = rv (E ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, rv_toNat, rv_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num),
    xor_top _ (revBits_lt 64 E), revBits_xor1 63 E]
theorem rv_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rv a = rv b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [rv_toNat, rv_toNat] at this
    exact revBits_inj ha hb this
  · rintro rfl; rfl
theorem revBits_zero : ∀ n, revBits n 0 = 0
  | 0 => rfl
  | n + 1 => by simp only [revBits, Nat.zero_mod, Nat.zero_mul, Nat.zero_div, revBits_zero n]
theorem revBits_one (n : Nat) : revBits (n + 1) 1 = 2 ^ n := by
  simp only [revBits, show (1 : Nat) % 2 = 1 from rfl, show (1 : Nat) / 2 = 0 from rfl, revBits_zero, one_mul,
    add_zero]
theorem rv_one : rv 1 = BitVec.ofNat 64 (2 ^ 63) := by unfold rv; rw [revBits_one 63]
theorem rv_eq_top (E : Nat) (hE : E < 2 ^ 64) : rv E = BitVec.ofNat 64 (2 ^ 63) ↔ E = 1 := by
  rw [← rv_one]; exact rv_inj hE (by norm_num)
theorem revBits_allOnes : ∀ n, revBits n (2 ^ n - 1) = 2 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    have h1 : (2 ^ (n + 1) - 1) % 2 = 1 := by
      have : 0 < 2 ^ n := by positivity
      rw [Nat.pow_succ]; omega
    have h2 : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
      have : 0 < 2 ^ n := by positivity
      rw [Nat.pow_succ]; omega
    simp only [revBits, h1, h2, revBits_allOnes n, one_mul]
    have : 0 < 2 ^ n := by positivity
    rw [Nat.pow_succ]; omega
theorem rv_ne_neg1 (E : Nat) (hE : E < 4096) : rv E ≠ -1#64 := by
  intro h
  have hm : (-1#64 : BitVec 64) = rv (2 ^ 64 - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [rv_toNat, revBits_allOnes 64]; rfl
  rw [hm, rv_inj (by omega) (by norm_num)] at h
  omega
end SigGolfCandidate.T3M.Verify.FtsRev
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
abbrev selC (a : HashOutput) (c : Nat) : Selection := (selections a).getD c ⟨0, []⟩
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FCtx where
  pk : Digest
  w : WBytes
  a : HashOutput
namespace FCtx
def idx (F : FCtx) : Nat := F.a.toNat % 2 ^ 31
def sel (F : FCtx) (c : Nat) : Selection := selC F.a c
def g (F : FCtx) (s : Nat) : Nat := T3M.selLeaf (F.sel (s / 3)) (s % 3)
theorem idx_lt (F : FCtx) : F.idx < 2 ^ 31 := Nat.mod_lt _ (by decide)
end FCtx
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def layerPc : Nat := 656
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FtsOut (F : FCtx) (root : Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  root : DigAt u 0x100 root
  wit : Orig F.w (fun o => o < 64 ∨ 10568 ≤ o) u
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : WBytes) (index : Nat) (r : Option Digest) : T3.M Bool :=
  match r with
  | some root => do
      let __x ← layersP w index 4 (root, 0, 0)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb
theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]
theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]
theorem trPc_vals : (∀ c, c < 64 → trPc 2 c = 5520 + 101 * c) ∧ (∀ c, c < 64 → trPc 1 c = 11984 + 101 * c) ∧
    (∀ c, c < 128 → trPc 0 c = 18455 + 134 * c) := by decide
theorem mkOff_vals : mkOff 3 0 6 = 36 ∧ mkOff 2 0 6 = 36 ∧ mkOff 1 0 7 = 42 ∧ mkOff 0 1 6 = 33 := by decide
theorem mkFin_succ (lay leaf : Nat) (hlay : lay < 4) :
    mkFin lay leaf + 1 = (if lay = 3 then 5525 + 101 * mkSh 3 0 leaf else if lay = 2 then 11989 + 101 * mkSh 2 0 leaf
      else if lay = 1 then 18460 + 134 * mkSh 1 0 leaf else 38675 + 53 * mkSh 0 1 leaf) := by
  obtain ⟨o3, o2, o1, o0⟩ := mkOff_vals
  interval_cases lay
  · simp only [mkFin, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl, o0, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 1 - 1 = 0 from rfl, show mkBits 1 0 = 7 from rfl, o1, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 2 - 1 = 0 from rfl, show mkBits 2 0 = 6 from rfl, o2, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 3 - 1 = 0 from rfl, show mkBits 3 0 = 6 from rfl, o3, mkShp]; norm_num; omega
theorem ofNat4_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
theorem mkEc_last_vals : (∀ leaf, leaf < 128 → mkEc 1 leaf (hL 1 - 1) + 1 = trPc 0 leaf) ∧
    (∀ leaf, leaf < 64 → mkEc 2 leaf (hL 2 - 1) + 1 = trPc 1 leaf) ∧
    (∀ leaf, leaf < 64 → mkEc 3 leaf (hL 3 - 1) + 1 = trPc 2 leaf) := by decide +kernel
theorem mkEc_last (n leaf : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 3) (hleaf : leaf < 2 ^ hL n) :
    mkEc n leaf (hL n - 1) + 1 = trPc (n - 1) leaf := by
  obtain ⟨e1, e2, e3⟩ := mkEc_last_vals
  rcases hn with rfl | rfl | rfl
  · exact e1 leaf (by simpa [hL] using hleaf)
  · exact e2 leaf (by simpa [hL] using hleaf)
  · exact e3 leaf (by simpa [hL] using hleaf)
theorem pad_lo32 (x : Digest) : (dlo x).toNat / 2 ^ 32 = (x.extractLsb' 32 96).toNat % 2 ^ 32 := by
  simp only [dlo, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  norm_num
  omega
theorem pad_hi (x : Digest) : dhi x = BitVec.ofNat 64 ((x.extractLsb' 32 96).toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [dhi, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  norm_num
  omega
def RestIn (w : WBytes) (pk : Digest) (index n : Nat) (M : T3.LayerMessage) (s : MachineState) : Prop :=
  if n = 0 then CmpIn pk M.1 s else LayerIn w pk index (n - 1) M s
theorem mkEnd_cmp (w : WBytes) (pk : Digest) (index : Nat) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index (Fin.ofNat 4 0) ends u) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index (Fin.ofNat 4 0)).1 u root t) :
    CmpIn pk root t := by
  have hleaf := leaf_lt index (Fin.ofNat 4 0)
  have hpc := ht.pc
  rw [mkFin_succ 0 _ (by decide)] at hpc
  refine ⟨⟨mkSh 0 1 (route index (Fin.ofNat 4 0)).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · rw [hpc]; rfl
  · intro p hp
    simp only [cmpK,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg]
      congr 1
      exact (mkDst_chunk _).symm
  · change DigAt t (13336+48*(mkSh 0 1 (route index (Fin.ofNat 4 0)).1/32%2)) root
    rw [mkDst_chunk]
    exact ht.root
theorem mkAfter_next (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (n : Nat) (hn : n < 4)
    (h0 : n ≠ 0) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index (Fin.ofNat 4 n) ends u)
    (v : Digest) (t : MachineState) (ht : MAfter w pk n (route index (Fin.ofNat 4 n)).1 u (hL n - 1) v t) :
    LayerIn w pk index (n - 1) (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
      (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
      ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) v) t := by
  have hv := ofNat4_val n hn
  have hleaf := leaf_lt index (Fin.ofNat 4 n)
  rw [hv] at hleaf
  have hL0 : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => h0 (by have := congrArg Fin.val h; rw [hv] at this; exact this)
  have hkU : KnownOK (lfK n) u := by have := hu.glob.1; rwa [hv] at this
  have hh : height (Fin.ofNat 4 n) = hL n := by rw [← hL_eq, hv]
  have hn' : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  have hB : encB (n - 1) = mkBlk n (hL n - 1) ∧ mkBo n (hL n - 1) = mkBase n ∧ mkBase n = layerEnd (n - 1) ∧
      6 ≤ hL n := by
    rcases hn' with rfl | rfl | rfl <;> decide
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, -⟩ := mkBo_facts n (hL n - 1) hn (by omega)
  have hn3 : n - 1 ≠ 3 := by omega
  have hmb : merkleBlock (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1) = mkBo n (hL n - 1) := by
    rw [hh, ← mkBo_eq, hv]
  have hkt : KnownOK (mkKc n ++ [(.x11, 64)]) t := by
    have := ht.known
    simpa [mkLvlK, show hL n - 1 ≠ 0 by omega] using this
  refine ⟨by omega, hidx, ?_, ⟨?_, ht.glob.2⟩, ?_, ?_, ?_, Or.inr ⟨mkCur n (hL n - 1)
    ((route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2), ?_, ht.dstReg⟩⟩
  ·
    refine ⟨(route index (Fin.ofNat 4 n)).1, ?_, ?_⟩
    · have hc : 2 ^ hL n ≤ nCopy (n - 1) := by
        obtain ⟨-, n2, n1, n0⟩ := nCopy_eq
        rcases hn' with rfl | rfl | rfl
        · rw [show 1 - 1 = 0 from rfl, n0]; decide
        · rw [show 2 - 1 = 1 from rfl, n1]; decide
        · rw [show 3 - 1 = 2 from rfl, n2]; decide
      omega
    · rw [ht.pc]
      exact congrArg pcOf (mkEc_last n _ hn' hleaf)
  ·
    intro p hp
    simp only [preK, if_neg hn3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, baseK] at hp
    rw [show n - 1 + 1 = n by omega] at hp
    have hkp := ht.keep
    rcases hp with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht.glob.1 _ (by simp [baseK])
    · exact ht.glob.1 _ (by simp [baseK])
    · rw [hkp .x27 (by simp [mkKeep]), hkU (.x27, BitVec.ofNat 64 (hw 1 n)) (by simp [lfK, postLf, leafK])]
    · rw [hkp .x24 (by simp [mkKeep]), hkU (.x24, 0x10000) (by simp [lfK, lfKeepK, h0])]
    · rw [hkp .x2 (by simp [mkKeep]), hkU (.x2, 0x3fe00) (by simp [lfK, lfKeepK])]
    · rw [hkp .x20 (by simp [mkKeep]), hkU (.x20, BitVec.ofNat 64 M1c) (by simp [lfK, lfKeepK, h0])]
    · rw [hkp .x21 (by simp [mkKeep]), hkU (.x21, BitVec.ofNat 64 M2c) (by simp [lfK, lfKeepK, h0])]
    · exact hkt _ (by simp)
    · rw [hkp .x28 (by simp [mkKeep]), hkU (.x28, BitVec.ofNat 64 (headerBank 0 0)) (by simp [lfK, lfKeepK, h0])]
    all_goals exact hkt _ (by simp [mkKc])
  ·
    rw [show rReg (n - 1) = .x30 by simp [rReg, hn3], ht.keep .x30 (by simp [mkKeep]), hu.t5,
      tree_next index _ hL0, hv]
  ·
    have hO := ht.orig
    have hnode := ht.node
    have hbl := mkBit_lt (route index (Fin.ofNat 4 n)).1 (hL n - 1)
    have hpad := hO.dig (mkBo n (hL n - 1) + 32) (by omega) (by unfold WX; omega)
      ⟨by omega, by omega, by unfold mkCur mkBlk; interval_cases (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 <;> omega⟩
      ⟨by omega, by omega, by unfold mkCur mkBlk; interval_cases (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 <;> omega⟩
    have e32 : WIT + (mkBo n (hL n - 1) + 32) = mkBlk n (hL n - 1) + 32 := by unfold WIT mkBlk; omega
    rw [e32, show mkBlk n (hL n - 1) + 32 + 8 = mkBlk n (hL n - 1) + 40 by omega] at hpad
    rw [hB.1]
    unfold T3.pairOf wpath wmerklePad
    rw [hmb, hh]
    rcases (show (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 = 0 ∨
        (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide, if_false]
      have hsib := hO.dig (mkBo n (hL n - 1) + 48) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩
      have e48 : WIT + (mkBo n (hL n - 1) + 48) = mkBlk n (hL n - 1) + 48 := by unfold WIT mkBlk; omega
      rw [e48] at hsib
      refine ⟨?_, hsib, ?_, ?_⟩
      · simpa [mkCur] using hnode
      · rw [hpad.1]; exact pad_lo32 _
      · rw [hpad.2]; exact pad_hi _
    · rw [hb] at hnode hO
      simp only [hb, show (1 : Nat) ≠ 0 by decide, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo n (hL n - 1)) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
      have e0 : WIT + mkBo n (hL n - 1) = mkBlk n (hL n - 1) := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      refine ⟨hsib, ?_, ?_, ?_⟩
      · simpa [mkCur] using hnode
      · rw [hpad.1]; exact pad_lo32 _
      · rw [hpad.2]; exact pad_hi _
  ·
    intro j hj ⟨h1, h2⟩
    exact ht.orig j hj ⟨h1, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
  ·
    have hbl := mkBit_lt (route index (Fin.ofNat 4 n)).1 (hL n - 1)
    simp only [dstSet, if_neg hn3, List.mem_cons, List.not_mem_nil, or_false, mkCur, hB.1]
    omega
def lCyc : Nat → Nat
  | 0 => 8
  | n + 1 => layerCost n 0 + (if n = 0 then mkCyc n else mkCycP n) + lCyc n
def lFuel : Nat → Nat
  | 0 => 9
  | n + 1 => layerFuel n + (if n = 0 then mkFuel n else mkFuelP n) + lFuel n
theorem lCyc_4 : lCyc 4 = 5751 := by decide
theorem lFuel_4 : lFuel 4 ≤ 8051 := by decide
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ M s, RestIn w pk index n M s →
      GoodQ s (lFuel n) (lCyc n) Q (lCyc n) (ccM (layersP w index n M) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [RestIn, if_true] at hs
    rw [show layersP w index 0 M = pure (some M.1) from rfl, ccM_pure, kFin_some]
    exact cmp_good pk M.1 s hs Q hQ
  | succ n ih =>
    intro hn M s hs
    have hs' : LayerIn w pk index n M s := by simpa [RestIn] using hs
    have hv := ofNat4_val n (by omega)
    by_cases h0 : n = 0
    · subst h0
      have hg := layersP_good_top w pk index M s hs' (kFin pk) (kFin_none pk) (lFuel 0 + mkFuel 0)
        (lCyc 0 + mkCyc 0) (lCyc 0 + mkCyc 0) Q (fun ends u hu => by
          rw [ccM_bind]
          have hm := merkle_good w pk index (Fin.ofNat 4 0) ends u hidx hu
            (fun r => ccM (layersP w index 0 (r, 0, 0)) (kFin pk)) (lFuel 0) (lCyc 0) (lCyc 0) Q
            (fun root t ht => ih (by omega) (root, 0, 0) t (by
              simp only [RestIn, if_true]
              exact mkEnd_cmp w pk index ends u hu root t (by rw [hv] at ht; exact ht))) hv
          rw [hv] at hm
          exact hm)
      exact hg.mono (by simp only [lFuel, ↓reduceIte]; omega) (by simp only [lCyc, ↓reduceIte]; omega)
        (fun q => ⟨q, by simp only [lCyc, ↓reduceIte]; omega⟩)
    · have hg := layersP_good_low w pk index n (by omega) h0 M s hs' (kFin pk) (kFin_none pk) (lFuel n + mkFuelP n)
        (lCyc n + mkCycP n) (lCyc n + mkCycP n) Q (fun ends u hu => by
          have hh : height (Fin.ofNat 4 n) = hL n := by rw [← hL_eq, hv]
          have e : (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
              merklePairP w index (Fin.ofNat 4 n) >>= layersP w index n) =
              (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
                fun v => (List.range (hL n - 1)).foldlM (mkStep w index (Fin.ofNat 4 n)) v) >>= fun node =>
                layersP w index n (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
                  (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
                  ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) node) := by
            simp only [bind_assoc]
            congr 1; funext v
            rw [merklePairP_eq, hh]
            simp only [bind_assoc, pure_bind]
          rw [e, ccM_bind]
          have hm := merkle_pair_good w pk index (Fin.ofNat 4 n) ends u hidx hu
            (fun node => ccM (layersP w index n (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
              (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
              ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) node)) (kFin pk))
            (lFuel n) (lCyc n) (lCyc n) Q
            (fun node t ht => ih (by omega) _ t (by
              simp only [RestIn, if_neg h0]
              exact mkAfter_next w pk index hidx n (by omega) h0 ends u hu node t (by rw [hv] at ht; exact ht)))
          rw [hv] at hm
          exact hm)
      exact hg.mono (by simp only [lFuel, if_neg h0]; omega) (by simp only [lCyc, if_neg h0]; omega)
        (fun q => ⟨q, by simp only [lCyc, if_neg h0]; omega⟩)
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8057 8057 Q 5757 (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb) := by
  have hidx : a.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl (root, 0, 0) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb =
      ccM (layersP w (a.toNat % 2 ^ 31) 4 (root, 0, 0)) (kFin pk) := by
    unfold afterFts; rw [ccM_bind]; rfl
  rw [e]
  rw [lCyc_4] at hg
  have hF := lFuel_4
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
end SigGolfCandidate.T3M
end
section
namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def hLoad (i d : Nat) : E := .ld (addC (.reg .x28) (hOff i d))
def GoodQFor (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
structure Layout where
  image : Image
  jumpTableWord : Nat
  rejectWord : Nat
  chainWord : Fin 728 → Nat
  childWord : Fin 128 → Nat
  coordWord : Fin 9 → Nat
  forestWord : Nat
  valueOffset : Fin 9 → Fin 7 → Nat
  siblingOffset : Fin 9 → Fin 7 → Nat
  leafAddress : Fin 9 → Nat
  rootAddress : Fin 9 → Nat
structure Budget where
  fuel : Nat
  allCycles : Nat
  acceptCycles : Nat
def layerEntryWord : Nat := 656
def layerWitnessOffset : Nat := 10568
def forestRootAddress : Nat := 0x100
def digestAttemptLimit : Nat := 2 ^ 21
def OpeningAt (L : Layout) (w : WBytes) (sig : ClaudeWCT.WCT9.Signature) : Prop :=
  ∀ k i, (sig.openings k).values i = wdig w (L.valueOffset k i) ∧
    (sig.openings k).path i = wdig w (L.siblingOffset k i)
end W9Machine
end
