import SigGolfCandidate.T3M.Verify.CanonicalTables
import SigGolfCandidate.T3M.Verify.Init

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Verify.Nonbinary (PAIR_DATA TAIL_DATA)
def GTAB : Nat := 0xfef000
def candidateSub : Submission := { submission with image := fun p => if p=.verify then fixture else submission.image p }
@[simp] theorem candidateSub_verify : candidateSub.image .verify=fixture := rfl
theorem candidateSub_admissible : candidateSub.Admissible := by
  refine ⟨submission_admissible.1,?_⟩
  intro p
  cases p
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · change fixture.Valid submission.sizes submission.layout
    refine ⟨?_,?_⟩
    · exact image_size
    · unfold layoutValid
      have hb : dataBase fixture=0xfef000 := by unfold dataBase; rw [data_length]; rfl
      rw [hb]
      decide +kernel

theorem dataBase_c : dataBase fixture=GTAB := by
  unfold dataBase
  rw [data_length]
  rfl
theorem data_c_slice (off : Nat) :
    fixture.data.drop (2048+off)=Images.verifyData.drop off := by
  change (prefixData++Images.verifyData).drop (2048+off)=_
  rw [←prefix_length,List.drop_length_add_append]
theorem data_c_byte (off : Nat) :
    fixture.data.getD (2048+off) 0=Images.verifyData.getD off 0 := by
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD]
  change (prefixData++Images.verifyData)[2048+off]?.getD 0=_
  rw [←prefix_length,List.getElem?_append_right (by omega)]
  simp
theorem data_c_word (k : Nat) (hk : k<12) :
    bytesToWordLE ((fixture.data.drop (69536+8*k)).take 8)=BitVec.ofNat 64 (dataWords.getD k 0) := by
  rw [show 69536+8*k=2048+(67488+8*k) by omega,data_c_slice]
  exact verifyData_word k hk
theorem data_c_header (k : Nat) (hk : k<2048) :
    bytesToWordLE ((fixture.data.drop (18432+8*k)).take 8)=BitVec.ofNat 64 (headerWord k) := by
  rw [show 18432+8*k=2048+(16384+8*k) by omega,data_c_slice]
  exact verifyHeader_word k hk
theorem data_c_tab (k : Nat) (hk : k<2048) :
    bytesToWordLE ((fixture.data.drop (2048+8*k)).take 8)=BitVec.ofNat 64 (T3.Rev.revBits 64 (2048+k)) := by
  rw [data_c_slice]
  exact verifyData_tab k hk
theorem data_c_prefix (k : Nat) (hk : k<256) :
    bytesToWordLE ((fixture.data.drop (8*k)).take 8)=bytesToWordLE ((prefixData.drop (8*k)).take 8) := by
  change bytesToWordLE (((prefixData++Images.verifyData).drop (8*k)).take 8)=_
  rw [List.drop_append_of_le_length (by rw [prefix_length];omega),
    List.take_append_of_le_length (by rw [List.length_drop,prefix_length];omega)]

structure InitC (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (0x40 + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0x40 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  /-- The embedded data words at `DATA` (T3K). -/
  data : DataOK s
  /-- n3-99: `sp = dataBase = TAB` (the selection code composes table addresses with it). -/
  sp : s.getReg .x2 = BitVec.ofNat 64 GTAB

  tables : TablesOK s

theorem init_c (m : Legacy.Message) (pk : PublicKey) (w : Bytes 25240) (s : MachineState)
    (h : initialState candidateSub .verify (m, pk, w) = some s) : InitC m pk w s := by
  unfold initialState at h
  simp only [candidateSub_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers candidateSub.sizes candidateSub.layout .verify (m, pk, w) =
      [(0x40, bytes m), (0xA0, bytes pk), (0x800, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil,candidateSub_verify]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 25240 := length_bytes w
  have lD := data_length
  have eD := dataBase_c
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase fixture))
    fixture.data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 0x40) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x800) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase fixture))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if GTAB ≤ A ∧ A < GTAB + 8 * ((69632 + 7) / 8) ∧ (A - GTAB) % 8 = 0 then
        bytesToWordLE (((fixture.data).drop (A - GTAB)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords fixture.data blank (dataBase fixture) A
      (by rw [lD, eD]; unfold GTAB; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < GTAB → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold GTAB at hA; omega), if_neg (by omega)]
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
  have gb : ∀ A, GTAB ≤ A → A < 2 ^ 24 →
      (s3.setReg .x2 (BitVec.ofNat 64 (dataBase fixture))).getByte
        (BitVec.ofNat 64 A) = fixture.data.getD (A - GTAB) 0 := by
    intro A hA hA'
    rw [T3M.getByte_eq_word _ _ (by omega), gm,
      g3 _ (by omega), if_neg (by unfold GTAB at hA; omega),
      g2 _ (by omega), if_neg (by unfold GTAB at hA; omega),
      g1 _ (by omega), if_neg (by unfold GTAB at hA; omega),
      g0 _ (by omega), if_pos (by unfold GTAB at *; omega),
      extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos (Nat.mod_lt A (show 0 < 8 by decide))]
    have hidx : A / 8 * 8 - GTAB + A % 8 = A - GTAB := by
      unfold GTAB at hA ⊢
      omega
    rw [hidx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,?_⟩
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
        g1 _ (by unfold WIT; omega), if_neg (by unfold WIT; omega), g0z _ (by unfold WIT GTAB; omega),
        wword_zero w j (by omega)]
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by omega), g0z A (by simp only [GTAB,TAB] at *; omega)]
  · refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro k hk
      obtain ⟨hk1, hk2⟩ := DATA_ge k hk
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
        if_neg (by omega), g0 _ (by omega), if_pos (by unfold DATA GTAB; omega),
        show DATA + 8 * k - GTAB = 69536 + 8 * k by unfold DATA GTAB; omega,
        data_c_word k hk]
    · intro i hi
      rw [gb _ (by unfold Search.TOP_DATA GTAB; omega) (by unfold Search.TOP_DATA; omega)]
      have hidx : Search.TOP_DATA + i - GTAB = 65536 + i := by
        unfold Search.TOP_DATA GTAB; omega
      rw [hidx]
      rw [show 65536+i=2048+(63488+i) by omega,data_c_byte]
      exact Search.verifyData_sum i hi
    · intro i hi
      rw [gb _ (by unfold PAIR_DATA GTAB; omega) (by unfold PAIR_DATA; omega)]
      have hidx : PAIR_DATA + i - GTAB = 36864 + i := by
        unfold PAIR_DATA GTAB; omega
      rw [hidx]
      rw [show 36864+i=2048+(34816+i) by omega,data_c_byte]
      exact Search.verifyData_pair i hi
    · intro i hi
      rw [gb _ (by unfold TAIL_DATA GTAB; omega) (by unfold TAIL_DATA; omega)]
      have hidx : TAIL_DATA + i - GTAB = 53248 + i := by
        unfold TAIL_DATA GTAB; omega
      rw [hidx]
      rw [show 53248+i=2048+(51200+i) by omega,data_c_byte]
      exact Search.verifyData_tail i hi
    · intro k hk
      rw [gm,g3 _ (by unfold HDATA; omega),if_neg (by unfold HDATA; omega),
        g2 _ (by unfold HDATA; omega),if_neg (by unfold HDATA; omega),
        g1 _ (by unfold HDATA; omega),if_neg (by unfold HDATA; omega),
        g0 _ (by unfold HDATA; omega),if_pos (by unfold HDATA GTAB; omega),
        show HDATA+8*k-GTAB=18432+8*k by unfold HDATA GTAB; omega,data_c_header k hk]
    · intro j hj
      rw [gm, g3 _ (by simp only [GTAB,TAB] at *; omega), if_neg (by simp only [GTAB,TAB] at *; omega), g2 _ (by simp only [GTAB,TAB] at *; omega),
        if_neg (by simp only [GTAB,TAB] at *; omega), g1 _ (by simp only [GTAB,TAB] at *; omega), if_neg (by simp only [GTAB,TAB] at *; omega),
        g0 _ (by simp only [GTAB,TAB] at *; omega), if_pos (by simp only [GTAB,TAB] at *; omega),
        show TAB + 8 * j - GTAB = 2048+8 * j by unfold TAB GTAB; omega, data_c_tab j hj]
  · simp [MachineState.setReg, MachineState.getReg]
    exact congrArg (BitVec.ofNat 64) eD

  · intro k hk
    rw [gm,g3 _ (by simp only [GTAB,TAB] at *;omega),if_neg (by simp only [GTAB,TAB] at *;omega),
      g2 _ (by simp only [GTAB,TAB] at *;omega),if_neg (by simp only [GTAB,TAB] at *;omega),
      g1 _ (by simp only [GTAB,TAB] at *;omega),if_neg (by simp only [GTAB,TAB] at *;omega),
      g0 _ (by simp only [GTAB,TAB] at *;omega),if_pos (by simp only [GTAB,TAB] at *;omega),
      show 0xfef000+8*k-GTAB=8*k by simp only [GTAB,TAB] at *;omega,data_c_prefix k hk]

#print axioms init_c
end SigGolfCandidate.T3M.CanonicalNative
