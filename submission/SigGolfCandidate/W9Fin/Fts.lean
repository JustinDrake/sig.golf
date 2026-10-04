import SigGolfCandidate.T3M.Verify.Compose
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctImage
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.W9Drv.Gate
import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.T3M.Submission
import SigGolfCandidate.W9Drv.CoordReturn

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def FtsGood : Prop :=
  ∀ (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u →
    K none = pure (false, 0) →
    (∀ root t, FtsOut ⟨pk, w, a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) →
    GoodQFor Frozen.image u (N + 2023) (C + 2023) Q (A + 1896)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a
        else pure none) K)
end W9Drv
end

section

namespace W9Fin
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open W9Machine W9Drv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gHookWords : List (BitVec 32) := [0x6003803,37748847]
def gHook : Result :=
  ⟨⟨RegFile.init.set .x16 (.ld (.c (BitVec.ofNat 64 96))), [], []⟩, .c (pcOf 27), .jump, 2, 2⟩
theorem gHook_checked : rOK (symRun {} gHookWords (pcOf 17) 2) gHook = true := by decide +kernel
theorem gHook_linked : sliceChecked 17 gHookWords = true := by decide +kernel
theorem hook_steps (u : MachineState) (hpc : u.pc = pcOf 17) :
    Steps Frozen.image u 2 2 (gHook.toState u) ∧ (gHook.toState u).pc = pcOf 27 ∧
      (gHook.toState u).mem = u.mem ∧
      ∀ r, r ≠ .x16 → (gHook.toState u).getReg r = u.getReg r := by
  refine ⟨block_steps gHook_checked gHook_linked rfl u hpc, rfl, toState_mem_nil _ _ rfl, ?_⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | rfl | exact absurd rfl hr
end W9Fin
end

section



set_option linter.unusedSimpArgs false
namespace W9Fin
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
def bankOK : Bool :=
  (List.range 9).all fun k =>
    bytesToWordLE ((Images.verifyPrefixData.drop (8 * (64 * k + 56))).take 8) ==
      BitVec.ofNat 64 (1 + 3 * 256 + (4 + k) * 65536) &&
    bytesToWordLE ((Images.verifyPrefixData.drop (8 * (64 * k + 57))).take 8) ==
      BitVec.ofNat 64 (1 + 6 * 256 + k * 65536)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem bankOK_eq : bankOK = true := by decide +kernel
abbrev Bank (u : MachineState) : Prop := W9Drv.HeaderBank u
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 4608 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Bank t := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hm _ (by unfold VERIFY_DATA; omega) (by unfold VERIFY_DATA; have := k.isLt; omega)]
    exact h.node k
  · rw [hm _ (by unfold VERIFY_DATA; omega) (by unfold VERIFY_DATA; have := k.isLt; omega)]
    exact h.leaf k
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 24264) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 576) :
    s.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8 * j)) =
      bytesToWordLE ((Images.verifyPrefixData.drop (8 * j)).take 8) := by
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
  rw [gm, g3 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g2 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g1 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g0 _ (by unfold VERIFY_DATA; omega), if_pos (by unfold VERIFY_DATA; omega),
    show VERIFY_DATA + 8 * j - VERIFY_DATA = 8 * j by omega]
  show bytesToWordLE ((Images.verifyData.drop (8 * j)).take 8) = _
  rw [Images.verifyData, List.drop_append_of_le_length (by rw [Images.verifyPrefixData_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, Images.verifyPrefixData_length]; omega)]
theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 24264) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  have hB := List.all_eq_true.mp bankOK_eq
  have hk : ∀ k : Fin 9, _ := fun k : Fin 9 => hB k.val (List.mem_range.mpr k.isLt)
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hkt := hk k
    simp only [Bool.and_eq_true] at hkt
    rw [show 0xfee600 + 512 * k.val + 448 = VERIFY_DATA + 8 * (64 * k.val + 56) by unfold VERIFY_DATA; omega,
      init_word m pk w s h _ (by have := k.isLt; omega)]
    exact beq_iff_eq.mp hkt.1
  · have hkt := hk k
    simp only [Bool.and_eq_true] at hkt
    rw [show 0xfee600 + 512 * k.val + 456 = VERIFY_DATA + 8 * (64 * k.val + 57) by unfold VERIFY_DATA; omega,
      init_word m pk w s h _ (by have := k.isLt; omega)]
    exact beq_iff_eq.mp hkt.2
abbrev cw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def rejectPc : Nat := 743
def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc, true, steps, brs, none, steps⟩
def lwuDc : E := .un (.ld .wu 0) (.ld (cw 0x810))
def proBr (d : Bool) : Br := ⟨.ne, .bin .srl lwuDc (cw 21), .c 0, d⟩
def proSpec : Spec :=
  ⟨[(.x4, cw 3073)],
    [(⟨none, BitVec.ofNat 64 0x28⟩, .ld (cw 0x808)), (⟨none, BitVec.ofNat 64 0x20⟩, .ld (cw 0x800)),
      (⟨none, BitVec.ofNat 64 0x30⟩, cw 0xc01), (⟨none, BitVec.ofNat 64 0x38⟩, .bin .sll lwuDc (cw 32))],
    16, true, 16, [proBr false], none, 16⟩
def proPost : List (Reg × Word) := baseK ++ [(.x10, 32), (.x11, 64), (.x12, 96)]
theorem proCheck : specB [] [] baseK (runAt k0 [] 0 [.br false]) proSpec [] proPost [.x2] = true := by
  decide +kernel
theorem proRejCheck : specB [] [] [] (runAt k0 [] 0 [.br true]) (rejSpec 8 [proBr true]) [] [] [] = true := by
  decide +kernel
theorem lwuDc_eval (w : WBytes) (s : MachineState) (hW : WitAll w s) :
    lwuDc.eval s = BitVec.ofNat 64 (wdc w).toNat := by
  have h2 : s.getMem (BitVec.ofNat 64 0x810) = wword w 2 := hW 2 (by unfold WX; omega)
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 0x810)) 0).toNat = _
  rw [h2]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wdc, wle32, dcOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have : (w.toNat / 2 ^ (64 * 2) % 2 ^ 64 / 2 ^ (0 / 4 * 32) % 2 ^ 32) = w.toNat / 2 ^ 128 % 2 ^ 32 := by
    rw [show 0 / 4 * 32 = 0 by rfl, pow_zero, Nat.div_one, show 64 * 2 = 128 by rfl,
      Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [this]
theorem dc_lt (w : WBytes) : (wdc w).toNat < 2 ^ 32 := (wdc w).isLt
theorem proBr_iff (w : WBytes) (s : MachineState) (hW : WitAll w s) (d : Bool) :
    Br.holds s (proBr d) ↔ d = decide ((wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit) := by
  have hd := dc_lt w
  simp only [proBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, lwuDc_eval w s hW]
  have e : (BitVec.ofNat 64 (wdc w).toNat >>> ((BitVec.ofNat 64 21).toNat % 64)) =
      BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (wdc w).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (wdc w).toNat / 2 ^ 21 < 2 ^ 64 by omega)]
  rw [e]
  by_cases h : (wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit
  · have hne : BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      unfold ClaudeWCT.WCT9.digestAttemptLimit at h
      simp at this; omega
    rw [show (BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) != (0 : Word)) = true from bne_iff_ne.mpr hne,
      decide_eq_true h]
    exact eq_comm
  · have h0 : (wdc w).toNat / 2 ^ 21 = 0 := by unfold ClaudeWCT.WCT9.digestAttemptLimit at h; omega
    rw [h0, decide_eq_false h, show (BitVec.ofNat 64 0 != (0 : Word)) = false by decide]
    exact eq_comm
structure DgPre (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) : Prop where
  pc : t.pc = pcOf 16
  known : KnownOK proPost t
  wit : WitAll w t
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t
  sp : t.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank t
structure DgOut (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 17
  known : KnownOK proPost u
  wit : WitAll w u
  pk : PkOK pk u
  nwords : ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x80 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u
  sp : u.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank u
theorem digest_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s)
    (hb : Bank s) :
    ((wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit → ∃ u, Steps image s 8 8 u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → ∃ t, Steps image s 16 16 t ∧
        fetch image t = some (.base .ECALL) ∧
        hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (digestInput (wrho w) m (wdc w))) ∧
        DgPre m pk w t) := by
  have hk : KnownOK k0 s := hs.known
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_run proRejCheck s hs.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
      hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run proCheck s hs.pc hk (by
      intro b hb; simp only [proSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit false).mpr (by simp; omega)) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpec.mem A := ht.mem
    have hkt : KnownOK proPost t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 32 := hkt (.x10, 32) (by simp [proPost])
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [proPost])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := hkt (.x12, 96) (by simp [proPost])
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 0x20 → A ≠ 0x28 → A ≠ 0x30 → A ≠ 0x38 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simpa using fun h => by omega⟩
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 32 64 96 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hl := digestInput_length (wrho w) m (wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 32 hl h10 (by decide) (by decide) h11
      rw [wordsOf_digestInput]
      have e20 : t.getMem (BitVec.ofNat 64 32) = dlo (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x20) = True by decide, if_true, if_false, E.eval]
        have h0 : s.getMem (BitVec.ofNat 64 0x800) = wword w 0 := hs.wit 0 (by unfold WX; omega)
        rw [h0]
        exact (Verify.wdig_lo w 0).symm
      have e28 : t.getMem (BitVec.ofNat 64 (32 + 8)) = dhi (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 0x28) = True by decide, if_true, E.eval]
        have h1 : s.getMem (BitVec.ofNat 64 0x808) = wword w 1 := hs.wit 1 (by unfold WX; omega)
        rw [h1]
        exact (Verify.wdig_hi w 0).symm
      have e30 : t.getMem (BitVec.ofNat 64 (32 + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x30) = True by decide, if_true, if_false, E.eval]
        rfl
      have e38 : t.getMem (BitVec.ofNat 64 (32 + 24)) = BitVec.ofNat 64 (hdr1 0 (wdc w).toNat) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x30) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x38) = True by decide, if_true, if_false]
        show BinOp.eval .sll (lwuDc.eval s) (BitVec.ofNat 64 32) = _
        rw [lwuDc_eval w s hs.wit]
        simp only [BinOp.eval]
        rw [ofNat_shl' _ 32, hdr1_eq 0 _ (by norm_num) (dc_lt w)]
        congr 1
        rw [show 32 % 2 ^ 64 % 64 = 32 by norm_num]; ring
      have em : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (32 + 32 + 8 * k)) = m.extractLsb' (64 * k) 64 := by
        intro k hk
        rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega), ← hs.msg k hk]
      rw [e20, e28, e30, e38, show 32 + 32 = 32 + 32 + 8 * 0 by rfl, em 0 (by omega),
        show 32 + 40 = 32 + 32 + 8 * 1 by rfl, em 1 (by omega), show 32 + 48 = 32 + 32 + 8 * 2 by rfl,
        em 2 (by omega), show 32 + 56 = 32 + 32 + 8 * 3 by rfl, em 3 (by omega)]
    · refine ⟨ht.pc rfl, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [frame _ (by unfold WIT WX at *; omega) (by unfold WIT; omega) (by unfold WIT; omega)
          (by unfold WIT; omega) (by unfold WIT; omega)]
        exact hs.wit j hj
      · exact ⟨(frame 0xA0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.1,
          (frame 0xA8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.2⟩
      · intro A hA hz
        unfold WIT at hA
        rw [frame A (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hs.zero A hA (by omega)
      · apply hs.data.congr
        intro A hA hEnd
        exact frame A (by omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega)
      · rw [ht.keep .x2 (by simp)]; exact hs.sp
      · exact hb.congr (fun A hA _ => frame A (by unfold VERIFY_DATA at *; omega)
          (by unfold VERIFY_DATA at hA; omega) (by unfold VERIFY_DATA at hA; omega)
          (by unfold VERIFY_DATA at hA; omega) (by unfold VERIFY_DATA at hA; omega))
theorem digest_out (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) (ht : DgPre m pk w t)
    (a : HashOutput) : DgOut m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := ht.known (.x12, 96) (by simp [proPost])
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, ht.pc]; rfl
  · intro j hj
    rw [writeHash_frame t a 96 _ h12 (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT; omega))]
    exact ht.wit j hj
  · exact ⟨(writeHash_frame t a 96 0xA0 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.1,
      (writeHash_frame t a 96 0xA8 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.2⟩
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact writeHash_at0 t a 96 h12 (by omega)
    · exact writeHash_at8 t a 96 h12 (by omega)
    · exact writeHash_at16 t a 96 h12 (by omega)
    · exact writeHash_at24 t a 96 h12 (by omega)
  · intro A hA hz
    unfold WIT at hA
    rw [writeHash_frame t a 96 A h12 (by omega) (by omega) (by omega)]
    exact ht.zero A (by unfold WIT; omega) (by omega)
  · apply ht.data.congr
    intro A hA hEnd
    exact writeHash_frame t a 96 A h12 (by omega) (by omega)
      (Or.inr (by unfold TAB at hA; omega))
  · rw [writeHash_getReg]; exact ht.sp
  · exact ht.bank.congr (fun A hA _ => writeHash_frame t a 96 A h12 (by unfold VERIFY_DATA at *; omega) (by omega)
      (Or.inr (by unfold VERIFY_DATA at hA; omega)))
theorem digestP_good (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s)
    (hb : Bank s) {N C A : Nat} {Q : Prop} (K : Option HashOutput → OracleComp HashSpec Obs)
    (hK : K none = pure (false, 0))
    (hcont : ∀ a u, DgOut m pk w a u → GoodQ u N C Q A (K (some a))) :
    GoodQ s (N + 17) (C + 24) Q (A + 24) (ccM (ClaudeWCT.W9.T3M.digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs hb
  unfold ClaudeWCT.W9.T3M.digestP
  by_cases hdc : (wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit
  · rw [if_pos hdc, ccM_pure, hK]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej hdc
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold SigGolfCandidate.T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by simp [proPost, baseK])
    have := GoodQ.publicHash_bind (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem gatePre_of_hook (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (hu : DgOut m pk w a u) :
    Steps W9Machine.Frozen.image u 2 2 (gHook.toState u) ∧
      W9Drv.GatePre pk w a (gHook.toState u) := by
  obtain ⟨hst, hpc', hm, hr⟩ := hook_steps u hu.pc
  have e : ∀ A, (gHook.toState u).getMem A = u.getMem A := fun A => congrFun hm A
  have h5 : u.getReg .x5 = 0 := hu.known (.x5, 0) (by simp [proPost, baseK])
  have h18 : u.getReg .x18 = 0xFFF := hu.known (.x18, 0xFFF) (by simp [proPost, baseK])
  have hglob : Glob baseK w pk u := by
    refine ⟨?_, hu.wit.hdr, hu.pk, ?_, ?_, hu.data⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact h5
      · exact h18
    · intro A hA
      simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl <;> exact hu.zero _ (by unfold WIT; omega) (by omega)
    · show (u.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hu.zero CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega)]
      rfl
  refine ⟨hst, hpc', W9Drv.glob_congr hglob hm ((hr .x5 (by decide)).trans h5)
      ((hr .x18 (by decide)).trans h18), fun k hk => (e _).trans (hu.nwords k hk),
    ⟨fun k => (e _).trans (hu.bank.node k), fun k => (e _).trans (hu.bank.leaf k)⟩,
    fun j hj => (e _).trans (hu.wit j hj)⟩
end W9Fin
end

section

namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def fPrepWords : List (BitVec 32) := [4535,0xf0118193,0x40303823,0x41603c23,0x40003023,0x40003423,0x40000513,335545747,268437011,115]
def fTailWords : List (BitVec 32) := [0x5a40006f]
def fPrep : Result :=
  ⟨⟨(((RegFile.init.set .x3 (.c 3841)).set .x10 (.c 1024)).set .x11 (.c 320)).set .x12 (.c 256),
    [(⟨none, 1032⟩, .c 0), (⟨none, 1024⟩, .c 0), (⟨none, 1048⟩, .reg .x22),
      (⟨none, 1040⟩, .c 3841)], []⟩, .c (pcOf 226), .ecall, 9, 9⟩
def fTail : Result := ⟨SymState.init, .c (pcOf 588), .jump, 1, 1⟩
theorem fPrep_checked : rOK (symRun {} fPrepWords (pcOf 217) 10) fPrep = true := by decide +kernel
theorem fPrep_linked : sliceChecked 217 fPrepWords = true := by decide +kernel
theorem fTail_checked : rOK (symRun {} fTailWords (pcOf 227) 1) fTail = true := by decide +kernel
theorem fTail_linked : sliceChecked 227 fTailWords = true := by decide +kernel
end W9Drv
end

section


namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M HashInput pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
open W9Machine
abbrev forestIn := ClaudeWCT.WCT9.forestInput
theorem forestIn_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestIn index pairs).length = 320 := by
  simp only [forestIn, ClaudeWCT.WCT9.forestInput, List.length_append, bytesLE_length,
    SigGolfCandidate.T3.zero16, List.length_replicate, List.length_flatMap]
  simp [h]
theorem wordsOf_forestIn (index : Nat) (pairs : List (Digest × Digest)) :
    wordsOf (forestIn index pairs) =
      [0, 0, BitVec.ofNat 64 (hdr0 15 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        pairs.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
  unfold forestIn ClaudeWCT.WCT9.forestInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]), wordsOf_append _ _ (by simp [SigGolfCandidate.T3.zero16]), wordsOf_header]
  have hp : ∀ ps : List (Digest × Digest),
      wordsOf (ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)) =
        ps.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons]
      rw [wordsOf_append _ _ (by simp [bytesLE_length]),
        wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
      rfl
  rw [hp]
  rfl
theorem pad64_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    pad64 (forestIn index pairs) = forestIn index pairs := by
  simp [pad64, forestIn_length index pairs h]
theorem blocks_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (toQ (pad64 (forestIn index pairs))).blocks = 5 := by
  rw [pad64_forestIn index pairs h,
    blocks_toQ (by rw [Aligned, forestIn_length index pairs h]; omega), forestIn_length index pairs h]
theorem hdr0_forest15 (idx : Nat) (hi : idx < 2^32) : hdr0 15 0 idx 0 = 3841 := by
  rw [hdr0_eq 15 0 idx 0 (by decide) (by decide) hi (by decide)]; norm_num
theorem hdr1_forest15 (idx : Nat) (hi : idx < 2^32) : hdr1 idx 0 = idx := by
  unfold hdr1; rw [Nat.mod_eq_of_lt hi]; simp
theorem fPrep_mem (u : MachineState) (B : Nat) (hB : B < 2^64) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) =
      if B = 1032 then 0 else if B = 1024 then 0
      else if B = 1048 then u.getReg .x22 else if B = 1040 then 3841
      else u.getMem (BitVec.ofNat 64 B) := by
  rw [Result.toState_getMem]
  change memEval u [(⟨none, BitVec.ofNat 64 1032⟩, .c 0), (⟨none, BitVec.ofNat 64 1024⟩, .c 0),
    (⟨none, BitVec.ofNat 64 1048⟩, .reg .x22), (⟨none, BitVec.ofNat 64 1040⟩, .c 3841)] (BitVec.ofNat 64 B) = _
  rw [memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_cons_ofNat _ _ _ _ _ hB (by norm_num), memEval_nil]
  rfl
theorem fPrep_frame (u : MachineState) (B : Nat) (hB : B < 2^64)
    (h : B ≠ 1032 ∧ B ≠ 1024 ∧ B ≠ 1048 ∧ B ≠ 1040) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) = u.getMem (BitVec.ofNat 64 B) := by
  rw [fPrep_mem u B hB, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2]
theorem forest_words (u : MachineState) (idx : Nat) (pairs : List (Digest × Digest))
    (hlen : pairs.length = 9) (hi : idx < 2^31)
    (h22 : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hr : ∀ i, i < 9 → DigAt u (1056+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt u (1056+32*i+16) (pairs.getD i (0,0)).2) :
    (fPrep.toState u).readWords (BitVec.ofNat 64 1024) 40 =
      wordsOf (pad64 (forestIn idx pairs)) := by
  have hp : ∀ i, i < 9 → DigAt (fPrep.toState u) (1056+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt (fPrep.toState u) (1056+32*i+16) (pairs.getD i (0,0)).2 := by
    intro i hi9
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.2
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.2
  rw [readWords_ofNat _ 1024 40 (by norm_num), pad64_forestIn idx pairs hlen,
    wordsOf_forestIn, show List.range 40 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] from rfl]
  match pairs, hlen, hp with
  | [p0,p1,p2,p3,p4,p5,p6,p7,p8], _, hp =>
    have d0 := hp 0 (by decide)
    have d1 := hp 1 (by decide)
    have d2 := hp 2 (by decide)
    have d3 := hp 3 (by decide)
    have d4 := hp 4 (by decide)
    have d5 := hp 5 (by decide)
    have d6 := hp 6 (by decide)
    have d7 := hp 7 (by decide)
    have d8 := hp 8 (by decide)
    norm_num [List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6 d7 d8
    have h16 : (fPrep.toState u).getMem (BitVec.ofNat 64 1040) =
        BitVec.ofNat 64 (hdr0 15 0 idx 0) := by
      rw [fPrep_mem u _ (by norm_num), hdr0_forest15 idx (by omega)]; rfl
    have h24 : (fPrep.toState u).getMem (BitVec.ofNat 64 1048) =
        BitVec.ofNat 64 (hdr1 idx 0) := by
      rw [fPrep_mem u _ (by norm_num), hdr1_forest15 idx (by omega)]; exact h22
    have z0 : (fPrep.toState u).getMem (BitVec.ofNat 64 1024) = 0 := by
      rw [fPrep_mem u _ (by norm_num)]; rfl
    have z1 : (fPrep.toState u).getMem (BitVec.ofNat 64 1032) = 0 := by
      rw [fPrep_mem u _ (by norm_num)]; rfl
    simp only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceAdd, d0.1.1, d0.1.2, d0.2.1, d0.2.2, d1.1.1, d1.1.2, d1.2.1, d1.2.2, d2.1.1, d2.1.2, d2.2.1, d2.2.2, d3.1.1, d3.1.2, d3.2.1, d3.2.2, d4.1.1, d4.1.2, d4.2.1, d4.2.2, d5.1.1, d5.1.2, d5.2.1, d5.2.2, d6.1.1, d6.1.2, d6.2.1, d6.2.2, d7.1.1, d7.1.2, d7.2.1, d7.2.2, d8.1.1, d8.1.2, d8.2.1, d8.2.2,
      h16, h24, z0, z1, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil]
theorem forest_good (pk : Digest) (w : WBytes) (a : HashOutput)
    (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a 9 roots u)
    (hnext : ∀ root t, FtsOut ⟨pk, w, a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K root)) :
    GoodQFor Frozen.image u (N + 11) (C + 50) Q (A + 50)
      (ccM (ClaudeWCT.WCT9.forestPk (a.toNat % 2 ^ 31) roots) K) := by
  have hi : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have st1 := block_steps fPrep_checked fPrep_linked rfl u hu.pc
  have st1' : Steps Frozen.image u 9 9 (fPrep.toState u) := st1
  set s1 := fPrep.toState u with hs1
  have hf := block_ecall fPrep_checked fPrep_linked rfl u rfl
  have r1 : ∀ x, x ≠ .x3 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → s1.getReg x = u.getReg x := by
    intro x h3 h10 h11 h12
    rw [hs1, Result.toState_getReg]
    cases x <;> first | rfl | exact absurd rfl ‹_›
  have h5 : s1.getReg .x5 = 0 :=
    (r1 .x5 (by decide) (by decide) (by decide) (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
  have h10 : s1.getReg .x10 = BitVec.ofNat 64 0x400 := by rw [hs1, Result.toState_getReg]; rfl
  have h11 : s1.getReg .x11 = BitVec.ofNat 64 (64 * (4 + 1)) := by rw [hs1, Result.toState_getReg]; rfl
  have h12 : s1.getReg .x12 = BitVec.ofNat 64 0x100 := by rw [hs1, Result.toState_getReg]; rfl
  have h22 : s1.getReg .x22 = BitVec.ofNat 64 (idxOf a) :=
    (r1 .x22 (by decide) (by decide) (by decide) (by decide)).trans hu.index
  have hv : hashArgumentsValid s1 = true :=
    hashArgs_of s1 0x400 320 0x100 h10 h11 h12 (by decide) (by decide) (by norm_num) (by decide)
      (by norm_num)
  have hin : hashInput s1 = toQ (pad64 (forestIn (idxOf a) roots)) :=
    hashInput_toQ s1 _ 4 0x400 (by rw [pad64_forestIn _ _ hu.length, forestIn_length _ _ hu.length]) h10 (by decide) (by norm_num)
      h11 (by norm_num) (forest_words u (idxOf a) roots hu.length hi hu.index hu.pairs)
  have g1 : Glob [] w pk s1 :=
    Glob_toState hu.glob fPrep.st (fPrep.pc.eval u) (by decide) rfl
  have o1 : Orig w (fun o => o < 64 ∨ 10568 ≤ o) s1 :=
    hu.layer.frame (fun j hj _ => fPrep_frame u _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
  have hpost : ∀ ans : BitVec 256, GoodQFor Frozen.image (writeHash s1 ans) (N + 1) (C + 1) Q (A + 1)
      (ccM (pure (ans.extractLsb' 0 128) : M Digest) K) := by
    intro ans
    rw [ccM_pure]
    have hpc : (writeHash s1 ans).pc = pcOf 227 := by
      rw [writeHash_pc]
      show pcOf 226 + 4 = pcOf 227
      exact SigGolfCandidate.T3M.pcOf_add4 226
    have st2 := block_steps fTail_checked fTail_linked rfl (writeHash s1 ans) hpc
    have st2' : Steps Frozen.image (writeHash s1 ans) 1 1 (fTail.toState (writeHash s1 ans)) := st2
    set t := fTail.toState (writeHash s1 ans) with ht
    have mt : t.mem = (writeHash s1 ans).mem := toState_mem_nil _ _ rfl
    have et : ∀ A, t.getMem A = (writeHash s1 ans).getMem A := fun A => congrFun mt A
    have hout : FtsOut ⟨pk, w, a⟩ (ans.extractLsb' 0 128) t := by
      refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
      · have gg := Glob_writeHash g1 ans 0x100 h12 (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · change (writeHash s1 ans).getReg .x5 = 0
            rw [writeHash_getReg]; exact h5
          · change (writeHash s1 ans).getReg .x18 = 4095
            rw [writeHash_getReg, r1 .x18 (by decide) (by decide) (by decide) (by decide)]
            exact hu.glob.1 (.x18,4095) (by simp [baseK])
        · exact fun j hj => (et _).trans (gg.2.1 j hj)
        · exact ⟨(et _).trans gg.2.2.1.1, (et _).trans gg.2.2.1.2⟩
        · exact fun A hA => (et _).trans (gg.2.2.2.1 A hA)
        · change (t.getMem _).toNat / 2^32 = 0
          rw [et]; exact gg.2.2.2.2.1
        · exact gg.2.2.2.2.2.congr (fun A _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x22 = _
        rw [writeHash_getReg]; exact h22
      · obtain ⟨e0, e1⟩ := writeHash_lo s1 ans 0x100 h12 (by norm_num)
        exact ⟨(et _).trans e0, (et _).trans e1⟩
      · have o2 := Orig_writeHash o1 ans 0x100 h12 (by norm_num)
        have o3 : Orig w (fun o => o < 64 ∨ 10568 ≤ o) (writeHash s1 ans) :=
          o2.mono (fun o ho => ⟨ho, Or.inr (by unfold WIT; omega)⟩)
        exact o3.frame (fun j _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x12 = _
        rw [writeHash_getReg]
        exact h12
    exact (hnext _ t hout).steps st2'
  have hq := GoodQFor.shortHash_bind (f := fun d : Digest => (pure d : M Digest)) (K := K)
    hf h5 hv hin hpost
  rw [blocks_forestIn _ _ hu.length, bind_pure] at hq
  have := hq.steps st1'
  change GoodQFor Frozen.image u (N+11) (C+50) Q (A+50) (ccM (shortHash (forestIn (idxOf a) roots)) K)
  exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
#print axioms forest_good
end W9Drv
end

section



namespace W9Fin
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
theorem goodQ_frozen (hbridge : W9Machine.Frozen.image = Images.verifyImage) {s : MachineState} {N C A : Nat}
    {Q : Prop} {X : OracleComp HashSpec Obs} :
    W9Machine.GoodQFor W9Machine.Frozen.image s N C Q A X ↔ GoodQ s N C Q A X := by
  rw [hbridge]; rfl
def afterDigest (pk : Digest) (w : WBytes) (N : HashOutput) : SigGolfCandidate.T3.M Bool :=
  (if ClaudeWCT.W9.T3M.gateOk N then ClaudeWCT.W9.T3M.wctP w N else pure none) >>=
    afterFts pk w (N.toNat % 2 ^ 31)
theorem verifyP_eq (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) :
    ClaudeWCT.W9.T3M.verifyP m pk w = (ClaudeWCT.W9.T3M.digestP m w >>= fun o => match o with
      | some N => afterDigest pk w N
      | none => pure false) := by
  unfold ClaudeWCT.W9.T3M.verifyP afterDigest
  congr 1; funext o
  rcases o with _ | N
  · rfl
  · cases hg : ClaudeWCT.W9.T3M.gateOk N
    · simp only [hg, Bool.not_false, if_true, if_false, Bool.false_eq_true, pure_bind, afterFts]
    · simp only [hg, Bool.not_true, if_true, if_false, Bool.false_eq_true]
      rfl
theorem afterDigest_good (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood)
    (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (hu : DgOut m pk w a u) :
    GoodQ u (8050 + 2023 + 2) (8050 + 2023 + 2) True (5706 + 1896 + 2) (ccM (afterDigest pk w a) Kb) := by
  obtain ⟨hst, hpre⟩ := gatePre_of_hook m pk w a u hu
  have h := fts pk w a _ 8050 8050 5706 True (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb) hpre
    (by simp only [afterFts, ccM_pure, Kb])
    (fun root t ht => (goodQ_frozen hbridge).mpr (after_good pk w True trivial a root t ht))
  have h2 := (goodQ_frozen hbridge).mp (h.steps hst)
  unfold afterDigest
  rw [ccM_bind]
  exact h2
def fuelBound : Nat := 17 + (8050 + 2023 + 2)
def cycleBoundAll : Nat := 24 + (8050 + 2023 + 2)
def cycleBound : Nat := 24 + (5706 + 1896 + 2)
theorem fuelBound_eq : fuelBound = 10092 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10099 := rfl
theorem cycleBound_eq' : cycleBound = 7628 := rfl
theorem cycleBound_eq : cycleBound = ClaudeWCT.W9.T3M.Final.verifyCycleBound := rfl
theorem verify_good (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 24264) (s : MachineState)
    (hs : initialState submission .verify (m, pk, w) = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs)
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hu => afterDigest_good hbridge fts m pk w a u hu)
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem I0_verify : I0.verify = Images.verifyImage := rfl
theorem init_mk (sI eI : Riscv.Image) (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 24264) :
    initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) =
      initialState submission .verify (m, pk, w) :=
  rfl
theorem mk_verify (sI eI : Riscv.Image) :
    (⟨sI, eI, Images.verifyImage⟩ : ClaudeWCT.W9.T3M.Images).verify = Images.verifyImage := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 24264) :
    ∃ s, initialState submission .verify (m, pk, w) = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_refines_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good hbridge fts m pk w s hs CYCLE_LIMIT fuelBound_le).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk w))
  rw [← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl
theorem verify_terminates_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyTerminates I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good hbridge fts m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1
theorem verify_accept_cycles_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w h
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good hbridge fts m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have := (hg.2.2 hsucc).2
  rw [cycleBound_eq] at this
  exact this
theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI hbridge fts, verify_terminates_of I hI hbridge fts,
    verify_accept_cycles_of I hI hbridge fts⟩
theorem verify_inputs
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs_of I0 I0_verify hbridge fts
end W9Fin
#print axioms W9Fin.verify_inputs_of
#print axioms W9Fin.verify_inputs
end

section



namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
def finishFts (a : HashOutput) (state : Option (List (Digest × Digest))) : M (Option Digest) :=
  match state with
  | none => pure none
  | some roots => some <$> ClaudeWCT.WCT9.forestPk (idxOf a) roots
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => if k.val = 0 then 205 else 207)).sum
def coordsAccept (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => if k.val = 0 then 200 else 202)).sum
theorem fold_none (w : WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, ClaudeWCT.W9.T3M.wctStep, pure_bind] using ih
theorem coordinates_good (chains : Chain.AllGood Frozen.layout) (pk : Digest) (w : WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (roots : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : CoordPre pk w a n roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) :
    GoodQFor Frozen.image u (N + (coordsCost ks + 50)) (C + (coordsCost ks + 50)) Q
      (A + (coordsAccept ks + 50))
      (ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some roots) >>= finishFts a) K) := by
  induction ks generalizing n roots u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishFts]
    have hf := forest_good pk w a roots u N C A Q (fun root => K (some root)) hu hnext
    rw [map_eq_bind_pure_comp, ccM_bind]
    simp only [Function.comp_apply, ccM_pure]
    exact hf.mono (by change N + 11 ≤ N + 50; omega) (by rfl) (fun hq => ⟨hq, by rfl⟩)
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) state >>= finishFts a) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishFts, ccM_pure, hnone]
    have hstep := coord_good chains pk w a k roots u (N + (coordsCost ks + 50))
      (C + (coordsCost ks + 50)) (A + (coordsAccept ks + 50)) Q K' hu hkNone
      (fun root t hh => ih (k.val + 1) (roots ++ [root]) t ht (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind]
theorem fts_good (chains : Chain.AllGood Frozen.layout) : FtsGood := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ClaudeWCT.W9.T3M.wctP w a) K else K none
  have hg := gate_good pk w a u (N + 1911) (C + 1911) (A + 1866) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := coordinates_good chains pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide)
        (by simp) ht hnone hnext
      rw [show coordsCost (List.finRange 9) + 50 = 1911 by decide,
        show coordsAccept (List.finRange 9) + 50 = 1866 by decide] at hc
      apply hc.congr
      change ccM (_ >>= finishFts a) K = ccM (ClaudeWCT.W9.T3M.wctP w a) K
      apply congrArg (fun p : M (Option Digest) => ccM p K)
      unfold ClaudeWCT.W9.T3M.wctP
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option Digest) =>
        (List.finRange 9).foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor Frozen.image u (N + 1941) (C + 1941) Q (A + 1896)
    (KG (ClaudeWCT.W9.T3M.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)).congr
  cases ClaudeWCT.W9.T3M.gateOk a <;> simp [KG, ccM_pure]
#print axioms fts_good
end W9Drv
end

section


namespace W9Fin
theorem verify_inputs'_of (I : ClaudeWCT.W9.T3M.Images)
    (hI : I.verify = SigGolfCandidate.T3M.Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (chains : W9Machine.Chain.AllGood W9Machine.Frozen.layout) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  verify_inputs_of I hI hbridge (W9Drv.fts_good chains)
theorem verify_inputs'
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (chains : W9Machine.Chain.AllGood W9Machine.Frozen.layout) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs hbridge (W9Drv.fts_good chains)
end W9Fin
#print axioms W9Fin.verify_inputs'_of
#print axioms W9Fin.verify_inputs'
end
