import SigGolfCandidate.W9Drv.Gate
import SigGolfCandidate.W9Drv.FtsDefs
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending

section

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gHookWords : List (BitVec 32) := [0x6003803,20971631]
def gHook : Result :=
  ⟨⟨RegFile.init.set .x16 (.ld (.c (BitVec.ofNat 64 96))), [], []⟩, .c (pcOf 23), .jump, 2, 2⟩
theorem gHook_checked : rOK (symRun {} gHookWords (pcOf 17) 2) gHook = true := by decide +kernel
theorem gHook_linked : sliceChecked 17 gHookWords = true := by decide +kernel
theorem hook_steps (u : MachineState) (hpc : u.pc = pcOf 17) :
    Steps Frozen.image u 2 2 (gHook.toState u) ∧ (gHook.toState u).pc = pcOf 23 ∧
      (gHook.toState u).mem = u.mem ∧
      ∀ r, r ≠ .x16 → (gHook.toState u).getReg r = u.getReg r := by
  refine ⟨block_steps gHook_checked gHook_linked rfl u hpc, rfl, toState_mem_nil _ _ rfl, ?_⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | rfl | exact absurd rfl hr
theorem gate_good17 (pk : Digest) (w : WBytes) (a : HashOutput)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Bool → OracleComp HashSpec Obs)
    (hpc : u.pc = pcOf 17) (hglob : Glob baseK w pk u) (hdig : DigestAt a u)
    (hbank : HeaderBank (idxOf a) u) (hwit : WitAll w u)
    (hnone : K false = pure (false, 0))
    (hnext : ∀ t, CoordPre pk w a 0 [] t →
      GoodQFor Frozen.image t N C Q A (K true)) :
    GoodQFor Frozen.image u (N + 44) (C + 44) Q (A + 44) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  obtain ⟨hst, hpc', hm, hr⟩ := hook_steps u hpc
  have e : ∀ A, (gHook.toState u).getMem A = u.getMem A := fun A => congrFun hm A
  have hpre : GatePre pk w a (gHook.toState u) := by
    refine ⟨hpc', glob_congr hglob hm ((hr .x5 (by decide)).trans (hglob.1 (.x5, 0) (by simp [baseK])))
      ((hr .x18 (by decide)).trans (hglob.1 (.x18, 0xFFF) (by simp [baseK]))),
      fun k hk => (e _).trans (hdig k hk), ⟨fun k t ht d hd => (e _).trans (hbank.chain k t ht d hd),
      fun k => (e _).trans (hbank.node k), fun k => (e _).trans (hbank.leaf k)⟩,
      fun j hj => (e _).trans (hwit j hj)⟩
  have := (gate_good pk w a _ N C A Q K hpre hnone hnext).steps hst
  exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end

section



set_option linter.unusedSimpArgs false
namespace W9Fin
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
def bankOK : Bool :=
  (List.range 9).all fun k =>
    ((List.range 7).all fun t => (List.range 3).all fun d =>
      bytesToWordLE ((Images.verifyPrefixData.drop (8 * (64 * k + 8 * t + d))).take 8) ==
        BitVec.ofNat 64 (0x501 + 65536 * k + 2 ^ 32 * (d + 256 * t))) &&
    bytesToWordLE ((Images.verifyPrefixData.drop (8 * (64 * k + 56))).take 8) ==
      BitVec.ofNat 64 (0xb01 + 65536 * k) &&
    bytesToWordLE ((Images.verifyPrefixData.drop (8 * (64 * k + 57))).take 8) ==
      BitVec.ofNat 64 (0x601 + 65536 * k)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem bankOK_eq : bankOK = true := by decide +kernel
def Bank (u : MachineState) : Prop := ∀ index, index < 2 ^ 32 → W9Drv.HeaderBank index u
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 4608 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Bank t := by
  intro index hi
  obtain ⟨hc, hn, hl⟩ := h index hi
  refine ⟨fun k t' ht d hd => ?_, fun k => ?_, fun k => ?_⟩
  · rw [hm _ (by unfold W9Machine.Chain.table VERIFY_DATA; omega)
      (by unfold W9Machine.Chain.table VERIFY_DATA; have := k.isLt; omega)]
    exact hc k t' ht d hd
  · rw [hm _ (by unfold W9Machine.Chain.table VERIFY_DATA; omega)
      (by unfold W9Machine.Chain.table VERIFY_DATA; have := k.isLt; omega)]
    exact hn k
  · rw [hm _ (by unfold W9Machine.Chain.table VERIFY_DATA; omega)
      (by unfold W9Machine.Chain.table VERIFY_DATA; have := k.isLt; omega)]
    exact hl k
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 25240) (s : MachineState)
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
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((25240 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
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
theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 25240) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  intro index hi
  have hB := List.all_eq_true.mp bankOK_eq
  have hk : ∀ k : Fin 9, _ := fun k : Fin 9 => hB k.val (List.mem_range.mpr k.isLt)
  refine ⟨fun k t ht d hd => ?_, fun k => ?_, fun k => ?_⟩
  · have hkt := hk k
    simp only [Bool.and_eq_true] at hkt
    have e := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hkt.1.1 t (List.mem_range.mpr ht)) d
      (List.mem_range.mpr hd))
    rw [show W9Machine.Chain.table k + 64 * t + 8 * d = VERIFY_DATA + 8 * (64 * k.val + 8 * t + d) by
        unfold W9Machine.Chain.table VERIFY_DATA; omega,
      init_word m pk w s h _ (by have := k.isLt; omega), e,
      hdr0_eq 5 k.val index (d + 256 * t) (by decide) (by have := k.isLt; omega) hi (by omega)]
  · have hkt := hk k
    simp only [Bool.and_eq_true] at hkt
    have e := beq_iff_eq.mp hkt.1.2
    rw [show W9Machine.Chain.table k + 448 = VERIFY_DATA + 8 * (64 * k.val + 56) by
        unfold W9Machine.Chain.table VERIFY_DATA; omega,
      init_word m pk w s h _ (by have := k.isLt; omega), e, ClaudeWCT.W9.Machine.Merkle.w0n,
      hdr0_eq 11 k.val index 0 (by decide) (by have := k.isLt; omega) hi (by omega)]
    congr 1
  · have hkt := hk k
    simp only [Bool.and_eq_true] at hkt
    have e := beq_iff_eq.mp hkt.2
    rw [show W9Machine.Chain.table k + 456 = VERIFY_DATA + 8 * (64 * k.val + 57) by
        unfold W9Machine.Chain.table VERIFY_DATA; omega,
      init_word m pk w s h _ (by have := k.isLt; omega), e,
      hdr0_eq 6 k.val index 0 (by decide) (by have := k.isLt; omega) hi (by omega)]
    congr 1
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
    Steps W9Machine.Frozen.image u 2 2 (W9Drv.gHook.toState u) ∧
      W9Drv.GatePre pk w a (W9Drv.gHook.toState u) := by
  obtain ⟨hst, hpc', hm, hr⟩ := W9Drv.hook_steps u hu.pc
  have e : ∀ A, (W9Drv.gHook.toState u).getMem A = u.getMem A := fun A => congrFun hm A
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
      ((hr .x18 (by decide)).trans h18), fun k hk => (e _).trans (hu.nwords k hk), ?_,
    fun j hj => (e _).trans (hu.wit j hj)⟩
  have hb := hu.bank (W9Drv.idxOf a) (show a.toNat % 2 ^ 31 < 2 ^ 32 by omega)
  exact ⟨fun k t ht d hd => (e _).trans (hb.chain k t ht d hd), fun k => (e _).trans (hb.node k),
    fun k => (e _).trans (hb.leaf k)⟩
end W9Fin
end

section



namespace W9Fin
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.ExpandLink (I0)
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
    GoodQ u (8057 + 2023 + 2) (8057 + 2023 + 2) True (5757 + 2023 + 2) (ccM (afterDigest pk w a) Kb) := by
  obtain ⟨hst, hpre⟩ := gatePre_of_hook m pk w a u hu
  have h := fts pk w a _ 8057 8057 5757 True (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb) hpre
    (by simp only [afterFts, ccM_pure, Kb])
    (fun root t ht => (goodQ_frozen hbridge).mpr (after_good pk w True trivial a root t ht))
  have h2 := (goodQ_frozen hbridge).mp (h.steps hst)
  unfold afterDigest
  rw [ccM_bind]
  exact h2
def fuelBound : Nat := 17 + (8057 + 2023 + 2)
def cycleBoundAll : Nat := 24 + (8057 + 2023 + 2)
def cycleBound : Nat := 24 + (5757 + 2023 + 2)
theorem cycleBound_actual : cycleBound = 7806 := rfl
theorem fuelBound_eq : fuelBound = 10099 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10106 := rfl
theorem cycleBound_eq : cycleBound = ClaudeWCT.W9.T3M.Final.verifyCycleBound := rfl
theorem verify_good (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 25240) (s : MachineState)
    (hs : initialState submission .verify (m, pk, w) = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs)
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hu => afterDigest_good hbridge fts m pk w a u hu)
theorem init_I0 (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 25240) :
    initialState (ClaudeWCT.W9.T3M.submission I0) .verify (m, pk, w) = initialState submission .verify (m, pk, w) :=
  rfl
theorem I0_verify : I0.verify = Images.verifyImage := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 25240) :
    ∃ s, initialState submission .verify (m, pk, w) = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_refines (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 := by
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission I0) .verify (m, pk, w) = some s := (init_I0 m pk w).trans hs
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
theorem verify_terminates (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 := by
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission I0) .verify (m, pk, w) = some s := (init_I0 m pk w).trans hs
  have hg := (verify_good hbridge fts m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, I0_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1
theorem verify_accept_cycles (hbridge : W9Machine.Frozen.image = Images.verifyImage) (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 := by
  intro hash m pk w h
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission I0) .verify (m, pk, w) = some s := (init_I0 m pk w).trans hs
  have hg := (verify_good hbridge fts m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, I0_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have := (hg.2.2 hsucc).2
  rw [cycleBound_eq] at this
  exact this
theorem verify_inputs
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (fts : W9Drv.FtsGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  ⟨verify_refines hbridge fts, verify_terminates hbridge fts, verify_accept_cycles hbridge fts⟩
end W9Fin
#print axioms W9Fin.verify_inputs
end
