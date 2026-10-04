import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Drv.GateDefs

section

namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gJumpWords : List (BitVec 32) := [16777327]
def gCheckWords : List (BitVec 32) :=
  [0x06003b03,0x01fb5193,0x0121f1b3,0x06018863]
def gSetupWords : List (BitVec 32) :=
  [0x000b0b1b,0x100313,0x200393,0x2031b93,0x17b04b3,0x17486b3,0x17689b3,0x1798a33,0x17a0ab3,0x17a8d33,0x17d0f33,0x84190413,0xfefe37,0xe00e0e13,0x10137,0xffc10113,0xcfeb7,0x800e8e93,0xd7c37,0x800c0c13]
def gRejectWords : List (BitVec 32) := [1049235,1049875,115]
def gateE : E := .bin .and (.bin .srl (.ld (.c (BitVec.ofNat 64 96))) (.c (BitVec.ofNat 64 31)))
  (.reg .x18)
def idxE : E := .bin (.w .add) (.reg .x22) (.c 0)
def heapE (h : Nat) : E := addC idxE (BitVec.ofNat 64 (2 ^ 32 * h))
def gJump : Result := ⟨SymState.init, .c (pcOf 27), .jump, 1, 1⟩
def gCheck : Result :=
  ⟨⟨(RegFile.init.set .x3 gateE).set .x22
      (.ld (.c (BitVec.ofNat 64 96))), [], []⟩,
    .ite .eq gateE (.c 0) (.c (pcOf 48)) (.c (pcOf 21)), .branch, 4, 4⟩
def gSetup : Result :=
  ⟨⟨{ RegFile.init with
      r2 := .c (BitVec.ofNat 64 0xfffc),
      r6 := .c 1,
      r7 := .c 2,
      r8 := addC (.reg .x18) (-1983),
      r22 := idxE,
      r23 := .c (BitVec.ofNat 64 (2 ^ 32)),
      r24 := .c (BitVec.ofNat 64 0xd6800),
      r28 := .c (BitVec.ofNat 64 (0xfee600 + 2048)),
      r29 := .c (BitVec.ofNat 64 0xce800),
      r9 := heapE 1,
      r13 := heapE 2,
      r19 := heapE 3,
      r20 := heapE 4,
      r21 := heapE 5,
      r26 := heapE 6,
      r30 := heapE 7 }, [], []⟩,
    .c (pcOf 68), .fuel, 20, 20⟩
def gRejectJumpWords : List (BitVec 32) := [0x00c0006f]
def gRejectJump : Result := ⟨SymState.init, .c (pcOf 24), .jump, 1, 1⟩
def gReject : Result :=
  ⟨⟨(RegFile.init.set .x5 (.c 1)).set .x10 (.c 1), [], []⟩, .c (pcOf 26), .ecall, 2, 2⟩
theorem gJump_checked : rOK (symRun {} gJumpWords (pcOf 23) 1) gJump = true := by decide +kernel
theorem gJump_linked : sliceChecked 23 gJumpWords = true := by decide +kernel
theorem gCheck_checked : rOK (symRun {} gCheckWords (pcOf 17) 4) gCheck = true := by decide +kernel
theorem gCheck_linked : sliceChecked 17 gCheckWords = true := by decide +kernel
theorem gSetup_checked : rOK (symRun {} gSetupWords (pcOf 48) 20) gSetup = true := by decide +kernel
theorem gSetup_linked : sliceChecked 48 gSetupWords = true := by decide +kernel
theorem gRejectJump_checked : rOK (symRun {} gRejectJumpWords (pcOf 21) 1) gRejectJump = true := by decide +kernel
theorem gRejectJump_linked : sliceChecked 21 gRejectJumpWords = true := by decide +kernel
theorem gReject_checked : rOK (symRun {} gRejectWords (pcOf 24) 3) gReject = true := by decide +kernel
theorem gReject_linked : sliceChecked 24 gRejectWords = true := by decide +kernel
end W9Drv
end

section


namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Merkle
open W9Machine
theorem block_steps {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hpc : s.pc = pcOf p) :
    Steps Frozen.image s r.steps r.cycles (r.toState s) :=
  symRun_sound (rOK_eq hc) (slice_at p words hl) s hpc (by simp [Result.obligs, hob, Oblig.all])
theorem block_ecall {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hstop : r.stop = .ecall) :
    fetch Frozen.image (r.toState s) = some (.base .ECALL) :=
  symRun_ecall (rOK_eq hc) (slice_at p words hl) s (by simp [Result.obligs, hob, Oblig.all]) hstop
theorem toState_mem_nil (r : Result) (s : MachineState) (h : r.st.mem = []) :
    (r.toState s).mem = s.mem := by
  show memEval s r.st.mem = s.mem
  rw [h]; rfl
theorem init_getReg (s : MachineState) (x : Reg) : (RegFile.init.get x).eval s = s.getReg x := by
  cases x <;> rfl
theorem glob_congr {w : WBytes} {pk : Digest} {s t : MachineState} (h : Glob baseK w pk s)
    (hm : t.mem = s.mem) (h5 : t.getReg .x5 = 0) (h18 : t.getReg .x18 = 0xFFF) :
    Glob baseK w pk t := by
  obtain ⟨-, h0, h2, h3, h4, h5'⟩ := h
  have e : ∀ A, t.getMem A = s.getMem A := fun A => congrFun hm A
  refine ⟨?_, fun j hj => (e _).trans (h0 j hj), ⟨(e _).trans h2.1, (e _).trans h2.2⟩,
    fun a ha => (e _).trans (h3 a ha), ?_, h5'.congr (fun A _ _ => e _)⟩
  · intro p hp
    simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h5
    · exact h18
  · show (t.getMem _).toNat / 2 ^ 32 = 0
    rw [e]; exact h4
theorem gate_val (x : Word) :
    ((x >>> 31) &&& BitVec.ofNat 64 4095).toNat = x.toNat / 2 ^ 31 % 4096 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  rw [show (4095 : Nat) % 2 ^ 64 = 2 ^ 12 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
theorem idx_val (x : Word) :
    (x <<< 33) >>> 33 = BitVec.ofNat 64 (x.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have := x.isLt
  omega
theorem heap_val (i h : Nat) (hi : i < 2 ^ 31) :
    BitVec.ofNat 64 (2 ^ 32 * h) ||| BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 2 ^ 32 * h) := by
  rw [ofNat_or_disjoint i (2 ^ 32 * h) 32 (by omega) (by simp), Nat.add_comm]
theorem idxE_eval (s : MachineState) (hlo : (s.getReg .x22).toNat % 2 ^ 32 < 2 ^ 31) :
    idxE.eval s = BitVec.ofNat 64 ((s.getReg .x22).toNat % 2 ^ 31) := by
  change (wordResult .add ((s.getReg .x22).truncate 32) ((0 : Word).truncate 32)).signExtend 64 = _
  have h32 : ((s.getReg .x22).truncate 32).toNat < 2 ^ 31 := by
    simpa only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] using hlo
  have hmsb : ((s.getReg .x22).truncate 32).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [show 32 - 1 = 31 by rfl, decide_eq_false_iff_not]
    omega
  change ((s.getReg .x22).truncate 32 + (0#32)).signExtend 64 = _
  rw [BitVec.add_zero, BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat]
  omega
theorem heapE_eval (s : MachineState) (h : Nat) :
    (heapE h).eval s = idxE.eval s + BitVec.ofNat 64 (2 ^ 32 * h) := by
  exact addC_eval s idxE (BitVec.ofNat 64 (2 ^ 32 * h))
theorem gateE_eval (s : MachineState) (h18 : s.getReg .x18 = 0xFFF) :
    gateE.eval s = (s.getMem (BitVec.ofNat 64 96) >>> 31) &&& BitVec.ofNat 64 4095 := by
  change (s.getMem (BitVec.ofNat 64 96) >>> 31) &&& s.getReg .x18 = _
  rw [h18]
  rfl
theorem word0_toNat (a : HashOutput) : (a.extractLsb' 0 64).toNat = a.toNat % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
theorem gate_iff (a : HashOutput) :
    ((a.extractLsb' 0 64 >>> 31) &&& BitVec.ofNat 64 4095 = 0) ↔
      ClaudeWCT.W9.T3M.gateOk a = true := by
  simp only [ClaudeWCT.W9.T3M.gateOk, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [gate_val, word0_toNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [gate_val, word0_toNat, show (0 : BitVec 64).toNat = 0 from rfl]
    omega
theorem index_eq (a : HashOutput) : (a.extractLsb' 0 64).toNat % 2 ^ 31 = idxOf a := by
  rw [word0_toNat]; unfold idxOf; omega
theorem gate_good (pk : Digest) (w : WBytes) (a : HashOutput)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Bool → OracleComp HashSpec Obs)
    (hu : GatePre pk w a u) (hnone : K false = pure (false, 0))
    (hnext : ∀ t, CoordPre pk w a 0 [] t →
      GoodQFor Frozen.image t N C Q A (K true)) :
    GoodQFor Frozen.image u (N + 24) (C + 24) Q (A + 24) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  -- The hook enters the gate check directly; no jump or state mutation is needed.
  let s1 := u
  have m1 : s1.mem = u.mem := rfl
  have r1 : ∀ x, s1.getReg x = u.getReg x := fun _ => rfl
  have pc1 : s1.pc = pcOf 17 := hu.pc
  have st2 := block_steps gCheck_checked gCheck_linked rfl s1 pc1
  set s2 := gCheck.toState s1 with hs2
  have m2 : s2.mem = u.mem := (toState_mem_nil _ _ rfl).trans m1
  have hw0 : s1.getMem (BitVec.ofNat 64 96) = a.extractLsb' 0 64 := by
    have := hu.digest 0 (by decide)
    simpa [MachineState.getMem, m1] using this
  have pc2 : s2.pc = if gateE.eval s1 == 0 then pcOf 48 else pcOf 21 := by
    show (E.ite .eq gateE (.c 0) (.c (pcOf 48)) (.c (pcOf 21))).eval s1 = _
    rfl
  have hg : gateE.eval s1 = (a.extractLsb' 0 64 >>> 31) &&& BitVec.ofNat 64 4095 := by
    rw [gateE_eval s1 (hu.glob.1 (.x18, 0xFFF) (by simp [baseK])), hw0]
  have st2' : Steps Frozen.image s1 4 4 s2 := st2
  by_cases hok : ClaudeWCT.W9.T3M.gateOk a = true
  ·
    rw [hok]
    have hz : gateE.eval s1 = 0 := hg.trans ((gate_iff a).mpr hok)
    have pc2' : s2.pc = pcOf 48 := by rw [pc2, hz]; rfl
    have st3 := block_steps gSetup_checked gSetup_linked rfl s2 pc2'
    set s3 := gSetup.toState s2 with hs3
    have st3' : Steps Frozen.image s2 20 20 s3 := st3
    have m3 : s3.mem = u.mem := (toState_mem_nil _ _ rfl).trans m2
    have e3 : ∀ A, s3.getMem A = u.getMem A := fun A => congrFun m3 A
    have r22 : s2.getReg .x22 = a.extractLsb' 0 64 := by
      rw [hs2, Result.toState_getReg]; exact hw0
    have hlow32 : (s2.getReg .x22).toNat % 2 ^ 32 < 2 ^ 31 := by
      have hmask := congrArg BitVec.toNat hz
      rw [hg, gate_val] at hmask
      change (a.extractLsb' 0 64).toNat / 2 ^ 31 % 4096 = 0 at hmask
      rw [r22]
      omega
    have hidx : idxE.eval s2 = BitVec.ofNat 64 (idxOf a) := by
      rw [idxE_eval s2 hlow32, r22, index_eq]
    have hia : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have heapv : ∀ h, (heapE h).eval s2 = BitVec.ofNat 64 (idxOf a + 2 ^ 32 * h) := fun h => by
      rw [heapE_eval, hidx, ofNat_add_ofNat]
    have h5 : s3.getReg .x5 = 0 := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x5 = 0
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x5 = 0
      rw [r1]; exact hu.glob.1 (.x5, 0) (by simp [baseK])
    have h18 : s3.getReg .x18 = 0xFFF := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x18 = 0xFFF
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x18 = 0xFFF
      exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
    have h8 : s3.getReg .x8 = BitVec.ofNat 64 2112 := by
      rw [hs3, Result.toState_getReg]
      change (addC (.reg .x18) (-1983)).eval s2 = _
      rw [addC_eval]
      change s2.getReg .x18 + (-1983 : Word) = _
      have h18s2 : s2.getReg .x18 = 0xFFF := by
        rw [hs2, Result.toState_getReg]
        exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
      rw [h18s2]
      decide +kernel
    have hpre : CoordPre pk w a 0 [] s3 := by
      refine ⟨by decide, rfl, rfl, glob_congr hu.glob m3 h5 h18, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
        rfl, h8, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_, ?_⟩
      · intro k hk; rw [e3]; exact hu.digest k hk
      · obtain ⟨hc, hn, hl⟩ := hu.bank
        exact ⟨fun k t ht d hd => (e3 _).trans (hc k t ht d hd), fun k => (e3 _).trans (hn k),
          fun k => (e3 _).trans (hl k)⟩
      · rw [hs3, Result.toState_getReg]; exact hidx
      · intro hn; omega
      · intro h h1 h7
        rw [hs3, Result.toState_getReg]
        interval_cases h
        · exact heapv 1
        · exact heapv 2
        · exact heapv 3
        · exact heapv 4
        · exact heapv 5
        · exact heapv 6
        · exact heapv 7
      · intro k _ off hoff h8
        unfold OrigW
        rw [e3]
        have hw := hu.wit ((64 + 1024 * k.val + off) / 8) (by unfold WX; have := k.isLt; omega)
        rw [show WIT + 8 * ((64 + 1024 * k.val + off) / 8) = Chain.base k + off by
          unfold WIT Chain.base; omega] at hw
        have e : 8 * (Chain.base k + off - 0x800) = 64 * ((64 + 1024 * k.val + off) / 8) := by
          unfold Chain.base; omega
        rw [hw, wword, e]
      · exact (hu.wit.orig _).frame (fun j _ _ => e3 _)
      · intro A hA; rw [e3]; exact hu.forestZero A hA
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x11 = 64
        rw [hs2, Result.toState_getReg]
        exact hu.hashLen
    have := (((hnext s3 hpre).steps st3').steps st2')
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  ·
    have hok' : ClaudeWCT.W9.T3M.gateOk a = false := by simpa using hok
    rw [hok', hnone]
    have hnz : gateE.eval s1 ≠ 0 := fun h => hok ((gate_iff a).mp (hg.symm.trans h))
    have pc2' : s2.pc = pcOf 21 := by
      rw [pc2, if_neg (by simpa only [beq_iff_eq] using hnz)]
    have stJ := block_steps gRejectJump_checked gRejectJump_linked rfl s2 pc2'
    set sj := gRejectJump.toState s2
    have pcJ : sj.pc = pcOf 24 := rfl
    have st3 := block_steps gReject_checked gReject_linked rfl sj pcJ
    have st3' : Steps Frozen.image sj 2 2 (gReject.toState sj) := st3
    have hf := block_ecall gReject_checked gReject_linked rfl sj rfl
    have hr : GoodQFor Frozen.image (gReject.toState sj) 1 1 Q A (pure (false, 0)) :=
      GoodQFor.reject hf (by rw [Result.toState_getReg]; rfl) (by rw [Result.toState_getReg]; rfl)
    have := ((hr.steps st3').steps stJ).steps st2'
    dsimp only [gRejectJump] at this
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end
