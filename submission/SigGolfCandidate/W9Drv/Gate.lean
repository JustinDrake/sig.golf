import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Drv.GateDefs

section

namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gJumpWords : List (BitVec 32) := [35134227,35347219,104857711]
def gCheckWords : List (BitVec 32) :=
  [33051027,19001779,104547]
def gSetupWords : List (BitVec 32) :=
  [1049363,2098067,33755539,23168179,3442355,3574195,3770931,3803827,3837235,4001587,5175,0x84040413,0xfefe37,0xe00e0e13,65847,0xffc10113,851639,0x800e8e93,883767,0x800c0c13]
def gRejectWords : List (BitVec 32) := [1049235,1049875,115]
def gateE : E := .bin .and (.bin .srl (.ld (.c (BitVec.ofNat 64 96))) (.c (BitVec.ofNat 64 31)))
  (.c (BitVec.ofNat 64 4095))
def idxE : E := .bin .srl (.bin .sll (.reg .x22) (.c (BitVec.ofNat 64 33))) (.c (BitVec.ofNat 64 33))
def heapE (h : Nat) : E := .bin .or (.c (BitVec.ofNat 64 (2 ^ 32 * h))) idxE
def cachedGateE : E := .bin .and (.bin .srl (.reg .x16) (.c 31)) (.reg .x18)
def cachedIdxE : E := .bin .srl (.bin .sll (.reg .x16) (.c 33)) (.c 33)
def additiveHeapE (h : Nat) : E := .bin .add (.reg .x22) (.c (BitVec.ofNat 64 (2 ^ 32 * h)))
def gJump : Result :=
  ⟨⟨RegFile.init.set .x22 cachedIdxE, [], []⟩, .c (pcOf 48), .jump, 3, 3⟩
def gCheck : Result :=
  ⟨⟨RegFile.init.set .x3 cachedGateE, [], []⟩,
    .ite .ne cachedGateE (.c 0) (.c (pcOf 24)) (.c (pcOf 21)), .branch, 3, 3⟩
def gSetup : Result :=
  ⟨⟨((((((((((((((RegFile.init.set .x2 (.c (BitVec.ofNat 64 0xfffc))).set .x3 (.c (BitVec.ofNat 64 (2 ^ 32)))).set .x6 (.c 1)).set .x7 (.c 2)).set
      .x8 (.c (BitVec.ofNat 64 2112))).set .x9 (additiveHeapE 1)).set .x13 (additiveHeapE 2)).set .x19 (additiveHeapE 3)).set
      .x20 (additiveHeapE 4)).set .x21 (additiveHeapE 5)).set .x24 (.c (BitVec.ofNat 64 0xd6800))).set
      .x26 (additiveHeapE 6)).set .x28 (.c (BitVec.ofNat 64 (0xfee600 + 2048)))).set .x29
      (.c (BitVec.ofNat 64 0xce800))).set .x30 (additiveHeapE 7), [], []⟩,
    .c (pcOf 68), .fuel, 20, 20⟩
def gReject : Result :=
  ⟨⟨(RegFile.init.set .x5 (.c 1)).set .x10 (.c 1), [], []⟩, .c (pcOf 26), .ecall, 2, 2⟩
theorem gJump_checked : rOK (symRun {} gJumpWords (pcOf 21) 3) gJump = true := by decide +kernel
theorem gJump_linked : sliceChecked 21 gJumpWords = true := by decide +kernel
theorem gCheck_checked : rOK (symRun {} gCheckWords (pcOf 18) 3) gCheck = true := by decide +kernel
theorem gCheck_linked : sliceChecked 18 gCheckWords = true := by decide +kernel
theorem gSetup_checked : rOK (symRun {} gSetupWords (pcOf 48) 20) gSetup = true := by decide +kernel
theorem gSetup_linked : sliceChecked 48 gSetupWords = true := by decide +kernel
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
theorem idxE_eval (s : MachineState) :
    idxE.eval s = BitVec.ofNat 64 ((s.getReg .x22).toNat % 2 ^ 31) := by
  rw [← idx_val]; rfl
theorem heapE_eval (s : MachineState) (h : Nat) :
    (heapE h).eval s = BitVec.ofNat 64 (2 ^ 32 * h) ||| idxE.eval s := rfl
theorem gateE_eval (s : MachineState) :
    gateE.eval s = (s.getMem (BitVec.ofNat 64 96) >>> 31) &&& BitVec.ofNat 64 4095 := rfl
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
    GoodQFor Frozen.image u (N + 26) (C + 26) Q (A + 26) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  have st1 := block_steps gCheck_checked gCheck_linked rfl u hu.pc
  set s1 := gCheck.toState u with hs1
  have m1 : s1.mem = u.mem := toState_mem_nil _ _ rfl
  have r1 : ∀ x, x ≠ .x3 → s1.getReg x = u.getReg x := fun x hx => by
    rw [hs1, Result.toState_getReg]
    cases x <;> first | rfl | exact absurd rfl hx
  have pc1 : s1.pc = if cachedGateE.eval u != 0 then pcOf 24 else pcOf 21 := rfl
  have hg : cachedGateE.eval u = (a.extractLsb' 0 64 >>> 31) &&& BitVec.ofNat 64 4095 := by
    change (u.getReg .x16 >>> 31) &&& u.getReg .x18 = _
    rw [hu.cached, hu.glob.1 (.x18, 0xFFF) (by simp [baseK])]
    rfl
  have st1' : Steps Frozen.image u 3 3 s1 := st1
  by_cases hok : ClaudeWCT.W9.T3M.gateOk a = true
  ·
    rw [hok]
    have hz : cachedGateE.eval u = 0 := hg.trans ((gate_iff a).mpr hok)
    have pc1' : s1.pc = pcOf 21 := by rw [pc1, hz]; rfl
    have st2 := block_steps gJump_checked gJump_linked rfl s1 pc1'
    set s2 := gJump.toState s1 with hs2
    have st2' : Steps Frozen.image s1 3 3 s2 := st2
    have m2 : s2.mem = u.mem := (toState_mem_nil _ _ rfl).trans m1
    have st3 := block_steps gSetup_checked gSetup_linked rfl s2 (show s2.pc = pcOf 48 from rfl)
    set s3 := gSetup.toState s2 with hs3
    have st3' : Steps Frozen.image s2 20 20 s3 := st3
    have m3 : s3.mem = u.mem := (toState_mem_nil _ _ rfl).trans m2
    have e3 : ∀ A, s3.getMem A = u.getMem A := fun A => congrFun m3 A
    have hidx : s2.getReg .x22 = BitVec.ofNat 64 (idxOf a) := by
      rw [hs2, Result.toState_getReg]
      change (s1.getReg .x16 <<< 33) >>> 33 = _
      rw [r1 .x16 (by decide), hu.cached, idx_val, index_eq]
    have heapv : ∀ h, (additiveHeapE h).eval s2 = BitVec.ofNat 64 (idxOf a + 2 ^ 32 * h) := fun h => by
      change s2.getReg .x22 + BitVec.ofNat 64 (2 ^ 32 * h) = _
      rw [hidx, BitVec.ofNat_add]
    have h5 : s3.getReg .x5 = 0 := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x5 = 0
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x5 = 0
      rw [r1 .x5 (by decide)]; exact hu.glob.1 (.x5, 0) (by simp [baseK])
    have h18 : s3.getReg .x18 = 0xFFF := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x18 = 0xFFF
      rw [hs2, Result.toState_getReg]
      exact (r1 .x18 (by decide)).trans (hu.glob.1 (.x18, 0xFFF) (by simp [baseK]))
    have hpre : CoordPre pk w a 0 [] s3 := by
      refine ⟨by decide, rfl, rfl, glob_congr hu.glob m3 h5 h18, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_⟩
      · intro k hk; rw [e3]; exact hu.digest k hk
      · obtain ⟨hc, hn, hl⟩ := hu.bank
        exact ⟨fun k t ht d hd => (e3 _).trans (hc k t ht d hd), fun k => (e3 _).trans (hn k),
          fun k => (e3 _).trans (hl k)⟩
      · rw [hs3, Result.toState_getReg]; exact hidx
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
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x16 = a.extractLsb' 0 64
        rw [hs2, Result.toState_getReg]
        exact (r1 .x16 (by decide)).trans hu.cached
    have := ((((hnext s3 hpre).steps st3').steps st2').steps st1')
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  ·
    have hok' : ClaudeWCT.W9.T3M.gateOk a = false := by simpa using hok
    rw [hok', hnone]
    have hnz : cachedGateE.eval u ≠ 0 := fun h => hok ((gate_iff a).mp (hg.symm.trans h))
    have pc1' : s1.pc = pcOf 24 := by
      rw [pc1, if_pos (bne_iff_ne.mpr hnz)]
    have st3 := block_steps gReject_checked gReject_linked rfl s1 pc1'
    have st3' : Steps Frozen.image s1 2 2 (gReject.toState s1) := st3
    have hf := block_ecall gReject_checked gReject_linked rfl s1 rfl
    have hr : GoodQFor Frozen.image (gReject.toState s1) 1 1 Q A (pure (false, 0)) :=
      GoodQFor.reject hf (by rw [Result.toState_getReg]; rfl) (by rw [Result.toState_getReg]; rfl)
    have := (hr.steps st3').steps st1'
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end
