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
  [0x6003b03,0x7803183,8491411,52547987,5353875,0xfe0180e3]
def gSetupWords : List (BitVec 32) :=
  [35330835,35347219,29038483,34281619,1049491,2098835,3148179,4196883,5245587,6294803,7343891,67110291,66359,11771411,12452915,3018291,4290969875,851639,2148437651,883767,2148273171,12583023]
def gRejectWords : List (BitVec 32) := [1049235,1049875,115]
def gateE : E := .bin .sltu
  (.bin .srl (.bin .sll (.ld (.c (BitVec.ofNat 64 120))) (.c (BitVec.ofNat 64 8)))
    (.c (BitVec.ofNat 64 50))) (.c (BitVec.ofNat 64 5))
def idxE : E := .bin .srl (.bin .sll (.reg .x22) (.c (BitVec.ofNat 64 33))) (.c (BitVec.ofNat 64 33))
def heapE (h : Nat) : E := .bin .or (.c (BitVec.ofNat 64 (2 ^ 32 * h))) idxE
def gJump : Result := ⟨SymState.init, .c (pcOf 27), .jump, 1, 1⟩
def gCheck : Result :=
  ⟨⟨(RegFile.init.set .x3 gateE).set .x22 (.ld (.c (BitVec.ofNat 64 96))), [], []⟩,
    .ite .eq gateE (.c 0) (.c (pcOf 24)) (.c (pcOf 33)), .branch, 6, 6⟩
def gSetup : Result :=
  ⟨⟨(((((((((((((((((RegFile.init).set .x2 (.c (BitVec.ofNat 64 0xfffc))).set .x6 (.c 65536)).set .x7 (.c 1)).set .x8 (.c (BitVec.ofNat 64 2112))).set .x11 (.c 64)).set .x13 (.c 2)).set .x15 (.bin .sll idxE (.c 27))).set .x17 (.bin .sll idxE (.c 32))).set .x19 (.c 3)).set .x20 (.c 4)).set .x21 (.c 5)).set .x22 (idxE)).set .x24 (.c (BitVec.ofNat 64 0xd6800))).set .x26 (.c 6)).set .x28 (.c (BitVec.ofNat 64 (0xfee600 + 2048)))).set .x29 (.c (BitVec.ofNat 64 0xce800))).set .x30 (.c 7), [], []⟩, .c (pcOf 57), .jump, 22, 22⟩
def gReject : Result :=
  ⟨⟨(RegFile.init.set .x5 (.c 1)).set .x10 (.c 1), [], []⟩, .c (pcOf 26), .ecall, 2, 2⟩
theorem gJump_checked : rOK (symRun {} gJumpWords (pcOf 23) 1) gJump = true := by decide +kernel
theorem gJump_linked : sliceChecked 23 gJumpWords = true := by decide +kernel
theorem gCheck_checked : rOK (symRun {} gCheckWords (pcOf 27) 6) gCheck = true := by decide +kernel
theorem gCheck_linked : sliceChecked 27 gCheckWords = true := by decide +kernel
theorem gSetup_checked : rOK (symRun {} gSetupWords (pcOf 33) 22) gSetup = true := by decide +kernel
theorem gSetup_linked : sliceChecked 33 gSetupWords = true := by decide +kernel
theorem gReject_checked : rOK (symRun {} gRejectWords (pcOf 24) 3) gReject = true := by decide +kernel
theorem gReject_linked : sliceChecked 24 gRejectWords = true := by decide +kernel
end W9Drv
end

section


namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
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
theorem gate_val (x : BitVec 64) :
    ((x <<< 8) >>> 50).toNat = x.toNat / 2 ^ 42 % 2 ^ 14 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  omega
theorem digest_gate_val (a : BitVec 256) :
    ((a.extractLsb' 192 64 <<< 8) >>> 50).toNat = a.toNat / 2 ^ 234 % 2 ^ 14 := by
  rw [gate_val, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega
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
theorem gateE_eval (s : MachineState) (a : BitVec 256)
    (hw : s.getMem (BitVec.ofNat 64 120) = a.extractLsb' 192 64) :
    gateE.eval s = if decide (a.toNat / 2 ^ 234 % 2 ^ 14 < 5) then 1 else 0 := by
  change (if BitVec.ult ((s.getMem (BitVec.ofNat 64 120) <<< 8) >>> 50)
    (BitVec.ofNat 64 5) then (1 : BitVec 64) else 0) = _
  rw [hw]
  simp only [BitVec.ult, digest_gate_val, BitVec.toNat_ofNat]
theorem word0_toNat (a : HashOutput) : (a.extractLsb' 0 64).toNat = a.toNat % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
theorem index_eq (a : HashOutput) : (a.extractLsb' 0 64).toNat % 2 ^ 31 = idxOf a := by
  rw [word0_toNat]; unfold idxOf; omega
theorem gate_good (pk : Digest) (w : WBytes) (a : HashOutput)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Bool → OracleComp HashSpec Obs)
    (hu : GatePre pk w a u) (hnone : K false = pure (false, 0))
    (hnext : ∀ t, CoordPre pk w a 0 [] t →
      GoodQFor Frozen.image t N C Q A (K true)) :
    GoodQFor Frozen.image u (N + 28) (C + 28) Q (A + 28) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  let s1 := u
  have m1 : s1.mem = u.mem := rfl
  have r1 : ∀ x, s1.getReg x = u.getReg x := fun _ => rfl
  have pc1 : s1.pc = pcOf 27 := hu.pc
  have st2 := block_steps gCheck_checked gCheck_linked rfl s1 pc1
  set s2 := gCheck.toState s1 with hs2
  have m2 : s2.mem = u.mem := (toState_mem_nil _ _ rfl).trans m1
  have hw0 : s1.getMem (BitVec.ofNat 64 96) = a.extractLsb' 0 64 := by
    have := hu.digest 0 (by decide)
    simpa [MachineState.getMem, m1] using this
  have hw3 : s1.getMem (BitVec.ofNat 64 120) = a.extractLsb' 192 64 := by
    have := hu.digest 3 (by decide)
    simpa [MachineState.getMem, m1] using this
  have pc2 : s2.pc = if gateE.eval s1 == 0 then pcOf 24 else pcOf 33 := by
    show (E.ite .eq gateE (.c 0) (.c (pcOf 24)) (.c (pcOf 33))).eval s1 = _
    rfl
  have hg : gateE.eval s1 = if ClaudeWCT.W9.T3M.gateOk a then 1 else 0 :=
    gateE_eval s1 a hw3
  have st2' : Steps Frozen.image s1 6 6 s2 := st2
  by_cases hok : ClaudeWCT.W9.T3M.gateOk a = true
  ·
    rw [hok]
    have hz : gateE.eval s1 = 1 := by simpa [hok] using hg
    have pc2' : s2.pc = pcOf 33 := by rw [pc2, hz]; rfl
    have st3 := block_steps gSetup_checked gSetup_linked rfl s2 pc2'
    set s3 := gSetup.toState s2 with hs3
    have st3' : Steps Frozen.image s2 22 22 s3 := st3
    have m3 : s3.mem = u.mem := (toState_mem_nil _ _ rfl).trans m2
    have e3 : ∀ A, s3.getMem A = u.getMem A := fun A => congrFun m3 A
    have r22 : s2.getReg .x22 = a.extractLsb' 0 64 := by
      rw [hs2, Result.toState_getReg]; exact hw0
    have hidx : idxE.eval s2 = BitVec.ofNat 64 (idxOf a) := by
      rw [idxE_eval, r22, index_eq]
    have hia : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
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
      rw [r1]; exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
    have hpre : CoordPre pk w a 0 [] s3 := by
      refine {
        le := (by decide), length := rfl, pc := rfl,
        glob := glob_congr hu.glob m3 h5 h18,
        digest := ?_, bank := ?_, index := ?_, heaps := ?_,
        stepOne := rfl, stepTwo := rfl, hashLen := rfl, coordStep := rfl,
        prefixReg := ?_, nodeHeader := fun h => False.elim (h rfl), nodeIndex := ?_, cached := fun h => False.elim (h rfl),
        mask := rfl, jt := rfl, childBlock := rfl, baseReg := rfl, headerReg := rfl,
        pairs := fun i hi => absurd hi (Nat.not_lt_zero _), coords := ?_, layer := ?_ }
      · intro k hk; rw [e3]; exact hu.digest k hk
      · exact ⟨fun k => (e3 _).trans (hu.bank.node k),
          fun k => (e3 _).trans (hu.bank.leaf k)⟩
      · rw [hs3, Result.toState_getReg]; exact hidx
      · intro h h2 h7
        interval_cases h <;> rfl
      · change idxE.eval s2 <<< 27 = _
        rw [hidx]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
        simp
      · change idxE.eval s2 <<< 32 = _
        rw [hidx]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
      · intro k _ off hoff h8
        unfold OrigW
        rw [e3]
        have hw := hu.wit ((64 + 1024 * k.val + off) / 8) (by unfold WX; have := k.isLt; omega)
        rw [show WIT + 8 * ((64 + 1024 * k.val + off) / 8) = coordinateBase k + off by
          unfold WIT coordinateBase; omega] at hw
        have e : 8 * (coordinateBase k + off - 0x800) = 64 * ((64 + 1024 * k.val + off) / 8) := by
          unfold coordinateBase; omega
        rw [hw, wword, e]
      · exact (hu.wit.orig _).frame (fun j _ _ => e3 _)
    have := (((hnext s3 hpre).steps st3').steps st2')
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  ·
    have hok' : ClaudeWCT.W9.T3M.gateOk a = false := by simpa using hok
    rw [hok', hnone]
    have hz : gateE.eval s1 = 0 := by simpa [hok'] using hg
    have pc2' : s2.pc = pcOf 24 := by
      rw [pc2, hz]; rfl
    have st3 := block_steps gReject_checked gReject_linked rfl s2 pc2'
    have st3' : Steps Frozen.image s2 2 2 (gReject.toState s2) := st3
    have hf := block_ecall gReject_checked gReject_linked rfl s2 rfl
    have hr : GoodQFor Frozen.image (gReject.toState s2) 1 1 Q A (pure (false, 0)) :=
      GoodQFor.reject hf (by rw [Result.toState_getReg]; rfl) (by rw [Result.toState_getReg]; rfl)
    have := (hr.steps st3').steps st2'
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
#print axioms gate_good
end W9Drv
end
