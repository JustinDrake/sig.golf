import SigGolfCandidate.T3M.Verify.CanonicalBanks
import SigGolfCandidate.T3M.Verify.FtsEnd
import SigGolfCandidate.T3M.CanonicalPort.Combined

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def forestK : List (Reg × Word) := carryK ++ [(.x29,BitVec.ofNat 64 A4_LIMIT)]
def restoreKeep : List Reg := allKeep.filter fun r => r≠.x7 ∧ r≠.x18 ∧ r≠.x14
def restoreSpec : Spec :=
  ⟨[(.x7,SigGolfCandidate.T3M.Verify.cw 2),(.x18,SigGolfCandidate.T3M.Verify.cw 4095),(.x14,.bin .add (.reg .x14) (.c (-880#64)))],
    [],648,false,5,[],none,5⟩
def restoreCheck : Bool :=
  rawB (runAtC {} [] [648] (banks[6]!+13) []) restoreSpec [] restoreKeep
theorem restore_checked : restoreCheck=true := by decide +kernel

structure ForestCIn (F : FCtx) (roots : List Digest) (ptr : Nat) (s : MachineState) : Prop where
  glob : Glob forestK F.w F.pk s
  idx : s.getReg .x22=BitVec.ofNat 64 F.idx
  pc : s.pc=pcOf forestPc
  a4 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr-880)
  rts : RootsOK roots s
  hroots : roots.length=7
  wit : WitF F.w ptr s
  maxptr : ptr ≤ 32168

theorem restore_forest (F : FCtx) (ptr : Nat) (roots : List Digest) (s : MachineState)
    (hp : ptr ≤ 32168) (hs : BanksEnd F ptr roots s) :
    ∃ t, Steps fixture s 5 5 t ∧ ForestCIn F roots ptr t := by
  obtain ⟨t,hr⟩ := raw_run restore_checked s hs.pc (by simp [KnownOK])
    (by simp [restoreSpec]) (by simp)
  have hm : ∀ A, t.getMem A=s.getMem A := by intro A; rw [hr.mem]; rfl
  have hpres : ∀ r v, (r,v)∈bankK F 6 → r∈restoreKeep → t.getReg r=v := by
    intro r v h1 h2; exact (hr.keep r h2).trans (hs.known (r,v) h1)
  have hk : KnownOK forestK t := by
    intro p h
    simp only [forestK,carryK,baseK,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with ((h | h) | h) | h
    · subst p; exact hpres .x5 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
    · subst p; exact hr.regs (.x18,SigGolfCandidate.T3M.Verify.cw 4095) (by simp [restoreSpec])
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hpres .x2 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
      · exact hr.regs (.x7,SigGolfCandidate.T3M.Verify.cw 2) (by simp [restoreSpec])
      · exact hpres .x8 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
      · exact hpres .x9 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
      · exact hpres .x13 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
    · subst p; exact hpres .x29 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
  have hg := hs.common.control hr rfl
  refine ⟨t,hr.steps,⟨⟨hk,hg.glob.2⟩,?_,hr.pc rfl,?_,?_,hs.len,?_,hp⟩⟩
  · exact hpres .x22 _ (by simp [bankK]) (by simp [restoreKeep,allKeep])
  · rw [hr.regs (.x14,.bin .add (.reg .x14) (.c (-880#64))) (by simp [restoreSpec])]
    change s.getReg .x14+(-880#64)=_
    rw [hs.pointer,show (-880#64)=BitVec.ofNat 64 0-BitVec.ofNat 64 880 by decide]
    simpa only [Nat.add_zero] using CanonicalPort.ofNat_add_off0 (WIT+ptr) 0 880
      (by unfold WIT; omega) (by unfold WIT; omega)
  · intro k hk'; exact ⟨(hm _).trans (hs.rootsOk k hk').1,(hm _).trans (hs.rootsOk k hk').2⟩
  · intro o ho; rw [hm]; exact hs.orig o ho

def forestCheckC : Bool :=
  specB [] [] carryK (runAtC {} forestK [] forestPc [.br false]) forestSpecF [] carryK [.x22] &&
  specB [] [] [] (runAtC {} forestK [] forestPc [.br true]) (rejSpec 4 [capBr true]) [] [] []
theorem forest_checked_c : forestCheckC=true := by decide +kernel

def HaltC1 (s : MachineState) : Prop :=
  fetch fixture s=some (.base .ECALL) ∧ s.getReg .x5=1 ∧ s.getReg .x10=1
structure ForestCOut (F : FCtx) (root : Digest) (s : MachineState) : Prop where
  glob : Glob carryK F.w F.pk s
  idx : s.getReg .x22=BitVec.ofNat 64 F.idx
  pc : s.pc=pcOf layerPc
  root : DigAt s 0x100 root
  wit : Orig F.w (fun o => o<64 ∨ 11288≤o) s

theorem cap_br_ptr (s : MachineState) (ptr : Nat)
    (hr : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr-880)) (hp : ptr≤32168) (d : Bool) :
    Br.holds s (capBr d) ↔ d=decide (10568<ptr) := by
  simp only [Br.holds,capBr,CmpOp.eval,Rv.E.eval,hr]
  have he : (BitVec.ofNat 64 A4_LIMIT).ult (BitVec.ofNat 64 (WIT+ptr-880))=
      decide (10568<ptr) := by
    simp only [BitVec.ult,toNat_ofNat_lt (show A4_LIMIT<2^64 by unfold A4_LIMIT; omega),
      toNat_ofNat_lt (show WIT+ptr-880<2^64 by unfold WIT; omega),decide_eq_decide]
    unfold A4_LIMIT WIT; omega
  rw [he]; exact eq_comm

theorem forest_step_c (F : FCtx) (roots : List Digest) (ptr : Nat) (m : MachineState)
    (h : ForestCIn F roots ptr m) :
    (10568 < ptr → ∃ u, Steps fixture m 4 4 u ∧ HaltC1 u) ∧
    (ptr ≤ 10568 → ∃ u, Steps fixture m 7 7 u ∧ fetch fixture u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
      hashArgumentsValid u = true ∧ hashInput u = toQ (T3.pad64 (forestInput F.idx roots)) ∧
      ∀ ans : BitVec 256, ForestCOut F (ans.extractLsb' 0 128) (Legacy.Riscv.writeHash u ans)) := by
  have hk : KnownOK forestK m := h.glob.1
  have tF := forest_checked_c
  unfold forestCheckC at tF
  simp only [Bool.and_eq_true] at tF
  obtain ⟨tPass, tRej⟩ := tF
  have hcap := cap_br_ptr m ptr h.a4 h.maxptr
  have hi32 : F.idx < 2 ^ 32 := lt_trans F.idx_lt (by norm_num)
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · obtain ⟨u, hu⟩ := spec_runC tRej m h.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (hcap true).mpr (by simp [hgt])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec]), hu.regs (.x10, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec])⟩
  · obtain ⟨u, hu⟩ := spec_runC tPass m h.pc hk (by
      intro b hb; simp only [forestSpecF, List.mem_singleton] at hb; subst hb
      exact (hcap false).mpr (by simp; omega)) (by simp)
    have hmem : ∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
        if B = FOREST + 24 then BitVec.ofNat 64 F.idx
        else if B = FOREST + 16 then BitVec.ofNat 64 0xb01 else m.getMem (BitVec.ofNat 64 B) := by
      intro B hB
      rw [hu.mem]; simp only [forestSpecF]
      rw [memEval_cons_ofNat _ _ _ _ _ hB (by unfold FOREST; omega),
        memEval_cons_ofNat _ _ _ _ _ hB (by unfold FOREST; omega), memEval_nil]
      simp only [Rv.E.eval, h.idx, SigGolfCandidate.T3M.Verify.cw]
    have hfr : ∀ B, B < 2 ^ 64 → B ≠ FOREST + 16 → B ≠ FOREST + 24 →
        u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) :=
      fun B hB h1 h2 => by rw [hmem B hB, if_neg h2, if_neg h1]
    have h10 : u.getReg .x10 = BitVec.ofNat 64 FOREST := hu.regs (.x10, SigGolfCandidate.T3M.Verify.cw FOREST) (by simp [forestSpecF])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 128 := hu.regs (.x11, SigGolfCandidate.T3M.Verify.cw 128) (by simp [forestSpecF])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 0x100 := hu.regs (.x12, SigGolfCandidate.T3M.Verify.cw 0x100) (by simp [forestSpecF])
    have hr := h.hroots
    have hrts : RootsOK roots u :=
      h.rts.frame (fun k hk => ⟨hfr _ (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot FOREST; split <;> omega) (by unfold forestSlot FOREST; split <;> omega),
        hfr _ (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot FOREST; split <;> omega) (by unfold forestSlot FOREST; split <;> omega)⟩)
    have hlen := forestInput_length F.idx roots h.hroots
    have hin : hashInput u = toQ (T3.pad64 (forestInput F.idx roots)) := by
      rw [pad64_forestInput F.idx roots h.hroots]
      refine hashInput_toQ u _ 1 FOREST (by rw [hlen]) h10 (by unfold FOREST; omega) (by unfold FOREST; omega)
        (by rw [h11]) (by norm_num) ?_
      refine forest_words u F.idx roots h.hroots hrts ?_ ?_
      · rw [hmem _ (by norm_num), if_neg (by unfold FOREST; omega), if_pos (by unfold FOREST; omega),
          hdr0_forest F.idx hi32]
      · rw [hmem _ (by norm_num), if_pos (by unfold FOREST; omega), hdr1_forest F.idx hi32]
    refine ⟨u, hu.steps, hu.ecall rfl, hu.known (.x5, 0) (by simp [carryK, baseK]),
      hashArgs_of u _ 128 _ h10 h11 h12 (by unfold FOREST; omega) (by decide) (by unfold FOREST; norm_num)
        (by decide) (by norm_num), hin, fun ans => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact Glob_writeHash (hu.glob _ _ _ h.glob (RelOK.nil m)) ans 0x100 h12 (by decide)
    · rw [writeHash_getReg, hu.keep .x22 (by simp)]; exact h.idx
    · rw [writeHash_pc, hu.pc rfl]; exact pcOf_add4 655
    · exact writeHash_lo u ans 0x100 h12 (by norm_num)
    · have hw : Orig F.w (fun o => o < 64 ∨ leafNT o ∨ ptr ≤ o) u :=
        h.wit.frame (fun jj h1 h2 => hfr _ (by unfold WIT WX at *; omega) (by unfold WIT FOREST; omega)
          (by unfold WIT FOREST; omega))
      have hw2 := Orig_writeHash hw ans 0x100 h12 (by norm_num)
      have hp := hle
      exact hw2.mono (fun o ho => ⟨by rcases ho with ho | ho; exact Or.inl ho; exact Or.inr (Or.inr (by omega)),
        Or.inr (by unfold WIT; omega)⟩)


theorem forest_out_port {F root s} (h : ForestCOut F root s) :
    CanonicalPort.Verify.Glob CanonicalPort.Verify.carryK F.w F.pk s := by
  obtain ⟨hk,hw,hpk,hz,hh,hd⟩ := h.glob
  exact ⟨hk,hw,hpk,hz,hh,⟨hd.constants,hd.sum,⟨hd.packed.pair,hd.packed.tail⟩,hd.headers,hd.tab⟩⟩

#print axioms restore_forest
#print axioms forest_step_c
#print axioms forest_out_port
end SigGolfCandidate.T3M.CanonicalNative
