import SigGolfCandidate.T3M.Verify.CanonicalDigest
import SigGolfCandidate.T3M.Verify.CanonicalTwinChecks
import SigGolfCandidate.T3M.Verify.CanonicalCompose

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)

theorem dgo_control {m pk w a} {s t : MachineState} (h : DgOutC m pk w a (s.setPC (pcOf 18)))
    (hk : KnownOK twinK t) (hm : ∀ A, t.getMem A=s.getMem A) :
    DgOutC m pk w a (t.setPC (pcOf 18)) := by
  refine ⟨rfl,hk,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj; change t.getMem _=wword w j; rw [hm]; exact h.wit j hj
  · exact ⟨(hm _).trans h.pk.1,(hm _).trans h.pk.2⟩
  · intro j hj; change t.getMem _=_; rw [hm]; exact h.nwords j hj
  · intro A hA hzero; change t.getMem _=0; rw [hm]; exact h.zero A hA hzero
  · exact h.data.congr (fun A _ _ => hm _)
  · exact hk (.x2,BitVec.ofNat 64 TAB) (by simp [twinK])
  · intro k hh; change t.getMem _=_; rw [hm]; exact h.tables k hh
  · change hashInput t=_
    rw [CanonicalPort.mkHashInput_congr
      (show t.getReg .x10=s.getReg .x10 from
        (hk (.x10,32) (by simp [twinK,proPost])).trans (h.known (.x10,32) (by simp [proPostC,proPost])).symm)
      (show t.getReg .x11=s.getReg .x11 from
        (hk (.x11,64) (by simp [twinK,proPost])).trans (h.known (.x11,64) (by simp [proPostC,proPost])).symm) hm]
    exact h.input

structure TwinPre (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput)
    (s : MachineState) : Prop where
  old : DgOutC m pk w a (s.setPC (pcOf 18))
  pc : s.pc=pcOf 221960
  nregs : NRegs a s

structure TwinOut (m : T3.Message) (pk : Digest) (w : WBytes) (a b : HashOutput)
    (s : MachineState) : Prop where
  old : DgOutC m pk w b (s.setPC (pcOf 18))
  pc : s.pc=pcOf 221961
  nregs : NRegs a s

theorem twin_load (m pk w a s) (h : DgOutC m pk w a s) :
    ∃ t, Steps fixture s 5 5 t ∧ TwinPre m pk w a t := by
  obtain ⟨t,ht⟩ := spec_runC twin_load_checked s h.pc h.known (by simp [twinLoadSpec]) (by simp)
  have hm : ∀ A, t.getMem A=s.getMem A := fun A => by rw [ht.mem];rfl
  have hfake : DgOutC m pk w a (s.setPC (pcOf 18)) := by
    simpa only [show s.setPC (pcOf 18)=s from by rw [←h.pc]; cases s;rfl] using h
  refine ⟨t,ht.steps,⟨dgo_control hfake ht.known hm,ht.pc rfl,?_⟩⟩
  intro k hk
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl
  · exact (ht.regs (.x16,nE 0) (by simp [twinLoadSpec])).trans (h.nwords 0 (by decide))
  · exact (ht.regs (.x17,nE 1) (by simp [twinLoadSpec])).trans (h.nwords 1 (by decide))
  · exact (ht.regs (.x27,nE 2) (by simp [twinLoadSpec])).trans (h.nwords 2 (by decide))
  · exact (ht.regs (.x28,nE 3) (by simp [twinLoadSpec])).trans (h.nwords 3 (by decide))

theorem twin_hash_out {m pk w a s} (h : TwinPre m pk w a s) (b : HashOutput) :
    TwinOut m pk w a b (writeHash s b) := by
  have hd : s.getReg .x12=96 := h.old.known (.x12,96) (by simp [proPostC,proPost])
  refine ⟨?_,?_,?_⟩
  · refine ⟨rfl,h.old.known.writeHash b,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro j hj
      change (writeHash s b).getMem _=wword w j
      rw [writeHash_frame s b 96 _ hd (by unfold WIT WX at *;omega) (by decide) (Or.inr (by unfold WIT;omega))]
      exact h.old.wit j hj
    · exact ⟨(writeHash_frame s b 96 0xA0 hd (by decide) (by decide) (Or.inr (by decide))).trans h.old.pk.1,
        (writeHash_frame s b 96 0xA8 hd (by decide) (by decide) (Or.inr (by decide))).trans h.old.pk.2⟩
    · intro k hk
      change (writeHash s b).getMem _=_
      rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl
      · exact writeHash_at0 s b 96 hd (by decide)
      · exact writeHash_at8 s b 96 hd (by decide)
      · exact writeHash_at16 s b 96 hd (by decide)
      · exact writeHash_at24 s b 96 hd (by decide)
    · intro A hA hz
      change (writeHash s b).getMem _=0
      rw [writeHash_frame s b 96 A hd (by unfold WIT at hA;omega) (by decide) (by omega)]
      exact h.old.zero A hA hz
    · exact h.old.data.congr (fun A hA _ => writeHash_frame s b 96 A hd (by omega) (by decide)
        (Or.inr (by unfold TAB at hA;omega)))
    · change (writeHash s b).getReg .x2=BitVec.ofNat 64 TAB
      rw [writeHash_getReg]; exact h.old.sp
    · exact h.old.tables.hash_frame s b 96 hd (by decide)
    · change hashInput (writeHash s b)=_
      rw [hash_input_write_c s b
        (h.old.known (.x10,32) (by simp [proPostC,proPost]))
        (h.old.known (.x11,64) (by simp [proPostC,proPost])) hd]
      exact h.old.input
  · rw [writeHash_pc,h.pc]
    exact pcOf_add4 221960
  · intro k hk; rw [writeHash_getReg]; exact h.nregs k hk

theorem twin_word_eq (a b : HashOutput) (h : ∀ k, k<4 →
    a.extractLsb' (64*k) 64=b.extractLsb' (64*k) 64) : a=b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have he := congrArg (fun v : BitVec 64 => v.getLsbD (i%64)) (h (i/64) (by omega))
  simp only [BitVec.getLsbD_extractLsb',show i%64<64 from Nat.mod_lt _ (by decide),
    decide_true,Bool.true_and] at he
  simpa only [show 64*(i/64)+i%64=i by omega] using he

theorem twin_br_holds {m pk w a b s} (h : TwinOut m pk w a b s) (k : Nat) (hk : k<4) (d : Bool) :
    (twinBr k d).holds s ↔
      (b.extractLsb' (64*k) 64 != a.extractLsb' (64*k) 64)=d := by
  change (s.getMem (BitVec.ofNat 64 (0x60+8*k)) != s.getReg (nReg k))=d ↔ _
  have hn : s.getMem (BitVec.ofNat 64 (0x60+8*k))=b.extractLsb' (64*k) 64 := h.old.nwords k hk
  rw [hn,h.nregs k hk]

structure TwinSel (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput)
    (s : MachineState) : Prop where
  old : DgOutC m pk w a (s.setPC (pcOf 18))
  pc : s.pc=pcOf 22
  nregs : NRegs a s

theorem twin_guard_accept {m pk w a b s} (h : TwinOut m pk w a b s) (he : b=a) :
    ∃ t, Steps fixture s 9 9 t ∧ TwinSel m pk w a t := by
  subst b
  obtain ⟨t,ht⟩ := spec_runC twin_pass_checked s h.pc h.old.known (by
    intro br hbr
    simp only [twinPassSpec,twinPassBrs,List.mem_reverse,List.mem_map,List.mem_range] at hbr
    obtain ⟨k,hk,rfl⟩ := hbr
    exact (twin_br_holds h k hk false).mpr (by simp)) (by simp)
  have hm : ∀ A, t.getMem A=s.getMem A := fun A => by rw [ht.mem];rfl
  refine ⟨t,ht.steps,⟨dgo_control h.old ht.known hm,ht.pc rfl,?_⟩⟩
  intro k hk
  rw [ht.keep (nReg k) (by rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with
    rfl | rfl | rfl | rfl <;> decide)]
  exact h.nregs k hk

theorem twin_guard_reject {m pk w a b s} (h : TwinOut m pk w a b s) (he : b≠a) :
    ∃ t k, Steps fixture s k k t ∧ k≤10 ∧ HaltC1 t := by
  have hw : ∃ k, k<4 ∧ b.extractLsb' (64*k) 64≠a.extractLsb' (64*k) 64 := by
    by_contra hn
    push Not at hn
    exact he (twin_word_eq b a hn)
  let k := Nat.find hw
  have hk : k<4 := (Nat.find_spec hw).1
  have hne : b.extractLsb' (64*k) 64≠a.extractLsb' (64*k) 64 := (Nat.find_spec hw).2
  have hearly : ∀ j, j<k → b.extractLsb' (64*j) 64=a.extractLsb' (64*j) 64 := by
    intro j hj
    by_contra hne'
    exact Nat.find_min' hw ⟨by omega,hne'⟩ |> fun hh => by dsimp only [k] at hj;omega
  obtain ⟨t,ht⟩ := spec_runC (twin_reject_checked ⟨k,hk⟩) s h.pc h.old.known (by
    intro br hbr
    simp only [twinRejectSpec,twinRejectBrs,List.mem_append,List.mem_singleton,List.mem_reverse,
      List.mem_map,List.mem_range] at hbr
    rcases hbr with rfl | ⟨j,hj,rfl⟩
    · exact (twin_br_holds h k hk true).mpr (by simp [hne])
    · exact (twin_br_holds h j (by omega) false).mpr (by simp [hearly j hj])) (by simp)
  exact ⟨t,4+2*k,ht.steps,by omega,ht.ecall rfl,
    ht.regs (.x5,SigGolfCandidate.T3M.Verify.cw 1) (by simp [twinRejectSpec]),
    ht.regs (.x10,SigGolfCandidate.T3M.Verify.cw 1) (by simp [twinRejectSpec])⟩

theorem twin_sel_ready {m pk w a s} (h : TwinSel m pk w a s) :
    ∃ t, Steps fixture s 2 2 t ∧ SelState pk w a 0 t := by
  have hk : KnownOK selK s := selK_of
    (h.old.known.mono (fun p hp => List.mem_append_left _ (List.mem_append_left _ hp))) h.old.sp
  obtain ⟨t,ht⟩ := spec_runC twin_sel_checked s h.pc hk (by simp [twinSelSpec]) (by simp)
  have hm : ∀ A, t.getMem A=s.getMem A := fun A => by rw [ht.mem];rfl
  refine ⟨t,ht.steps,⟨⟨ht.pc rfl,selK_base ht.known,?_,?_,?_,?_,?_,?_,?_,?_,selK_sp ht.known⟩,
    ht.tables h.old.tables (RelOK.nil s)⟩⟩
  · intro k hk
    rw [ht.keep (nReg k) (by rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with
      rfl | rfl | rfl | rfl <;> decide)]
    exact h.nregs k hk
  · rw [ht.regs (.x22,twinSelE) (by simp [twinSelSpec])]
    apply BitVec.eq_of_toNat_eq
    have hn : s.getReg .x16=a.extractLsb' 0 64 := h.nregs 0 (by decide)
    simp only [twinSelE,E.eval,hn]
    rw [srl_toNat _ 33 (by decide),sll_toNat _ 33 (by decide),BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero,BitVec.toNat_ofNat]
    omega
  · intro c k hc hk;omega
  · intro c hc;omega
  · intro j hj; rw [hm];exact h.old.wit j hj
  · exact ⟨(hm _).trans h.old.pk.1,(hm _).trans h.old.pk.2⟩
  · intro A hA hz _; rw [hm];exact h.old.zero A hA hz
  · exact h.old.data.congr (fun A _ _ => hm _)

#print axioms twin_hash_out
#print axioms twin_guard_reject
#print axioms twin_sel_ready
end SigGolfCandidate.T3M.CanonicalNative
