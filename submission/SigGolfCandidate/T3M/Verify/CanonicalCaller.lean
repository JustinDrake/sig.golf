import SigGolfCandidate.T3M.Verify.CanonicalBankEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def callerKeep : List Reg := allKeep.filter fun r =>
  r≠.x19 ∧ r≠.x24 ∧ r≠.x25 ∧ r≠.x27 ∧ r≠.x28
def callerSpec (c : Nat) : Spec :=
  ⟨[(.x24,.bin .add (.reg .x24) (cE 24)),(.x19,.bin .add (.reg .x19) (cE 144)),
    (.x25,.bin .add (.reg .x25) (cE (if c=0 then 32 else 16))),
    (.x27,.bin .add (.reg .x27) (.reg .x31)),(.x28,.bin .add (.reg .x28) (.reg .x31))],
    [],banks[c+1]!,false,5,[],none,5⟩
def callerCheck (c : Nat) : Bool :=
  rawB (runAtC {} [] [banks[c+1]!] (banks[c]!+13) []) (callerSpec c) [] callerKeep
theorem caller_checked : ∀ c : Fin 6, callerCheck c.val=true := by decide +kernel

theorem caller_run (c : Nat) (hc : c<6) (s : MachineState) (hpc : s.pc=pcOf (banks[c]!+13)) :
    ∃ t, RawRes (callerSpec c) callerKeep s t := by
  exact raw_run (caller_checked ⟨c,hc⟩) s hpc (by simp [KnownOK]) (by simp [callerSpec]) (by simp)

theorem caller_entry (F : FCtx) (c ptr : Nat) (roots : List Digest) (node : Digest)
    (s : MachineState) (hc : c<6) (hs : BankReturned F c ptr roots node s) :
    ∃ t, Steps fixture s 5 5 t ∧ BankEntry F (c+1) ptr (roots++[node]) t := by
  obtain ⟨t,hr⟩ := caller_run c hc s hs.pc
  have hm : ∀ A, t.getMem A=s.getMem A := by intro A; rw [hr.mem]; rfl
  have hpres : ∀ r v, (r,v)∈bankK F c → r∈callerKeep → t.getReg r=v := by
    intro r v hp hk; exact (hr.keep r hk).trans (hs.known (r,v) hp)
  have hk : KnownOK (entryK F (c+1)) t := by
    intro p hp
    simp [entryK,bankK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpres .x2 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x5 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x8 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x9 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x13 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x11 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · rw [hr.regs (.x19,.bin .add (.reg .x19) (cE 144)) (by simp [callerSpec])]
      change s.getReg .x19+144#64=_
      rw [hs.known (.x19,BitVec.ofNat 64 (WIT+64+144*c)) (by simp [bankK])]
      rw [show 144#64=BitVec.ofNat 64 144 by rfl,BitVec.ofNat_add_ofNat]
      congr 1 <;> omega
    · exact hpres .x20 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x21 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x22 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · rw [hr.regs (.x24,.bin .add (.reg .x24) (cE 24)) (by simp [callerSpec])]
      change s.getReg .x24+24#64=_
      rw [hs.known (.x24,BitVec.ofNat 64 (ETAB+24*c)) (by simp [bankK])]
      rw [show 24#64=BitVec.ofNat 64 24 by rfl,BitVec.ofNat_add_ofNat]
      congr 1 <;> omega
    · rw [hr.regs (.x25,.bin .add (.reg .x25) (cE (if c=0 then 32 else 16))) (by simp [callerSpec])]
      change s.getReg .x25+(if c=0 then 32#64 else 16#64)=_
      rw [show (if c=0 then 32#64 else 16#64)=BitVec.ofNat 64 (if c=0 then 32 else 16) by
        split_ifs <;> rfl]
      rw [hs.known (.x25,BitVec.ofNat 64 (forestSlot c)) (by simp [bankK]),BitVec.ofNat_add_ofNat]
      have hf : forestSlot c+(if c=0 then 32 else 16)=forestSlot (c+1) := by
        by_cases hz : c=0
        · subst c; decide
        · simp [forestSlot,hz,show c+1≠0 by omega]; omega
      exact congrArg (BitVec.ofNat 64) hf
    · rw [hr.regs (.x27,.bin .add (.reg .x27) (.reg .x31)) (by simp [callerSpec])]
      change s.getReg .x27+s.getReg .x31=_
      rw [hs.known (.x27,BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)) (by simp [bankK]),
        hs.known (.x31,0x10000#64) (by simp [bankK]),
        show 0x10000#64=BitVec.ofNat 64 65536 by rfl,BitVec.ofNat_add_ofNat]
      congr 1
      have h0 : nodeW0 c<2^32 := by unfold nodeW0; omega
      have h1 : nodeW0 (c+1)<2^32 := by unfold nodeW0; omega
      simp only [hdr1,Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1]
      unfold nodeW0; omega
    · rw [hr.regs (.x28,.bin .add (.reg .x28) (.reg .x31)) (by simp [callerSpec])]
      change s.getReg .x28+s.getReg .x31=_
      rw [hs.known (.x28,BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx)) (by simp [bankK]),
        hs.known (.x31,0x10000#64) (by simp [bankK]),
        show 0x10000#64=BitVec.ofNat 64 65536 by rfl,BitVec.ofNat_add_ofNat]
      congr 1
      have h0 : leafW0 c<2^32 := by unfold leafW0; omega
      have h1 : leafW0 (c+1)<2^32 := by unfold leafW0; omega
      simp only [hdr1,Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1]
      unfold leafW0; omega
    · exact hpres .x29 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
    · exact hpres .x31 _ (by simp [bankK]) (by simp [callerKeep,allKeep])
  refine ⟨t,hr.steps,⟨hr.pc rfl,?_,hk,hs.common.control hr rfl,?_,?_⟩⟩
  · rw [hr.keep .x14 (by simp [callerKeep,allKeep])]; exact hs.pointer
  · intro o ho; rw [hm]; exact hs.orig o ho
  · intro k hk'; exact ⟨(hm _).trans (hs.roots k hk').1,(hm _).trans (hs.roots k hk').2⟩

#print axioms caller_entry
end SigGolfCandidate.T3M.CanonicalNative
