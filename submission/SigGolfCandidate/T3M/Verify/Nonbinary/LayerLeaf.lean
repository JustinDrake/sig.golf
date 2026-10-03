import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3M.Verify.LeafSem

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15]
def topChainWrites (A : Nat) : Prop := (512 ≤ A ∧ A < 1488) ∨ (14104 ≤ A ∧ A < 17576)

/-- The global chain fold's final register/memory interface is exactly the top leaf block's input. -/
theorem topLeafReady_of (w : WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ends : List Digest) (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hp : s.pc = pcOf (trPc 0 c + 69))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites)
    (hlen : ends.length = 54) (hend : ∀j<54, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk : KnownOK (leafK 0) s := by
    intro p hp
    simp [leafK,baseK] at hp
    rcases hp with rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs]), he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [bK,layK,baseK,hw])
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_,_) (by simp [bK])
  have hg := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hfr : Frame (writeHash t a) s topChainWrites :=
    (he.frame.trans hf).mono (by intro A h; simpa using h)
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h <;> omega) hk
  refine ⟨hp,hglob,?_,?_,?_,?_,hlen,hend,?_⟩
  · intro p hp
    simp [lfKeepK,leaf28] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs])]
    all_goals try exact he.s6
    all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [bK,layK,entry28,baseK])
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.s7 0 rfl
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.t5 0 rfl
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.tp 0 rfl
  · have ho := topEntry_orig w pk index c t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by norm_num [layerBase,T3.height,layerEnd] at *;omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [layerBase,T3.height] at hp
      unfold topChainWrites WIT
      omega)

end SigGolfCandidate.T3M
