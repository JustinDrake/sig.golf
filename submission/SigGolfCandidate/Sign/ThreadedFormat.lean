import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def threadedPositionWord (p : Nat) : Word :=
  ((BitVec.ofNat 64 p >>> 3) <<< 4) +
    ((0#64 - (if (0#64).ult (BitVec.ofNat 64 p >>> 3) then 1#64 else 0#64)) &&& 848#64) +
    ((BitVec.ofNat 64 p &&& 7#64) <<< 16)

theorem threadedPositionWord_eq : ∀ p, p < 336 → threadedPositionWord p =
    BitVec.ofNat 64 (chainPtr (p / 8) + 65536 * (p % 8)) := by decide +kernel

theorem threadedPositionWord_index (i j : Nat) (hi : i < 42) (hj : j < 8) :
    threadedPositionWord (8 * i + j) = BitVec.ofNat 64 (chainPtr i + 65536 * j) := by
  rw [threadedPositionWord_eq _ (by omega)]
  rw [show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega]

theorem threaded_thunk_2972 (s : MachineState) (hpc : s.pc = pcOf 2972) (p : Nat)
    (hp : p < 336) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 563 ∧
      t.getReg .x10 = BitVec.ofNat 64 192 ∧ RegsEq s t [.x3, .x10, .x29] ∧
      Frame s t (fun a => a = 192) ∧
      t.getMem (BitVec.ofNat 64 192) = replaceWord32 (s.getMem (BitVec.ofNat 64 192)) 1
        ((BitVec.ofNat 64 (chainPtr (p / 8) + 65536 * (p % 8))).truncate 32) := by
  have hobl : blk2972.res.obligs s := by simp only [blk2972.res, rv_simp]
  refine ⟨_, symRun_sound blk2972 codeAt_2972 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [blk2972.res, rv_simp]
  · simp only [blk2972.res, rv_simp]
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro a ha hW
    simp only [blk2972.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  · simp only [blk2972.res, rv_simp, h24, ↓reduceIte]
    simp only [show (3#64).toNat % 64 = 3 from rfl, show (4#64).toNat % 64 = 4 from rfl,
      show (16#64).toNat % 64 = 16 from rfl]
    have heq := threadedPositionWord_eq p hp
    unfold threadedPositionWord at heq
    rw [heq]

theorem threaded_fetch_563 (s : MachineState) (hpc : s.pc = pcOf 563) :
    fetch image s = some (.base .ECALL) := by
  have h : CodeAt image (pcOf 563) [0x00000073#32] := by unfold CodeAt; decide +kernel
  exact (h.fetch s hpc).trans rfl

theorem threaded_thunk_2984 (s : MachineState) (hpc : s.pc = pcOf 2984) (p : Nat)
    (hp : p < 336) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 672 ∧
      t.getReg .x10 = BitVec.ofNat 64 192 ∧ RegsEq s t [.x3, .x10, .x29] ∧
      Frame s t (fun a => a = 192) ∧
      t.getMem (BitVec.ofNat 64 192) = replaceWord32 (s.getMem (BitVec.ofNat 64 192)) 1
        ((BitVec.ofNat 64 (chainPtr (p / 8) + 65536 * (p % 8))).truncate 32) := by
  have hobl : blk2984.res.obligs s := by simp only [blk2984.res, rv_simp]
  refine ⟨_, symRun_sound blk2984 codeAt_2984 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [blk2984.res, rv_simp]
  · simp only [blk2984.res, rv_simp]
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro a ha hW
    simp only [blk2984.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  · simp only [blk2984.res, rv_simp, h24, ↓reduceIte]
    simp only [show (3#64).toNat % 64 = 3 from rfl, show (4#64).toNat % 64 = 4 from rfl,
      show (16#64).toNat % 64 = 16 from rfl]
    have heq := threadedPositionWord_eq p hp
    unfold threadedPositionWord at heq
    rw [heq]

theorem threaded_fetch_672 (s : MachineState) (hpc : s.pc = pcOf 672) :
    fetch image s = some (.base .ECALL) := by
  have h : CodeAt image (pcOf 672) [0x00000073#32] := by unfold CodeAt; decide +kernel
  exact (h.fetch s hpc).trans rfl

theorem threaded_tree_format (s : MachineState) (hpc : s.pc = pcOf 556) (m p : Nat)
    (hp : p < 336) (h23 : s.getReg .x23 = BitVec.ofNat 64 m)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 563 ∧
      t.getReg .x23 = BitVec.ofNat 64 (m + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 192 ∧
      RegsEq s t [.x3, .x10, .x23, .x29] ∧ Frame s t (fun a => a = 192) ∧
      t.getMem (BitVec.ofNat 64 192) = replaceWord32 (s.getMem (BitVec.ofNat 64 192)) 1
        ((BitVec.ofNat 64 (chainPtr (p / 8) + 65536 * (p % 8))).truncate 32) := by
  have hs := symRun_sound blk556 codeAt_556 s hpc (by simp only [blk556.res, rv_simp])
  let u := blk556.res.toState s
  have upc : u.pc = pcOf 2972 := by simp only [u, blk556.res, rv_simp]
  have ur : RegsEq s u [.x23] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have um : ∀ a, u.getMem a = s.getMem a := by intro a; simp only [u, blk556.res, rv_simp]
  obtain ⟨t, ut, tpc, t10, tr, tf, tm⟩ := threaded_thunk_2972 u upc p hp (by rw [ur.get .x24, h24])
  refine ⟨t, hs.trans ut, tpc, ?_, t10, ?_, ?_, ?_⟩
  · rw [tr.get .x23]
    simp only [u, blk556.res, rv_simp, h23, ofNat_add_ofNat]
  · exact (ur.trans tr).mono (by decide)
  · intro a ha hW; rw [tf a ha hW, um]
  · rw [tm, um]

theorem threaded_top_format (s : MachineState) (hpc : s.pc = pcOf 666) (p : Nat)
    (hp : p < 336) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 672 ∧
      t.getReg .x10 = BitVec.ofNat 64 192 ∧ RegsEq s t [.x3, .x10, .x29] ∧
      Frame s t (fun a => a = 192) ∧
      t.getMem (BitVec.ofNat 64 192) = replaceWord32 (s.getMem (BitVec.ofNat 64 192)) 1
        ((BitVec.ofNat 64 (chainPtr (p / 8) + 65536 * (p % 8))).truncate 32) := by
  have hs := symRun_sound blk666 codeAt_666 s hpc (by simp only [blk666.res, rv_simp])
  let u := blk666.res.toState s
  have upc : u.pc = pcOf 2984 := by simp only [u, blk666.res, rv_simp]
  have ur : RegsEq s u [] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> rfl
  have um : ∀ a, u.getMem a = s.getMem a := by intro a; simp only [u, blk666.res, rv_simp]
  obtain ⟨t, ut, tpc, t10, tr, tf, tm⟩ := threaded_thunk_2984 u upc p hp (by rw [ur.get .x24, h24])
  refine ⟨t, hs.trans ut, tpc, t10, ?_, ?_, ?_⟩
  · exact (ur.trans tr).mono (by decide)
  · intro a ha hW; rw [tf a ha hW, um]
  · rw [tm, um]

end SigGolfCandidate.Sign
