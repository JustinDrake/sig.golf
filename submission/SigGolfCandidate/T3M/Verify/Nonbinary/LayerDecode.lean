import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.Prologue
import SigGolfCandidate.T3M.Verify.Nonbinary.Halt
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- Registers changed by the direct link, strong decoder, and top-chain dispatch prologue. -/
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x19,.x22,.x24,.x15]

/-- Exact transition interface. `u` is the state immediately after the encoding HASH. -/
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : s.getReg .x1 = pcOf (p + 18)
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = Search.topWindow v 17
  s6 : s.getReg .x22 = 15064#64
  s3 : s.getReg .x19 = 15768#64
  mask : s.getReg .x24 = 130048#64
  table : s.getReg .x15 = 712704#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)

/-- The direct linked call from a top transition copy to the shared decoder. -/
theorem topCall_step (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 17)) (hk : KnownOK (bK 0) u) :
    ∃ s, Steps image u 1 1 s ∧ s.pc = pcOf 96160 ∧ s.getReg .x1 = pcOf (trPc 0 c + 18) ∧
      RegsExcept u s [.x1] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := spec_run hcc u hpc (by simp [KnownOK]) (by simp [specTopCall]) (by simp)
  refine ⟨s, hs.steps, hs.pc rfl, ?_, ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 18))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl

/-- Every failed mixed-radix decode reaches HALT(1), with at most 65 instructions. -/
theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps image (writeHash t a) k k s ∧ k ≤ 65 ∧
      fetch image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_step c hc _ hpc hk
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := Verify.Nonbinary.decode_reject s _ ps hv hd hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := Verify.Nonbinary.reject_halt r pr
  refine ⟨1 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩

/-- Exact 67-instruction top transition from the HASH answer to the first mixed-radix chain entry. -/
theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps image (writeHash t a) 67 67 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_step c hc _ hpc hk
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨r, er, pr, h16, h17, h29, h24, rr, fr⟩ := Verify.Nonbinary.decode_ok s _ ps hv hd hgood
  obtain ⟨z, ez, pz, lo, hi, s6, s3, mask, tab, rz, fz⟩ := Verify.Nonbinary.prologue_spec r _ pr h24 h16 h17
  refine ⟨z, (e.trans er).trans ez, ⟨?_, ?_, lo, ?_, ?_, s6, s3, mask, tab, ?_, ?_⟩⟩
  · rw [pz]
    exact Nonbinary.prologue_target _
  · rw [rz.get (by decide), rr.get (by decide), ra]
  · rw [hi]; exact (Search.topWindow_cross _).symm
  · rw [rz.get (by decide), h29]
  · exact ((rs.trans rr).trans rz).mono (by decide)
  · exact ((fs.trans fr).trans fz).mono (by simp)

end SigGolfCandidate.T3M
