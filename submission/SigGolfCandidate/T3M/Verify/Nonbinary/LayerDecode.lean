import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.Prologue
import SigGolfCandidate.T3M.Verify.Nonbinary.Prefix
import SigGolfCandidate.T3M.Verify.Nonbinary.Halt
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- Registers changed by the two jumps, strong decoder, and top-chain dispatch prologue. -/
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x19,.x22,.x24,.x15,.x28]

/-- Exact transition interface. `u` is the state immediately after the encoding HASH. -/
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : s.getReg .x1 = pcOf (p + 69)
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = Search.topWindow v 17
  s6 : s.getReg .x22 = 14344#64
  s3 : s.getReg .x19 = 15048#64
  mask : s.getReg .x24 = 130048#64
  table : s.getReg .x15 = 712704#64
  «prefix» : s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4)
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)

/-- Both direct jumps from a top transition copy to the shared decoder. -/
theorem topCall_jumps (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 13)) (hk : KnownOK (bK 0) u) :
    ∃ s, Steps image u 2 2 s ∧ s.pc = pcOf 724 ∧ s.getReg .x1 = pcOf (trPc 0 c + 69) ∧
      RegsExcept u s [.x1] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := spec_run hcc u hpc (by simp [KnownOK]) (by simp [specTopCall]) (by simp)
  refine ⟨s, hs.steps, hs.pc rfl, ?_, ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 69))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl

/-- The two direct jumps plus the packed-prefix helper. -/
theorem topCall_step (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 13)) (hk : KnownOK (bK 0) u)
    (hmem : u.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ s, Steps image u 8 8 s ∧ s.pc = pcOf 96160 ∧ s.getReg .x1 = pcOf (trPc 0 c + 69) ∧
      s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4) ∧
      RegsExcept u s [.x1,.x3,.x28] ∧ Frame u s (fun _ => False) := by
  obtain ⟨r, er, pr, ra, rr, fr⟩ := topCall_jumps c hc u hpc hk
  have hm : r.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) := by
    rw [fr.get (by decide) (by simp), hmem]
  obtain ⟨s, es, ps, hp, rs, fs⟩ := Nonbinary.prefix_spec r pr hm
  refine ⟨s, er.trans es, ps, ?_, ?_, (rr.trans rs).mono (by decide), ?_⟩
  · rw [rs.get (by decide), ra]
  · rw [hp, rr.get (by decide)]
  · exact (fr.trans fs).mono (by simp)

/-- Every failed mixed-radix decode reaches HALT(1), with at most 71 instructions. -/
theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps image (writeHash t a) k k s ∧ k ≤ 71 ∧
      fetch image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 13) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 12) + 4 = pcOf (trPc 0 c + 13)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 12)
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  obtain ⟨s, e, ps, ra, hp, rs, fs⟩ := topCall_step c hc _ hpc hk
    (hglob.2.2.2.2.2.prefix 0 (by decide))
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := Verify.Nonbinary.decode_reject s _ ps hv hd hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := Verify.Nonbinary.reject_halt r pr
  refine ⟨8 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩

/-- Exact 76-instruction top transition including the packed-prefix setup. -/
theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps image (writeHash t a) 76 76 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 13) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 12) + 4 = pcOf (trPc 0 c + 13)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 12)
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  obtain ⟨s, e, ps, ra, hp, rs, fs⟩ := topCall_step c hc _ hpc hk
    (hglob.2.2.2.2.2.prefix 0 (by decide))
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨r, er, pr, h16, h17, h29, rr, fr⟩ := Verify.Nonbinary.decode_ok s _ ps hv hd hgood
  obtain ⟨z, ez, pz, lo, hi, s6, s3, mask, tab, rz, fz⟩ := Verify.Nonbinary.prologue_spec r _ pr h16 h17
  refine ⟨z, (e.trans er).trans ez, ⟨?_, ?_, lo, ?_, ?_, s6, s3, mask, tab, ?_, ?_, ?_⟩⟩
  · rw [pz]
    exact Nonbinary.prologue_target _
  · rw [rz.get (by decide), rr.get (by decide), ra]
  · rw [hi]; exact (Search.topWindow_cross _).symm
  · rw [rz.get (by decide), h29]
  · rw [rz.get (by decide), rr.get (by decide), hp]
  · exact ((rs.trans rr).trans rz).mono (by decide)
  · exact ((fs.trans fr).trans fz).mono (by simp)

end SigGolfCandidate.T3M
