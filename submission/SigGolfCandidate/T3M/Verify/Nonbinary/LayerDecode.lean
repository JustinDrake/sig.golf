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

/-- Registers changed by the two jumps, strong decoder, and top-chain dispatch prologue. -/
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x19,.x22,.x24,.x15]

/-- Exact transition interface. `u` is the state immediately after the encoding HASH. -/
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : s.getReg .x1 = pcOf (p + 19)
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = Search.topWindow v 17
  s6 : s.getReg .x22 = 15064#64
  s3 : s.getReg .x19 = 15768#64
  mask : s.getReg .x24 = 130048#64
  table : s.getReg .x15 = 712704#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)

/-- Full E8: the two answer loads through `a2` and `jal ra` into the shared decoder after its loads. -/
theorem topCall_step (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 16)) (hob : ∀ o ∈ ansObl, o.holds u) :
    ∃ s, Steps image u 3 3 s ∧ s.pc = pcOf 96162 ∧ s.getReg .x1 = pcOf (trPc 0 c + 19) ∧
      s.getReg .x16 = a6E.eval u ∧ s.getReg .x17 = a7E.eval u ∧
      RegsExcept u s [.x1, .x16, .x17] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := spec_run hcc u hpc (by simp [KnownOK]) (by simp [specTopCall]) hob
  refine ⟨s, hs.steps, hs.pc rfl, ?_, hs.regs (.x16, a6E) (by simp [specTopCall]),
    hs.regs (.x17, a7E) (by simp [specTopCall]), ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 19))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    case x16 => simp at hr
    case x17 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl

/-- The common prefix of both top transitions: the call, the answer in `a6`/`a7`, the frame facts. -/
theorem topCall_of (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ s, Steps image (writeHash t a) 3 3 s ∧ s.pc = pcOf 96162 ∧ s.getReg .x1 = pcOf (trPc 0 c + 19) ∧
      s.getReg .x16 = (a.extractLsb' 0 128).extractLsb' 0 64 ∧
      s.getReg .x17 = (a.extractLsb' 0 128).extractLsb' 64 64 ∧
      RegsExcept (writeHash t a) s [.x1, .x16, .x17] ∧ Frame (writeHash t a) s (fun _ => False) ∧
      Glob (bK 0) w pk (writeHash t a) := by
  obtain ⟨D, hD, h12⟩ := ht.dst
  have hDf := dst_facts 0 (by decide) D hD
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 16) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 15) + 4 = pcOf (trPc 0 c + 16)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 15)
  have hob : ∀ o ∈ ansObl, o.holds (writeHash t a) :=
    ansObl_holds _ D (by rw [writeHash_getReg]; exact h12) hDf.2.2.2.2.2.1 hDf.2.2.2.2.2.2
  obtain ⟨s, e, ps, ra, h16, h17, rs, fs⟩ := topCall_step c hc _ hpc hob
  have hans := ansAt_of t a D h12 (by omega)
  refine ⟨s, e, ps, ra, ?_, ?_, rs, fs, Glob_writeHash ht.glob a D h12 hDf.1⟩
  · rw [h16, a6E_eval hans]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  · rw [h17, a7E_eval hans]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Every failed mixed-radix decode reaches HALT(1), with at most 65 instructions. -/
theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps image (writeHash t a) k k s ∧ k ≤ 65 ∧
      fetch image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  obtain ⟨s, e, ps, ra, h16, h17, rs, fs, hglob⟩ := topCall_of w pk index c hc t ht a
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := Verify.Nonbinary.decode_reject2 s _ ps h16 h17 hd hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := Verify.Nonbinary.reject_halt r pr
  refine ⟨3 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩

/-- Exact 67-instruction top transition from the HASH answer to the first mixed-radix chain entry (full E8). -/
theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps image (writeHash t a) 67 67 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  obtain ⟨s, e, ps, ra, h16', h17', rs, fs, hglob⟩ := topCall_of w pk index c hc t ht a
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨r, er, pr, h16, h17, h29, h24, rr, fr⟩ := Verify.Nonbinary.decode_ok2 s _ ps h16' h17' hd hgood
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
