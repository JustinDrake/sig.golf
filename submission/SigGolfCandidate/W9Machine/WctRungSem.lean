import SigGolfCandidate.W9Machine.WctRelativeMem

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest pad64)
theorem rungRRel_mem (s : MachineState) (rb : Reg) (digit p A X : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hX : X < 2 ^ 64) (hstep : (posE digit).eval s = BitVec.ofNat 64 digit) :
    ((rungRRel rb digit dst p).toState s).getMem (BitVec.ofNat 64 X) =
      if X = A + 16 then StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 4
        (BitVec.ofNat 64 digit) else s.getMem (BitVec.ofNat 64 X) := by
  have hk : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (A + 16) := by
    simp only [Addr.eval, E.eval, h10]
    exact ofNat_add_ofNat A 16
  have hm := memEval_one s ⟨some (.reg .x10), 16⟩
    (.bin (.st .b 4) (.ld (addC (.reg .x10) 16)) (posE digit)) (A + 16) X
    hk (by omega) hX
  have ha : BitVec.ofNat 64 A + (16 : Word) = BitVec.ofNat 64 (A + 16) :=
    ofNat_add_ofNat A 16
  simpa only [Result.toState_getMem, rungRRel, E.eval, BinOp.eval, addC_eval, h10,
    hstep, ha] using hm
theorem rungRRel_frame (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hstep : (posE digit).eval s = BitVec.ofNat 64 digit) :
    Frame s ((rungRRel rb digit dst p).toState s) (fun X => X = A + 16) := by
  intro X hX hn
  rw [rungRRel_mem s rb digit p A X dst h10 hhi hX hstep, if_neg hn]
theorem rungRRel_hashInput (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (pad0 hdr pad1 value : Digest) (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (halign : A % 8 = 0) (hhi : A + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hstep : (posE digit).eval s = BitVec.ofNat 64 digit)
    (hlo : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 4
      (BitVec.ofNat 64 digit) = hdr.extractLsb' 0 64)
    (hhigh : s.getMem (BitVec.ofNat 64 (A + 24)) = hdr.extractLsb' 64 64)
    (hp0 : DigAt s A pad0) (hp1 : DigAt s (A + 32) pad1) (hv : DigAt s (A + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput ((rungRRel rb digit dst p).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := rungRRel_frame s rb digit p A dst h10 hhi hstep
  refine ClaudeWCT.W9.Machine.Merkle.hashInput_blk4 _ A pad0 hdr pad1 value
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h10)
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h11)
    halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  constructor
  · rw [rungRRel_mem s rb digit p A (A + 16) dst h10 hhi (by omega) hstep, if_pos rfl]
    exact hlo
  · rw [rungRRel_mem s rb digit p A (A + 16 + 8) dst h10 hhi (by omega) hstep, if_neg (by omega)]
    simpa only [Nat.add_assoc] using hhigh
end W9Machine
