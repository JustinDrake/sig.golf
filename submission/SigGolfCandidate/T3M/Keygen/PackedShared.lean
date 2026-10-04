import SigGolfCandidate.T3M.Keygen.Blocks
import SigGolfCandidate.T3M.Keygen.PackedLayers
import SigGolfCandidate.T3M.Sign.PackedHeader
import SigGolfCandidate.T3M.Keygen.PackedSource
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
open PackedBlocks
set_option backward.isDefEq.respectTransparency false
def headerK (lay : Layer) : Nat := if lay.val = 0 then 30 else if lay.val = 1 then 33 else 34
def rungK (lay : Layer) : Nat := headerK lay + 5
def rungC (lay : Layer) : Nat := headerK lay + 12
theorem shared_header {image : Image} {b : Nat} (h : SubAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      HeaderPost s t (height lay) := by
  rcases h.2.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · fin_cases lay
    · exact keygen_header_0 s hpc h8
    · exact keygen_header_1 s hpc h8
    · exact keygen_header_2 s hpc h8
    · exact keygen_header_3 s hpc h8
  · fin_cases lay
    · exact sign_header_0 s hpc h8
    · exact sign_header_1 s hpc h8
    · exact sign_header_2 s hpc h8
    · exact sign_header_3 s hpc h8
theorem shared_header_source {image : Image} {b : Nat} (h : SubAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x201A0 ∧ t.getReg .x11 = 64#64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x201A0 + 48) ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := shared_header h s hpc lay h8
  refine ⟨t, st, pc, post.arg0, post.arg1, post.arg2,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm
end SigGolfCandidate.T3M.Keygen
