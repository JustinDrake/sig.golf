import SigGolfCandidate.W9Machine.WctImageLink
import SigGolfCandidate.W9Machine.WctChainPieces

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def sliceChecked (pc : Nat) (words : List (BitVec 32)) : Bool :=
  decide (pc < 242202) && (words == (Frozen.codeFrom pc).take words.length)
theorem slice_at (pc : Nat) (words : List (BitVec 32)) (h : sliceChecked pc words = true) :
    CodeAt Frozen.image (pcOf pc) words := by
  simp only [sliceChecked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hb := Frozen.codeFrom_at pc h.1
  have hpref : words <+: Frozen.codeFrom pc := h.2 ▸ List.take_prefix _ _
  exact ⟨hb.1, hb.2.1, by
    have := hpref.length_le
    have := hb.2.2.1
    omega, hpref.trans hb.2.2.2⟩
theorem chainPiece_steps (p : ChainPiece) (hlink : sliceChecked p.pc p.words = true)
    (hcheck : p.checked = true) (s : MachineState) (hpc : s.pc = pcOf p.pc)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) :
    Steps Frozen.image s p.result.steps p.result.cycles (p.result.toState s) := by
  exact symRun_sound (rOK_eq hcheck) (slice_at p.pc p.words hlink) s hpc
    ((Oblig.all_iff s _).mpr hob)
theorem chainPiece_ecall (p : ChainPiece) (hlink : sliceChecked p.pc p.words = true)
    (hcheck : p.checked = true) (s : MachineState)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) (hstop : p.result.stop = .ecall) :
    SigGolfCandidate.Legacy.Riscv.fetch Frozen.image (p.result.toState s) =
      some (.base .ECALL) := by
  exact symRun_ecall (rOK_eq hcheck) (slice_at p.pc p.words hlink) s
    ((Oblig.all_iff s _).mpr hob) hstop
end W9Machine
