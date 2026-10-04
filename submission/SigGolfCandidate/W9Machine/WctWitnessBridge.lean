import SigGolfCandidate.W9Machine.WctChainInvDefs
import SigGolfCandidate.T3M.Verify.ChainSem

set_option autoImplicit false
namespace W9Machine.Chain
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem Pre.origW {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u : MachineState} (h : Pre L w index k j rank u)
    (off : Nat) (ho : off < 1024) (ha : off % 8 = 0) : OrigW w u (base k + off) := by
  have he : base k + off - 0x800 = V3.regionOffset k.val + off := by
    simp only [base, coordinateBase, V3.regionOffset]
    omega
  simpa only [OrigW, he] using h.witness off ho ha
theorem inv_initial (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) (u : MachineState) (hu : Pre L w index k j rank u) :
    Inv u index k j {} [] u := by
  refine ⟨fun _ _ => rfl, Frame.refl _ _, ?_, rfl, fun _ => trivial, hu.hashLen, ?_⟩
  · intro off ho; rfl
  · intro h; simp at h
end W9Machine.Chain
