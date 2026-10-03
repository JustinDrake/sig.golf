import SigGolfCandidate.T3M.Verify.Compose

/-! The complete verifier bound from the organizer's initial state.
Accepting runs cost at most 2716 + 5 + 6091 = 8812 cycles (T3X: the lower layers' WOTS header table). The
conservative all-input cycle bound 15431 and fuel 15424 are retained. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

/-- The cycle bound of accepting runs: V2's 2716 through the forest HASH, the layer-3 load block (5) and `lCyc 4` for
the layers and the compare. -/
def cycleBound : Nat := 2716 + 5 + lCyc 4

/-- A cycle bound of every run under every oracle. -/
def cycleBoundAll : Nat := 7384 + 8047

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 7377 + 8047

theorem cycleBound_eq : cycleBound = 8812 := by unfold cycleBound; rw [lCyc_4]
theorem cycleBoundAll_eq : cycleBoundAll = 15431 := rfl
theorem fuelBound_eq : fuelBound = 15424 := rfl

/-- **The whole verify run** from the organizer's initial state. -/
theorem verify_good (input : Legacy.Input submission.sizes .verify) (s : MachineState)
    (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (verifyP input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  rw [fuelBound_eq, cycleBoundAll_eq, cycleBound_eq]
  exact verifyP_good m pk w s (init_ok m pk w s hs)

end SigGolfCandidate.T3M
