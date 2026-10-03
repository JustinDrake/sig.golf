import SigGolfCandidate.T3M.Verify.Compose

/-! The complete verifier bound from the organizer's initial state.
The packed-chain accepting bound is `2639 + 6 + 5790 = 8435` cycles.
Layer costs are 1280 / 1261 / 1262 / 1191 for layers 3..0, with Merkle costs
168 / 168 / 181 / 271 and comparison cost 8. The all-input cycle bound remains
15425 and fuel 15418; `6 + lFuel 4 ≤ 8050` retains the existing post-forest allowance. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

/-- The cycle bound of accepting runs: 2639 through the forest HASH, the layer-3 load block (6) and `lCyc 4` for
the layers and the compare. -/
def cycleBound : Nat := 2639 + 6 + lCyc 4

/-- A cycle bound of every run under every oracle. -/
def cycleBoundAll : Nat := 7375 + 8050

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 7368 + 8050

theorem cycleBound_eq : cycleBound = 8435 := by unfold cycleBound; rw [lCyc_4]
theorem cycleBoundAll_eq : cycleBoundAll = 15425 := rfl
theorem fuelBound_eq : fuelBound = 15418 := rfl

/-- **The whole verify run** from the organizer's initial state. -/
theorem verify_good (input : Legacy.Input submission.sizes .verify) (s : MachineState)
    (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (verifyP input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  rw [fuelBound_eq, cycleBoundAll_eq, cycleBound_eq]
  exact verifyP_good m pk w s (init_ok m pk w s hs)

end SigGolfCandidate.T3M
