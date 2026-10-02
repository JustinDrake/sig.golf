import SigGolfCandidate.T3M.Verify.Compose

/-! # V3: the verify bounds and the whole run from the organizer's initial state

The bounds are derived from the per-family costs (`Compose`):
* **`cycleBound = 2836 + 6 + lCyc 4 = 9023`** (accepting runs): V2's words 0..358 and FTS through the forest HASH
  (`128 + P + 3 + 879 + 15 F ≤ 2836`, `P ≤ 56`, `F ≤ 118`), T3K's layer-3 load block (6), V1's four layers to `LeafOut`
  (`layerCost lay 0` = 1365 / 1356 / 1356 / 1274), V3's Merkle phases (`mkCyc` = 172 / 172 / 186 / 292) and the
  compare (8);
* `cycleBoundAll = 7375 + 7999 = 15374` (every run, every oracle; V2's interface uses the layers' bound
  `7999 ≥ 6 + lFuel 4` as their all-path cycle bound), `fuelBound = 7368 + 7999 = 15367` (steps).

`verify_good`: from `initialState submission .verify input`, `GoodQ s fuelBound cycleBoundAll True cycleBound
(ccM (verifyP m pk w) Kb)`. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

/-- The cycle bound of accepting runs: V2's 2836 through the forest HASH, the layer-3 load block (6) and `lCyc 4` for
the layers and the compare. -/
def cycleBound : Nat := 2836 + 6 + lCyc 4

/-- A cycle bound of every run under every oracle. -/
def cycleBoundAll : Nat := 7375 + 7999

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 7368 + 7999

theorem cycleBound_eq : cycleBound = 9023 := by unfold cycleBound; rw [lCyc_4]
theorem cycleBoundAll_eq : cycleBoundAll = 15374 := rfl
theorem fuelBound_eq : fuelBound = 15367 := rfl

/-- **The whole verify run** from the organizer's initial state. -/
theorem verify_good (input : Legacy.Input submission.sizes .verify) (s : MachineState)
    (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (verifyP input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  rw [fuelBound_eq, cycleBoundAll_eq, cycleBound_eq]
  exact verifyP_good m pk w s (init_ok m pk w s hs)

end SigGolfCandidate.T3M
