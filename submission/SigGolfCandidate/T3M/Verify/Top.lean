import SigGolfCandidate.T3M.Verify.Compose

/-! The complete verifier bound from the organizer's initial state.
Accepting runs cost at most 2675 + 6 + 6068 = 8749 cycles (n3-99 relabelled FTS: 2791 → 2676; digest header cut
2676 → 2675; lower-layer cuts and the T3X WOTS header table with T3Y one-`lui` entry stubs: layers
1338 / 1321 / 1321 / 1290 for layers 3..0 (top: cryptogakusei's complemented decoder tail, −2), Merkle 168 / 168 / 181 / 273 for layers 3..0 after the BIG2 header
word-0 merge, compare 8). The all-input
cycle bound is 15425 and the fuel 15418 (`6 + lFuel 4 = 8050` after the forest). -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

/-- The cycle bound of accepting runs: V2's 2675 through the forest HASH, the layer-3 load block (6) and `lCyc 4` for
the layers and the compare. -/
def cycleBound : Nat := 2675 + 6 + lCyc 4

/-- A cycle bound of every run under every oracle. -/
def cycleBoundAll : Nat := 7375 + 8050

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 7368 + 8050

theorem cycleBound_eq : cycleBound = 8749 := by unfold cycleBound; rw [lCyc_4]
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
