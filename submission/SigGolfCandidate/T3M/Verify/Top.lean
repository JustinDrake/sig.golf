import SigGolfCandidate.T3M.Verify.Compose

/-! The complete verifier bound from the organizer's initial state.
Accepting runs cost at most 2666 + 4 + 5953 = 8623 cycles (BIG6 E1: 34297362's top decoder mask reuse and `x24`-based
prologue, top layer 1236 → 1234; BIG6 E2: layer 3 reuses `t1, s10, t6, s8` from 34297362's forest register
permutation, 1317 → 1313) (BIG5: be9ec77f's reversed-label forest with three checked
side bits 2667, our digest header cut −1 → 2666; layer-3 load block 6 → 4 (no `lui sp`, no dead `2^40` load);
layer 3 reuses the four constants carried from the forest, −4) (n3-99 relabelled FTS: 2791 → 2676; digest header cut
2676 → 2675; lower-layer cuts and the T3X WOTS header table with T3Y one-`lui` entry stubs: layers
1313 / 1304 / 1304 / 1234 for layers 3..0 (lower: 745a58d5 table-slot heads land on their digit's `ecall`, −15 each;
0c30a009 inline entry stub and leaf-pk return, −2 each;
top: cryptogakusei's complemented decoder tail, −2; BIG3 T3Z header-table heads, −54), Merkle 168 / 168 / 181 / 273 for layers 3..0 after the BIG2 header
word-0 merge, compare 8). The all-input
cycle bound is 15473 and the fuel 15466 (`4 + lFuel 4 ≤ 8050` after the forest). -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

/-- The cycle bound of accepting runs: V2's 2666 through the forest HASH, the layer-3 load block (4) and `lCyc 4` for
the layers and the compare. -/
def cycleBound : Nat := 2666 + 4 + lCyc 4

/-- A cycle bound of every run under every oracle. -/
def cycleBoundAll : Nat := 7423 + 8050

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 7416 + 8050

theorem cycleBound_eq : cycleBound = 8623 := by unfold cycleBound; rw [lCyc_4]
theorem cycleBoundAll_eq : cycleBoundAll = 15473 := rfl
theorem fuelBound_eq : fuelBound = 15466 := rfl

/-- **The whole verify run** from the organizer's initial state. -/
theorem verify_good (input : Legacy.Input submission.sizes .verify) (s : MachineState)
    (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (ccM (verifyP input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  rw [fuelBound_eq, cycleBoundAll_eq, cycleBound_eq]
  exact verifyP_good m pk w s (init_ok m pk w s hs)

end SigGolfCandidate.T3M
