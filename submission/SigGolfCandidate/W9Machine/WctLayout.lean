import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Witness.Layout

set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
structure Layout where
  image : Image
  chainWord : Fin 728 → Nat
  childWord : Fin 128 → Nat
  returnWord : Fin 9 → Nat
def GoodQFor (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
structure Budget where
  fuel : Nat
  allCycles : Nat
  acceptCycles : Nat
def layerEntryWord : Nat := 588
def layerWitnessOffset : Nat := 9288
def forestRootAddress : Nat := 0x100
def coordinateBase (k : Fin 9) : Nat := 2112 + 1024 * k.val
def headerTable (k : Fin 9) : Nat := 0xfee600 + 512 * k.val
def pairAddress (k : Fin 9) : Nat := 0x420 + 32 * k.val
end W9Machine
