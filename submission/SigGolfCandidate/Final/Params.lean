/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of every accepting verify run (`Verify.cycleBound`: `2908` for the
prologue, digest, setup and PORS, plus `layersCost 5 = 7647`; the feasible worst case is `10554`). -/
def verifyCycleBound : Nat := 10555

/-- The witness charge `⌈16128 / 256⌉` (W1: `rho` and the PORS secrets in layer 0's tweak slots,
the witness buffer `0x900 .. 0x4800`). -/
def witnessCharge : Nat := 63

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
