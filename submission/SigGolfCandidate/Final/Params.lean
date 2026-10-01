/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound from the exact verifier simulation. The uniform
185 layer targets and checked two-fold PORS prefixes are included in the bound. -/
def verifyCycleBound : Nat := 10429

/-- The witness charge `⌈16128 / 256⌉` (W1: `rho` and the PORS secrets in layer 0's tweak slots,
the witness buffer `0x900 .. 0x4800`). -/
def witnessCharge : Nat := 63

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
