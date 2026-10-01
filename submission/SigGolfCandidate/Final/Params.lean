/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of every accepting verify run (`Verify.cycleBound`: `2929` for the
prologue, digest, setup and PORS, plus `layersCost 5 = 7690`). -/
def verifyCycleBound : Nat := 10619

/-- The witness charge `⌈16384 / 256⌉`. -/
def witnessCharge : Nat := 64

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
