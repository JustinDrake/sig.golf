/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of every accepting verify run. -/
def verifyCycleBound : Nat := 11481

/-- The witness charge `⌈6348 / 256⌉`. -/
def witnessCharge : Nat := 25

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
