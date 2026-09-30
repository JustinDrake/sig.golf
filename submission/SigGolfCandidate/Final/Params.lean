/-!
# Iteration parameters

The only numbers that change between optimization iterations of the submission: the proved
bound on accepting verify runs' RISC-V cycles and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of accepting verify runs. -/
def verifyCycleBound : Nat := 11605

/-- The witness charge `⌈6348 / 256⌉`. -/
def witnessCharge : Nat := 25

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
