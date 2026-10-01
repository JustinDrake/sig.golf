/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound from the exact verifier simulation. The four-instruction
conditional-half selector saves twenty cycles over the inherited bound. -/
def verifyCycleBound : Nat := 10496

/-- The witness charge `⌈16384 / 256⌉`. -/
def witnessCharge : Nat := 64

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
