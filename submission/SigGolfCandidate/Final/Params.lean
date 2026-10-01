/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound after fifteen leaf-offset instruction eliminations,
three static root-header loads, one retained top-layer base, and the exact structural
PORS segment credit. Query formatting is an injective global relabel. The top-4-bit selector
with targets [185,185,185,185,186] (layer-4 target set in the root tail) saves eighteen further
cycles. -/
def verifyCycleBound : Nat := 10339

/-- The witness charge `⌈16384 / 256⌉`. -/
def witnessCharge : Nat := 64

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
