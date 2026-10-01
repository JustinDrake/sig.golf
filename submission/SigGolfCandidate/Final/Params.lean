/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound: the root-aware compressed-tree certificate gives
14 credits, including zero-fold segments and nonroot paths with at least three folds.
The exact bit-reversed prefix implementation therefore bounds the PORS segments by2322. -/
def verifyCycleBound : Nat := 10350

/-- The witness charge `⌈15872 / 256⌉`: consumed lower-layer tweak slots hold
authentication paths, and the witness buffer is `0xa00 .. 0x4800`. -/
def witnessCharge : Nat := 62

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
