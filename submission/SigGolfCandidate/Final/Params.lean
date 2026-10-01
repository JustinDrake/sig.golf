/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound from the exact verifier simulation. The mixed
185/186 layer targets save eighteen chain cycles and retain one zero checksum correction; the relabelled PORS
headers (`Ref.Rev.efield`) fold with one `slliw` (`-117`) for a header-table load per leaf (`+30`) and the
table constants (`+4`). Sparse-stream initialization adds one instruction. -/
def verifyCycleBound : Nat := 10359

/-- The witness charge `⌈14080 / 256⌉`; sparse PORS stream in unused tweak slots,
with the external witness buffer `0x1100 .. 0x4800`. -/
def witnessCharge : Nat := 55

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
