/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Universal accepting-run bound from the exact verifier simulation. The mixed
185/186 layer targets save eighteen chain cycles and retain one zero checksum correction; the relabelled PORS
headers (`Ref.Rev.efield`) fold with one `slliw` (`-117`) for a header-table load per leaf (`+30`) and the
table constants (`+4`). -/
def verifyCycleBound : Nat := 10358

/-- The witness charge `⌈15872 / 256⌉`: consumed lower-layer tweak slots hold
authentication paths, and the witness buffer is `0xa00 .. 0x4800`. -/
def witnessCharge : Nat := 62

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
