/-!
# Iteration parameters

The numeric parameters for the proved bound on accepting verification runs and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Upper bound on every accepting verify run, proved by `Verify.verify_accept_cycles_tight` at `Verify.cycleBound - 1`.
This is a proof bound; no exact-image accepting-run profile is claimed. -/
def verifyCycleBound : Nat := 10595

/-- The witness charge `⌈16384 / 256⌉`. -/
def witnessCharge : Nat := 64

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
