import SigGolfCandidate.T3M.Verify.CanonicalBlocks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
namespace SigGolfCandidate.T3M.CanonicalNative
theorem blocks_checked_3 : ∀ i : Fin 6, checkGeom (18+i.val)=true := by decide +kernel
end SigGolfCandidate.T3M.CanonicalNative
