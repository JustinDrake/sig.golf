import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge
import SigGolfCandidate.T3.Secc.WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (a : ChainAddr)
variable {T T' : Answers} (hT : ∀ q, Untouched a q → T q = T' q)
include hT
theorem honestForest_congr (index : Nat) : Extract.honestForest T index = Extract.honestForest T' index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr (fun _ hq => hT _ (ClaudeWCT.WCT9.Wots.ftsQuery_untouched a hq))
theorem leafMsg_congr : leafMsg T a.key = leafMsg T' a.key := by
  unfold leafMsg
  split
  · rename_i h
    unfold Extract.honestRoot
    rw [builtTree_congr_of_lay a hT (fun he => by
      have := congrArg Fin.val he
      simp only at this
      omega)]
  · exact honestForest_congr a hT _
theorem referenceSearch_congr : referenceSearch T a.key = referenceSearch T' a.key := by
  unfold referenceSearch
  rw [leafMsg_congr a hT]
  exact (respects_counterSearch a _ _ _ _ _ _).eval_eq hT
end Mask
theorem depth_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, Mask.Untouched a q → T q = T' q) :
    depth T a = depth T' a := by
  unfold depth referenceDigits
  rw [Mask.referenceSearch_congr a hT]
theorem referenceDigits_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, Mask.Untouched a q → T q = T' q) :
    referenceDigits T a.key = referenceDigits T' a.key := by
  unfold referenceDigits
  rw [Mask.referenceSearch_congr a hT]
end ClaudeWCT.W9.T3.Security.Wots
