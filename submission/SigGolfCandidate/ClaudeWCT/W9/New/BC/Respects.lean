import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Rows
import SigGolfCandidate.T3.Secc.WotsTransportShort

namespace ClaudeWCT.W9.T3.Security.Wots.Mask
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
theorem untouched_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Untouched a (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)))) :=
  untouched_of_hdr a _ (header 4 lay.val tree 0 leaf)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _))
theorem untouched_layerEncodingP (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : BitVec 96) :
    Untouched a (.inl (.inr (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg counter pad)))) :=
  untouched_of_hdr a _ (header 4 lay.val tree 0 leaf)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _))
theorem respects_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Respects (Untouched a) (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter)) :=
  Respects.shortHash _ (untouched_layerEncoding a lay tree leaf msg counter)
theorem respects_layerCounterSearch (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, Respects (Untouched a) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine Respects.bind (respects_layerEncoding a _ _ _ _ _) fun answer => ?_
      split
      · exact ih _
      · exact Respects.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Mask
namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
theorem layerCounterSearch_respects (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    ShortRespects (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      refine ShortRespects.bind (ShortRespects.shortHash _ ?_) fun answer => ?_
      · rw [← ClaudeWCT.W9.T3M.BC.layerEncodingInputP_zero, ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact ih _
        · exact ShortRespects.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Ref
