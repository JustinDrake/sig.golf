import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.T3.Secc.WotsExtractChain

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
def PosSource : Extract.Pos → Prop
  | .chain lay tree leaf i step => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay ∧ i < chainCount lay ∧ step + 1 < 2 ^ width lay i
  | .leaf lay tree leaf => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay
  | .node lay tree level node => tree < 2 ^ 31 ∧ level < height lay ∧ node < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 31
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 7 ∧ step < 3
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
def StructuralHitSrc (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ PosSource position ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
theorem StructuralHitSrc.toStructuralHit {answers : Answers} {trace : List Entry}
    (h : StructuralHitSrc answers trace) : StructuralHit answers trace := by
  obtain ⟨position, input, answer, hm, hpos, hb, -, hc, hh⟩ := h
  exact ⟨position, input, answer, hm, hpos, hb, hc, hh⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
