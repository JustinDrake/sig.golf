import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Encode
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic

namespace ClaudeWCT.W9.T3M.WctExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
def HonestQ (answers : Answers) (N : HashOutput) (c : WCT9.Coord) (q : Spec.Domain) : Prop :=
  (∃ t : Fin 7, ∃ s, 3 - WCT9.digit (WCT9.rank N c) t ≤ s ∧ s < 3 ∧
      q = .inl (.inr (Extract.honestInput answers
        (.wctChain (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val s)))) ∨
    q = .inl (.inr (Extract.honestInput answers (.wctLeaf (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val))) ∨
    ∃ l, l < 6 ∧ q = .inl (.inr (Extract.honestInput answers
      (.wctNode (N.toNat % 2 ^ 31) c.val l ((WCT9.child N c).val / 2 ^ (l + 1)))))
def CoordHonest (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord) : Prop :=
  (∀ t : Fin 7, wreveal w c.val t.val (WCT9.digit (WCT9.rank N c) t) =
      Extract.wctValue answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val
        (3 - WCT9.digit (WCT9.rank N c) t) ∧
    (0 < WCT9.digit (WCT9.rank N c) t →
      wcpads w c.val t.val = (0, 0) ∧ wcHeaderPad w c.val t.val = 0)) ∧
  (∀ l, l < 7 → wsib w c.val (WCT9.child N c).val l =
      treeValue (Extract.ftsLevels answers (N.toNat % 2 ^ 31) c.val) l ((WCT9.child N c).val / 2 ^ l ^^^ 1) ∧
    (l < 6 → wmpad w c.val l = 0))
def WctHonest (answers : Answers) (N : HashOutput) (w : WBytes) : Prop :=
  (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
      q = .inl (.inr (Extract.honestInput answers (.forest (N.toNat % 2 ^ 31)))) ∨
      ∃ c : WCT9.Coord, HonestQ answers N c q) ∧
    ∀ c : WCT9.Coord, CoordHonest answers N w c
end ClaudeWCT.W9.T3M.WctExtract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafValue)
def msgFits (lay : Layer) : WCT9.LayerMsg → Prop
  | .forest _ => lay.val = 3
  | .pair _ _ => lay.val < 3
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  (∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay j = 0)) ∧
  (∀ i, i < chainCount lay →
    wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i →
        wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0))
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) (digits : List Nat) :
    Prop :=
  (wbcCtr w lay).toNat < counterLimit ∧
    decode lay (evalWithAnswerFn answers (shortHash (layerEncodingInputP lay (route index lay).2 (route index lay).1
      msg (wbcCtr w lay) (wbcPad w lay)))) = some digits
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) : Spec.Domain :=
  .inl (.inr (pad64 (layerEncodingInputP lay (route index lay).2 (route index lay).1 msg (wbcCtr w lay) (wbcPad w lay))))
def Good (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∃ digits, Frame answers w index lay (honestMsg answers index lay) digits ∧ LayerShaped answers w index lay digits
def Diverge (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (qs : List Spec.Domain) : Prop :=
  ∃ msg digits, msgFits lay msg ∧ msg ≠ honestMsg answers index lay ∧ Frame answers w index lay msg digits ∧
    LayerShaped answers w index lay digits ∧ encodingQuery w index lay msg ∈ qs
end ClaudeWCT.W9.T3M.Extract
