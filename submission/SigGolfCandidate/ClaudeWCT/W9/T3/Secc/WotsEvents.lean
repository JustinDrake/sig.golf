import SigGolfCandidate.ClaudeWCT.W9.T3.BPORS
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.PaddedWitness
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : WCT9.LayerMsg :=
  if h : L.lay.val < 3 then
    .pair (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).1
      (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).2
  else .forest (Extract.honestForest answers ((L.tree * 2 ^ height L.lay + L.leaf) % 2 ^ 31))
theorem msgFits_leafMsg (answers : Answers) (L : LeafAddr) : Extract.msgFits L.lay (leafMsg answers L) := by
  unfold leafMsg
  split_ifs with h
  · exact h
  · show L.lay.val = 3
    have := L.lay.isLt
    omega
def encRow (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96) : HashInput :=
  pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad)
theorem encRow_zero (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    encRow L msg counter 0 = pad64 (WCT9.layerEncodingInput L.lay L.tree L.leaf msg counter) := by
  unfold encRow
  cases msg <;> rfl
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (WCT9.layerCounterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 counterLimit)
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
    (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRow trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRow trace a (depth answers a - 2) start middle ∧
    SeenRow trace a (depth answers a - 1) middle (frontierValue answers a)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encRow L (leafMsg answers L) selected.1 0
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter pad answer, Extract.msgFits L.lay message ∧ (encRow L message counter pad, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encRow L message counter pad) ∧
    decode L.lay (low answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encRow a.key message counter pad) ∧
    decode a.key.lay (low answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0
def OtherChainRow (answers : Answers) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step)
def StructuralClass (answers : Answers) (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers input
  | _ => True
def StructuralHit (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
def WotsPrimitive (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, EncodingMatchAt answers trace L) ∨ StructuralHit answers trace ∨
    (∃ a, TwoEdgeAt answers trace a) ∨
    (∃ a b, a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, MarkerAt answers trace a ∧ ContactAt answers trace a)
def VerifierWots (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitive answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
end ClaudeWCT.W9.T3.Security.Wots
