import SigGolfCandidate.T3.BPORS
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
structure LeafAddr where
  lay : Layer
  tree : Nat
  leaf : Nat
  deriving DecidableEq
structure ChainAddr where
  key : LeafAddr
  chain : Nat
  deriving DecidableEq
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : (Digest × BitVec 96 × Digest) :=
  if h : L.lay.val < 3 then Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)
  else (Extract.honestForest answers (L.tree * 2 ^ height L.lay + L.leaf), 0, 0)
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (counterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 counterLimit)
def dummyDigits (lay : Layer) : List Nat :=
  if lay.val = 0 then List.replicate 31 4 ++ [2] ++ List.replicate 22 0
  else List.replicate 22 5 ++ List.replicate 20 4 ++ [if lay=3 then 4 else 5]
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
    (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def chainRow (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  chainInput a.key.lay a.key.tree a.key.leaf a.chain step value
abbrev Entry := HashInput × HashOutput
def low (output : HashOutput) : Digest := output.extractLsb' 0 128
def SeenRow (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ low answer = out
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRow trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRow trace a (depth answers a - 2) start middle ∧
    SeenRow trace a (depth answers a - 1) middle (frontierValue answers a)
def encodingRow (L : LeafAddr) (message : Digest × BitVec 96 × Digest) (counter : BitVec 32) : HashInput :=
  pad64 (encodingInput L.lay L.tree L.leaf message counter)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encodingRow L (leafMsg answers L) selected.1
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter answer, (encodingRow L message counter, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encodingRow L message counter) ∧
    decode L.lay (low answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter answer digits, (encodingRow a.key message counter, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encodingRow a.key message counter) ∧
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
def entriesOf (answers : Answers) (qs : List Spec.Domain) : List Entry :=
  qs.filterMap fun q => match q with
    | .inl (.inr input) => some (input, answers (.inl (.inr input)))
    | _ => none
def VerifierWots (answers : Answers) (publicKey : Digest) (forgery : Final.ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitive answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
def VerifierAllGood (answers : Answers) (publicKey : Digest) (forgery : Final.ForgeryP) : Prop :=
  ∃ message witness N, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = N ∧
    (∀ l : Layer, Extract.Good answers witness (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N witness
end SigGolfCandidate.T3.Security.Wots
