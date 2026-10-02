import SigGolfCandidate.T3.BPORS

/-!
# SECC shared WOTS vocabulary (BP-A §3; definitions only)

The honest reference word of every leaf (`referenceDigits`: the honest signer's counter search, or a fixed
valid dummy word when it fails), the frontier of every chain (`depth`, `frontierValue`), canonical rows, and the
five T3 primitive events of the small route (record `GraphPrimitiveEvent`): `EncodingMatchAt`,
`StructuralHit`, `TwoEdgeAt`, two `ContactAt`, `MarkerAt ∧ ContactAt`. Every object is a function of a complete
answers table (the completion of `SeccLaw.completedExperiment`). Streams W/F/C/E/S/A import this file; do not
redefine these names elsewhere.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)

/-- A WOTS key pair (one leaf of one hypertree tree). -/
structure LeafAddr where
  lay : Layer
  tree : Nat
  leaf : Nat
  deriving DecidableEq

/-- One chain of a WOTS key pair. -/
structure ChainAddr where
  key : LeafAddr
  chain : Nat
  deriving DecidableEq

/-- The honest message of a leaf: root of its child tree, or the forest pk at layer 3
(agrees with `Extract.honestMsg answers index lay` at `route index lay`). -/
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : Digest :=
  if h : L.lay.val < 3 then Extract.honestRoot answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)
  else Extract.honestForest answers (L.tree * 2 ^ height L.lay + L.leaf)

/-- The honest signer's counter search at a leaf (the reference selection). -/
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (counterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 counterLimit)

/-- A fixed valid word used when the honest search fails (the record's `dummy`; conservative).
Top layer: 49 radix-4 chains then 9 radix-8 chains, digit sum 126 (48·2 + 3 + 9·3). Lower layers: 42 radix-8
data digits summing to 190 (22·5 + 20·4) and the checksum digit `target − 190` (5 at layers 1, 2; 4 at layer 3).
Validity in `T3.code` is proved where it is used. -/
def dummyDigits (lay : Layer) : List Nat :=
  if lay.val = 0 then List.replicate 48 2 ++ [3] ++ List.replicate 9 3
  else List.replicate 22 5 ++ List.replicate 20 4 ++ [if lay.val = 3 then 4 else 5]

/-- The reference word of every leaf, signed or not (record: `referenceFamilyWords selections dummy`). -/
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)

/-- Frontier position (disclosure depth) of a chain. -/
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0

/-- Frontier value: the honest chain value at the frontier (the generic `endpoint`). -/
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
    (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)

/-- The canonical (zero-pad) chain row; `chainInput` is already 64 bytes. -/
def chainRow (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  chainInput a.key.lay a.key.tree a.key.leaf a.chain step value

/-- An observed (non-honest) query and its answer. -/
abbrev Entry := HashInput × HashOutput

def low (output : HashOutput) : Digest := output.extractLsb' 0 128

/-- The trace holds the canonical row `(a, step, value)` with low answer `out`. -/
def SeenRow (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ low answer = out

/-- Record `Contact`: a last-prefix-step row answering the frontier value. -/
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRow trace a (depth answers a - 1) value (frontierValue answers a)

/-- Record `TwoEdge` (`SeenTwoEdge`): two consecutive prefix rows ending at the frontier value. -/
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRow trace a (depth answers a - 2) start middle ∧
    SeenRow trace a (depth answers a - 1) middle (frontierValue answers a)

/-- An encoding row of a leaf. -/
def encodingRow (L : LeafAddr) (message : Digest) (counter : BitVec 32) : HashInput :=
  pad64 (encodingInput L.lay L.tree L.leaf message counter)

/-- The honest (selected) encoding input of a leaf, when the search succeeds. -/
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encodingRow L (leafMsg answers L) selected.1

/-- Record `EncodingOutputMatch`: a non-reference encoding row of `L` decoding to the reference word. -/
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter answer, (encodingRow L message counter, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encodingRow L message counter) ∧
    decode L.lay (low answer) = some (referenceDigits answers L)

/-- Record `EntryMarker`: a non-reference encoding row of the leaf of `a` decoding to a unit neighbor
of the reference word lowered at chain `a.chain` (stated on digit lists; 57 such words). -/
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter answer digits, (encodingRow a.key message counter, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encodingRow a.key message counter) ∧
    decode a.key.lay (low answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0

/-- Class "other" chain rows: padded rows, or canonical rows at or above the frontier. -/
def OtherChainRow (answers : Answers) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step)

/-- A query at a parsed position is an "other"-class (structural) query: not a canonical prefix row. -/
def StructuralClass (answers : Answers) (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers input
  | _ => True

/-- Record `ReferenceStructuralMatch.Seen` for T3: a header-preserving distinct-input hit of an
"other"-class query on the honest output at its parsed position. -/
def StructuralHit (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input

/-- The T3 primitive event (record `GraphPrimitiveEvent`): the union of the five events. -/
def WotsPrimitive (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, EncodingMatchAt answers trace L) ∨ StructuralHit answers trace ∨
    (∃ a, TwoEdgeAt answers trace a) ∨
    (∃ a b, a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, MarkerAt answers trace a ∧ ContactAt answers trace a)

/-- Public queries of a deterministic run with their answers. -/
def entriesOf (answers : Answers) (qs : List Spec.Domain) : List Entry :=
  qs.filterMap fun q => match q with
    | .inl (.inr input) => some (input, answers (.inl (.inr input)))
    | _ => none

/-- Case (A)+(B) of a forgery under a completion: its byte verification has a WOTS primitive event
among its own queries (stream W turns PEX's `Conclusion` alternatives (A)/(B) into this). -/
def VerifierWots (answers : Answers) (publicKey : Digest) (forgery : Final.ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitive answers (entriesOf answers (queried answers (verifyP message publicKey witness)))

/-- Case (C) of a forgery (SEC / BP-B): every layer `Good` and the FTS part honest-shaped. -/
def VerifierAllGood (answers : Answers) (publicKey : Digest) (forgery : Final.ForgeryP) : Prop :=
  ∃ message witness N, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = N ∧
    (∀ l : Layer, Extract.Good answers witness (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N witness


end SigGolfCandidate.T3.Security.Wots
