import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding
import SigGolfCandidate.ClaudeWCT.WCT9.Limits
import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.T3.Secc.WotsExtractWord

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr IsDigestRow)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeResidualT3 : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
abbrev Coord := CanonGraph.Node ⊕ CanonGraph.SecretIndex
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 4096 then some (.inl (.leaf ⟨lay, tree, ⟨c, h⟩⟩)) else none)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)
def wctItem (a : WctAddr) (p : Nat) : Coord :=
  if p = 0 then .inr (.inr a) else .inl (.wctChain (a, ⟨(p - 1) % 3, Nat.mod_lt _ (by decide)⟩))
def ftsChild (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 128 then some (.inl (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.wctNode n)
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, 3)]
  | .leaf L => (List.range (chainCount L.lay)).map fun i => (.inl (.chain (endPoint L i)), listBlock i)
  | .node n => ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .wctChain p => [(wctItem p.1 p.2.val, 3)]
  | .wctLeaf L => List.ofFn fun t : Fin 7 => (wctItem (L.index, L.coord, L.child, t) 3, listBlock t.val)
  | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .forest index => (List.range 9).map fun c => (.inl (.wctNode (ftsRootNode index (fin9 c))), listBlock c)
noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128
  | .inr s => secretsOf A s
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)
def keygenDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))
def wctOpened (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  List.ofFn fun t : Fin 7 => wctItem (index, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)
def wctPath (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  (List.range 7).filterMap fun l => ftsChild index k l ((WCT9.child N k).val / 2 ^ l ^^^ 1)
def ftsItems (index : Fin (2^31)) (N : HashOutput) : List Coord :=
  (List.finRange 9).flatMap fun k => wctOpened index k N ++ wctPath index k N
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) N ++ layerItems digitsOf (digestIndex N)
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N
def RouteOk (A : Answers) (index : Nat) : Prop := ∀ lay : Layer, (Wots.referenceSearch A (routeAddr index lay)).isSome
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (WCT9.digestSearch (evalWithAnswerFn A (privateNonce message)) message 0
    WCT9.digestAttemptLimit)
noncomputable def signDisclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (N.toNat % 2 ^ 31) then signItems A N else []
    | none => []
  else []
def msgCoord (L : EncLeaf) : Coord :=
  if h : L.1.lay.val < 3 then .inl (.node (rootNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L)))
  else .inl (.forest (childIndex L))
def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ N : CanonGraph.Node, Extract.posOf input = some N.toPos ∧
    ((∃ cs, firstUnknown K N = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (input ≠ Extract.honestInput A N.toPos ∧ answer.extractLsb' 0 128 = honestValue A (.inl N)))
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : Digest) (ctr : BitVec 32), input = Wots.encodingRow L.toWots m ctr ∧
    ((¬K (msgCoord L) ∧ m = honestValue A (msgCoord L)) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (answer.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))
def ContactTest (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  StructuralContact A K input answer ∨ EncodingContact A K input answer
end ClaudeWCT.W9.T3.Security.LargeResidual
