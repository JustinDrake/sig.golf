import SigGolfCandidate.SphincsSecurity.Compat
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 181
def numLayers : Nat := 5
def totalHeight : Nat := 34
def maxLayerHeight : Nat := 11
def ftsTreeHeight : Nat := 14
def ftsOpenings : Nat := 15
def ftsAuthCapacity : Nat := 118
def ftsSegments : Nat := 2 * ftsOpenings - 1
def signatureLimit : Nat := 2 ^ 32
def digestAttemptLimit : Nat := 2 ^ 20
def encodingAttemptLimit : Nat := 2 ^ 22
abbrev MasterSeed := BitVec 256
abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
abbrev Index := Fin (2 ^ totalHeight)
abbrev TreeIndex := Fin (2 ^ totalHeight)
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev FtsTree := Fin 1
abbrev IndexGroup := Fin ftsOpenings
abbrev SlotCode := Fin (ftsOpenings + 1)
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8
abbrev ChainPair := Fin (numChains / 2)
abbrev FtsPair := Fin (2 ^ (ftsTreeHeight - 1))
def evenChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; unfold numChains at *; omega⟩
def oddChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; unfold numChains at *; omega⟩
def chainPairOf (chainIdx : ChainIndex) : ChainPair := ⟨chainIdx.val / 2, by have := chainIdx.isLt; unfold numChains at *; omega⟩
def evenFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
def oddFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val + 1, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
def ftsPairOf (leaf : FtsLeaf) : FtsPair := ⟨leaf.val / 2, by have := leaf.isLt; unfold ftsTreeHeight at *; omega⟩
def unpairChains {α : Type} (pairs : ChainPair → α × α) (chainIdx : ChainIndex) : α :=
  if chainIdx.val % 2 = 0 then (pairs (chainPairOf chainIdx)).1 else (pairs (chainPairOf chainIdx)).2
def unpairFtsLeaves {α : Type} (pairs : FtsPair → α × α) (leaf : FtsLeaf) : α :=
  if leaf.val % 2 = 0 then (pairs (ftsPairOf leaf)).1 else (pairs (ftsPairOf leaf)).2
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else if lay.val < 4 then 6 else 5
def topLayer : Layer := ⟨0, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits
def messageDigestBits : Nat := hashOutputBits
abbrev MessageDigest := BitVec messageDigestBits
def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq
structure Segment where
  folds : Fin 16
  merge : Bool
  parity : Bool
  nodes : Fin folds.val → Digest
  parity_normal : folds.val = 0 → parity = false
deriving DecidableEq
def Segment.normalized (folds : Fin 16) (merge parity : Bool) (nodes : Fin folds.val → Digest) : Segment :=
  ⟨folds, merge, parity && decide (folds.val ≠ 0), nodes, fun h => by simp [h]⟩
instance : Inhabited Segment := ⟨⟨0, false, false, fun index => index.elim0, fun _ => rfl⟩⟩
def Segment.node (segment : Segment) (i : Nat) : Digest :=
  if h : i < segment.folds.val then segment.nodes ⟨i, h⟩ else 0
structure FtsSignature where
  perm : Fin ftsOpenings → SlotCode
  secrets : Fin ftsOpenings → Digest
  segments : Fin ftsSegments → Segment
deriving DecidableEq
structure Signature where
  randomness : Randomness
  fts : FtsSignature
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)
structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 40
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq
def protocolDomainSep : UInt8 := 1
def fieldBytes (fields : TweakFields) : HashInput :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++
    bytesLE 1 (fields.tree.extractLsb' 32 8) ++
    bytesLE 4 fields.position ++ bytesLE 4 (fields.tree.extractLsb' 0 32) ++ bytesLE 4 fields.index
def tweakFields (tag layer tree position index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 8 layer, BitVec.ofNat 40 tree,
    BitVec.ofNat 32 position, BitVec.ofNat 32 index⟩
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : Nat)
  | ftsNode (index : Index) (tree : FtsTree) (heapIdx : Nat)
  | message
deriving DecidableEq
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => tweakFields 1 lay tree (chainLength * chainIdx + step) leaf
  | .leaf lay tree leaf => tweakFields 2 lay tree 0 leaf
  | .node lay tree level nodeIdx => tweakFields 3 lay tree level nodeIdx
  | .encoding lay tree leaf => tweakFields 4 lay tree 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 tree index 0 leaf
  | .ftsNode index tree heapIdx => tweakFields 10 tree index 0 heapIdx
  | .message => tweakFields 12 0 0 0 0
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : HashInput :=
  [1,7] ++ bytesLE 26 (seed.extractLsb' 0 208) ++ bytesLE 32 message ++ bytesLE 4 trial
inductive KeygenDomain where
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | fts (index : Index) (tree : FtsTree) (pair : FtsPair)
  | mask (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ maxLayerHeight))
deriving DecidableEq
def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf pair => tweakFields 0 lay tree pair leaf
  | .fts index tree pair => tweakFields 8 tree index 0 pair
  | .mask level nodeIdx => tweakFields 13 0 0 level nodeIdx
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed
abbrev TopRegion := (level : Fin maxLayerHeight) → Fin (2 ^ (maxLayerHeight - level.val)) → Digest
structure TopCache where
  tag : HashOutput
  region : TopRegion
deriving DecidableEq
def TopCache.node (cache : TopCache) (level nodeIdx : Nat) : Digest :=
  if hlevel : level < maxLayerHeight then
    if hnode : nodeIdx < 2 ^ (maxLayerHeight - level) then cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnode⟩
    else 0
  else 0
def regionBytes (region : TopRegion) : HashInput :=
  (List.ofFn fun level : Fin maxLayerHeight => (List.ofFn (region level)).flatMap (bytesLE 16)).flatten
def macHashInput (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) : HashInput :=
  fieldBytes ⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ ++ bytesLE 16 parameter ++ bytesLE 32 seed ++ regionBytes region
namespace TargetSum
def sum (x : Encoding) : Nat := ∑ i, (x i).val
def Valid (x : Encoding) : Prop := sum x = targetSum
instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))
def digitsPerHalf : Nat := numChains / 2
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none
end TargetSum
abbrev HashSpec := HashInput →ₒ HashOutput
abbrev OracleWorld := unifSpec + HashSpec
namespace Concrete
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by
      unfold layerHeight maxLayerHeight; split <;> (try split) <;> omega))⟩
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)
def porsTree : FtsTree := ⟨0, by decide⟩
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def ftsHeapIndex (level nodeIdx : Nat) : Nat := 2 ^ (ftsTreeHeight - level) + nodeIdx
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : Nat)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)
def foldPayload (right : Bool) (sibling current : Digest) : HashInput :=
  if right then nodePayload sibling current else nodePayload current sibling
def foldSegment (parameter : PublicParameter) (index : Index) (segment : Segment) :
    Nat → Nat → Digest → Nat → m (Digest × Nat)
  | 0, _, current, heap => pure (current, heap)
  | remaining + 1, position, current, heap => do
      let right := if position = 0 then segment.parity else decide (heap % 2 = 1)
      let parent ← tweakableHash parameter (.ftsNode index porsTree (heap / 2))
        (foldPayload right (segment.node position) current)
      foldSegment parameter index segment remaining (position + 1) parent (heap / 2)
inductive PendingHash where
  | leaf (value : Nat) (secret : Digest)
  | merge (heapIdx : Nat) (left : Digest)
structure RecoverState where
  node : Digest
  heap : Nat
  stack : List (Digest × Nat)
  folds : Nat
  segment : Nat
def RecoverState.initial : RecoverState := ⟨0, 0, [], 0, 0⟩
def recoverSegments (parameter : PublicParameter) (index : Index) (segments : Fin ftsSegments → Segment) :
    Nat → PendingHash → RecoverState → m (Option RecoverState)
  | 0, _, _ => pure none
  | fuel + 1, pending, state => do
      if hsegment : state.segment < ftsSegments then
        let segment := segments ⟨state.segment, hsegment⟩
        if ftsTreeHeight < segment.folds.val then
          return none
        else if segment.folds.val ≠ 0 ∧ segment.parity ≠ decide (state.heap % 2 = 1) then
          return none
        else
          let start ← match pending with
            | .leaf value secret => ftsLeafHash parameter index porsTree value secret
            | .merge heapIdx left =>
                tweakableHash parameter (.ftsNode index porsTree heapIdx) (nodePayload left state.node)
          let (node, heap) ← foldSegment parameter index segment segment.folds.val 0 start state.heap
          let state : RecoverState :=
            { state with node := node, heap := heap, folds := state.folds + segment.folds.val,
                         segment := state.segment + 1 }
          if segment.merge then
            match state.stack with
            | [] => return none
            | (left, sibling) :: rest =>
                if sibling = heap then
                  recoverSegments parameter index segments fuel (.merge (heap / 2) left)
                    { state with stack := rest, heap := heap / 2 }
                else
                  return none
          else
            return some state
      else
        return none
def recoverLeaves (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : Nat → Nat → Nat → RecoverState → m (Option RecoverState)
  | 0, _, _, state => pure (some state)
  | remaining + 1, position, previous, state => do
      if hposition : position < ftsOpenings then
        let value := values (fts.perm ⟨position, hposition⟩)
        if 0 < position ∧ ¬ previous < value then
          return none
        else if position + 1 = ftsOpenings ∧ ¬ value < 2 ^ ftsTreeHeight then
          return none
        else
          let some state ← recoverSegments parameter index fts.segments ftsSegments
              (.leaf value (fts.secrets ⟨position, hposition⟩))
              { state with heap := 2 ^ ftsTreeHeight ||| value }
            | return none
          let state := if position + 1 < ftsOpenings then
              { state with stack := (state.node, state.heap ^^^ 1) :: state.stack } else state
          recoverLeaves parameter index values fts remaining (position + 1) value state
      else
        return none
def ftsRecover (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : m (Option Digest) := do
  let some state ← recoverLeaves parameter index values fts ftsOpenings 0 0 RecoverState.initial
    | return none
  if state.folds ≤ ftsAuthCapacity ∧ state.heap = 1 ∧ state.stack = [] then
    return some state.node
  else
    return none
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 (0 : Digest) ++ bytesLE 32 message
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun slot => (digest.extractLsb' (totalHeight + ftsTreeHeight * slot.val) ftsTreeHeight).toFin
def slotValue (leaves : IndexGroup → FtsLeaf) (code : SlotCode) : Nat :=
  if h : code.val < ftsOpenings then (leaves ⟨code.val, h⟩).val else 2 ^ ftsTreeHeight
def bitLength (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def octopusSize (sorted : List Nat) : Nat :=
  ftsTreeHeight + 2 + (List.zipWith (fun a b => bitLength (a ^^^ b)) sorted sorted.tail).sum -
    2 * sorted.length
def sortedSlots (leaves : IndexGroup → FtsLeaf) : List IndexGroup :=
  (List.finRange ftsOpenings).insertionSort fun r r' => (leaves r).val ≤ (leaves r').val
def sortedLeaves (leaves : IndexGroup → FtsLeaf) : List Nat :=
  (sortedSlots leaves).map fun r => (leaves r).val
def AdmissibleLeaves (leaves : IndexGroup → FtsLeaf) : Prop :=
  Function.Injective leaves ∧ octopusSize (sortedLeaves leaves) ≤ ftsAuthCapacity
instance (leaves : IndexGroup → FtsLeaf) : Decidable (AdmissibleLeaves leaves) :=
  inferInstanceAs (Decidable (Function.Injective leaves ∧ _))
def Admissible (digest : MessageDigest) : Prop := AdmissibleLeaves (digestLeaves digest)
instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (AdmissibleLeaves (digestLeaves digest)))
structure ScheduleSegment where
  merge : Bool
  parity : Bool
  reads : List (Nat × Nat)
deriving DecidableEq, Inhabited
structure ScheduleState where
  done : List ScheduleSegment
  stack : List Nat
  heap : Nat
  parity : Bool
  reads : List (Nat × Nat)
def scheduleStep (state : ScheduleState) (height : Nat) : ScheduleState :=
  let fold : ScheduleState :=
    { state with reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
                 heap := state.heap / 2 }
  match state.stack with
  | top :: rest =>
      if top = state.heap then
        { state with done := state.done ++ [⟨true, state.parity, state.reads⟩], stack := rest,
                     heap := state.heap / 2, parity := decide (state.heap / 2 % 2 = 1), reads := [] }
      else fold
  | [] => fold
def scheduleLeaves : List Nat → ScheduleState → ScheduleState
  | [], state => state
  | v :: rest, state =>
      let heap := 2 ^ ftsTreeHeight ||| v
      let top := match rest with
        | [] => ftsTreeHeight
        | w :: _ => bitLength (v ^^^ w) - 1
      let state := (List.range top).foldl scheduleStep
        { state with heap := heap, parity := decide (heap % 2 = 1), reads := [] }
      let state := { state with done := state.done ++ [⟨false, state.parity, state.reads⟩] }
      scheduleLeaves rest (match rest with
        | [] => state
        | _ :: _ => { state with stack := (state.heap ^^^ 1) :: state.stack })
def schedule (sorted : List Nat) : List ScheduleSegment :=
  (scheduleLeaves sorted ⟨[], [], 0, false, []⟩).done
def ScheduleSegment.folds (segment : ScheduleSegment) : Fin 16 :=
  ⟨segment.reads.length % 16, Nat.mod_lt _ (by decide)⟩
def ScheduleSegment.byte (segment : ScheduleSegment) : Nat :=
  segment.reads.length + 16 * (if segment.merge then 1 else 0) + 32 * (if segment.parity then 1 else 0)
def ScheduleSegment.toSegment (segment : ScheduleSegment) (nodes : Fin segment.folds.val → Digest) :
    Segment :=
  Segment.normalized segment.folds segment.merge segment.parity nodes
def honestFts (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest) :
    FtsSignature :=
  let slots := sortedSlots leaves
  let segments := schedule (sortedLeaves leaves)
  { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
    secrets := fun s => secret (leaves (slots.getD s.val ⟨0, by decide⟩))
    segments := fun j =>
      let segment := segments.getD j.val default
      segment.toSegment fun i =>
        let position := segment.reads.getD i.val (0, 0)
        node position.1 position.2 }
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none
def CountersInRange (signature : Signature) : Prop :=
  ∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit
instance (signature : Signature) : Decidable (CountersInRange signature) :=
  inferInstanceAs (Decidable (∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit))
def verifyCore (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let some ftsPublicKey ← ftsRecover publicKey.parameter index (slotValue (digestLeaves digest))
      signature.fts
    | return false
  let some root ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey | return false
  return decide (root = publicKey.root)
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  if CountersInRange signature then verifyCore publicKey message signature else pure false
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩
def buildLevel (hashNode : Nat → Digest → Digest → m Digest) (width : Nat) (below : Nat → Digest) :
    m (Nat → Digest) := do
  let row ← sequenceFin (n := width) fun nodeIdx =>
    hashNode nodeIdx.val (below (2 * nodeIdx.val)) (below (2 * nodeIdx.val + 1))
  return fun nodeIdx => if h : nodeIdx < width then row ⟨nodeIdx, h⟩ else 0
def buildLevels (hashNode : Nat → Nat → Digest → Digest → m Digest) (height : Nat)
    (leaves : Nat → Digest) : Nat → m (Nat → Nat → Digest)
  | 0 => pure fun _ nodeIdx => leaves nodeIdx
  | levels + 1 => do
      let table ← buildLevels hashNode height leaves levels
      let row ← buildLevel (hashNode (levels + 1)) (2 ^ (height - (levels + 1))) (table levels)
      return fun level nodeIdx => if level = levels + 1 then row nodeIdx else table level nodeIdx
def zeroEncoding : Encoding := fun _ => ⟨0, by decide⟩
def buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) : m (Digest × Digest) := do
  let start ← secret
  let value ← chainWalk parameter lay tree leaf chainIdx 0 digit start
  let endpoint ← chainWalk parameter lay tree leaf chainIdx digit (chainLength - 1 - digit) value
  return (value, endpoint)
def buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → m Digest) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let chains ← sequenceFin fun chainIdx =>
    buildChain parameter lay tree leaf chainIdx (secret chainIdx) (digits chainIdx).val
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)
def buildLayerTable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)
def buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)
def buildFtsTree (parameter : PublicParameter) (index : Index) (secret : FtsLeaf → m Digest) :
    m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin fun leafIdx : FtsLeaf => do
    let value ← secret leafIdx
    let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
    return (value, hashed)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)
def encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : Nat → Nat → m (Option (Counter × Encoding))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => return some (BitVec.ofNat counterBits counter, encoding)
      | none => encodingSearch parameter lay tree leaf message attempts (counter + 1)
abbrev LayerOutput := Counter × (ChainIndex → Digest) × (Nat → Digest)
def signTopLayer (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let values ← sequenceFin fun chainIdx => do
    let start ← secret leaf chainIdx
    chainWalk parameter topLayer tree leaf chainIdx 0 (encoding chainIdx).val start
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)
def signLayers (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayer parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTree parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayers parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none
def LayerOutput.toSignature (lay : Layer) (output : LayerOutput) : LayerSignature lay :=
  ⟨output.1, output.2.1, fun level => output.2.2 level.val⟩
def signFrom (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest)
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, table) ← buildFtsTree parameter index (ftsSecret porsTree)
  let some parts ← signLayers parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩
attribute [irreducible] verify
def buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainPair → m (Digest × Digest)) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret pair
    let first ← buildChain parameter lay tree leaf (evenChain pair) (pure secrets.1) (digits (evenChain pair)).val
    let second ← buildChain parameter lay tree leaf (oddChain pair) (pure secrets.2) (digits (oddChain pair)).val
    return (first, second)
  let chains := unpairChains pairs
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)
def buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeafPaired parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)
def buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let (leaves, table) ← buildLayerTablePaired parameter lay tree secret leaf digits
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)
def buildFtsTreePaired (parameter : PublicParameter) (index : Index)
    (secret : FtsPair → m (Digest × Digest)) : m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let pairs ← sequenceFin fun pair : FtsPair => do
    let secrets ← secret pair
    let first ← ftsLeafHash parameter index porsTree (evenFtsLeaf pair).val secrets.1
    let second ← ftsLeafHash parameter index porsTree (oddFtsLeaf pair).val secrets.2
    return ((secrets.1, first), (secrets.2, second))
  let leaves := unpairFtsLeaves pairs
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)
def signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret leaf pair
    let first ← chainWalk parameter topLayer tree leaf (evenChain pair) 0 (encoding (evenChain pair)).val secrets.1
    let second ← chainWalk parameter topLayer tree leaf (oddChain pair) 0 (encoding (oddChain pair)).val secrets.2
    return (first, second)
  let values := unpairChains pairs
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)
def signLayersPaired (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayerPaired parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTreePaired parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayersPaired parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none
def signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsPair → m (Digest × Digest))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest))
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, table) ← buildFtsTreePaired parameter index (ftsSecret porsTree)
  let some parts ← signLayersPaired parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩
end Concrete
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message trial))
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  $ᵗ MasterSeed
namespace Seeded
open Concrete
structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
def splitSecrets (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)
def otsSecret (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (pair : ChainPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.ots lay tree leaf pair) seed))
def ftsSecret (parameter : PublicParameter) (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pair : FtsPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.fts index tree pair) seed))
def maskDomain (level nodeIdx : Nat) : KeygenDomain :=
  .mask ⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩ ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩
def maskSecret (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) : m Digest :=
  deriveKey parameter (maskDomain level nodeIdx) seed
def maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest) :
    m TopRegion :=
  do
  let rows ← sequenceFin fun level : Fin maxLayerHeight => do
    let row ← sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← maskSecret parameter seed level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val
def cachedTopNode (parameter : PublicParameter) (seed : MasterSeed) (cache : TopCache) (level nodeIdx : Nat) :
    m Digest := do
  let mask ← maskSecret parameter seed level nodeIdx
  return cache.node level nodeIdx ^^^ mask
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × TopCache × SecretKey) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree (otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let root := table (layerHeight topLayer) 0
  let region ← maskRegion 0 seed table
  let tag ← oracleHash (macHashInput 0 seed region)
  return (⟨root, 0⟩, ⟨tag, region⟩, ⟨seed, 0, root⟩)
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Nat →
    m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)
      match ← signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => signDigestLoop secretKey message attempts (trial + 1)
def signChecked (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let some (randomness, index, leaves) ← signDigestLoop secretKey message digestAttemptLimit 0
    | return none
  signFromPaired secretKey.parameter index (ftsSecret secretKey.parameter secretKey.seed index)
    (otsSecret secretKey.parameter secretKey.seed)
    (cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves
def sign (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let tag ← oracleHash (macHashInput secretKey.parameter secretKey.seed cache.region)
  if tag = cache.tag then signChecked secretKey cache message else return none
end Seeded
end SphincsSecurity
