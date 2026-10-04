import SigGolfCandidate.T3.Core
import SigGolfCandidate.ClaudeWCT.WCT9.Codebook

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def coordinates : Nat := 9
def children : Nat := 128
def chains : Nat := 7
def gateBits : Nat := 14
def fieldBits : Nat := 14
def fieldLimit : Nat := 16016
abbrev Coord := Fin 9
abbrev Child := Fin 128
abbrev Rank := Fin 728
def wctHeader (tag lay tree position index : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 +
    (tree / 2 ^ 32 % 256) * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32 +
    tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96)
def coordBase (k : Nat) : Nat := [43,64,85,106,128,149,170,192,213].getD k 0
def child (output : HashOutput) (coord : Coord) : Child :=
  ⟨output.toNat / 2 ^ coordBase coord.val % 128, Nat.mod_lt _ (by decide)⟩
def field (output : HashOutput) (coord : Coord) : Nat :=
  output.toNat / 2 ^ (coordBase coord.val + 7) % 2 ^ 14
def rank (output : HashOutput) (coord : Coord) : Rank :=
  ⟨field output coord % 728, Nat.mod_lt _ (by decide)⟩
def admissible (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 234 % 2 ^ 14 < 5) &&
    (List.range 9).all (fun coord =>
      decide (output.toNat / 2 ^ (coordBase coord + 7) % 2 ^ 14 < 16016))
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if admissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter + 1) fuel
def ftsChainLow (index coord selected chain step : Nat) : Nat :=
  0x80 + chain % 8 * 2 ^ 2 + step % 4 * 2 ^ 8 + coord % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 +
    index % 2 ^ 31 * 2 ^ 27
def ftsChainHeaderP (index coord selected chain step : Nat) (high : BitVec 64) : BitVec 128 :=
  high ++ BitVec.ofNat 64 (ftsChainLow index coord selected chain step)
def ftsChainHeader (index coord selected chain step : Nat) : BitVec 128 :=
  ftsChainHeaderP index coord selected chain step 0
def chainInput (index coord selected chain step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (ftsChainHeader index coord selected chain step) ++
    zero16 ++ bytesLE 16 value
def chain (index coord selected i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInput index coord selected i step value)) value
def leafHash (index coord selected : Nat) (ends : List Digest) : M Digest :=
  shortHash (bytesLE 16 (ends.getD 0 0) ++
    bytesLE 16 (wctHeader 6 coord index 0 selected) ++ (ends.drop 1).flatMap (bytesLE 16))
def buildChild (index coord selected : Nat) (word : Rank) : M (Digest × List Digest) := do
  let state ← (List.finRange 4).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let seeds ← privatePair 8 coord index 0 (4 * selected + pair.val)
      (List.finRange 2).foldlM
        (fun (state : List Digest × List Digest) half => do
          if h : 2 * pair.val + half.val < 7 then
            let i : Fin 7 := ⟨2 * pair.val + half.val, h⟩
            let secret := if half.val = 0 then seeds.1 else seeds.2
            let deficit := digit word i
            let value ← chain index coord selected i.val 0 (3 - deficit) secret
            let last ← chain index coord selected i.val (3 - deficit) deficit value
            pure (state.1 ++ [last], state.2 ++ [value])
          else pure state) state) ([], [])
  let root ← leafHash index coord selected state.1
  pure (root, state.2)
def nodeLayer (coord : Nat) : Nat := 4 + coord
def wctNodeHeader (coord index heap : Nat) : BitVec 128 := header 3 (nodeLayer coord) index 0 heap
def wctNodeHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  nodeHash 3 (nodeLayer coord) index heap left right
def heapBuild (index coord : Nat) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 2 126).reverse.foldlM (fun nodes heap => do
    let value ← wctNodeHash coord index heap (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
    pure (nodes.set! heap value)) ((List.replicate 128 (0 : Digest) ++ leaves).toArray)
def heapLevels (heap : Array Digest) : List (List Digest) :=
  (List.range 7).map fun level =>
    (List.range (2 ^ (7 - level))).map fun i => heap.getD (2 ^ (7 - level) + i) 0
def buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest) j => do
      let (root, values) ← buildChild index coord.val j word
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])
  let nodes ← heapBuild index coord.val state.1
  pure (heapLevels nodes, state.2)
def forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput :=
  zero16 ++ bytesLE 16 (header 15 0 index 0 0) ++
    pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)
def forestPk (index : Nat) (pairs : List (Digest × Digest)) : M Digest :=
  shortHash (forestInput index pairs)
inductive LayerMsg where
  | forest (root : Digest)
  | pair (left right : Digest)
  deriving DecidableEq
def pairEncodingInputP (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (header 4 up.val tree 0 leaf) ++ bytesLE 4 counter ++ bytesLE 12 pad ++
    bytesLE 16 right
def layerEncodingInput (lay : Layer) (tree leaf : Nat) : LayerMsg → BitVec 32 → HashInput
  | .forest root, counter => encodingInput lay tree leaf root counter
  | .pair left right, counter => pairEncodingInputP lay tree leaf left right counter 0
def layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat))
  | 0 => pure none
  | fuel + 1 => do
      let answer ← shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
      match decode lay answer with
      | none => layerCounterSearch lay tree leaf msg (counter + 1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits))
def topLevel (lay : Layer) : Fin (height lay) :=
  ⟨height lay - 1, by fin_cases lay <;> decide⟩
def topPair (lay : Layer) (levels : List (List Digest)) : Digest × Digest :=
  ((levels.getD (height lay - 1) []).getD 0 0, (levels.getD (height lay - 1) []).getD 1 0)
def signLayersBC (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (_, digits) ← layerCounterSearch lay tree leaf msg 0 counterLimit | pure none
      if n = 0 then
        let part ← signTop cache leaf digits
        pure (some [part])
      else
        let (levels, values) ← buildTree lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBC cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
structure Opening where
  values : Fin 7 → Digest
  path : Fin 7 → Digest
structure Signature where
  rho : Digest
  openings : Coord → Opening
  layers : (lay : Layer) → LayerSignature lay
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
def toT3Signature (sig : Signature) : SigGolfCandidate.T3.Signature :=
  ⟨sig.rho, fun _ => 0, fun _ => 0, sig.layers⟩
def toT3Witness (w : Witness) : SigGolfCandidate.T3.Witness :=
  ⟨toT3Signature w.signature, w.digestCounter, w.counters⟩
def recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    SigGolfCandidate.T3.chain lay tree leaf i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)
  let value ← SigGolfCandidate.T3.leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHash 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2) value
  let other := (sig.layers lay).path (topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def expandLayersBC (sig : Signature) (index : Nat) :
    Nat → LayerMsg → M (Option (Digest × List (BitVec 32)))
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits) ← layerCounterSearch lay tree leaf msg 0 counterLimit | pure none
      if n = 0 then
        let root ← recoverLayer (toT3Signature sig) index lay digits
        pure (some (root, [counter]))
      else
        let pair ← recoverLayerPair sig index lay digits
        let some (root, counters) ← expandLayersBC sig index n (.pair pair.1 pair.2) | pure none
        pure (some (root, counters ++ [counter]))
def verifyLayersBC (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInput lay tree leaf msg counter)
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> recoverLayer (toT3Signature w.signature) index lay digits
      else do
        let pair ← recoverLayerPair w.signature index lay digits
        verifyLayersBC w index n (.pair pair.1 pair.2)
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let root ← forestPk index state.2
  let some layers ← signLayersBC cache index 4 (.forest root) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def sign (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message
def serializeOpening (opened : Opening) : HashInput :=
  (List.ofFn opened.values).flatMap (bytesLE 16) ++
    (List.ofFn opened.path).flatMap (bytesLE 16)
def serialize (sig : Signature) : HashInput :=
  bytesLE 16 sig.rho ++ (List.ofFn sig.openings).flatMap serializeOpening ++
    (List.ofFn fun lay => serializeLayer (sig.layers lay)).flatten
def recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord) :
    M (Digest × Digest) := do
  let selected := child output coord
  let word := rank output coord
  let ends ← (List.finRange 7).mapM fun i =>
    let deficit := digit word i
    chain index coord.val selected.val i.val (3 - deficit) deficit ((sig.openings coord).values i)
  let root ← leafHash index coord.val selected.val ends
  let top ← (List.finRange 6).foldlM
    (fun value level => do
      let other := (sig.openings coord).path level.castSucc
      let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      wctNodeHash coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1))
        pair.1 pair.2) root
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def recoverFts (sig : Signature) (index : Nat) (output : HashOutput) : M Digest := do
  let pairs ← (List.finRange 9).mapM (recoverCoordinate sig index output)
  forestPk index pairs
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts w.signature index output
  let some root ← verifyLayersBC w index 4 (.forest root) | pure false
  pure (root == pk)
def keygen := SigGolfCandidate.T3.keygen
end ClaudeWCT.WCT9
