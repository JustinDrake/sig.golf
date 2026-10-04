import SigGolfCandidate.T3.Core
import SigGolfCandidate.ClaudeWCT.WCT9.Codebook
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def coordinates : Nat := 9
def children : Nat := 128
def chains : Nat := 7
def gateBits : Nat := 12
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
  decide (output.toNat / 2 ^ 31 % 2 ^ 12 = 0) &&
    (List.range 9).all (fun coord =>
      decide (output.toNat / 2 ^ (coordBase coord + 7) % 2 ^ 14 < 16016))
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if admissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter + 1) fuel
def chainInput (index coord selected chain step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (wctHeader 5 coord index (step + 256 * chain) selected) ++
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
def buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest) j => do
      let (root, values) ← buildChild index coord.val j word
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])
  let nodes ← (List.range' 1 127).reverse.foldlM
    (fun nodes heap => do
      let value ← nodeHash 11 coord.val index heap
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value)) ((List.replicate 128 (0 : Digest) ++ state.1).toArray)
  let levels := (List.range 8).map fun level =>
    (List.range (2 ^ (7 - level))).map fun i => nodes.getD (2 ^ (7 - level) + i) 0
  pure (levels, state.2)
def forestPk (index : Nat) (roots : List Digest) : M Digest :=
  shortHash (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 15 0 index 0 0) ++
    (roots.drop 1).flatMap (bytesLE 16))
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
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List Digest) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening], state.2 ++ [(levels.getD 7 []).getD 0 0])) ([], [])
  let root ← forestPk index state.2
  let some layers ← signLayers cache index 4 (root, 0, 0) | pure none
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
    M Digest := do
  let selected := child output coord
  let word := rank output coord
  let ends ← (List.finRange 7).mapM fun i =>
    let deficit := digit word i
    chain index coord.val selected.val i.val (3 - deficit) deficit ((sig.openings coord).values i)
  let root ← leafHash index coord.val selected.val ends
  (List.finRange 7).foldlM
    (fun value level => do
      let other := (sig.openings coord).path level
      let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      nodeHash 11 coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1))
        pair.1 pair.2) root
def recoverFts (sig : Signature) (index : Nat) (output : HashOutput) : M Digest := do
  let roots ← (List.finRange 9).mapM (recoverCoordinate sig index output)
  forestPk index roots
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayers (toT3Signature sig) index 4 (root, 0, 0) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts w.signature index output
  let some root ← verifyLayers (toT3Witness w) index 4 (root, 0, 0) | pure false
  pure (root == pk)
def keygen := SigGolfCandidate.T3.keygen
end ClaudeWCT.WCT9
