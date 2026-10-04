import SigGolfCandidate.T3M.Witness.Layout
import SigGolfCandidate.ClaudeWCT.WCT9.Limits
import SigGolfCandidate.T3M.Witness.Basic

section


namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig sibOff)
abbrev WBytes := SigGolfCandidate.T3M.WBytes
def regionBase (k : Nat) : Nat := 64 + 1024 * k
def wctEnd : Nat := 9280
def wctChainBlock (k t : Nat) : Nat := regionBase k + (832 - 64 * t)
def wctLeafBlock (k : Nat) : Nat := regionBase k + 880
def wctLeafSlot (k t : Nat) : Nat := regionBase k + (if t = 0 then 880 else 896 + 16 * t)
def wctMerkleBlock (k l : Nat) : Nat := regionBase k + 64 * (6 - l)
def wopen (w : WBytes) (k t : Nat) : Digest := wdig w (wctChainBlock k t + 48)
def wleaf (w : WBytes) (k t : Nat) : Digest := wdig w (wctLeafSlot k t)
def wreveal (w : WBytes) (k t d : Nat) : Digest := if d = 0 then wleaf w k t else wopen w k t
def wcpads (w : WBytes) (k t : Nat) : Digest × Digest :=
  (wdig w (wctChainBlock k t), wdig w (wctChainBlock k t + 32))
def wsib (w : WBytes) (k child l : Nat) : Digest := wdig w (wctMerkleBlock k l + sibOff (child / 2 ^ l % 2))
def wmpad (w : WBytes) (k l : Nat) : Digest := wdig w (wctMerkleBlock k l + 32)
def wcHeaderPad (w : WBytes) (k t : Nat) : BitVec 64 := (wdig w (wctChainBlock k t + 16)).extractLsb' 64 64
def bcCounterOff (lay : Layer) : Nat := (![14824, 18024, 21160, 32] : Layer → Nat) lay
def wbcCtr (w : WBytes) (lay : Layer) : BitVec 32 := SigGolfCandidate.T3M.wle32 w (bcCounterOff lay)
def wbcPad (w : WBytes) (lay : Layer) : BitVec 96 := w.extractLsb' (8 * (bcCounterOff lay + 4)) 96
theorem wctLeafSlot_zero (k : Nat) : wctLeafSlot k 0 = wctChainBlock k 0 + 48 := by
  simp [wctLeafSlot, wctChainBlock]
theorem wleaf_zero (w : WBytes) (k : Nat) : wleaf w k 0 = wopen w k 0 := by
  unfold wleaf wopen; rw [wctLeafSlot_zero]
end ClaudeWCT.W9.T3M
end

section


namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wrho wdc wle32 wvalue wpath wchainPads wmerklePad wchainHeaderPad chainP layerP
  nodeHashP recoverLayerP)
open SphincsSecurity (bytesLE)
def wctChainInputP (index coord child t step : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    HashInput :=
  bytesLE 16 padA ++ bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step padB) ++ bytesLE 16 padC ++
    bytesLE 16 value
def wctChainP (index coord child t start count : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (wctChainInputP index coord child t step padA padB padC value)) value
def wctNodeHashP (coord index heap : Nat) (left pad right : Digest) : M Digest :=
  nodeHashP 3 (WCT9.nodeLayer coord) index heap left pad right
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ WCT9.digestAttemptLimit then pure none else some <$> digest (wrho w) m (wdc w)
def gateOk (N : HashOutput) : Bool := decide (N.toNat / 2 ^ 234 % 2 ^ 14 < 5)
def fieldOk (N : HashOutput) (coord : WCT9.Coord) : Bool := decide (WCT9.field N coord < WCT9.fieldLimit)
def wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child) (word : WCT9.Rank) :
    M (Digest × Digest) := do
  let ends ← (List.finRange 7).mapM fun t =>
    wctChainP index coord.val child.val t.val (3 - WCT9.digit word t) (WCT9.digit word t)
      (wcpads w coord.val t.val).1 (wcHeaderPad w coord.val t.val) (wcpads w coord.val t.val).2
      (wreveal w coord.val t.val (WCT9.digit word t))
  let leaf ← WCT9.leafHash index coord.val child.val ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := wsib w coord.val child.val level.val
    let pair := if child.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + child.val / 2 ^ (level.val + 1)) pair.1
      (wmpad w coord.val level.val) pair.2) leaf
  let other := wsib w coord.val child.val 6
  pure (if child.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def wctStep (w : WBytes) (N : HashOutput) (state : Option (List (Digest × Digest))) (coord : WCT9.Coord) :
    M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if !fieldOk N coord then return none
  let pair ← wctCoordP w (N.toNat % 2 ^ 31) coord (WCT9.child N coord) (WCT9.rank N coord)
  pure (some (pairs ++ [pair]))
def wctP (w : WBytes) (N : HashOutput) : M (Option Digest) := do
  let some pairs ← (List.finRange 9).foldlM (wctStep w N) (some []) | pure none
  some <$> WCT9.forestPk (N.toNat % 2 ^ 31) pairs
def layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) : HashInput :=
  match msg with
  | .forest root => encodingInput lay tree leaf root counter
  | .pair left right => WCT9.pairEncodingInputP lay tree leaf left right counter pad
def layerPairP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay j.val) pair.2) value
  let other := wpath w lay leaf (height lay - 1)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def layersBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInputP lay tree leaf msg counter (wbcPad w lay))
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> layerP w index lay digits
      else do
        let pair ← layerPairP w index lay digits
        layersBC w index n (.pair pair.1 pair.2)
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← wctP w N | pure false
  let some root ← layersBC w index 4 (.forest root) | pure false
  pure (root == pk)
structure Pads where
  wctChain : WCT9.Coord → Fin 7 → Digest × Digest
  wctChainHigh : WCT9.Coord → Fin 7 → BitVec 64
  wctMerkle : WCT9.Coord → Fin 7 → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
  bc : Layer → BitVec 96
instance : Zero Pads :=
  ⟨⟨fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩⟩
def Pads.toT3 (pads : Pads) : SigGolfCandidate.T3M.Pads :=
  ⟨fun _ => 0, fun _ => 0, pads.chain, pads.merkle, pads.chainHeader⟩
def recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) : M (Digest × Digest) := do
  let selected := WCT9.child output coord
  let word := WCT9.rank output coord
  let ends ← (List.finRange 7).mapM fun i =>
    wctChainP index coord.val selected.val i.val (3 - WCT9.digit word i) (WCT9.digit word i)
      (pads.wctChain coord i).1 (pads.wctChainHigh coord i) (pads.wctChain coord i).2
      ((sig.openings coord).values i)
  let root ← WCT9.leafHash index coord.val selected.val ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := (sig.openings coord).path level.castSucc
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1
      (pads.wctMerkle coord level.castSucc) pair.2) root
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
def recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) : M Digest := do
  let pairs ← (List.finRange 9).mapM (recoverCoordinateP sig pads index output)
  WCT9.forestPk index pairs
def recoverLayerPairP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 (pads.chainHeader lay i) ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkle lay (Fin.castLE (Nat.sub_le _ _) j)) pair.2) value
  let other := (sig.layers lay).path (WCT9.topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def verifyLayersBCP (w : WCT9.Witness) (pads : Pads) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (layerEncodingInputP lay tree leaf msg counter (pads.bc lay))
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> recoverLayerP (WCT9.toT3Signature w.signature) pads.toT3 index lay digits
      else do
        let pair ← recoverLayerPairP w.signature pads index lay digits
        verifyLayersBCP w pads index n (.pair pair.1 pair.2)
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if !WCT9.admissible output then return false
  let index := output.toNat % 2 ^ 31
  let root ← recoverFtsP w.signature pads index output
  let some root ← verifyLayersBCP w pads index 4 (.forest root) | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ WCT9.digestAttemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end ClaudeWCT.W9.T3M
end
