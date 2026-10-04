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
theorem wctLeafSlot_zero (k : Nat) : wctLeafSlot k 0 = wctChainBlock k 0 + 48 := by
  simp [wctLeafSlot, wctChainBlock]
theorem wleaf_zero (w : WBytes) (k : Nat) : wleaf w k 0 = wopen w k 0 := by
  unfold wleaf wopen; rw [wctLeafSlot_zero]
end ClaudeWCT.W9.T3M
end

section


namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wrho wdc wctr layersP nodeHashP verifyLayersP)
open SphincsSecurity (bytesLE)
def wctChainInputP (index coord child t step : Nat) (pad0 pad1 value : Digest) : HashInput :=
  bytesLE 16 pad0 ++ bytesLE 16 (WCT9.wctHeader 5 coord index (step + 256 * t) child) ++ bytesLE 16 pad1 ++
    bytesLE 16 value
def wctChainP (index coord child t start count : Nat) (pad0 pad1 value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (wctChainInputP index coord child t step pad0 pad1 value)) value
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ WCT9.digestAttemptLimit then pure none else some <$> digest (wrho w) m (wdc w)
def gateOk (N : HashOutput) : Bool := decide (N.toNat / 2 ^ 234 % 2 ^ 14 < 5)
def fieldOk (N : HashOutput) (coord : WCT9.Coord) : Bool := decide (WCT9.field N coord < WCT9.fieldLimit)
def wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child) (word : WCT9.Rank) :
    M Digest := do
  let ends ← (List.finRange 7).mapM fun t =>
    wctChainP index coord.val child.val t.val (3 - WCT9.digit word t) (WCT9.digit word t)
      (wcpads w coord.val t.val).1 (wcpads w coord.val t.val).2 (wreveal w coord.val t.val (WCT9.digit word t))
  let leaf ← WCT9.leafHash index coord.val child.val ends
  (List.finRange 7).foldlM (fun value level => do
    let other := wsib w coord.val child.val level.val
    let pair := if child.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 11 coord.val index (2 ^ (6 - level.val) + child.val / 2 ^ (level.val + 1)) pair.1
      (wmpad w coord.val level.val) pair.2) leaf
def wctStep (w : WBytes) (N : HashOutput) (state : Option (List Digest)) (coord : WCT9.Coord) :
    M (Option (List Digest)) := do
  let some roots := state | pure none
  if !fieldOk N coord then return none
  let root ← wctCoordP w (N.toNat % 2 ^ 31) coord (WCT9.child N coord) (WCT9.rank N coord)
  pure (some (roots ++ [root]))
def wctP (w : WBytes) (N : HashOutput) : M (Option Digest) := do
  let some roots ← (List.finRange 9).foldlM (wctStep w N) (some []) | pure none
  some <$> WCT9.forestPk (N.toNat % 2 ^ 31) roots
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← wctP w N | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)
structure Pads where
  wctChain : WCT9.Coord → Fin 7 → Digest × Digest
  wctMerkle : WCT9.Coord → Fin 7 → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
instance : Zero Pads := ⟨⟨fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0⟩⟩
def Pads.toT3 (pads : Pads) : SigGolfCandidate.T3M.Pads :=
  ⟨fun _ => 0, fun _ => 0, pads.chain, pads.merkle, pads.chainHeader⟩
def recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) : M Digest := do
  let selected := WCT9.child output coord
  let word := WCT9.rank output coord
  let ends ← (List.finRange 7).mapM fun i =>
    wctChainP index coord.val selected.val i.val (3 - WCT9.digit word i) (WCT9.digit word i)
      (pads.wctChain coord i).1 (pads.wctChain coord i).2 ((sig.openings coord).values i)
  let root ← WCT9.leafHash index coord.val selected.val ends
  (List.finRange 7).foldlM (fun value level => do
    let other := (sig.openings coord).path level
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 11 coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1
      (pads.wctMerkle coord level) pair.2) root
def recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) : M Digest := do
  let roots ← (List.finRange 9).mapM (recoverCoordinateP sig pads index output)
  WCT9.forestPk index roots
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if !WCT9.admissible output then return false
  let index := output.toNat % 2 ^ 31
  let root ← recoverFtsP w.signature pads index output
  let some root ← verifyLayersP (WCT9.toT3Witness w) pads.toT3 index 4 root | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ WCT9.digestAttemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end ClaudeWCT.W9.T3M
end
