import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Witness.Encode

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wrho wdc wvalue wpath wchainPads wmerklePad wchainHeaderPad zeros layerBytes)
open SphincsSecurity (bytesLE)
def expandN (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) := do
  let some (counter, output) ← WCT9.digestSearch sig.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let root ← WCT9.recoverFts sig index output
  let some (root, counters) ← WCT9.expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
def headerBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++ zeros 28
def merkleBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 7).reverse.flatMap fun l =>
    if child / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.path l)
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 6).reverse.flatMap fun i => zeros 48 ++ bytesLE 16 (op.values i.succ)
def leafBytes (op : WCT9.Opening) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ (List.finRange 6).flatMap fun i => bytesLE 16 (op.values i.succ)
def regionBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  merkleBytes child op ++ chainBytes op ++ zeros 48 ++ leafBytes op ++ zeros 16
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytes (WCT9.child N k).val (sig.openings k)
def bcTopBlock (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  if leaf / 2 ^ (height lay - 1) % 2 = 1 then
    bytesLE 16 (ls.path (WCT9.topLevel lay)) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28
  else zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path (WCT9.topLevel lay))
def layerBytesBC (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  bcTopBlock lay leaf ls ctr ++ (layerBytes lay leaf ls).drop 64
def layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
  else layerBytesBC lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes w ++ wctBytes N w.signature ++ zeros 1288 ++ (List.finRange 4).flatMap (layerRegion N w)
def witEnc (N : HashOutput) (w : WCT9.Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : WCT9.Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : WCT9.Witness where
  signature :=
    { rho := wrho w
      openings := fun k =>
        ⟨fun t => wreveal w k.val t.val (WCT9.digit (WCT9.rank N k) t),
          fun l => wsib w k.val (WCT9.child N k).val l.val⟩
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wbcCtr w lay
def padDecP (_N : HashOutput) (w : WBytes) : Pads where
  wctChain k t := wcpads w k.val t.val
  wctChainHigh k t := wcHeaderPad w k.val t.val
  wctMerkle k l := if l.val < 6 then wmpad w k.val l.val else 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := if j.val + 1 < height lay ∨ lay.val = 0 then wmerklePad w lay j.val else 0
  chainHeader lay i := wchainHeaderPad w lay i.val
  bc lay := wbcPad w lay
def Shaped (N : HashOutput) (_w : WBytes) : Prop := WCT9.admissible N = true
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  if !gateOk N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← wctP w N | pure false
  let some root ← layersBC w index 4 (.forest root) | pure false
  pure (root == pk)
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !gateOk N then pure false else (fun _ => false) <$> wctP w N
end ClaudeWCT.W9.T3M
