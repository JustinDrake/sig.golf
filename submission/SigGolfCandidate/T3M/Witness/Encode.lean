import SigGolfCandidate.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Witness.Schedule
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def expandN (message : Message) (pk : Digest) (sig : Signature) : M (Option (HashOutput × Witness)) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFts sig index (selections output) | pure none
  let some (root, counters) ← expandLayers sig index 4 (root, 0, 0) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
def zeros (n : Nat) : List UInt8 := List.replicate n 0
def headerBytes (w : Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++
    (List.finRange 4).flatMap (fun lay => bytesLE 4 (w.counters lay)) ++ zeros 28
def leafBytes (sig : Signature) : List UInt8 :=
  (List.finRange 21).flatMap (fun s => zeros 32 ++ bytesLE 16 (sig.secrets s)) ++ zeros 16
def foldBytes (E : Nat) (sib : Digest) : List UInt8 :=
  if E % 2 = 1 then bytesLE 16 sib ++ zeros 64 else zeros 48 ++ bytesLE 16 sib ++ zeros 16
def segBytes (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) : List UInt8 :=
  [UInt8.ofNat seg.byte0] ++ zeros 7 ++ (List.range seg.a).flatMap fun r =>
    foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)
def streamBytes (chosen : List Selection) (proof : Fin 115 → Digest) : List UInt8 :=
  (((schedule chosen).flatMap (segBytes chosen proof)) ++ zeros 9480).take 9480
def layerBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  (List.finRange (height lay)).reverse.flatMap (fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.flatMap (fun i => zeros 48 ++ bytesLE 16 (ls.values i))
def layerStorage (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  layerBytes lay leaf ls
def witList (N : HashOutput) (w : Witness) : List UInt8 :=
  headerBytes w ++ leafBytes w.signature ++ streamBytes (selections N) w.signature.proof ++
    (List.finRange 4).flatMap fun lay =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
def witEnc (N : HashOutput) (w : Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : Witness where
  signature :=
    { rho := wrho w
      secrets := fun s => wsecret w s.val
      proof := fun k => match slotOffset (selections N) k with
        | some off => wdig w off
        | none => 0
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wctr w lay
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  leaf s := wleafPad w s.val
  fold k := match slotBlock (selections N) k with
    | some blk => wdig w (blk + 32)
    | none => 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := wmerklePad w lay j.val
  chainHeader lay i := wchainHeaderPad w lay i.val
def Shaped (N : HashOutput) (w : WBytes) : Prop :=
  selectionsOk (selections N) = true ∧ admissible (selections N) = true ∧ StreamMatches (selections N) w
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
end SigGolfCandidate.T3M
