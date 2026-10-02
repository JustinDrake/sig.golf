import SigGolfCandidate.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Witness.Schedule

/-! # Witness encoding and decoding (stream W)

* `expandN`: Core's `expand` that also returns the accepted digest answer `N` (the encoding depends on it: the
  stream schedule on the selections, the Merkle sides on the index); `expand_eq_expandN` in `Honest`.
* `witEnc N w`: the machine witness bytes (`t3m/ref3/witness.build`): rho, dc, counters, the secrets at `+32` of
  the leaf blocks, the honest stream (`schedule (selections N)`, siblings by `foldSlot`), chain values at `+48`,
  Merkle siblings at `L`/`R` by the leaf index bits; every other byte zero.
* `witDecP N w`, `padDecP N w`: the Core witness and the pads a byte witness denotes when its stream has the
  honest shape for the selections of `N` (proof slots read through `streamPlan`; unused slots zero).
* `Shaped N w`: the selections of `N` pass the machine's checks and the stream headers match the schedule. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)

/-- Core's `expand`, also returning the digest answer `N` it accepted. -/
def expandN (message : Message) (pk : Digest) (sig : Signature) : M (Option (HashOutput × Witness)) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFts sig index (selections output) | pure none
  let some (root, counters) ← expandLayers sig index 4 root | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))

/-! ## Encoding -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : List UInt8 := List.replicate n 0

/-- `[0,64)`: rho, dc, the four layer counters, 28 zero bytes. -/
def headerBytes (w : Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++
    (List.finRange 4).flatMap (fun lay => bytesLE 4 (w.counters lay)) ++ zeros 28

/-- `[64,1088)`: 21 chunks `[P_s | T | secret_s]` (pads and T zero) and the last block's zero pad. -/
def leafBytes (sig : Signature) : List UInt8 :=
  (List.finRange 21).flatMap (fun s => zeros 32 ++ bytesLE 16 (sig.secrets s)) ++ zeros 16

/-- A fold block and its gap (80 bytes): the sibling at `L` when the folded node's heap index is odd, else `R`. -/
def foldBytes (E : Nat) (sib : Digest) : List UInt8 :=
  if E % 2 = 1 then bytesLE 16 sib ++ zeros 64 else zeros 48 ++ bytesLE 16 sib ++ zeros 16

/-- A segment: header byte, 7 zero bytes, its fold blocks with the proof slots `foldSlot` places there. -/
def segBytes (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) : List UInt8 :=
  [UInt8.ofNat seg.byte0] ++ zeros 7 ++ (List.range seg.a).flatMap fun r =>
    foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)

/-- `[1088,11288)`: the honest stream, zero-filled (cut at 10,200 bytes, which only over-cap selections reach). -/
def streamBytes (chosen : List Selection) (proof : Fin 115 → Digest) : List UInt8 :=
  (((schedule chosen).flatMap (segBytes chosen proof)) ++ zeros 10200).take 10200

/-- Layer `lay`'s region: Merkle blocks of levels `h-1 .. 0` (sibling at `L` iff bit `j` of `leaf` is 1, else
`R`), then chain blocks of chains `n-1 .. 0` (value at `+48`). -/
def layerBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  (List.finRange (height lay)).reverse.flatMap (fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.flatMap (fun i => zeros 48 ++ bytesLE 16 (ls.values i))

/-- The 25,240 witness bytes of `witEnc N w`. -/
def witList (N : HashOutput) (w : Witness) : List UInt8 :=
  headerBytes w ++ leafBytes w.signature ++ streamBytes (selections N) w.signature.proof ++
    (List.finRange 4).flatMap fun lay =>
      layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)

/-- The machine witness of an expansion with digest answer `N` (byte `i` = `witList N w` at `i`). -/
def witEnc (N : HashOutput) (w : Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))

/-- `expandN` followed by the witness encoding (SEC's `expandB`). -/
def expandB (message : Message) (pk : Digest) (sig : Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig

/-! ## Decoding -/

/-- The Core witness of a byte witness whose stream has the honest shape for the selections of `N`: payload
fields at their offsets, proof slot `k` from its fold block (`slotOffset`; unused slots zero), Merkle siblings
on the side given by the index bits of `N`. -/
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

/-- The pads of a byte witness with the honest stream shape for the selections of `N`. -/
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  leaf s := wleafPad w s.val
  fold k := match slotBlock (selections N) k with
    | some blk => wdig w (blk + 32)
    | none => 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := wmerklePad w lay j.val

/-- The stream of `w` has the honest shape for the digest answer `N`: the selections pass the machine's check
and Core's admissibility, and every header byte matches the schedule on its live bits. -/
def Shaped (N : HashOutput) (w : WBytes) : Prop :=
  selectionsOk (selections N) = true ∧ admissible (selections N) = true ∧ StreamMatches (selections N) w

instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance

end SigGolfCandidate.T3M
