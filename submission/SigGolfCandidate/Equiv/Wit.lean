import SigGolfCandidate.Equiv.Slices

/-!
# The witness decoder, the compact signature, and the abstract expansion (PORS+FP)

The abstract `Signature` is witness-shaped (`SphincsSecurity.FtsSignature`: slot codes, secrets and the
29 stack-machine segments). This file fixes the three maps the Bridge needs (design:
`work/design/WS7a-SCHEME.md` §3):

* `witSig : List Byte → Signature` / `witDec : Bytes 16384 → Signature` parse a witness exactly as the
  verifier (`Ref.verifyList`) reads it: `rho` at `0`, the slot code of the `s`-th leaf
  `(pi_s & 0x78) >> 3` from byte `16 + s`, the secrets at `32 + 16 s`, the segment stream from
  `Ref.wStream = 272` by a pointer (header byte `b`: `a = b mod 16`, merge = bit 4, `t` = bit 5,
  normalised when `a = 0`; the `a` nodes at `ptr + 8 + 16 i`; next header at `ptr + 8 + 16 a`), bytes
  beyond the witness read as zero, and the W1a layer fields: the chain values at `blockOff lay i + 48`,
  the paths at `pathOff lay`, the counters at `ctrOff lay` (`c0 .. c3` at `2944 + 4 lay`, `c4` at 2392).
* `padDec : Bytes 16384 → ChainPads`: the 32 pad bytes `blockOff lay i + 16 .. + 48` of every chain
  block as two digests (`padDec_eq_zero_iff`: the pad is `0` iff the 32 bytes are zero).
* `compressList` / `compress : Signature → Bytes 6032`: `rho | secrets | the nodes of segments
  0..28 concatenated, zero padded (or cut) to 117 nodes | per layer chain values, path` (no counters).
* `aExpand m pk σ`: the digest query of `rho = σ[0..16)` and `m` through the abstract hash, the
  pure partial witness `Ref.expandOf` of the reference, the abstract PORS stack machine on it, then
  per layer the least-counter search (and below the top the verifier's chains, leaf and fold).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes)
open SphincsSecurity (Digest Signature Layer ChainIndex Segment FtsSignature LayerSignature Message
  PublicKey)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## The witness decoder -/

/-- The 16 witness bytes at `o` as a digest (bytes beyond the witness read as zero, `Ref.wbytes`). -/
def wdig (w : List Byte) (o : Nat) : Digest := Ref.ofList 16 (Ref.wbytes w o 16)

/-- The segment whose header is at `p`: `a = b mod 16`, merge = bit 4, `t` = bit 5 of the header byte
`b = Ref.wbyte w p` (normalised to `false` when `a = 0`), node `i` at `p + 8 + 16 i`. -/
def segAt (w : List Byte) (p : Nat) : Segment :=
  Segment.normalized ⟨Ref.wbyte w p % 16, Nat.mod_lt _ (by decide)⟩
    (decide (Ref.wbyte w p / 16 % 2 = 1)) (decide (Ref.wbyte w p / 32 % 2 = 1))
    (fun i => wdig w (p + 8 + 16 * i.val))

/-- The header position of segment `j`: `Ref.wStream`, then `+ 8 + 16 a` per segment. -/
def segPtr (w : List Byte) : Nat → Nat
  | 0 => Ref.wStream
  | j + 1 => segPtr w j + 8 + 16 * (Ref.wbyte w (segPtr w j) % 16)

/-- The PORS part of a witness. -/
def witFts (w : List Byte) : FtsSignature where
  perm s := ⟨Ref.witPi w s.val / 8 % 16, by
    have := Nat.mod_lt (Ref.witPi w s.val / 8) (show 0 < 16 by decide)
    simp only [SphincsSecurity.ftsOpenings]; omega⟩
  secrets s := Ref.ofList 16 (Ref.witSecret w s.val)
  segments j := segAt w (segPtr w j.val)

/-- Layer `lay` of a witness: its counter (at `Ref.ctrOff lay`), chain values (`Ref.witChain`: the value
slot `blockOff lay i + 48`) and path (`Ref.witSib`: `pathOff lay + 16 l`). -/
def witLayer (w : List Byte) (lay : Layer) : LayerSignature lay :=
  ⟨Ref.ofList 4 (Ref.slice w (Ref.ctrOff lay.val) 4),
    fun i => Ref.ofList 16 (Ref.witChain w lay.val i.val),
    fun l => Ref.ofList 16 (Ref.witSib w lay.val l.val)⟩

/-- **The witness decoder** on byte lists. -/
def witSig (w : List Byte) : Signature :=
  ⟨Ref.ofList 16 (Ref.witRho w), witFts w, witLayer w⟩

/-- **The witness decoder**. -/
def witDec (w : Bytes 16384) : Signature := witSig (Ref.toList w)

/-- **The pad decoder** (W1a): the 32 bytes between the tweak slot and the value of chain block
`(lay, i)` (`Ref.witPad`), as two digests. Verify hashes them as they stand (`Ref.chainInputP`); the
honest pads are zero. Definitionally `Equiv.padOf (Ref.toList w)` (`Equiv/Verify.lean`). -/
def padDec (w : Bytes 16384) : SphincsSecurity.ChainPads := fun lay i =>
  (Ref.ofList 16 (Ref.slice (Ref.toList w) (Ref.blockOff lay.val i.val + 16) 16),
    Ref.ofList 16 (Ref.slice (Ref.toList w) (Ref.blockOff lay.val i.val + 32) 16))

/-! ## The compact signature -/

/-- The authentication nodes of a signature: the nodes of segments `0 .. 28`, concatenated. -/
def authNodes (σ : Signature) : List Digest :=
  (List.ofFn fun j => List.ofFn (σ.fts.segments j).nodes).flatten

/-- One layer: the 42 chain values and the path. The counter is not part of the compact
signature: the expansion recomputes it. -/
def layerBytes (σ : Signature) (lay : Layer) : List Byte :=
  (List.ofFn fun i => dv ((σ.layers lay).chainValues i)).flatten ++
    (List.ofFn fun j => dv ((σ.layers lay).path j)).flatten

/-- **The compact signature bytes**: `rho | 15 secrets | 117 authentication-node slots (the
segments' nodes in order, zero padded, cut at 117) | layer bodies 0..4` (no counters). -/
def compressList (σ : Signature) : List Byte :=
  dv σ.randomness ++ (List.ofFn fun s => dv (σ.fts.secrets s)).flatten ++
    (((authNodes σ).map dv).flatten ++ Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM) ++
    (List.ofFn (layerBytes σ)).flatten

/-- **The compact signature**. -/
def compress (σ : Signature) : Bytes 6032 := Ref.ofList 6032 (compressList σ)

/-! ## The abstract expansion -/

open SphincsSecurity.Concrete (treeIndexAt leafIndexAt encodingSearch recoverChain leafHash treeFold
  signaturePath) in
/-- The abstract counter phase on the witness-shaped signature `S0`: layers `k-1, .., 0` from `M`
(the signer's `encodingSearch` from `0`; below the top layer, the verifier's chains, leaf and fold).
Returns the counters, layer 0 first. -/
def aLayers (index : SphincsSecurity.Index) (S0 : Signature) : Nat → Digest → AComp (Option (List Nat))
  | 0, _ => pure (some [])
  | 1, M => do
    let lay : Layer := ⟨0, by decide⟩
    match ← encodingSearch (m := AComp) 0 lay (treeIndexAt index lay) (leafIndexAt index lay) M
        SphincsSecurity.encodingAttemptLimit 0 with
    | none => pure none
    | some (c, _) => pure (some [c.toNat])
  | n + 2, M =>
    if h : n + 1 < SphincsSecurity.numLayers then do
      let lay : Layer := ⟨n + 1, h⟩
      match ← encodingSearch (m := AComp) 0 lay (treeIndexAt index lay) (leafIndexAt index lay) M
          SphincsSecurity.encodingAttemptLimit 0 with
      | none => pure none
      | some (c, enc) =>
        let ends ← SphincsSecurity.Concrete.sequenceFin (m := AComp) fun ch =>
          recoverChain 0 lay (treeIndexAt index lay) (leafIndexAt index lay) ch (enc ch)
            ((S0.layers lay).chainValues ch)
        let leaf ← leafHash (m := AComp) 0 lay (treeIndexAt index lay) (leafIndexAt index lay) ends
        let root ← treeFold (m := AComp) 0 lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath S0 lay) (SphincsSecurity.layerHeight lay) leaf
        match ← aLayers index S0 (n + 1) root with
        | none => pure none
        | some cs => pure (some (cs ++ [c.toNat]))
    else pure none

/-- **The abstract expansion**: the digest of `rho = σ[0..16)` and the message, the reference's
pure partial witness `Ref.expandOf` (which fails on malformed signatures), the abstract PORS stack
machine on it (the message of the bottom layer), the counter phase, the counters written. -/
def aExpand (m : Message) (pk : PublicKey) (σ : Bytes 6032) : AComp (Option (Bytes 16384)) := do
  let d ← SphincsSecurity.Concrete.messageDigest (m := AComp) 0 pk.root m
    (Ref.ofList 16 (Ref.sigRho (Ref.toList σ)))
  match Ref.expandOf (Ref.toList σ) d.toNat with
  | none => pure none
  | some w0 =>
    let index := SphincsSecurity.Concrete.digestIndex d
    match ← SphincsSecurity.Concrete.ftsRecover (m := AComp) 0 index
        (SphincsSecurity.Concrete.slotValue (SphincsSecurity.Concrete.digestLeaves d)) (witFts w0) with
    | none => pure none
    | some M =>
      match ← aLayers index (witSig w0) SphincsSecurity.numLayers M with
      | none => pure none
      | some cs => pure (some (Ref.ofList 16384 (Ref.withCounters w0 cs)))

/-! ## Basic facts -/

theorem length_wbytes (w : List Byte) (o n : Nat) : (Ref.wbytes w o n).length = n := by
  simp [Ref.wbytes]

theorem dv_wdig (w : List Byte) (o : Nat) : dv (wdig w o) = Ref.wbytes w o 16 :=
  Ref.toList_ofList 16 _ (length_wbytes w o 16)

theorem length_layerBytes (σ : Signature) (lay : Layer) :
    (layerBytes σ lay).length = Ref.bodyBytes lay.val := by
  simp only [layerBytes, List.length_append]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _), length_flatten_ofFn _ 16 (fun j => length_dv _)]
  fin_cases lay <;> rfl

theorem length_compressList (σ : Signature) : (compressList σ).length = 6032 := by
  simp only [compressList, List.length_append, length_dv, List.length_take, Ref.zeros,
    List.length_replicate]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _)]
  have hl : (List.ofFn (layerBytes σ)).flatten.length = 3904 := by
    rw [List.length_flatten, List.map_ofFn]
    simp only [Function.comp_def, length_layerBytes, List.sum_ofFn]
    decide
  rw [hl]
  simp only [SphincsSecurity.ftsOpenings, Ref.porsM]
  omega

theorem toList_compress (σ : Signature) : Ref.toList (compress σ) = compressList σ :=
  Ref.toList_ofList 6032 _ (length_compressList σ)

/-! ## The pad decoder -/

theorem blockOff_bound (lay : Layer) (i : ChainIndex) : Ref.blockOff lay.val i.val + 64 ≤ 16384 := by
  have h1 := lay.isLt; have h2 := i.isLt
  simp only [SphincsSecurity.numLayers, SphincsSecurity.numChains] at h1 h2
  rw [Ref.blockOff_eq]; omega

theorem wdig_eq_slice (w : List Byte) (o : Nat) (h : o + 16 ≤ w.length) :
    dv (wdig w o) = Ref.slice w o 16 := by
  rw [dv_wdig]
  apply List.ext_getElem (by simp [Ref.wbytes, Ref.slice]; omega)
  intro j h1 h2
  simp only [Ref.wbytes, List.length_map, List.length_range] at h1
  simp only [Ref.wbytes, Ref.slice, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The two pad digests are the two halves of the 32 pad bytes. -/
theorem dv_padDec (w : Bytes 16384) (lay : Layer) (i : ChainIndex) :
    dv (padDec w lay i).1 ++ dv (padDec w lay i).2 = Ref.witPad (Ref.toList w) lay.val i.val := by
  have hb := blockOff_bound lay i
  have hl : (Ref.toList w).length = 16384 := Ref.length_toList w
  simp only [padDec]
  rw [dv_ofList_slice _ _ (by omega), dv_ofList_slice _ _ (by omega), Ref.witPad,
    show Ref.blockOff lay.val i.val + 32 = Ref.blockOff lay.val i.val + 16 + 16 by omega,
    show (32 : Nat) = 16 + 16 from rfl, slice_split]

/-- The pad bytes as the abstract chain payload writes them (`bytesLE 16 pad.1 ++ bytesLE 16 pad.2`). -/
theorem toB_padDec (w : Bytes 16384) (lay : Layer) (i : ChainIndex) :
    toB (SphincsSecurity.bytesLE 16 (padDec w lay i).1 ++ SphincsSecurity.bytesLE 16 (padDec w lay i).2) =
      Ref.witPad (Ref.toList w) lay.val i.val := by
  rw [toB_append, toB_bytesLE, toB_bytesLE]
  exact dv_padDec w lay i

theorem dv_zero_pad : dv 0 = Ref.zeros 16 := by decide

/-- **A pad is zero iff its 32 witness bytes are zero.** -/
theorem padDec_eq_zero_iff (w : Bytes 16384) (lay : Layer) (i : ChainIndex) :
    padDec w lay i = 0 ↔ Ref.witPad (Ref.toList w) lay.val i.val = Ref.zeros 32 := by
  rw [← dv_padDec w lay i, show Ref.zeros 32 = Ref.zeros 16 ++ Ref.zeros 16 from rfl]
  constructor
  · intro h; rw [h]; show dv 0 ++ dv 0 = _; rw [dv_zero_pad]
  · intro h
    have h' := List.append_inj h (by rw [length_dv]; rfl)
    rw [← dv_zero_pad] at h'
    exact Prod.ext (dv_injective h'.1) (dv_injective h'.2)

end SigGolfCandidate.Equiv
