import SigGolfCandidate.T3M.Witness.Layout

/-! # The byte-level padded verifier `verifyP` (stream W)

`verifyP m pk w` is the Lean transcription of `t3m/ref3/absverify_t3.verify`, query for query: the machine's
check order, its block formats with the free bytes (leaf, fold, chain and Merkle pads) hashed where they lie in
the witness, the W2 stream machine over the fold stream with the cap checked through the pointer, and the
counters/digits/chains/Merkle path of Core's `verifyLayers`. It uses public queries only.

It is written as named pieces so that the machine refinement streams can each own one:
`digestP` (dc check + digest query), `selectionsOk`, `ftsCoordP` (one coordinate of the stream machine; its
segment loop `segLoop`, folds `foldsP`), `ftsP` (seven coordinates, pointer cap, forest pk `forestPk`), `layerP`
(chains, leaf pk, Merkle path of one layer), `layersP` (counter check, encoding, decode, `layerP`, for layers
3..0), and the final comparison.

The second half of the file is Core's verifier with arbitrary pads, `verifyPads` (Core's `verify` with the
padded hash formats; `verifyPads_zero` in `Normal` shows it is `T3.verify` at zero pads): the normal form of
`verifyP` on schedule-shaped streams. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)

/-! ## Padded hash formats (Core's formats with the free 16-byte pads) -/

/-- FTS leaf `[pad0 | header 9 | secret | pad1]` (Core's `ftsLeaf` hashes zero pads). -/
def ftsLeafP (index coord leaf : Nat) (pad0 secret pad1 : Digest) : M Digest :=
  shortHash (bytesLE 16 pad0 ++ bytesLE 16 (header 9 coord index 0 leaf) ++ bytesLE 16 secret ++
    bytesLE 16 pad1)

/-- Tree node `[left | header tag | pad | right]` (Core's `nodeHash` hashes a zero pad). -/
def nodeHashP (tag lay tree heap : Nat) (left pad right : Digest) : M Digest :=
  shortHash (bytesLE 16 left ++ bytesLE 16 (header tag lay tree 0 heap) ++ bytesLE 16 pad ++ bytesLE 16 right)

/-- Chain step input `[pad0 | header 1 | pad1 | value]` (Core's `chainInput` has zero pads). -/
def chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) : HashInput :=
  bytesLE 16 pad0 ++ bytesLE 16 (header 1 lay.val tree (step + 256 * i) leaf) ++ bytesLE 16 pad1 ++
    bytesLE 16 value

/-- Core's `chain` with the two pads of the chain block, hashed unchanged at every step. -/
def chainP (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInputP lay tree leaf i step pad0 pad1 value)) value

/-! ## Digest and selections -/

/-- The dc check and the digest query `[rho | T(12, dc) | message]` (Core's `digest` on the witness fields);
`none` when `dc ≥ 2^20` (no query). -/
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ attemptLimit then pure none else some <$> digest (wrho w) m (wdc w)

/-- The machine's selection check: each sorted triple strictly increasing (Core checks `Nodup`; the cap is
checked by the stream pointer, `ftsP`). -/
def selectionsOk (chosen : List Selection) : Bool :=
  chosen.all fun s => match s.leaves with
    | [x0, x1, x2] => decide (x0 < x1) && decide (x1 < x2)
    | _ => false

/-! ## The fold stream machine (W2 format)

Header byte `b` of a segment: `a = b % 16` folds, `merge = b / 16 % 2`, `t = b / 32 % 2` (checked against the
current heap index's parity when `a > 0`); bits 6..7 and header bytes 1..7 are never read. -/

/-- What a segment hashes before its folds: the FTS leaf of slot `slot` (global leaf `g`) or a merge of the
stacked node `left` with the current node (parent heap index `heap`). -/
inductive Pending where
  | leaf (slot g : Nat)
  | merge (heap : Nat) (left : Digest)

/-- The pending hash of a segment: a leaf block hashed in place `[P_s | T(9) | secret_s | P_{s+1}]`, or a
merge `[left | T(10, heap) | 0 | node]` in a zeroed scratch frame (Core's `nodeHash`). -/
def pendingHash (w : WBytes) (index coord : Nat) (node : Digest) : Pending → M Digest
  | .leaf s g => ftsLeafP index coord g (wleafPad w s) (wsecret w s) (wleafPad w (s + 1))
  | .merge heap left => nodeHash 10 coord index heap left node

/-- One fold: block `r` of the segment at `ptr` holds the sibling at `L` when the current heap index `E` is odd
(the node is a right child) else at `R`, and the pad at `+32`; parent heap `E / 2`. -/
def foldStep (w : WBytes) (index coord ptr : Nat) (state : Digest × Nat) (r : Nat) : M (Digest × Nat) := do
  let blk := foldBlock ptr r
  let parent ← if state.2 % 2 = 1 then
      nodeHashP 10 coord index (state.2 / 2) (wdig w blk) (wdig w (blk + 32)) state.1
    else nodeHashP 10 coord index (state.2 / 2) state.1 (wdig w (blk + 32)) (wdig w (blk + 48))
  pure (parent, state.2 / 2)

/-- The `a` folds of the segment at `ptr`, from node `node` at heap index `E`. -/
def foldsP (w : WBytes) (index coord ptr a : Nat) (node : Digest) (E : Nat) : M (Digest × Nat) :=
  (List.range a).foldlM (foldStep w index coord ptr) (node, E)

/-- The segment loop of one leaf (`absverify_t3.fts`'s `while True`): read the header at `ptr`, reject `a > 11`
and a parity mismatch, hash the pending block, fold `a` times, advance the pointer; then stop (no merge, or
reject a merge on an empty stack) or pop the stacked `(pnode, Q)`, reject `Q ≠ E`, and continue with the merge
pending at `E / 2`. Returns `(node, E, ptr, stack)`; structural on the stack (at most two stacked nodes). -/
def segLoop (w : WBytes) (index coord : Nat) :
    List (Digest × Nat) → Pending → Nat → Nat → Digest →
      M (Option (Digest × Nat × Nat × List (Digest × Nat)))
  | stack, pending, E, ptr, node => do
      let b := (wbyte w ptr).toNat
      if 11 < b % 16 then return none
      if 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2 then return none
      let node ← pendingHash w index coord node pending
      let (node, E) ← foldsP w index coord ptr (b % 16) node E
      let ptr := segNext ptr (b % 16)
      match stack with
      | [] => return if b / 16 % 2 = 1 then none else some (node, E, ptr, [])
      | (pnode, Q) :: rest =>
          if b / 16 % 2 = 0 then return some (node, E, ptr, (pnode, Q) :: rest)
          if Q ≠ E then return none
          segLoop w index coord rest (.merge (E / 2) pnode) (E / 2) ptr node

/-- One coordinate of the stream machine from the header pointer `ptr`: leaves `j = 0, 1, 2` start at heap index
`2048 + g_j` with the leaf of slot `3 coord + j` pending; after leaves 0 and 1 the node is pushed with
`Q = E ^^^ 1`; reject (`coord-final`) unless the last leaf ends at `E = 1` with an empty stack. Returns the
coordinate root and the next header pointer. -/
def ftsCoordP (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    M (Option (Digest × Nat)) := do
  let some (n0, E0, p0, s0) ← segLoop w index coord [] (.leaf (3 * coord) (selLeaf sel 0))
      (2048 + selLeaf sel 0) ptr 0 | pure none
  let some (n1, E1, p1, s1) ← segLoop w index coord ((n0, E0 ^^^ 1) :: s0)
      (.leaf (3 * coord + 1) (selLeaf sel 1)) (2048 + selLeaf sel 1) p0 n0 | pure none
  let some (n2, E2, p2, s2) ← segLoop w index coord ((n1, E1 ^^^ 1) :: s1)
      (.leaf (3 * coord + 2) (selLeaf sel 2)) (2048 + selLeaf sel 2) p1 n1 | pure none
  if E2 = 1 ∧ s2 = [] then pure (some (n2, p2)) else pure none

/-- The FTS: coordinates 0..6 over one stream pointer, then reject (`fold-limit`) if the pointer passed
`streamEnd` (more than 121 fold blocks), then the forest pk `[root_0 | T(11) | root_1 .. root_6]`. -/
def ftsP (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))
  let some (roots, ptr) := state | pure none
  if streamEnd < ptr then return none
  pure (some (← forestPk index roots))

/-! ## Layers -/

/-- Chains of layer `lay` (chain `i` from its digit to `2^w - 1`, both pads of its block hashed at every step),
leaf pk (Core's `leafHash`), and the Merkle path (sibling at `L` iff bit `j` of the leaf index is 1, pad at
`+32`): the layer root. Core's `recoverLayer` with witness values, siblings and pads. -/
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (2 ^ width lay i.val - 1 - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay j.val) pair.2) value

/-- Layers `n-1, .., 0` (Core's `verifyLayers` with the witness counters and `layerP`). -/
def layersP (w : WBytes) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0, root => pure (some root)
  | n + 1, root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wctr w lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← layerP w index lay digits
      layersP w index n value

/-! ## The verifier -/

/-- `absverify_t3.verify`: dc check, digest, selections check, FTS stream machine with the pointer cap and the
forest pk, layers 3..0, comparison with `pk`. -/
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)

/-! ## Core's verifier with pads

`Pads` are the free bytes of a witness, structured: the 22 leaf pads `P_0 .. P_21` (leaf `s` hashes `P_s` and
`P_{s+1}`), one fold pad per proof slot (each fold block carries exactly one proof slot; merges hash zero), two
pads per chain block and one per Merkle block. `verifyPads` is Core's `verify` with these pads in the hashed
formats; at zero pads it is `T3.verify` (`verifyPads_zero`). -/

/-- The free bytes of a witness. -/
structure Pads where
  leaf : Fin 22 → Digest
  fold : Fin 121 → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest

/-- All pads zero (the honest witness). -/
instance : Zero Pads := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0⟩⟩

/-- Fold pad of the node `(level + 1, node)` of Core's DFS: the slot consumed by its empty child (`used` when
the left child is empty, `next` when the right one is), zero for a merge (both children non-empty). -/
def foldPad (pads : Pads) (leaves : List Nat) (level node used next : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pads.fold ⟨used % 121, Nat.mod_lt _ (by decide)⟩
  else if !hasLeaf leaves level (2 * node + 1) then pads.fold ⟨next % 121, Nat.mod_lt _ (by decide)⟩
  else 0

/-- Core's `recoverChild` with pads: the leaf of slot `s = 3 coord + j` hashes `P_s`, `P_{s+1}`; a fold hashes
the pad of its proof slot. -/
def recoverChildP (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 121 → Digest) (pads : Pads) : Nat → Nat → Nat → M (Option (Digest × Nat))
  | level, node, used =>
      if !hasLeaf leaves level node then
        if h : used < 121 then pure (some (proof ⟨used, h⟩, used + 1)) else pure none
      else match level with
      | 0 => do
          let s := 3 * coord + leaves.idxOf node
          let value ← ftsLeafP index coord node (pads.leaf ⟨s % 22, Nat.mod_lt _ (by decide)⟩)
            (values.getD (leaves.idxOf node) 0) (pads.leaf ⟨(s + 1) % 22, Nat.mod_lt _ (by decide)⟩)
          pure (some (value, used))
      | level + 1 => do
          let some (left, next) ← recoverChildP index coord leaves values proof pads level (2 * node) used
            | pure none
          let some (right, next') ← recoverChildP index coord leaves values proof pads level (2 * node + 1) next
            | pure none
          let value ← nodeHashP 10 coord index (2 ^ (11 - (level + 1)) + node) left
            (foldPad pads leaves level node used next) right
          pure (some (value, next'))

/-- Core's `recoverFts` with pads (the 3 outer folds hash the pad of their proof slot). -/
def recoverFtsP (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection) :
    M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, used) := state | pure none
      let sel := chosen.getD coord ⟨0, []⟩
      let selected := sel.leaves.map (fun s => sel.bucket * 128 + s)
      let values := (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
      let some (value, next) ← recoverChildP index coord selected values sig.proof pads 7 sel.bucket used
        | pure none
      let result ← (List.range 4).foldlM
        (fun (state : Option (Digest × Nat)) j => do
          let some (value, used) := state | pure none
          if h : used < 121 then
            let other := sig.proof ⟨used, h⟩
            let pair := if sel.bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
            let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + sel.bucket / 2 ^ (j + 1)) pair.1
              (pads.fold ⟨used, h⟩) pair.2
            pure (some (parent, used + 1))
          else pure none) (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) (some ([], 0))
  let some (roots, used) := state | pure none
  if !(List.range (121 - used)).all (fun j =>
      decide (sig.proof ⟨(used + j) % 121, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
  pure (some (← forestPk index roots))

/-- Core's `recoverLayer` with the chain and Merkle pads. -/
def recoverLayerP (sig : Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (2 ^ width lay i.val - 1 - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := (sig.layers lay).path j
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkle lay j) pair.2) value

/-- Core's `verifyLayers` with pads. -/
def verifyLayersP (w : Witness) (pads : Pads) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0, root => pure (some root)
  | n + 1, root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← recoverLayerP w.signature pads index lay digits
      verifyLayersP w pads index n value

/-- Core's verification after the digest query, with pads: admissibility, FTS, layers, comparison. -/
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : Witness) (pads : Pads) : M Bool := do
  let chosen := selections output
  if !digestAdmissible output then return false
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFtsP w.signature pads index chosen | pure false
  let some root ← verifyLayersP w pads index 4 root | pure false
  pure (root == pk)

/-- Core's `verify` with pads. -/
def verifyPads (m : Message) (pk : Digest) (w : Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads

end SigGolfCandidate.T3M
