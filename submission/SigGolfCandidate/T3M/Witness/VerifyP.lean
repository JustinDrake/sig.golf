import SigGolfCandidate.T3M.Witness.Layout

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def ftsLeafP (index coord leaf : Nat) (pad0 secret pad1 : Digest) : M Digest :=
  shortHash (bytesLE 16 pad0 ++ bytesLE 16 (header 9 coord index 0 leaf) ++ bytesLE 16 secret ++
    bytesLE 16 pad1)
def nodeHashP (tag lay tree heap : Nat) (left pad right : Digest) : M Digest :=
  shortHash (bytesLE 16 left ++ bytesLE 16 (header tag lay tree 0 heap) ++ bytesLE 16 pad ++ bytesLE 16 right)
def chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) : HashInput :=
  bytesLE 16 pad0 ++ bytesLE 16 (header 1 lay.val tree (step + 256 * i) leaf) ++ bytesLE 16 pad1 ++
    bytesLE 16 value
def chainP (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInputP lay tree leaf i step pad0 pad1 value)) value
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ attemptLimit then pure none else some <$> digest (wrho w) m (wdc w)
def selectionsOk (chosen : List Selection) : Bool :=
  chosen.all fun s => match s.leaves with
    | [x0, x1, x2] => decide (x0 < x1) && decide (x1 < x2)
    | _ => false
inductive Pending where
  | leaf (slot g : Nat)
  | merge (heap : Nat) (left : Digest)
def pendingHash (w : WBytes) (index coord : Nat) (node : Digest) : Pending → M Digest
  | .leaf s g => ftsLeafP index coord g (wleafPad w s) (wsecret w s) (wleafPad w (s + 1))
  | .merge heap left => nodeHash 10 coord index heap left node
def foldStep (w : WBytes) (index coord ptr : Nat) (state : Digest × Nat) (r : Nat) : M (Digest × Nat) := do
  let blk := foldBlock ptr r
  let parent ← if state.2 % 2 = 1 then
      nodeHashP 10 coord index (state.2 / 2) (wdig w blk) (wdig w (blk + 32)) state.1
    else nodeHashP 10 coord index (state.2 / 2) state.1 (wdig w (blk + 32)) (wdig w (blk + 48))
  pure (parent, state.2 / 2)
def foldsP (w : WBytes) (index coord ptr a : Nat) (node : Digest) (E : Nat) : M (Digest × Nat) :=
  (List.range a).foldlM (foldStep w index coord ptr) (node, E)
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
def ftsCoordP (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    M (Option (Digest × Nat)) := do
  let some (n0, E0, p0, s0) ← segLoop w index coord [] (.leaf (3 * coord) (selLeaf sel 0))
      (2048 + selLeaf sel 0) ptr 0 | pure none
  let some (n1, E1, p1, s1) ← segLoop w index coord ((n0, E0 ^^^ 1) :: s0)
      (.leaf (3 * coord + 1) (selLeaf sel 1)) (2048 + selLeaf sel 1) p0 n0 | pure none
  let some (n2, E2, p2, s2) ← segLoop w index coord ((n1, E1 ^^^ 1) :: s1)
      (.leaf (3 * coord + 2) (selLeaf sel 2)) (2048 + selLeaf sel 2) p1 n1 | pure none
  if E2 = 1 ∧ s2 = [] then pure (some (n2, p2)) else pure none
def ftsP (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))
  let some (roots, ptr) := state | pure none
  if streamEnd < ptr then return none
  pure (some (← forestPk index roots))
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay j.val) pair.2) value
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
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)
structure Pads where
  leaf : Fin 22 → Digest
  fold : Fin 115 → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
instance : Zero Pads := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0⟩⟩
def foldPad (pads : Pads) (leaves : List Nat) (level node used next : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pads.fold ⟨used % 115, Nat.mod_lt _ (by decide)⟩
  else if !hasLeaf leaves level (2 * node + 1) then pads.fold ⟨next % 115, Nat.mod_lt _ (by decide)⟩
  else 0
def recoverChildP (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (pads : Pads) : Nat → Nat → Nat → M (Option (Digest × Nat))
  | level, node, used =>
      if !hasLeaf leaves level node then
        if h : used < 115 then pure (some (proof ⟨used, h⟩, used + 1)) else pure none
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
          if h : used < 115 then
            let other := sig.proof ⟨used, h⟩
            let pair := if sel.bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
            let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + sel.bucket / 2 ^ (j + 1)) pair.1
              (pads.fold ⟨used, h⟩) pair.2
            pure (some (parent, used + 1))
          else pure none) (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) (some ([], 0))
  let some (roots, used) := state | pure none
  if !(List.range (115 - used)).all (fun j =>
      decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
  pure (some (← forestPk index roots))
def recoverLayerP (sig : Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := (sig.layers lay).path j
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkle lay j) pair.2) value
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
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : Witness) (pads : Pads) : M Bool := do
  let chosen := selections output
  if !digestAdmissible output then return false
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFtsP w.signature pads index chosen | pure false
  let some root ← verifyLayersP w pads index 4 root | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end SigGolfCandidate.T3M
