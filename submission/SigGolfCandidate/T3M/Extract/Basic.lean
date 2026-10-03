import SigGolfCandidate.T3M.Witness.Queries

/-! # Shared vocabulary of the padded structural extraction (streams PEX-L / PEX-F)

Deterministic extraction on an answers table: either an actual query of the byte verifier is a `HashHit` against
an honest reference input, or the hashed witness bytes are honest-shaped. The honest objects are Core's source
objects evaluated under the same table (`Correctness.builtTree`, `leafEnd`, `leafSeed`, `buildFts`).

* `Pos`: every honest reference position the extraction can name; `honestInput answers pos` is its complete
  (padded) oracle input. The reference's header block (bytes `[16,32)`) is shared by the actual hit input
  (`SameHeader`), so a `FirstHit.Reference` can be read off the actual input's header.
* `HitIn answers qs`: some public query of the list `qs` is a header-preserving `HashHit`.
* `ftsRoots`: the seven-coordinate loop of `ftsP` (the FTS part, PEX-F's domain); `ftsP_eq` splits `ftsP` into it,
  the pointer cap and the tag-11 forest hash. -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd)
open SphincsSecurity (bytesLE)

/-! ## Honest objects -/

/-- Honest root of the layer-`lay` tree `tree` (`treeValue` of Core's built levels). -/
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (builtTree answers lay tree) (height lay) 0

/-- Honest levels of the FTS tree of coordinate `coord` (Core's `buildFts`). -/
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  (evalWithAnswerFn answers (buildFts index coord)).1

/-- Honest FTS secret of global leaf `leaf` of coordinate `coord` (Core's `buildFts` secrets). -/
def ftsSecret (answers : Answers) (index coord leaf : Nat) : Digest :=
  (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0

/-- Honest FTS root of coordinate `coord`. -/
def ftsRoot (answers : Answers) (index coord : Nat) : Digest := treeValue (ftsLevels answers index coord) 11 0

/-- The seven honest FTS roots, in Core's order. -/
def ftsRootsHonest (answers : Answers) (index : Nat) : List Digest := (List.range 7).map (ftsRoot answers index)

/-- Raw input of a "first digest, header, remaining digests" hash (tag-2 leaf pk, tag-11 forest pk). -/
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)

/-- Raw input of Core's `leafHash`. -/
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (header 2 lay.val tree 0 leaf) (ends.drop 1)

/-- Raw input of Core's `forestPk`. -/
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  listInput (roots.getD 0 0) (header 11 0 index 0 0) (roots.drop 1)

/-- Honest forest pk (the honest message of layer 3). -/
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (forestPk index (ftsRootsHonest answers index))

/-- The honest message signed at layer `lay`: the honest root of the layer below (`lay + 1`) for `lay < 3`, the
honest forest pk for `lay = 3`. -/
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : Digest :=
  if h : lay.val < 3 then honestRoot answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2
  else honestForest answers index

/-! ## Reference positions -/

/-- An honest reference position. `node lay tree level node`: the Merkle node at `level + 1` of a hypertree tree
(children at `level`); `ftsNode index coord level node` likewise in an FTS tree. -/
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | ftsLeaf (index coord leaf : Nat)
  | ftsNode (index coord level node : Nat)

/-- The complete honest oracle input at a position (`pad64` applied, as queried). -/
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (builtTree answers lay tree) level (2 * node)) 0
      (treeValue (builtTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsRootsHonest answers index))
  | .ftsLeaf index coord leaf => pad64 (ftsLeafInputP index coord leaf 0 (ftsSecret answers index coord leaf) 0)
  | .ftsNode index coord level node => pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node)) 0
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))

/-- The header of a position's honest input (independent of the answers table: `hdrBlock_honestInput`). -/
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => header 1 lay.val tree (step + 256 * i) lf
  | .leaf lay tree lf => header 2 lay.val tree 0 lf
  | .node lay tree level nd => header 3 lay.val tree 0 (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 11 0 index 0 0
  | .ftsLeaf index coord lf => header 9 coord index 0 lf
  | .ftsNode index coord level nd => header 10 coord index 0 (2 ^ (11 - level - 1) + nd)

/-- Field bounds under which `Pos.hdr` is injective (`Pos.hdr_injective`): every position the extraction names
satisfies them. -/
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 40 ∧ lf < 2 ^ 32 ∧ i < 2 ^ 24 ∧ step < 256
  | .leaf _ tree lf => tree < 2 ^ 40 ∧ lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 40 ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .ftsLeaf index coord lf => coord < 256 ∧ index < 2 ^ 40 ∧ lf < 2 ^ 32
  | .ftsNode index coord level nd => coord < 256 ∧ index < 2 ^ 40 ∧ level < 11 ∧ nd < 2 ^ (11 - level - 1)

/-- The header block (bytes `[16,32)`) of an input. -/
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16

/-- Actual and honest inputs carry the same header block (same tag and position). -/
def SameHeader (actual honest : HashInput) : Prop := hdrBlock actual = hdrBlock honest

/-- A header-preserving distinct-input hit on an honest reference at a bounded position, at an actual public
query of `qs`. (With `Pos.hdr_injective` the position is a function of the actual input: `posOf_hit`.) -/
def HitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ HashHit answers (honestInput answers pos) actual ∧
    SameHeader actual (honestInput answers pos)

theorem HitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} (h : HitIn answers qs)
    (hsub : ∀ q ∈ qs, q ∈ qs') : HitIn answers qs' := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hsub _ hq, hh, hs⟩

theorem HitIn.append_left {answers : Answers} {qs : List Spec.Domain} (qs' : List Spec.Domain)
    (h : HitIn answers qs) : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_left _ hq

theorem HitIn.append_right {answers : Answers} {qs' : List Spec.Domain} (qs : List Spec.Domain)
    (h : HitIn answers qs') : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_right _ hq

/-! ## The FTS split of `ftsP` -/

/-- The seven-coordinate stream loop of `ftsP`: the coordinate roots and the final header pointer. -/
def ftsRoots (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option (List Digest × Nat)) :=
  (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))

theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← ftsRoots w index chosen
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl

end SigGolfCandidate.T3M.Extract
