import SigGolfCandidate.T3M.Witness.Queries

namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd)
open SphincsSecurity (bytesLE)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (builtTree answers lay tree) (height lay) 0
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  (evalWithAnswerFn answers (buildFts index coord)).1
def ftsSecret (answers : Answers) (index coord leaf : Nat) : Digest :=
  (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0
def ftsRoot (answers : Answers) (index coord : Nat) : Digest := treeValue (ftsLevels answers index coord) 11 0
def ftsRootsHonest (answers : Answers) (index : Nat) : List Digest := (List.range 7).map (ftsRoot answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (header 2 lay.val tree 0 leaf) (ends.drop 1)
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  listInput (roots.getD 0 0) (header 11 0 index 0 0) (roots.drop 1)
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (forestPk index (ftsRootsHonest answers index))
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : Digest :=
  if h : lay.val < 3 then honestRoot answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2
  else honestForest answers index
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | ftsLeaf (index coord leaf : Nat)
  | ftsNode (index coord level node : Nat)
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
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => header 1 lay.val tree (step + 256 * i) lf
  | .leaf lay tree lf => header 2 lay.val tree 0 lf
  | .node lay tree level nd => header 3 lay.val tree 0 (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 11 0 index 0 0
  | .ftsLeaf index coord lf => header 9 coord index 0 lf
  | .ftsNode index coord level nd => header 10 coord index 0 (2 ^ (11 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 40 ∧ lf < 2 ^ 32 ∧ i < 2 ^ 24 ∧ step < 256
  | .leaf _ tree lf => tree < 2 ^ 40 ∧ lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 40 ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .ftsLeaf index coord lf => coord < 256 ∧ index < 2 ^ 40 ∧ lf < 2 ^ 32
  | .ftsNode index coord level nd => coord < 256 ∧ index < 2 ^ 40 ∧ level < 11 ∧ nd < 2 ^ (11 - level - 1)
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
def SameHeader (actual honest : HashInput) : Prop := hdrBlock actual = hdrBlock honest
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
