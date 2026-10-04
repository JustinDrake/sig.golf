import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Extract.Normalize
import SigGolfCandidate.ClaudeWCT.WCT9.Limits

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd)
open SphincsSecurity (bytesLE)
export SigGolfCandidate.T3M.Extract (canonicalHeader)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (builtTree answers lay tree) (height lay) 0
noncomputable def honestPair (answers : Answers) (lay : Layer) (tree : Nat) : Digest × Digest :=
  (treeValue (builtTree answers lay tree) (height lay - 1) 0, treeValue (builtTree answers lay tree) (height lay - 1) 1)
def wctSeed (answers : Answers) (index coord child chain : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (4 * child + chain / 2))
  if chain % 2 = 0 then pair.1 else pair.2
def wctValue (answers : Answers) (index coord child chain step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chain index coord child chain 0 step (wctSeed answers index coord child chain))
def wctEnds (answers : Answers) (index coord child : Nat) : List Digest :=
  List.ofFn fun t : Fin 7 => wctValue answers index coord child t.val 3
def ftsLeaves (answers : Answers) (index coord : Nat) : List Digest :=
  List.ofFn fun j : Fin 128 => evalWithAnswerFn answers (WCT9.leafHash index coord j.val (wctEnds answers index coord j.val))
def ftsNodes (answers : Answers) (index coord : Nat) : Array Digest :=
  evalWithAnswerFn answers (WCT9.heapBuild index coord (ftsLeaves answers index coord))
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  WCT9.heapLevels (ftsNodes answers index coord)
def ftsPair (answers : Answers) (index coord : Nat) : Digest × Digest :=
  (treeValue (ftsLevels answers index coord) 6 0, treeValue (ftsLevels answers index coord) 6 1)
def ftsPairsHonest (answers : Answers) (index : Nat) : List (Digest × Digest) :=
  (List.range 9).map (ftsPair answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (header 2 lay.val tree 0 leaf) (ends.drop 1)
def wctLeafInput (index coord child : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (header 6 coord index 0 child) (ends.drop 1)
abbrev forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput := WCT9.forestInput index pairs
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.forestPk index (ftsPairsHonest answers index))
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : WCT9.LayerMsg :=
  if h : lay.val < 3 then
    .pair (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).1
      (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).2
  else .forest (honestForest answers index)
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | wctChain (index coord child chain step : Nat)
  | wctLeaf (index coord child : Nat)
  | wctNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (builtTree answers lay tree) level (2 * node)) 0
      (treeValue (builtTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsPairsHonest answers index))
  | .wctChain index coord child chain step => pad64 (WCT9.chainInput index coord child chain step
      (wctValue answers index coord child chain step))
  | .wctLeaf index coord child => pad64 (wctLeafInput index coord child (wctEnds answers index coord child))
  | .wctNode index coord level node => pad64 (nodeInputP 3 (WCT9.nodeLayer coord) index (2 ^ (7 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node)) 0
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => chainHeader lay tree lf i step
  | .leaf lay tree lf => header 2 lay.val tree 0 lf
  | .node lay tree level nd => header 3 lay.val tree 0 (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 15 0 index 0 0
  | .wctChain index coord child t step => WCT9.ftsChainHeader index coord child t step
  | .wctLeaf index coord child => header 6 coord index 0 child
  | .wctNode index coord level nd => WCT9.wctNodeHeader coord index (2 ^ (7 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 8
  | .leaf _ tree lf => tree < 2 ^ 40 ∧ lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 40 ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 7 ∧ step < 3
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
def SameHeader (actual honest : HashInput) : Prop :=
  canonicalHeader (hdrBlock actual) = canonicalHeader (hdrBlock honest)
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
theorem ftsPairsHonest_length (answers : Answers) (index : Nat) : (ftsPairsHonest answers index).length = 9 := by
  simp [ftsPairsHonest]
theorem wctEnds_length (answers : Answers) (index coord child : Nat) :
    (wctEnds answers index coord child).length = 7 := by
  simp [wctEnds]
end ClaudeWCT.W9.T3M.Extract
