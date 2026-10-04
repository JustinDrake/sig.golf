import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.WCT9.Honest

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ClaudeWCT.WCT9.heapBuild
theorem wctValue_three (answers : Answers) (index coord child : Nat) (t : Fin 7) :
    wctValue answers index coord child t.val 3 = WCT9.chainEnd answers index coord child t := rfl
theorem wctSeed_eq (answers : Answers) (index coord child : Nat) (t : Fin 7) :
    wctSeed answers index coord child t.val = WCT9.seed answers index coord child t := rfl
theorem wctEnds_eq (answers : Answers) (index coord child : Nat) :
    wctEnds answers index coord child = List.ofFn fun t : Fin 7 => WCT9.chainEnd answers index coord child t := rfl
theorem ftsLeaves_eq (answers : Answers) (index : Nat) (coord : WCT9.Coord) :
    ftsLeaves answers index coord.val = WCT9.coordLeaves answers index coord := rfl
theorem ftsNodes_eq (answers : Answers) (index : Nat) (coord : WCT9.Coord) :
    ftsNodes answers index coord.val = WCT9.coordNodes answers index coord := rfl
theorem ftsPair_eq_coordinatePair (answers : Answers) (index : Nat) (coord : WCT9.Coord) :
    ftsPair answers index coord.val = WCT9.coordinatePair answers index coord := by
  unfold ftsPair ftsLevels
  rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide),
    ftsNodes_eq]
  rfl
theorem ftsPairsHonest_eq (answers : Answers) (index : Nat) :
    ftsPairsHonest answers index = List.ofFn (WCT9.coordinatePair answers index) := by
  unfold ftsPairsHonest
  apply List.ext_getElem (by simp)
  intro n h1 h2
  have hn : n < 9 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact ftsPair_eq_coordinatePair answers index ⟨n, hn⟩
theorem honestForest_eq_recover (answers : Answers) (index : Nat) :
    honestForest answers index =
      evalWithAnswerFn answers (WCT9.forestPk index (List.ofFn (WCT9.coordinatePair answers index))) := by
  unfold honestForest
  rw [ftsPairsHonest_eq]
def heapLevel (heap : Nat) : Nat := 6 - Nat.log 2 heap
def heapNode (heap : Nat) : Nat := heap - 2 ^ Nat.log 2 heap
theorem heap_decomp {heap : Nat} (h1 : 2 ≤ heap) (h2 : heap < 128) :
    heapLevel heap < 6 ∧ heapNode heap < 2 ^ (7 - heapLevel heap - 1) ∧
      2 ^ (7 - heapLevel heap - 1) + heapNode heap = heap := by
  have hle : 2 ^ Nat.log 2 heap ≤ heap := Nat.pow_log_le_self 2 (by omega)
  have hlt : heap < 2 ^ (Nat.log 2 heap + 1) := Nat.lt_pow_succ_log_self (by decide) heap
  have hk : Nat.log 2 heap < 7 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr (by simpa using h2)
  have hk1 : 1 ≤ Nat.log 2 heap := Nat.le_log_of_pow_le (by decide) (by simpa using h1)
  have he : 7 - heapLevel heap - 1 = Nat.log 2 heap := by unfold heapLevel; omega
  refine ⟨by unfold heapLevel; omega, ?_, ?_⟩
  · rw [he]; unfold heapNode; rw [pow_succ] at hlt; omega
  · rw [he]; unfold heapNode; omega
noncomputable def Pos.ofFts (index : Nat) : WCT9.Wots.FtsPos → Pos
  | .chain coord child t step => .wctChain index coord.val child.val t.val step
  | .leaf coord child => .wctLeaf index coord.val child.val
  | .node coord heap => .wctNode index coord.val (heapLevel heap) (heapNode heap)
  | .forest => .forest index
theorem ofFts_bounded {index : Nat} (hidx : index < 2 ^ 31) (p : WCT9.Wots.FtsPos) (hp : p.Bounded) :
    (Pos.ofFts index p).Bounded := by
  cases p with
  | chain coord child t step => exact ⟨hidx, coord.isLt, child.isLt, t.isLt, hp⟩
  | leaf coord child => exact ⟨hidx, coord.isLt, child.isLt⟩
  | node coord heap =>
      obtain ⟨h1, h2, -⟩ := heap_decomp hp.1 hp.2
      exact ⟨hidx, coord.isLt, h1, h2⟩
  | forest => change index < 2 ^ 40; omega
private theorem bytesLE_zero'' : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem honestInput_ofFts (T : Answers) (index : Nat) (p : WCT9.Wots.FtsPos) (hp : p.Bounded) :
    honestInput T (Pos.ofFts index p) = WCT9.Wots.ftsHonestInput T index p := by
  cases p with
  | chain coord child t step => rfl
  | leaf coord child =>
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput, wctLeafInput, listInput, WCT9.leafInput,
        WCT9.leaf_header_eq]
      rfl
  | node coord heap =>
      obtain ⟨h1, h2, h3⟩ := heap_decomp hp.1 hp.2
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput]
      have hpow : 2 ^ (7 - heapLevel heap) = 2 * 2 ^ (7 - heapLevel heap - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 1 ≤ 2 ^ (7 - heapLevel heap - 1) := Nat.one_le_two_pow
      unfold ftsLevels
      rw [WCT9.heapLevels_value _ _ _ (by omega) (by omega), WCT9.heapLevels_value _ _ _ (by omega) (by omega),
        ftsNodes_eq]
      rw [show 2 ^ (7 - heapLevel heap) + 2 * heapNode heap = 2 * heap by omega,
        show 2 ^ (7 - heapLevel heap) + (2 * heapNode heap + 1) = 2 * heap + 1 by omega, h3]
      simp only [nodeInputP, block4, WCT9.nodeInput, bytesLE_zero'', WCT9.nodeLayer, WCT9.wctNodeHeader]
  | forest =>
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput, forestInput, ftsPairsHonest_eq]
theorem ftsHonestQuery_pos {T : Answers} {index : Nat} (hidx : index < 2 ^ 31) {x : HashInput}
    (h : WCT9.Wots.FtsHonestQuery T index (.inl (.inr x))) : ∃ pos : Pos, pos.Bounded ∧ x = honestInput T pos := by
  obtain ⟨p, hp, rfl⟩ := (show ∃ p : WCT9.Wots.FtsPos, p.Bounded ∧ x = WCT9.Wots.ftsHonestInput T index p from h)
  exact ⟨Pos.ofFts index p, ofFts_bounded hidx p hp, (honestInput_ofFts T index p hp).symm⟩
theorem honestForest_eq_wct9 (answers : Answers) (index : Nat) :
    honestForest answers index = WCT9.honestForest answers index := by
  rw [honestForest_eq_recover]
  rfl
end ClaudeWCT.W9.T3M.Extract
