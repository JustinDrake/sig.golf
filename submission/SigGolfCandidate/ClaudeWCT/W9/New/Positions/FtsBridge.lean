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
def heapLevel (heap : Nat) : Nat := 6 - Nat.log 2 heap
def heapNode (heap : Nat) : Nat := heap - 2 ^ Nat.log 2 heap
theorem heap_decomp {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 128) :
    heapLevel heap < 7 ∧ heapNode heap < 2 ^ (7 - heapLevel heap - 1) ∧
      2 ^ (7 - heapLevel heap - 1) + heapNode heap = heap := by
  have hle : 2 ^ Nat.log 2 heap ≤ heap := Nat.pow_log_le_self 2 (by omega)
  have hlt : heap < 2 ^ (Nat.log 2 heap + 1) := Nat.lt_pow_succ_log_self (by decide) heap
  have hk : Nat.log 2 heap < 7 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr (by simpa using h2)
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
      simp only [nodeInputP, block4, WCT9.nodeInput, bytesLE_zero'']
  | forest =>
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput, forestInput, listInput, WCT9.forestInput,
        ftsRootsHonest_eq]
theorem ftsHonestQuery_pos {T : Answers} {index : Nat} (hidx : index < 2 ^ 31) {x : HashInput}
    (h : WCT9.Wots.FtsHonestQuery T index (.inl (.inr x))) : ∃ pos : Pos, pos.Bounded ∧ x = honestInput T pos := by
  obtain ⟨p, hp, rfl⟩ := (show ∃ p : WCT9.Wots.FtsPos, p.Bounded ∧ x = WCT9.Wots.ftsHonestInput T index p from h)
  exact ⟨Pos.ofFts index p, ofFts_bounded hidx p hp, (honestInput_ofFts T index p hp).symm⟩
theorem honestForest_eq_wct9 (answers : Answers) (index : Nat) :
    honestForest answers index = WCT9.honestForest answers index := by
  rw [honestForest_eq_recover]
  rfl
end ClaudeWCT.W9.T3M.Extract
