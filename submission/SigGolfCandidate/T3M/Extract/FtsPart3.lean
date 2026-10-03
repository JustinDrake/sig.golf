import SigGolfCandidate.T3M.Extract.FtsPart2

namespace SigGolfCandidate.T3M.FtsExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem leavesHonest_selOk (sig : Signature) (pads : Pads) (secret : Nat → Digest) (coord : Nat) (sel : Selection)
    (hs : SelOk sel) (h : LeavesHonest coord (selectedLeaves sel) (coordValues sig coord) pads secret 7 sel.bucket) :
    ∀ j < 3, sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ = secret (selLeaf sel j) ∧
      pads.leaf ⟨(3 * coord + j) % 22, Nat.mod_lt _ (by decide)⟩ = 0 ∧
      pads.leaf ⟨(3 * coord + j + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0 := by
  intro j hj
  have hsel := hs.selected
  have h01 := hs.s01
  have h12 := hs.s12
  have h2 := hs.l2
  have hb := hs.b
  have e0 : selLeaf sel 0 = sel.bucket * 128 + sel.leaves.getD 0 0 := rfl
  have e1 : selLeaf sel 1 = sel.bucket * 128 + sel.leaves.getD 1 0 := rfl
  have e2 : selLeaf sel 2 = sel.bucket * 128 + sel.leaves.getD 2 0 := rfl
  generalize sel.leaves.getD 0 0 = x0 at h01 e0
  generalize sel.leaves.getD 1 0 = x1 at h01 h12 e1
  generalize sel.leaves.getD 2 0 = x2 at h12 h2 e2
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have hidx : (selectedLeaves sel).idxOf (selLeaf sel j) = j := by
    rw [hsel, e0, e1, e2]
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2]
    · exact List.idxOf_cons_self
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
  have hmem : selLeaf sel j ∈ selectedLeaves sel := by
    rw [hsel]
    rcases hj3 with rfl | rfl | rfl <;> simp
  have hlo : sel.bucket * 2 ^ 7 ≤ selLeaf sel j := by
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega
  have hhi : selLeaf sel j < (sel.bucket + 1) * 2 ^ 7 := by
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega
  obtain ⟨hv, hp0, hp1⟩ := h _ hmem hlo hhi
  simp only [hidx] at hv hp0 hp1
  refine ⟨?_, hp0, hp1⟩
  rw [← hv]
  simp [coordValues, hj]
theorem honInputL_built (answers : Answers) (index coord : Nat) (level node : Nat) (hl : level < 11)
    (hn : node < 2 ^ (11 - (level + 1))) :
    honInputL answers index coord (fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0)
        (level + 1) node =
      nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
        (treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level (2 * node)) 0
        (treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level (2 * node + 1)) := by
  have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
    rw [← pow_succ']; congr 1; omega
  simp only [honInputL]
  rw [honL_built answers index coord level (2 * node) (by omega) (by omega),
    honL_built answers index coord level (2 * node + 1) (by omega) (by omega)]
def builtSecret (answers : Answers) (index : Nat) : Nat → Nat → Digest :=
  fun c g => (evalWithAnswerFn answers (buildFts index c)).2.getD g 0
theorem honRoots_built (answers : Answers) (index : Nat) :
    honRoots answers index (builtSecret answers index) =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0 := by
  unfold honRoots
  apply List.map_congr_left
  intro c _
  exact honL_built answers index c 11 0 le_rfl (by decide)
theorem recoverFtsP_built_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (v : Digest) (hc : ChosenOk chosen)
    (hrun : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some v)
    (hroot : v = evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0))) :
    ((∀ q ∈ queried answers (recoverFtsP sig pads index chosen),
        q = .inl (.inr (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧
          q = .inl (.inr (honInputL answers index c (builtSecret answers index c) l n))) ∧
      ∀ c < 7, ∀ j < 3,
        sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ =
          builtSecret answers index c (selLeaf (chosen.getD c ⟨0, []⟩) j) ∧
        pads.leaf ⟨(3 * c + j) % 22, Nat.mod_lt _ (by decide)⟩ = 0 ∧
        pads.leaf ⟨(3 * c + j + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0) ∨
    ∃ actual, .inl (.inr actual) ∈ queried answers (recoverFtsP sig pads index chosen) ∧
      ((HashHit answers (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0))) actual ∧
        Extract.SameHeader actual (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧
          HashHit answers (honInputL answers index c (builtSecret answers index c) l n) actual ∧
          Extract.SameHeader actual (honInputL answers index c (builtSecret answers index c) l n)) := by
  have h := recoverFtsP_extract answers sig pads index chosen (builtSecret answers index) v
    (fun c hc' => (hc c hc').b) hrun (by rw [honRoots_built]; exact hroot)
  rw [honRoots_built] at h
  rcases h with ⟨hq, hl⟩ | hhit
  · exact Or.inl ⟨hq, fun c hc' => leavesHonest_selOk sig pads (builtSecret answers index c) c _ (hc c hc') (hl c hc')⟩
  · exact Or.inr hhit
theorem honestInput_forest (answers : Answers) (index : Nat) :
    Extract.honestInput answers (.forest index) = pad64 (Extract.forestInput index
      ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) := rfl
theorem honestInput_ftsLeaf (answers : Answers) (index coord leaf : Nat) :
    Extract.honestInput answers (.ftsLeaf index coord leaf) =
      honInputL answers index coord (builtSecret answers index coord) 0 leaf := by
  simp only [Extract.honestInput, pad64_ftsLeafInputP]; rfl
theorem honestInput_ftsNode (answers : Answers) (index coord level node : Nat) (hl : level < 11)
    (hn : node < 2 ^ (11 - (level + 1))) :
    Extract.honestInput answers (.ftsNode index coord level node) =
      honInputL answers index coord (builtSecret answers index coord) (level + 1) node := by
  rw [show builtSecret answers index coord = fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0 from rfl,
    honInputL_built answers index coord level node hl hn]
  simp only [Extract.honestInput, pad64_nodeInputP, Nat.sub_sub]; rfl
theorem honInputL_pos (answers : Answers) (index coord l n : Nat) (hl : l ≤ 11) (hn : n < 2 ^ (11 - l)) :
    (n < 2048 ∧ honInputL answers index coord (builtSecret answers index coord) l n =
        Extract.honestInput answers (.ftsLeaf index coord n) ∧ l = 0) ∨
      ∃ level, l = level + 1 ∧ level < 11 ∧ n < 2 ^ (11 - (level + 1)) ∧
        honInputL answers index coord (builtSecret answers index coord) l n =
          Extract.honestInput answers (.ftsNode index coord level n) := by
  cases l with
  | zero => exact Or.inl ⟨by simpa using hn, (honestInput_ftsLeaf ..).symm, rfl⟩
  | succ level => exact Or.inr ⟨level, rfl, by omega, hn, (honestInput_ftsNode answers index coord level n (by omega) hn).symm⟩
def FtsShaped (answers : Answers) (N : HashOutput) (w : WBytes) : Prop :=
  (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)),
      q = .inl (.inr (Extract.honestInput answers (.forest (N.toNat % 2 ^ 31)))) ∨
      ∃ c < 7, (∃ leaf < 2048, q = .inl (.inr (Extract.honestInput answers (.ftsLeaf (N.toNat % 2 ^ 31) c leaf)))) ∨
        ∃ level < 11, ∃ node < 2 ^ (11 - (level + 1)),
          q = .inl (.inr (Extract.honestInput answers (.ftsNode (N.toNat % 2 ^ 31) c level node)))) ∧
  ∀ c < 7, ∀ j < 3,
    wsecret w (3 * c + j) = Extract.ftsSecret answers (N.toNat % 2 ^ 31) c (selLeaf ((selections N).getD c ⟨0, []⟩) j) ∧
    wleafPad w (3 * c + j) = 0 ∧ wleafPad w (3 * c + j + 1) = 0
theorem ftsExtractSpecN_holds (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (Extract.honestForest answers (N.toNat % 2 ^ 31))) :
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))) ∨
      FtsShaped answers N w := by
  have h := recoverFtsP_built_extract answers (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31)
    (selections N) _ (chosenOk_of N hS.1) hrun rfl
  rcases h with ⟨hq, hl⟩ | ⟨actual, hmem, ⟨hh, hsh⟩ | ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
  · right
    refine ⟨fun q hq' => ?_, fun c hc j hj => ?_⟩
    · rcases hq q hq' with hf | ⟨c, hc, l, n, hl, hn, rfl⟩
      · exact Or.inl (by rw [hf, honestInput_forest])
      · refine Or.inr ⟨c, hc, ?_⟩
        rcases honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
        · exact Or.inl ⟨n, hn', by rw [he]⟩
        · exact Or.inr ⟨level, hlev, n, hn', by rw [he]⟩
    · obtain ⟨hs, hp0, hp1⟩ := hl c hc j hj
      have m21 : (c * 3 + j) % 21 = 3 * c + j := by rw [Nat.mod_eq_of_lt (by omega)]; ring
      have m22 : (3 * c + j) % 22 = 3 * c + j := Nat.mod_eq_of_lt (by omega)
      have m22' : (3 * c + j + 1) % 22 = 3 * c + j + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [witDecP, padDecP, m21, m22, m22'] at hs hp0 hp1
      exact ⟨hs, hp0, hp1⟩
  · left
    have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
    exact ⟨.forest _, actual, hidx, hmem, by rw [honestInput_forest]; exact hh, by rw [honestInput_forest]; exact hsh⟩
  · left
    have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
    rcases honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
    · exact ⟨.ftsLeaf _ c n, actual, ⟨by omega, hidx, by omega⟩, hmem, by rw [← he]; exact hh,
        by rw [← he]; exact hsh⟩
    · exact ⟨.ftsNode _ c level n, actual, ⟨by omega, hidx, hlev, by simpa only [Nat.sub_sub] using hn'⟩, hmem,
        by rw [← he]; exact hh, by rw [← he]; exact hsh⟩
end SigGolfCandidate.T3M.FtsExtract
