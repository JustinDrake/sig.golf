import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3M.Extract.Leaf
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def leafInput (index coord selected : Nat) (ends : List Digest) : HashInput :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (wctHeader 6 coord index 0 selected) ++
    (ends.drop 1).flatMap (bytesLE 16)
def nodeInput (coord index heap : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (header 11 coord index 0 heap) ++ zero16 ++ bytesLE 16 right
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 15 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem leafHash_eq (index coord selected : Nat) (ends : List Digest) :
    leafHash index coord selected ends = shortHash (leafInput index coord selected ends) := rfl
theorem nodeHash_eq (coord index heap : Nat) (left right : Digest) :
    nodeHash 11 coord index heap left right = shortHash (nodeInput coord index heap left right) := rfl
theorem forestPk_eq (index : Nat) (roots : List Digest) :
    forestPk index roots = shortHash (forestInput index roots) := rfl
theorem leafInput_length (index coord selected : Nat) (ends : List Digest) (hlen : ends.length = 7) :
    (leafInput index coord selected ends).length = 128 := by
  simp only [leafInput, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
theorem nodeInput_length (coord index heap : Nat) (left right : Digest) :
    (nodeInput coord index heap left right).length = 64 := by
  simp only [nodeInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem forestInput_length (index : Nat) (roots : List Digest) (hlen : roots.length = 9) :
    (forestInput index roots).length = 160 := by
  simp only [forestInput, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
theorem pad64_of_mod {x : HashInput} (h : x.length % 64 = 0) : pad64 x = x := by
  simp only [pad64, h, Nat.sub_zero, Nat.mod_self, List.replicate_zero, List.append_nil]
inductive FtsInput (index : Nat) : HashInput → Prop
  | chain {coord selected t step : Nat} (value : Digest) (hcoord : coord < 9) (hsel : selected < 128)
      (ht : t < 7) (hstep : step < 3) :
      FtsInput index (pad64 (chainInput index coord selected t step value))
  | leaf {coord selected : Nat} {ends : List Digest} (hcoord : coord < 9) (hsel : selected < 128)
      (hlen : ends.length = 7) :
      FtsInput index (pad64 (leafInput index coord selected ends))
  | node {coord heap : Nat} (left right : Digest) (hcoord : coord < 9) (hlo : 1 ≤ heap) (hhi : heap < 128) :
      FtsInput index (pad64 (nodeInput coord index heap left right))
  | forest {roots : List Digest} (hlen : roots.length = 9) :
      FtsInput index (pad64 (forestInput index roots))
def FtsSeed (index : Nat) (tweak : BitVec 128) : Prop :=
  ∃ coord selected pair, coord < 9 ∧ selected < 128 ∧ pair < 4 ∧
    tweak = header 8 coord index 0 (4 * selected + pair)
def FtsQuery (index : Nat) : Query → Prop
  | .inl (.inr input) => FtsInput index input
  | .inr (.inl tweak) => FtsSeed index tweak
  | _ => False
@[simp] theorem ftsQuery_public (index : Nat) (input : HashInput) :
    FtsQuery index (.inl (.inr input)) ↔ FtsInput index input := Iff.rfl
@[simp] theorem ftsQuery_private (index : Nat) (tweak : BitVec 128) :
    FtsQuery index (.inr (.inl tweak)) ↔ FtsSeed index tweak := Iff.rfl
theorem FtsInput.length {index : Nat} {x : HashInput} (h : FtsInput index x) :
    x.length = 64 ∨ x.length = 128 ∨ x.length = 192 := by
  cases h with
  | chain value hcoord hsel ht hstep =>
      left
      rw [pad64_of_mod (by rw [chainInput_length])]
      exact chainInput_length _ _ _ _ _ _
  | leaf hcoord hsel hlen =>
      right; left
      rw [pad64_of_mod (by rw [leafInput_length _ _ _ _ hlen])]
      exact leafInput_length _ _ _ _ hlen
  | node left right hcoord hlo hhi =>
      left
      rw [pad64_of_mod (by rw [nodeInput_length])]
      exact nodeInput_length _ _ _ _ _
  | forest hlen =>
      right; right
      rw [Cost.pad64_length, forestInput_length _ _ hlen]
theorem FtsInput.length_le {index : Nat} {x : HashInput} (h : FtsInput index x) : x.length ≤ 192 := by
  rcases h.length with h | h | h <;> omega
theorem ftsQuery_good {index : Nat} {q : Query} (h : FtsQuery index q) : GoodQuery q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases (show FtsInput index input from h).length with hl | hl | hl <;>
      exact ⟨by omega, by omega⟩
  · trivial
  · exact h.elim
theorem hdrBlock_pad64_prefix (a : HashInput) (h : BitVec 128) (rest : HashInput) (ha : a.length = 16) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (a ++ bytesLE 16 h ++ rest)) = bytesLE 16 h := by
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [ha, bytesLE_length]; omega)]
  unfold SigGolfCandidate.T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' (bytesLE_length 16 h)]
theorem FtsInput.hdrBlock {index : Nat} {x : HashInput} (h : FtsInput index x) :
    ∃ tag lay position idx, (tag = 5 ∨ tag = 6 ∨ tag = 11 ∨ tag = 15) ∧
      SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (header tag lay index position idx) := by
  cases h with
  | @chain coord selected t step value hcoord hsel ht hstep =>
      refine ⟨5, coord, step + 256 * t, selected, Or.inl rfl, ?_⟩
      unfold chainInput
      rw [List.append_assoc (zero16 ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [zero16]),
        wctHeader_eq_header _ _ _ _ _ (by decide)]
  | @leaf coord selected ends hcoord hsel hlen =>
      refine ⟨6, coord, 0, selected, Or.inr (Or.inl rfl), ?_⟩
      unfold leafInput
      rw [hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _), wctHeader_eq_header _ _ _ _ _ (by decide)]
  | @node coord heap left right hcoord hlo hhi =>
      refine ⟨11, coord, 0, heap, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      unfold nodeInput
      rw [List.append_assoc (bytesLE 16 left ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @forest roots hlen =>
      refine ⟨15, 0, 0, 0, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      unfold forestInput
      rw [hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
theorem bound_shortHashP {P : Query → Prop} (input : HashInput) (k : Nat)
    (hq : P (.inl (.inr (pad64 input)))) (hk : (pad64 input).length / 64 ≤ k) :
    Bound P (fun _ => True) k (shortHash input) := by
  unfold shortHash publicHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simpa only [weight, Nat.add_zero] using hk)
theorem bound_privatePairP {P : Query → Prop} (tag lay tree position index : Nat)
    (hq : P (.inr (.inl (header tag lay tree position index)))) :
    Bound P (fun _ => True) 1 (privatePair tag lay tree position index) := by
  unfold privatePair privateHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simp only [weight]; omega)
theorem allQueriesSatisfy_of_bound {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : AllQueriesSatisfy oa P := by
  induction h with
  | pure a k hp => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, ih⟩
theorem cbound_of_ftsBound {index : Nat} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound (FtsQuery index) Post k oa) : CBound Post k oa :=
  h.mono (fun _ hq => ftsQuery_good hq) (fun _ hp => hp)
section Programs
variable (index : Nat)
theorem ftsBound_chain (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 7) (hend : start + count ≤ 3) :
    Bound (FtsQuery index) (fun _ => True) count (chain index coord selected t start count value) := by
  unfold chain
  refine Bound.foldlM_range'_le start count _ (fun _ _ => True) (fun _ => 1) value trivial
    (fun n hn value _ => ?_) (fun _ _ => trivial) (by simp)
  exact bound_shortHashP _ 1 (FtsInput.chain value hcoord hsel ht (by omega))
    (by simp [Cost.pad64_length, chainInput_length])
theorem ftsBound_leafHash (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 7) :
    Bound (FtsQuery index) (fun _ => True) 2 (leafHash index coord selected ends) := by
  rw [leafHash_eq]
  exact bound_shortHashP _ 2 (FtsInput.leaf hcoord hsel hlen)
    (by rw [pad64_of_mod (by rw [leafInput_length _ _ _ _ hlen]), leafInput_length _ _ _ _ hlen])
theorem ftsBound_nodeHash (coord heap : Nat) (left right : Digest)
    (hcoord : coord < 9) (hlo : 1 ≤ heap) (hhi : heap < 128) :
    Bound (FtsQuery index) (fun _ => True) 1 (nodeHash 11 coord index heap left right) := by
  rw [nodeHash_eq]
  exact bound_shortHashP _ 1 (FtsInput.node left right hcoord hlo hhi)
    (by rw [pad64_of_mod (by rw [nodeInput_length]), nodeInput_length])
theorem ftsBound_forestPk (roots : List Digest) (hlen : roots.length = 9) :
    Bound (FtsQuery index) (fun _ => True) 3 (forestPk index roots) := by
  rw [forestPk_eq]
  exact bound_shortHashP _ 3 (FtsInput.forest hlen)
    (by rw [Cost.pad64_length, forestInput_length _ _ hlen])
theorem ftsBound_privatePair (coord selected pair : Nat) (hcoord : coord < 9) (hsel : selected < 128)
    (hpair : pair < 4) :
    Bound (FtsQuery index) (fun _ => True) 1 (privatePair 8 coord index 0 (4 * selected + pair)) :=
  bound_privatePairP _ _ _ _ _ ⟨coord, selected, pair, hcoord, hsel, hpair, rfl⟩
theorem ftsBound_childHalf (coord selected : Nat) (word : Rank) (pair : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (half : Fin 2) (hcoord : coord < 9) (hsel : selected < 128)
    (hstate : state.1.length = min (2 * pair.val + half.val) 7 ∧ state.2.length = min (2 * pair.val + half.val) 7) :
    Bound (FtsQuery index)
      (fun rows : List Digest × List Digest =>
        rows.1.length = min (2 * pair.val + half.val + 1) 7 ∧ rows.2.length = min (2 * pair.val + half.val + 1) 7)
      (if 2 * pair.val + half.val < 7 then 3 else 0) (childHalf index coord selected word pair seeds state half) := by
  unfold childHalf
  by_cases h : 2 * pair.val + half.val < 7
  · rw [dif_pos h, if_pos h]
    have hd := digit_le_three word ⟨2 * pair.val + half.val, h⟩
    refine (ftsBound_chain index coord selected _ 0 _ _ hcoord hsel h (by omega)).bind'
      (l := digit word ⟨2 * pair.val + half.val, h⟩) (fun value _ => ?_) (by omega)
    refine (ftsBound_chain index coord selected _ _ _ value hcoord hsel h (by omega)).bind'
      (l := 0) (fun last _ => ?_) (by omega)
    exact .pure _ 0 ⟨by simp only [List.length_append, List.length_singleton]; omega,
      by simp only [List.length_append, List.length_singleton]; omega⟩
  · rw [dif_neg h, if_neg h]
    exact .pure _ 0 ⟨by omega, by omega⟩
def pairCost (pair : Nat) : Nat := 1 + 3 * (min (2 * pair + 2) 7 - min (2 * pair) 7)
theorem ftsBound_childRows (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    Bound (FtsQuery index) (fun rows : List Digest × List Digest => rows.1.length = 7 ∧ rows.2.length = 7) 25
      (childRows index coord selected word) := by
  unfold childRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 4) _
    (fun i (rows : List Digest × List Digest) => rows.1.length = min (2 * i) 7 ∧ rows.2.length = min (2 * i) 7)
    pairCost ([], []) ⟨rfl, rfl⟩ (fun i hi rows hrows => ?_)).mono (fun _ h => h)
    (fun rows h => by simpa using h)).mono_k (by simp [pairCost, Finset.sum_range_succ])
  have hi4 : i < 4 := by simpa using hi
  simp only [List.getElem_finRange, Fin.cast_mk]
  refine (ftsBound_privatePair index coord selected i hcoord hsel hi4).bind (fun seeds _ => ?_)
  have hinner := Bound.foldlM_list (P := FtsQuery index) (List.finRange 2)
    (childHalf index coord selected word ⟨i, hi4⟩ seeds)
    (fun h (rows : List Digest × List Digest) =>
      rows.1.length = min (2 * i + h) 7 ∧ rows.2.length = min (2 * i + h) 7)
    (fun h => if 2 * i + h < 7 then 3 else 0) rows (by simpa using hrows) (fun h hh rows' hrows' => by
      have hh2 : h < 2 := by simpa using hh
      simp only [List.getElem_finRange, Fin.cast_mk]
      exact ftsBound_childHalf index coord selected word ⟨i, hi4⟩ seeds rows' ⟨h, hh2⟩ hcoord hsel hrows')
  refine (hinner.mono (fun _ h => h) (fun rows' h => ?_)).mono_k ?_
  · simp only [List.length_finRange] at h
    constructor <;> omega
  · simp only [List.length_finRange, Finset.sum_range_succ, Finset.sum_range_zero]
    interval_cases i <;> simp
theorem ftsBound_buildChild (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    Bound (FtsQuery index) (fun result : Digest × List Digest => result.2.length = 7) 27
      (buildChild index coord selected word) := by
  rw [buildChild_factor]
  refine (ftsBound_childRows index coord selected word hcoord hsel).bind' (l := 2) (fun rows hrows => ?_)
    (by decide)
  exact (ftsBound_leafHash index coord selected rows.1 hcoord hsel hrows.1).bind' (l := 0)
    (fun root _ => .pure _ 0 hrows.2) (by decide)
theorem ftsBound_coordRows (coord : Coord) (selected : Child) (word : Rank) :
    Bound (FtsQuery index) (fun _ => True) 3456 (coordRows index coord selected word) := by
  unfold coordRows
  refine (Bound.foldlM_range (P := FtsQuery index) 128 _ (fun _ _ => True) (fun _ => 27) ([], []) trivial
    (fun j hj state _ => ?_)).mono_k (by simp)
  exact (ftsBound_buildChild index coord.val j word coord.isLt hj).bind' (l := 0)
    (fun result _ => .pure _ 0 trivial) (by decide)
theorem ftsBound_heapBuild (coord : Nat) (hcoord : coord < 9) (leaves : List Digest) :
    Bound (FtsQuery index) (fun _ => True) 127 (heapBuild index coord leaves) := by
  unfold heapBuild
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.range' 1 127).reverse _ (fun _ _ => True)
    (fun _ => 1) _ trivial (fun i hi nodes _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).mono_k
    (by simp)
  have hi' : i < 127 := by simpa using hi
  rw [heap_order i hi']
  exact (ftsBound_nodeHash index coord (127 - i) _ _ hcoord (by omega) (by omega)).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_buildCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    Bound (FtsQuery index) (fun _ => True) 3583 (buildCoordinate index coord selected word) := by
  rw [buildCoordinate_factor]
  refine (ftsBound_coordRows index coord selected word).bind' (l := 127) (fun rows _ => ?_) (by decide)
  exact (ftsBound_heapBuild index coord.val coord.isLt rows.1).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by decide)
theorem ftsBound_forestRows (output : HashOutput) :
    Bound (FtsQuery index) (fun state : List Opening × List Digest => state.1.length = 9 ∧ state.2.length = 9)
      32247 (forestRows index output) := by
  unfold forestRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 9) _
    (fun i (state : List Opening × List Digest) => state.1.length = i ∧ state.2.length = i)
    (fun _ => 3583) ([], []) ⟨rfl, rfl⟩ (fun i hi state hstate => ?_)).mono (fun _ h => h)
    (fun state h => by simpa using h)).mono_k (by simp)
  unfold openingStep
  exact (ftsBound_buildCoordinate index _ _ _).bind' (l := 0)
    (fun result _ => .pure _ 0 ⟨by simp [hstate.1], by simp [hstate.2]⟩) (by decide)
theorem ftsBound_signForest (output : HashOutput) :
    Bound (FtsQuery index) (fun result : List Opening × Digest => result.1.length = 9) 32250
      (signForest index output) := by
  unfold signForest
  refine (ftsBound_forestRows index output).bind' (l := 3) (fun state hstate => ?_) (by decide)
  exact (ftsBound_forestPk index state.2 hstate.2).bind' (l := 0)
    (fun root _ => .pure _ 0 hstate.1) (by decide)
theorem recover_heap_bounds (level s : Nat) (hl : level < 7) (hs : s < 128) :
    1 ≤ 2 ^ (6 - level) + s / 2 ^ (level + 1) ∧ 2 ^ (6 - level) + s / 2 ^ (level + 1) < 128 := by
  interval_cases level <;> simp <;> omega
theorem ftsBound_recoverCoordinate (sig : Signature) (output : HashOutput) (coord : Coord) :
    Bound (FtsQuery index) (fun _ => True) 15 (recoverCoordinate sig index output coord) := by
  unfold recoverCoordinate
  dsimp only
  refine (Bound.mapM_list (P := FtsQuery index) (List.finRange 7) _ (fun i => digit (rank output coord) i)
    (fun i _ => ftsBound_chain index coord.val (child output coord).val i.val _ _ _ coord.isLt
      (child output coord).isLt i.isLt (by have := digit_le_three (rank output coord) i; omega))).bind'
    (l := 9) (fun ends hends => ?_) ?_
  · refine (ftsBound_leafHash index coord.val (child output coord).val ends coord.isLt (child output coord).isLt
      (by simpa using hends)).bind' (l := 7) (fun root _ => ?_) (by decide)
    refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 7) _ (fun _ _ => True) (fun _ => 1) root
      trivial (fun i hi value _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).mono_k (by simp)
    have hi7 : i < 7 := by simpa using hi
    simp only [List.getElem_finRange, Fin.cast_mk]
    have hb := recover_heap_bounds i (child output coord).val hi7 (child output coord).isLt
    exact ftsBound_nodeHash index coord.val _ _ _ coord.isLt hb.1 hb.2
  · rw [← Fin.sum_univ_def, step_count]
theorem ftsBound_recoverFts (sig : Signature) (output : HashOutput) :
    Bound (FtsQuery index) (fun _ => True) 138 (recoverFts sig index output) := by
  unfold recoverFts
  refine (Bound.mapM_list (P := FtsQuery index) (List.finRange 9) _ (fun _ => 15)
    (fun coord _ => ftsBound_recoverCoordinate index sig output coord)).bind' (l := 3)
    (fun roots hroots => ?_) (by simp)
  exact ftsBound_forestPk index roots (by simpa using hroots)
theorem chain_queries (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 7) (hend : start + count ≤ 3) :
    AllQueriesSatisfy (chain index coord selected t start count value) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_chain index coord selected t start count value hcoord hsel ht hend)
theorem leafHash_queries (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 7) :
    AllQueriesSatisfy (leafHash index coord selected ends) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_leafHash index coord selected ends hcoord hsel hlen)
theorem forestPk_queries (roots : List Digest) (hlen : roots.length = 9) :
    AllQueriesSatisfy (forestPk index roots) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestPk index roots hlen)
theorem buildChild_queries (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    AllQueriesSatisfy (buildChild index coord selected word) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildChild index coord selected word hcoord hsel)
theorem buildCoordinate_queries (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildCoordinate index coord selected word)
theorem forestRows_queries (output : HashOutput) :
    AllQueriesSatisfy (forestRows index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestRows index output)
theorem signForest_queries (output : HashOutput) :
    AllQueriesSatisfy (signForest index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_signForest index output)
theorem recoverCoordinate_queries (sig : Signature) (output : HashOutput) (coord : Coord) :
    AllQueriesSatisfy (recoverCoordinate sig index output coord) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverCoordinate index sig output coord)
theorem recoverFts_queries (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFts sig index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverFts index sig output)
end Programs
end ClaudeWCT.WCT9
