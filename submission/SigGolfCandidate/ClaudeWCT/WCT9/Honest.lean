import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots

namespace ClaudeWCT.WCT9.Wots
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
inductive FtsPos where
  | chain (coord : Coord) (child : Child) (t : Fin 7) (step : Nat)
  | leaf (coord : Coord) (child : Child)
  | node (coord : Coord) (heap : Nat)
  | forest
  deriving DecidableEq
def FtsPos.Bounded : FtsPos → Prop
  | .chain _ _ _ step => step < 3
  | .leaf _ _ => True
  | .node _ heap => 2 ≤ heap ∧ heap < 128
  | .forest => True
def ftsChainValue (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 7) (step : Nat) :
    Digest :=
  evalWithAnswerFn T (chain index coord.val child.val t.val 0 step (seed T index coord.val child.val t))
def ftsHonestInput (T : Answers) (index : Nat) : FtsPos → HashInput
  | .chain coord child t step =>
      pad64 (chainInput index coord.val child.val t.val step (ftsChainValue T index coord child t step))
  | .leaf coord child =>
      pad64 (leafInput index coord.val child.val (List.ofFn (chainEnd T index coord.val child.val)))
  | .node coord heap =>
      pad64 (nodeInput coord.val index heap ((coordNodes T index coord).getD (2 * heap) 0)
        ((coordNodes T index coord).getD (2 * heap + 1) 0))
  | .forest => pad64 (forestInput index (List.ofFn (coordinatePair T index)))
def FtsHonestQuery (T : Answers) (index : Nat) : Query → Prop
  | .inl (.inr input) => ∃ p : FtsPos, p.Bounded ∧ input = ftsHonestInput T index p
  | .inr (.inl tweak) => FtsSeed index tweak
  | _ => False
theorem ftsChainValue_end (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 7) :
    ftsChainValue T index coord child t 3 = chainEnd T index coord.val child.val t := rfl
theorem ftsChainValue_revealed (T : Answers) (index : Nat) (coord : Coord) (child : Child) (word : Rank)
    (t : Fin 7) :
    ftsChainValue T index coord child t (3 - digit word t) = chainValue T index coord.val child.val word t := rfl
theorem ftsHonestQuery_fts {T : Answers} {index : Nat} {q : Query} (h : FtsHonestQuery T index q) :
    FtsQuery index q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · obtain ⟨p, hp, rfl⟩ := (show ∃ p : FtsPos, p.Bounded ∧ input = ftsHonestInput T index p from h)
    cases p with
    | chain coord child t step => exact FtsInput.chain _ coord.isLt child.isLt t.isLt hp
    | leaf coord child => exact FtsInput.leaf coord.isLt child.isLt (by simp)
    | node coord heap => exact FtsInput.node _ _ coord.isLt hp.1 hp.2
    | forest => exact FtsInput.forest (by simp)
  · exact h
  · exact h.elim
theorem chain_zero' (index coord selected t start : Nat) (v : Digest) :
    chain index coord selected t start 0 v = pure v := rfl
theorem queried_chain_one (T : Answers) (index coord selected t s : Nat) (v : Digest) :
    SourceReplay.queried T (chain index coord selected t s 1 v) =
      [.inl (.inr (pad64 (chainInput index coord selected t s v)))] := rfl
theorem eval_ftsChain (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 7)
    (start count : Nat) :
    evalWithAnswerFn T (chain index coord.val child.val t.val start count
      (ftsChainValue T index coord child t start)) = ftsChainValue T index coord child t (start + count) := by
  unfold ftsChainValue
  rw [eval_chain_add, Nat.zero_add]
theorem eval_childRows_ends (T : Answers) (index coord selected : Nat) (word : Rank) :
    (evalWithAnswerFn T (childRows index coord selected word)).1 =
      List.ofFn (fun i : Fin 7 => chainEnd T index coord selected i) := by
  obtain ⟨he, -, hend, -⟩ := eval_childRows T index coord selected word
  apply List.ext_getElem (by simpa only [List.length_ofFn] using he)
  intro i hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using hend ⟨i, by omega⟩ (by omega)
theorem eval_coordRows_leaves (T : Answers) (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    (evalWithAnswerFn T (coordRows index coord selected word)).1 = coordLeaves T index coord := by
  obtain ⟨hlen, hroot, -⟩ := eval_coordRows T index coord selected word
  apply List.ext_getElem (by simpa only [coordLeaves, List.length_ofFn] using hlen)
  intro j hj hk
  simpa only [coordLeaves, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using hroot j (by omega)
namespace Structural
variable (T : Answers) (index : Nat)
theorem sat_query {q : Query} (h : FtsHonestQuery T index q) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (liftM (SigGolfCandidate.T3.Spec.query q)) :=
  Wots.Structural.QueriesSat.query h
theorem sat_privatePair (coord : Coord) (child : Child) (pair : Nat) (hpair : pair < 4) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (privatePair 8 coord.val index 0 (4 * child.val + pair)) := by
  unfold privatePair privateHash
  exact Wots.Structural.QueriesSat.bind
    (Wots.Structural.QueriesSat.query (show FtsHonestQuery T index (.inr (.inl _)) from
      ⟨coord.val, child.val, pair, coord.isLt, child.isLt, hpair, rfl⟩))
    (Wots.Structural.QueriesSat.pure' _)
theorem sat_chain (coord : Coord) (child : Child) (t : Fin 7) (start count : Nat) (hcount : start + count ≤ 3) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (chain index coord.val child.val t.val start count (ftsChainValue T index coord child t start)) := by
  induction count with
  | zero => rw [chain_zero']; exact Wots.Structural.QueriesSat.pure' _
  | succ count ih =>
      rw [chain_add index coord.val child.val t.val start count 1]
      refine Wots.Structural.QueriesSat.bind (ih (by omega)) ?_
      rw [eval_ftsChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      subst hq
      exact ⟨.chain coord child t (start + count), (by simp only [FtsPos.Bounded]; omega), rfl⟩
theorem sat_childHalf (coord : Coord) (child : Child) (word : Rank) (pair : Fin 4) (half : Fin 2)
    (rows : List Digest × List Digest) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (childHalf index coord.val child.val word pair
        (evalWithAnswerFn T (privatePair 8 coord.val index 0 (4 * child.val + pair.val))) rows half) := by
  unfold childHalf
  by_cases h : 2 * pair.val + half.val < 7
  · rw [dif_pos h]
    rw [← seed_half T index coord.val child.val pair half h]
    have hd := digit_le_three word ⟨2 * pair.val + half.val, h⟩
    have hz : seed T index coord.val child.val ⟨2 * pair.val + half.val, h⟩ =
        ftsChainValue T index coord child ⟨2 * pair.val + half.val, h⟩ 0 := rfl
    rw [hz]
    refine Wots.Structural.QueriesSat.bind (sat_chain T index coord child _ 0 _ (by omega)) ?_
    rw [eval_ftsChain, Nat.zero_add]
    exact Wots.Structural.QueriesSat.bind (sat_chain T index coord child _ _ _ (by omega))
      (Wots.Structural.QueriesSat.pure' _)
  · rw [dif_neg h]
    exact Wots.Structural.QueriesSat.pure' _
theorem sat_childRows (coord : Coord) (child : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (childRows index coord.val child.val word) := by
  unfold childRows
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)
  have hi4 : i < 4 := by simpa using hi
  simp only [List.getElem_finRange, Fin.cast_mk]
  refine Wots.Structural.QueriesSat.bind (sat_privatePair T index coord child i hi4) ?_
  exact Wots.Structural.QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial
    (fun h hh rows' _ => ⟨by
      have hh2 : h < 2 := by simpa using hh
      simp only [List.getElem_finRange, Fin.cast_mk]
      exact sat_childHalf T index coord child word ⟨i, hi4⟩ ⟨h, hh2⟩ rows', trivial⟩)
theorem sat_buildChild (coord : Coord) (child : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (buildChild index coord.val child.val word) := by
  rw [buildChild_factor]
  refine Wots.Structural.QueriesSat.bind (sat_childRows T index coord child word) ?_
  rw [eval_childRows_ends]
  refine Wots.Structural.QueriesSat.bind ?_ (Wots.Structural.QueriesSat.pure' _)
  rw [leafHash_eq]
  exact Wots.Structural.sat_shortHash _ ⟨.leaf coord child, trivial, rfl⟩
theorem sat_coordRows (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (coordRows index coord selected word) := by
  unfold coordRows
  refine Wots.Structural.QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun j hj rows _ => ⟨?_, trivial⟩)
  refine Wots.Structural.QueriesSat.bind (sat_buildChild T index coord ⟨j, hj⟩ word) ?_
  exact Wots.Structural.QueriesSat.pure' _
def HeapAgree (final : Array Digest) (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧ ∀ j, 128 - done ≤ j → nodes.getD j 0 = final.getD j 0
theorem sat_heapBuild (coord : Coord) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (heapBuild index coord.val (coordLeaves T index coord)) := by
  have hg := coordNodes_graph T index coord
  obtain ⟨hsize, hleaf, hnode⟩ := hg
  unfold heapBuild
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (HeapAgree (coordNodes T index coord)) _ ?_ ?_
  refine ⟨by simp [coordLeaves], ?_⟩
  · intro j hj
    by_cases hj' : j < 256
    · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
        List.length_replicate, ← hleaf j hj hj']
      simp only [Array.getD_eq_getD_getElem?]
    · have h1 : ((List.replicate 128 (0 : Digest) ++ coordLeaves T index coord).toArray).getD j 0 = 0 := by
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
        rw [List.getElem?_eq_none (by simp [coordLeaves]; omega)]
        rfl
      have h2 : (coordNodes T index coord).getD j 0 = 0 := by
        simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [h1, h2]
  · intro done hdone nodes ⟨hsz, hagree⟩
    have hd : done < 126 := by simpa only [List.length_reverse, List.length_range'] using hdone
    rw [heap_order done hd]
    have hl : nodes.getD (2 * (127 - done)) 0 = (coordNodes T index coord).getD (2 * (127 - done)) 0 :=
      hagree _ (by omega)
    have hr : nodes.getD (2 * (127 - done) + 1) 0 =
        (coordNodes T index coord).getD (2 * (127 - done) + 1) 0 := hagree _ (by omega)
    refine ⟨?_, ?_⟩
    · refine Wots.Structural.QueriesSat.bind ?_ (Wots.Structural.QueriesSat.pure' _)
      rw [hl, hr, nodeHash_eq]
      exact Wots.Structural.sat_shortHash _ ⟨.node coord (127 - done), ⟨by omega, by omega⟩, rfl⟩
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!, hsz], ?_⟩
      intro j hj
      by_cases he : j = 127 - done
      · subst he
        rw [getD_set_self nodes _ _ (by omega), hl, hr]
        exact (hnode (127 - done) (by omega) (by omega) (by omega)).symm
      · rw [getD_set_other nodes _ _ _ (Ne.symm he)]
        exact hagree j (by omega)
theorem sat_buildCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (buildCoordinate index coord selected word) := by
  rw [buildCoordinate_factor]
  refine Wots.Structural.QueriesSat.bind (sat_coordRows T index coord selected word) ?_
  rw [eval_coordRows_leaves]
  exact Wots.Structural.QueriesSat.bind (sat_heapBuild T index coord) (Wots.Structural.QueriesSat.pure' _)
theorem sat_forestRows (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (forestRows index output) := by
  unfold forestRows
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial
    (fun i hi state _ => ⟨?_, trivial⟩)
  unfold openingStep
  refine Wots.Structural.QueriesSat.bind (sat_buildCoordinate T index _ _ _) ?_
  generalize evalWithAnswerFn T (buildCoordinate index _ _ _) = x
  obtain ⟨levels, values⟩ := x
  exact Wots.Structural.QueriesSat.pure' _
theorem sat_forestPk :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (WCT9.forestPk index (List.ofFn (coordinatePair T index))) := by
  rw [forestPk_eq]
  exact Wots.Structural.sat_shortHash _ ⟨.forest, trivial, rfl⟩
theorem sat_signForest (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (signForest index output) := by
  unfold signForest
  refine Wots.Structural.QueriesSat.bind (sat_forestRows T index output) ?_
  rw [eval_forestRows]
  exact Wots.Structural.QueriesSat.bind (sat_forestPk T index) (Wots.Structural.QueriesSat.pure' _)
end Structural
section Congr
variable {T T' : Answers} {index : Nat} (hTT : ∀ q, FtsQuery index q → T q = T' q)
include hTT
theorem eval_congr {α : Type} {p : M α} (hp : AllQueriesSatisfy p (FtsQuery index)) :
    evalWithAnswerFn T p = evalWithAnswerFn T' p :=
  (respects_of_allQueriesSatisfy hp T T' hTT).1
theorem seed_congr (coord : Coord) (child : Child) (t : Fin 7) :
    seed T index coord.val child.val t = seed T' index coord.val child.val t := by
  simp only [seed]
  rw [eval_congr hTT (allQueriesSatisfy_of_bound (ftsBound_privatePair index coord.val child.val (t.val / 2)
    coord.isLt child.isLt (by omega)))]
theorem ftsChainValue_congr (coord : Coord) (child : Child) (t : Fin 7) (step : Nat) (hstep : step ≤ 3) :
    ftsChainValue T index coord child t step = ftsChainValue T' index coord child t step := by
  unfold ftsChainValue
  rw [seed_congr hTT]
  exact eval_congr hTT (chain_queries index _ _ _ 0 step _ coord.isLt child.isLt t.isLt (by omega))
theorem chainEnd_congr (coord : Coord) (child : Child) (t : Fin 7) :
    chainEnd T index coord.val child.val t = chainEnd T' index coord.val child.val t :=
  ftsChainValue_congr hTT coord child t 3 le_rfl
theorem chainValue_congr (coord : Coord) (child : Child) (word : Rank) (t : Fin 7) :
    chainValue T index coord.val child.val word t = chainValue T' index coord.val child.val word t :=
  ftsChainValue_congr hTT coord child t _ (Nat.sub_le _ _)
theorem childRoot_congr (coord : Coord) (child : Child) :
    childRoot T index coord.val child.val = childRoot T' index coord.val child.val := by
  unfold childRoot
  rw [show List.ofFn (fun i : Fin 7 => chainEnd T index coord.val child.val i) =
      List.ofFn (fun i : Fin 7 => chainEnd T' index coord.val child.val i) from
    congrArg List.ofFn (funext (chainEnd_congr hTT coord child))]
  exact eval_congr hTT (leafHash_queries index _ _ _ coord.isLt child.isLt (by simp))
theorem coordLeaves_congr (coord : Coord) : coordLeaves T index coord = coordLeaves T' index coord := by
  unfold coordLeaves
  exact congrArg List.ofFn (funext fun j => childRoot_congr hTT coord j)
theorem coordNodes_congr (coord : Coord) : coordNodes T index coord = coordNodes T' index coord := by
  unfold coordNodes
  rw [coordLeaves_congr hTT coord]
  exact eval_congr hTT (allQueriesSatisfy_of_bound (ftsBound_heapBuild index coord.val coord.isLt _))
theorem coordinatePair_congr (coord : Coord) : coordinatePair T index coord = coordinatePair T' index coord := by
  unfold coordinatePair
  rw [coordNodes_congr hTT]
theorem honestForest_congr : honestForest T index = honestForest T' index := by
  unfold honestForest
  rw [show List.ofFn (coordinatePair T index) = List.ofFn (coordinatePair T' index) from
    congrArg List.ofFn (funext (coordinatePair_congr hTT))]
  exact eval_congr hTT (forestPk_queries index _ (by simp))
theorem expectedOpening_congr (output : HashOutput) (coord : Coord) :
    expectedOpening T index output coord = expectedOpening T' index output coord := by
  unfold expectedOpening
  rw [eval_congr hTT (buildCoordinate_queries index coord _ _)]
theorem ftsHonestInput_congr (p : FtsPos) (hp : p.Bounded) :
    ftsHonestInput T index p = ftsHonestInput T' index p := by
  cases p with
  | chain coord child t step =>
      have hs : step < 3 := hp
      simp only [ftsHonestInput]
      rw [ftsChainValue_congr hTT coord child t step (by omega)]
  | leaf coord child =>
      simp only [ftsHonestInput]
      rw [show List.ofFn (chainEnd T index coord.val child.val) = List.ofFn (chainEnd T' index coord.val child.val)
        from congrArg List.ofFn (funext (chainEnd_congr hTT coord child))]
  | node coord heap =>
      simp only [ftsHonestInput]
      rw [coordNodes_congr hTT]
  | forest =>
      simp only [ftsHonestInput]
      rw [show List.ofFn (coordinatePair T index) = List.ofFn (coordinatePair T' index) from
        congrArg List.ofFn (funext (coordinatePair_congr hTT))]
theorem ftsHonestQuery_congr (q : Query) : FtsHonestQuery T index q ↔ FtsHonestQuery T' index q := by
  rcases q with (coin | input) | (tweak | other)
  · exact Iff.rfl
  · constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, ftsHonestInput_congr hTT p hp⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, (ftsHonestInput_congr hTT p hp).symm⟩
  · exact Iff.rfl
  · exact Iff.rfl
end Congr
namespace Mask
theorem ftsHonestInput_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (p : FtsPos) (hp : p.Bounded) :
    ftsHonestInput (maskAt answers a) index p = ftsHonestInput answers index p :=
  ftsHonestInput_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) p hp
theorem honestForest_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) :
    honestForest (maskAt answers a) index = honestForest answers index :=
  honestForest_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq))
theorem coordinatePair_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (coord : Coord) :
    coordinatePair (maskAt answers a) index coord = coordinatePair answers index coord :=
  coordinatePair_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) coord
theorem expectedOpening_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (output : HashOutput)
    (coord : Coord) :
    expectedOpening (maskAt answers a) index output coord = expectedOpening answers index output coord :=
  expectedOpening_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) output coord
theorem respects_digestSearch (a : ChainAddr) (rho : Digest) (message : Message) :
    ∀ fuel counter, Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Mask.Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Mask.Respects.bind (Wots.Mask.respects_digest a _ _ _) fun output => ?_
      split
      · exact Wots.Mask.Respects.pure' _
      · exact ih _
end Mask
namespace Enc
theorem ftsHonestInput_congr {T T' : Answers} (h : ∀ q, Wots.Enc.NonEnc q → T q = T' q) (index : Nat)
    (p : FtsPos) (hp : p.Bounded) : ftsHonestInput T index p = ftsHonestInput T' index p :=
  Wots.ftsHonestInput_congr (fun _ hq => h _ (ftsQuery_nonEnc hq)) p hp
theorem honestForest_congr {T T' : Answers} (h : ∀ q, Wots.Enc.NonEnc q → T q = T' q) (index : Nat) :
    honestForest T index = honestForest T' index :=
  Wots.honestForest_congr (fun _ hq => h _ (ftsQuery_nonEnc hq))
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Mask.Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Mask.Respects.bind (Wots.Enc.respects_digest _ _ _) fun output => ?_
      split
      · exact Wots.Mask.Respects.pure' _
      · exact ih _
end Enc
namespace Ref
theorem ftsHonestInput_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat) (p : FtsPos)
    (hp : p.Bounded) : ftsHonestInput A index p = ftsHonestInput T index p :=
  Wots.ftsHonestInput_congr (fun _ hq => hAT _ (ftsQuery_short hq)) p hp
theorem coordinatePair_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat) (coord : Coord) :
    coordinatePair A index coord = coordinatePair T index coord :=
  Wots.coordinatePair_congr (fun _ hq => hAT _ (ftsQuery_short hq)) coord
theorem expectedOpening_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat)
    (output : HashOutput) (coord : Coord) :
    expectedOpening A index output coord = expectedOpening T index output coord :=
  Wots.expectedOpening_congr (fun _ hq => hAT _ (ftsQuery_short hq)) output coord
theorem ftsHonestInput_length (T : Answers) (index : Nat) (p : FtsPos) (hp : p.Bounded) :
    (ftsHonestInput T index p).length ≤ SeccLaw.maxInputLength := by
  have h := ftsHonestQuery_fts (T := T) (index := index) (q := .inl (.inr (ftsHonestInput T index p)))
    ⟨p, hp, rfl⟩
  exact ftsQuery_short h
end Ref
namespace Structural
theorem sat_digestSearch_of (T : Answers) (Q : Query → Prop) (rho : Digest) (message : Message)
    (hQ : ∀ counter : BitVec 32, Q (.inl (.inr (pad64 (digestInput rho message counter))))) :
    ∀ fuel counter, Wots.Structural.QueriesSat T Q (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Structural.QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Structural.QueriesSat.bind (Wots.Structural.sat_publicHash _ (hQ _)) ?_
      split
      · exact Wots.Structural.QueriesSat.pure' _
      · exact ih _
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, Wots.Structural.QueriesSat T (Wots.Structural.HonestQuery T)
      (WCT9.digestSearch rho message counter fuel) :=
  sat_digestSearch_of T _ rho message fun _ => Or.inl (Wots.Structural.posOf_digest _ _ _)
end Structural
end ClaudeWCT.WCT9.Wots
