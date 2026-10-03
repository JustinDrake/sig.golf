import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Arith
import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsSecurity.Proof.SignatureLayout
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ExtractOts
import SigGolfCandidate.SphincsSecurity.Proof.Fts.HonestFts

section



namespace SphincsSecurity.Concrete
def ScheduleRead (r : Nat × Nat) : Prop := r.1 < ftsTreeHeight ∧ r.2 < 2 ^ (ftsTreeHeight - r.1)
def ScheduleGood (state : ScheduleState) : Prop :=
  (∀ segment ∈ state.done, ∀ r ∈ segment.reads, ScheduleRead r) ∧ ∀ r ∈ state.reads, ScheduleRead r
theorem heap_climb (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height ≤ ftsTreeHeight) :
    (2 ^ ftsTreeHeight + v) / 2 ^ height = 2 ^ (ftsTreeHeight - height) + v / 2 ^ height
      ∧ v / 2 ^ height < 2 ^ (ftsTreeHeight - height) := by
  have hsplit : 2 ^ ftsTreeHeight = 2 ^ (ftsTreeHeight - height) * 2 ^ height := by
    rw [← pow_add, Nat.sub_add_cancel hheight]
  have hpos : 0 < 2 ^ height := Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_comm]
  · rw [Nat.div_lt_iff_lt_mul hpos, ← hsplit]
    exact hv
theorem scheduleStep_good (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height < ftsTreeHeight)
    (state : ScheduleState) (hheap : state.heap = (2 ^ ftsTreeHeight + v) / 2 ^ height)
    (hgood : ScheduleGood state) :
    ScheduleGood (scheduleStep state height)
      ∧ (scheduleStep state height).heap = (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) := by
  obtain ⟨hclimb, hoffset⟩ := heap_climb v height hv hheight.le
  have heven : 2 ^ (ftsTreeHeight - height) = 2 * 2 ^ (ftsTreeHeight - height - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) = state.heap / 2 := by
    rw [hheap, div_pow_succ]
  have hfold : ScheduleGood { state with
      reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
      heap := state.heap / 2 } := by
    refine ⟨hgood.1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hgood.2 r hr
    · rw [List.mem_singleton] at hr
      subst r
      refine ⟨hheight, ?_⟩
      obtain ⟨j, hcase⟩ := index_sibling_cases state.heap
      rw [← nat_xor_eq]
      simp only
      rcases hcase with ⟨hc, hx, _⟩ | ⟨hc, hx, _⟩ <;> rw [hx] <;> omega
  unfold scheduleStep
  split
  · rename_i top rest hstack
    split
    · refine ⟨⟨fun segment hsegment => ?_, fun r hr => by simp at hr⟩, hhalf.symm⟩
      rcases List.mem_append.mp hsegment with hsegment | hsegment
      · exact hgood.1 segment hsegment
      · rw [List.mem_singleton] at hsegment
        subst segment
        exact hgood.2
    · exact ⟨hfold, hhalf.symm⟩
  · exact ⟨hfold, hhalf.symm⟩
theorem foldl_scheduleStep_good (v : Nat) (hv : v < 2 ^ ftsTreeHeight) :
    ∀ n, n ≤ ftsTreeHeight → ∀ state : ScheduleState, state.heap = 2 ^ ftsTreeHeight + v →
      ScheduleGood state →
      ScheduleGood ((List.range n).foldl scheduleStep state)
        ∧ ((List.range n).foldl scheduleStep state).heap = (2 ^ ftsTreeHeight + v) / 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro _ state hheap hgood
      simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.div_one]
      exact ⟨hgood, hheap⟩
  | succ n ih =>
      intro hn state hheap hgood
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hgood', hheap'⟩ := ih (by omega) state hheap hgood
      exact scheduleStep_good v n hv (by omega) _ hheap' hgood'
theorem bitLength_xor_le (v w : Nat) (hv : v < 2 ^ ftsTreeHeight) (hw : w < 2 ^ ftsTreeHeight) :
    bitLength (v ^^^ w) ≤ ftsTreeHeight := by
  have hlt : v ^^^ w < 2 ^ ftsTreeHeight := Nat.xor_lt_two_pow hv hw
  unfold bitLength
  split
  · omega
  · rename_i hne
    have := (Nat.log2_lt hne).mpr hlt
    omega
theorem leafClimb_good (v top : Nat) (hv : v < 2 ^ ftsTreeHeight) (htop : top ≤ ftsTreeHeight)
    (state : ScheduleState) (hgood : ScheduleGood state) :
    let climbed := (List.range top).foldl scheduleStep
      { state with heap := 2 ^ ftsTreeHeight ||| v,
                   parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    ScheduleGood { climbed with done := climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩] } := by
  intro climbed
  have hor : 2 ^ ftsTreeHeight ||| v = 2 ^ ftsTreeHeight + v := by
    have := Nat.two_pow_add_eq_or_of_lt hv 1
    simpa using this.symm
  obtain ⟨hclimb, _⟩ := foldl_scheduleStep_good v hv top htop
    { state with heap := 2 ^ ftsTreeHeight ||| v,
                 parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    hor ⟨hgood.1, fun r hr => by simp at hr⟩
  refine ⟨fun segment hsegment => ?_, hclimb.2⟩
  rcases List.mem_append.mp hsegment with hsegment | hsegment
  · exact hclimb.1 segment hsegment
  · rw [List.mem_singleton] at hsegment
    subst segment
    exact hclimb.2
theorem scheduleLeaves_good : ∀ (sorted : List Nat), (∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) →
    ∀ state : ScheduleState, ScheduleGood state → ScheduleGood (scheduleLeaves sorted state) := by
  intro sorted
  induction sorted with
  | nil => intro _ state hgood; exact hgood
  | cons v rest ih =>
      intro hsorted state hgood
      have hv : v < 2 ^ ftsTreeHeight := hsorted v (List.mem_cons_self ..)
      have hrest : ∀ w ∈ rest, w < 2 ^ ftsTreeHeight := fun w hw => hsorted w (List.mem_cons_of_mem _ hw)
      cases rest with
      | nil =>
          rw [scheduleLeaves.eq_2, scheduleLeaves.eq_1]
          exact leafClimb_good v ftsTreeHeight hv le_rfl state hgood
      | cons w rest' =>
          rw [scheduleLeaves.eq_def]
          dsimp only
          apply ih hrest
          have hle := bitLength_xor_le v w hv (hrest w (List.mem_cons_self ..))
          have hclosed := leafClimb_good v (bitLength (v ^^^ w) - 1) hv (by omega) state hgood
          exact ⟨hclosed.1, hclosed.2⟩
theorem schedule_read (sorted : List Nat) (hsorted : ∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) :
    ∀ segment ∈ schedule sorted, ∀ r ∈ segment.reads, ScheduleRead r :=
  (scheduleLeaves_good sorted hsorted ⟨[], [], 0, false, []⟩
    ⟨fun segment hsegment => by simp at hsegment, fun r hr => by simp at hr⟩).1
theorem sortedLeaves_lt (leaves : IndexGroup → FtsLeaf) :
    ∀ v ∈ sortedLeaves leaves, v < 2 ^ ftsTreeHeight := by
  intro v hv
  simp only [sortedLeaves, List.mem_map] at hv
  obtain ⟨r, _, rfl⟩ := hv
  exact (leaves r).isLt
theorem honestFts_congr (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ segment ∈ schedule (sortedLeaves leaves), ∀ r ∈ segment.reads,
      node r.1 r.2 = node' r.1 r.2) :
    honestFts leaves secret node = honestFts leaves secret node' := by
  unfold honestFts
  dsimp only
  rw [FtsSignature.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext j
  generalize hsegment : (schedule (sortedLeaves leaves)).getD j.val default = segment
  have hmem : segment ∈ schedule (sortedLeaves leaves) ∨ segment = default := by
    rw [← hsegment, List.getD_eq_getElem?_getD]
    cases h : (schedule (sortedLeaves leaves))[j.val]? with
    | none => exact Or.inr rfl
    | some s => exact Or.inl (List.mem_of_getElem? h)
  refine congrArg (ScheduleSegment.toSegment segment) ?_
  funext i
  have hi : i.val < segment.reads.length :=
    Nat.lt_of_lt_of_le i.isLt (Nat.mod_le _ _)
  rw [List.getD_eq_getElem _ _ hi]
  rcases hmem with hmem | hdefault
  · exact hnode segment hmem _ (List.getElem_mem hi)
  · subst hdefault
    exact (Nat.not_lt_zero i.val hi).elim
theorem honestFts_congr_tree (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ level nodeIdx, level < ftsTreeHeight → nodeIdx < 2 ^ (ftsTreeHeight - level) →
      node level nodeIdx = node' level nodeIdx) :
    honestFts leaves secret node = honestFts leaves secret node' :=
  honestFts_congr leaves secret node node' fun segment hsegment r hr =>
    let hread := schedule_read _ (sortedLeaves_lt leaves) segment hsegment r hr
    hnode r.1 r.2 hread.1 hread.2
end SphincsSecurity.Concrete
end

section

open OracleComp OracleSpec
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit true
set_option maxRecDepth 4096
def restrictPath (lay : Layer) (path : Fin maxLayerHeight → α) : Fin (layerHeight lay) → α :=
  fun level => path (level.castLE (layerHeight_le lay))
end SphincsSecurity
end

section





namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id)
theorem sequenceFin_option_eq {α : Type} {n : Nat} (values : Fin n → Option α) :
    sequenceFin (m := Option) values =
      if h : ∀ i, (values i).isSome then some (fun i => (values i).get (h i)) else none := by
  induction n with
  | zero =>
      rw [dif_pos (fun i => i.elim0)]
      simp only [sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      cases h0 : values 0 with
      | none =>
          rw [dif_neg (fun h => by have := h 0; rw [h0] at this; simp at this)]
          rw [sequenceFin, h0]
          rfl
      | some head =>
          have hstep : sequenceFin (m := Option) values =
              sequenceFin (m := Option) (fun i : Fin n => values i.succ) >>= fun tail =>
                some (Fin.cases head tail) := by
            rw [sequenceFin, h0]
            rfl
          rw [hstep, ih]
          by_cases hall : ∀ i, (values i).isSome
          · rw [dif_pos (fun i : Fin n => hall i.succ), dif_pos hall]
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
            funext i
            cases i using Fin.cases with
            | zero => simp [h0]
            | succ i => rfl
          · rw [dif_neg hall]
            have htail : ¬ ∀ i : Fin n, (values i.succ).isSome := by
              intro htail
              apply hall
              intro i
              cases i using Fin.cases with
              | zero => simp [h0]
              | succ i => exact htail i
            rw [dif_neg htail]
            rfl
theorem eval_buildLevel (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (width : Nat) (below : Nat → Digest) :
    evalWithAnswerFn f (buildLevel hashNode width below) = fun nodeIdx =>
      if h : nodeIdx < width then
        evalWithAnswerFn f (hashNode nodeIdx (below (2 * nodeIdx)) (below (2 * nodeIdx + 1)))
      else 0 := by
  simp only [buildLevel, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
theorem eval_buildLevels (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (height : Nat) (leaves : Nat → Digest) (node : Nat → Nat → Digest)
    (hleaf : ∀ nodeIdx, nodeIdx < 2 ^ height → leaves nodeIdx = node 0 nodeIdx)
    (hnode : ∀ level nodeIdx, level < height → nodeIdx < 2 ^ (height - (level + 1)) →
      evalWithAnswerFn f (hashNode (level + 1) nodeIdx (node level (2 * nodeIdx))
        (node level (2 * nodeIdx + 1))) = node (level + 1) nodeIdx)
    (levels : Nat) (hlevels : levels ≤ height) :
    ∀ level, level ≤ levels → ∀ nodeIdx, nodeIdx < 2 ^ (height - level) →
      evalWithAnswerFn f (buildLevels hashNode height leaves levels) level nodeIdx
        = node level nodeIdx := by
  induction levels with
  | zero =>
      intro level hlevel nodeIdx hnodeIdx
      have hl : level = 0 := by omega
      subst hl
      simp only [buildLevels, evalWithAnswerFn_pure]
      exact hleaf nodeIdx (by simpa using hnodeIdx)
  | succ levels ih =>
      intro level hlevel nodeIdx hnodeIdx
      simp only [buildLevels, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_buildLevel]
      by_cases hl : level = levels + 1
      · subst hl
        rw [if_pos rfl, dif_pos hnodeIdx]
        have hpow : 2 ^ (height - levels) = 2 * 2 ^ (height - (levels + 1)) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [ih (by omega) levels le_rfl (2 * nodeIdx) (by omega),
          ih (by omega) levels le_rfl (2 * nodeIdx + 1) (by omega)]
        exact hnode levels nodeIdx (by omega) hnodeIdx
      · rw [if_neg hl]
        exact ih (by omega) level (by omega) nodeIdx hnodeIdx
theorem eval_buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : OracleComp HashSpec Digest) (digit : Digit) :
    evalWithAnswerFn f (buildChain parameter lay tree leaf chainIdx secret digit.val) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val
          (evalWithAnswerFn f secret)),
        evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1)
          (evalWithAnswerFn f secret))) := by
  simp only [buildChain, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  congr 1
  have h := eval_recoverChain f parameter lay tree leaf chainIdx digit (evalWithAnswerFn f secret)
  simpa only [recoverChain] using h
theorem eval_buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLeaf parameter lay tree leaf (secret leaf) digits) =
      (fun chainIdx => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digits chainIdx).val (evalWithAnswerFn f (secret leaf chainIdx))),
        honestNode f parameter lay tree (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))
          0 leaf.val) := by
  rw [honestNode_zero_eq_leafHash]
  simp only [buildLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_buildChain,
    evalWithAnswerFn_pure, leafHash, eval_tweakableHash]
  rfl
theorem xor_div_lt {leaf height level : Nat} (hleaf : leaf < 2 ^ height) (hlevel : level < height) :
    Nat.xor (leaf / 2 ^ level) 1 < 2 ^ (height - level) := by
  have hdiv : leaf / 2 ^ level < 2 ^ (height - level) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    rwa [Nat.sub_add_cancel hlevel.le]
  exact Nat.xor_lt_two_pow hdiv (Nat.one_lt_two_pow (by omega))
theorem eval_buildLayerTree_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    let leaves := evalWithAnswerFn f (sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
      buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
        (if leafNat.val = leaf.val then digits else zeroEncoding))
    ∀ level, level ≤ layerHeight lay → ∀ nodeIdx, nodeIdx < 2 ^ (layerHeight lay - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
        (layerHeight lay)
        (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
        (layerHeight lay)) level nodeIdx
        = honestNode f parameter lay tree
            (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx := by
  intro leaves level hlevel nodeIdx hnodeIdx
  apply eval_buildLevels f _ _ _
    (fun level nodeIdx => honestNode f parameter lay tree
      (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx)
  · intro nodeIdx hnodeIdx
    rw [dif_pos hnodeIdx]
    simp only [leaves, evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    congr 1
    simp only [leafOfNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hnodeIdx
      (Nat.pow_le_pow_right (by omega) (layerHeight_le lay)))]
  · intro level nodeIdx _ _
    rw [eval_tweakableHash, honestNode_succ]
  · exact le_rfl
  · exact hlevel
  · exact hnodeIdx
theorem eval_buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    let result := evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)
    let table := fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)
    result.1 = (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (digits chainIdx).val (table leaf chainIdx)))
      ∧ (∀ level, level < layerHeight lay →
          result.2.1 level = honestNode f parameter lay tree table level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∧ result.2.2 = honestNode f parameter lay tree table (layerHeight lay) 0 := by
  intro result table
  have htable := eval_buildLayerTree_table f parameter lay tree secret leaf digits
  simp only [result, buildLayerTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_, ?_⟩
  · rw [dif_pos hleaf]
    simp only [evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    funext chainIdx
    simp only [leafOfNat_val, if_true, table]
  · intro level hlevel
    exact htable level hlevel.le _ (xor_div_lt hleaf hlevel)
  · exact htable _ le_rfl 0 (by simp)
theorem eval_buildLayerTree_root (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    (evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)).2.2
      = evalWithAnswerFn f (treeRoot parameter lay tree
          (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))) :=
  (eval_buildLayerTree f parameter lay tree secret leaf hleaf digits).2.2
theorem eval_keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    evalWithAnswerFn f (keygenRoot parameter secret)
      = evalWithAnswerFn f (treeRoot parameter topLayer rootTree secret) := by
  have h := eval_buildLayerTree_root f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩
    (Nat.two_pow_pos _) zeroEncoding
  simp only [evalWithAnswerFn_pure] at h
  unfold keygenRoot
  rw [evalWithAnswerFn_bind]
  split
  next values path root hresult =>
    rw [evalWithAnswerFn_pure, ← h, hresult]
theorem buildLayerTree_eq_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTree parameter lay tree secret leaf digits =
      (fun built : (Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest) =>
        ((if h : leaf.val < 2 ^ layerHeight lay then (built.1 ⟨leaf.val, h⟩).1 else fun _ => 0),
          (fun level => built.2 level (Nat.xor (leaf.val / 2 ^ level) 1)), built.2 (layerHeight lay) 0)) <$>
        buildLayerTable parameter lay tree secret leaf digits := by
  simp only [buildLayerTree, buildLayerTable, map_bind, bind_assoc, pure_bind, map_pure]
theorem eval_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (level : Nat) (hlevel : level ≤ layerHeight topLayer) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight topLayer - level)) :
    evalWithAnswerFn f (keygenTable parameter secret) level nodeIdx
      = honestNode f parameter topLayer rootTree secret level nodeIdx := by
  have htable := eval_buildLayerTree_table f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
    level hlevel nodeIdx hnodeIdx
  simp only [evalWithAnswerFn_pure] at htable
  unfold keygenTable
  rw [evalWithAnswerFn_bind]
  split
  next leaves table hresult =>
    rw [evalWithAnswerFn_pure]
    have hsnd := congrArg Prod.snd hresult
    simp only [buildLayerTable, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hsnd
    rw [← hsnd]
    exact htable
def TopAgrees (key : SecretKey) (topNode : Nat → Nat → OracleComp HashSpec Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    evalWithAnswerFn f (topNode level nodeIdx)
      = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) level nodeIdx
abbrev KeyTopHonest (key : SecretKey) : Prop :=
  TopAgrees f key (fun level nodeIdx => pure (key.top level nodeIdx))
noncomputable def honestTop (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → Nat → Digest :=
  evalWithAnswerFn f (keygenTable parameter secret)
theorem honestTop_root (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    honestTop f parameter secret (layerHeight topLayer) 0 =
      honestNode f parameter topLayer rootTree secret (layerHeight topLayer) 0 :=
  eval_keygenTable f parameter secret _ le_rfl 0 (by rw [Nat.sub_self, pow_zero]; exact Nat.one_pos)
theorem keyTopHonest_of_eq (key : SecretKey)
    (h : key.top = honestTop f key.parameter (key.otsSecret topLayer rootTree)) : KeyTopHonest f key := by
  intro level hlevel nodeIdx hnodeIdx
  have hheight : layerHeight topLayer = maxLayerHeight := rfl
  have heval := eval_keygenTable f key.parameter (key.otsSecret topLayer rootTree) level
    (by rw [hheight]; exact hlevel.le) nodeIdx (by rw [hheight]; exact hnodeIdx)
  rw [evalWithAnswerFn_pure, h]
  exact heval
theorem keyTopHonest_withTop (key : SecretKey) :
    KeyTopHonest f { key with top := honestTop f key.parameter (key.otsSecret topLayer rootTree) } :=
  keyTopHonest_of_eq f _ rfl
theorem eval_buildFtsTree (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → OracleComp HashSpec Digest) :
    let result := evalWithAnswerFn f (buildFtsTree parameter index secret)
    let table := fun leaf => evalWithAnswerFn f (secret leaf)
    result.1 = table
      ∧ ∀ level, level ≤ ftsTreeHeight → ∀ nodeIdx, nodeIdx < 2 ^ (ftsTreeHeight - level) →
          result.2 level nodeIdx = honestFtsNode f parameter index porsTree table level nodeIdx := by
  intro result table
  have htable : ∀ level, level ≤ ftsTreeHeight → ∀ nodeIdx, nodeIdx < 2 ^ (ftsTreeHeight - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx))
            (nodePayload left right))
        ftsTreeHeight
        (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then
          ((evalWithAnswerFn f (sequenceFin fun leafIdx : FtsLeaf => do
            let value ← secret leafIdx
            let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
            return (value, hashed))) ⟨nodeIdx, h⟩).2 else 0)
        ftsTreeHeight) level nodeIdx
        = honestFtsNode f parameter index porsTree table level nodeIdx := by
    apply eval_buildLevels f _ _ _ (fun level nodeIdx => honestFtsNode f parameter index porsTree table level nodeIdx)
    · intro nodeIdx hnodeIdx
      rw [dif_pos hnodeIdx]
      have h := honestFtsNode_zero f parameter index porsTree table ⟨nodeIdx, hnodeIdx⟩
      simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        ftsLeafHash, eval_tweakableHash] at h ⊢
      exact h.symm
    · intro level nodeIdx _ _
      rw [eval_tweakableHash, honestFtsNode_succ]
    · exact le_rfl
  simp only [result, buildFtsTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_⟩
  · simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, table]
  · exact htable
theorem eval_ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsOpen parameter index leaves secret)
      = honestFts leaves (secret porsTree) (honestFtsNode f parameter index porsTree (secret porsTree)) := by
  simp only [ftsOpen, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
  rfl
theorem eval_buildFtsTree_open (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → OracleComp HashSpec Digest) (leaves : IndexGroup → FtsLeaf) :
    let result := evalWithAnswerFn f (buildFtsTree parameter index secret)
    let table := fun (_ : FtsTree) leaf => evalWithAnswerFn f (secret leaf)
    honestFts leaves result.1 result.2 = evalWithAnswerFn f (ftsOpen parameter index leaves table)
      ∧ result.2 ftsTreeHeight 0 = evalWithAnswerFn f (ftsKey parameter index table) := by
  intro result table
  obtain ⟨hsecrets, hnodes⟩ := eval_buildFtsTree f parameter index secret
  refine ⟨?_, ?_⟩
  · rw [eval_ftsOpen, hsecrets]
    exact honestFts_congr_tree leaves _ _ _ fun level nodeIdx hlevel hnode =>
      hnodes level hlevel.le nodeIdx hnode
  · exact hnodes ftsTreeHeight le_rfl 0 (by simp)
theorem eval_otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    evalWithAnswerFn f (otsSignFrom parameter lay tree leaf secret message attempts counter)
      = (evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts counter)).map
          fun result => (result.1, fun chainIdx => evalWithAnswerFn f
            (chainWalk parameter lay tree leaf chainIdx 0 (result.2 chainIdx).val (secret chainIdx))) := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      simp only [otsSignFrom, encodingSearch, evalWithAnswerFn_bind, encode_eq]
      cases evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message
          (BitVec.ofNat counterBits counter)) with
      | none => exact ih (counter + 1)
      | some word =>
          simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
            Option.map_some]
def LayerOutput.toPadded (lay : Layer) (output : LayerOutput) : PaddedLayer :=
  (output.1, output.2.1, fun level => if level.val < layerHeight lay then output.2.2 level.val else 0)
theorem LayerOutput.toSignature_eq (lay : Layer) (output : LayerOutput) :
    LayerOutput.toSignature lay output = LayerSignature.ofPadded lay (LayerOutput.toPadded lay output) := by
  simp only [LayerOutput.toSignature, LayerOutput.toPadded, LayerSignature.ofPadded, Fin.val_castLE]
  congr
  funext level
  rw [if_pos level.isLt]
theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (treePath parameter lay tree secret leaf) = fun level =>
      if level.val < layerHeight lay then
        honestNode f parameter lay tree secret level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
      else 0 := by
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs <;> rfl
theorem eval_signLayers (key : SecretKey) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (secret lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topNode)
    (remaining : Nat) (hremaining : remaining ≤ numLayers) (message : Digest)
    (hmessage : ∀ h : 0 < remaining,
      message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩)) :
    match evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining message) with
    | none => ∃ lay : Layer, lay.val < remaining ∧ evalWithAnswerFn f (signLayer key index lay) = none
    | some parts => ∀ lay : Layer, lay.val < remaining →
        evalWithAnswerFn f (signLayer key index lay) = some (LayerOutput.toPadded lay (parts lay)) := by
  induction remaining generalizing message with
  | zero =>
      simp only [signLayers, evalWithAnswerFn_pure]
      intro lay hlay
      omega
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      let lay : Layer := ⟨remaining, hlayer⟩
      have hmsg : message = evalWithAnswerFn f (layerMessage key index lay) := hmessage (by omega)
      have htable : (fun leaf chainIdx => evalWithAnswerFn f
          (secret lay (treeIndexAt index lay) leaf chainIdx)) =
          key.otsSecret lay (treeIndexAt index lay) := by
        funext leaf chainIdx
        exact hsecret _ _ _ _
      have hspec : evalWithAnswerFn f (signLayer key index lay) =
          (evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0)).map fun result =>
              (result.1, fun chainIdx => evalWithAnswerFn f
                (chainWalk key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx 0
                  (result.2 chainIdx).val
                  (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)),
                evalWithAnswerFn f (treePath key.parameter lay (treeIndexAt index lay)
                  (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))) := by
        simp only [signLayer, evalWithAnswerFn_bind, ← hmsg, otsSign, eval_otsSignFrom]
        cases evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none => rfl
        | some result => simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hzero : remaining = 0
      · subst hzero
        have htree : treeIndexAt index lay = rootTree := Fin.ext (treeIndexAt_topLayer index)
        simp only [signLayers, dif_pos hlayer, ↓reduceIte, signTopLayer, evalWithAnswerFn_bind]
        rw [show topLayer = lay from rfl]
        cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none =>
            refine ⟨lay, Nat.lt_succ_self _, ?_⟩
            rw [hspec, hsearch]
            rfl
        | some result =>
            obtain ⟨counter, word⟩ := result
            simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_sequenceFin]
            intro other hother
            have hother' : other = lay := Fin.ext (by simp [lay]; omega)
            rw [hother', if_pos rfl, hspec, hsearch]
            simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq, true_and]
            refine ⟨?_, ?_⟩
            · funext chainIdx
              rw [hsecret]
            · rw [eval_treePath]
              funext level
              have hheight : layerHeight lay = maxLayerHeight := rfl
              rw [hheight]
              split_ifs with hlevel
              · rw [htree]
                exact (htop level.val hlevel _ (xor_div_lt (leafIndexAt_lt index lay) hlevel)).symm
              · exact absurd level.isLt hlevel
      simp only [signLayers, dif_pos hlayer, if_neg hzero, evalWithAnswerFn_bind]
      cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) message encodingAttemptLimit 0) with
      | none =>
          refine ⟨lay, Nat.lt_succ_self _, ?_⟩
          rw [hspec, hsearch]
          rfl
      | some result =>
          obtain ⟨counter, word⟩ := result
          have hbuild := eval_buildLayerTree f key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay) word
          rw [htable] at hbuild
          simp only [evalWithAnswerFn_bind]
          revert hbuild
          generalize evalWithAnswerFn f (buildLayerTree key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) word) = built
          rcases built with ⟨values, path, root⟩
          rintro ⟨hvalues, hpath, hroot⟩
          simp only at hvalues hpath hroot
          have hnext : ∀ h : 0 < remaining,
              root = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩) := by
            intro h
            have hbelow : remaining - 1 + 1 < numLayers := by omega
            rw [layerMessage, dif_pos hbelow]
            have hlay : (⟨remaining - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            rw [hlay, hroot]
            simp only [treeRoot, honestNode]
          have hrest := ih (by omega) root hnext
          revert hrest
          cases evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining root) with
          | none =>
              rintro ⟨other, hother, hnone⟩
              exact ⟨other, by omega, hnone⟩
          | some rest =>
              intro hrest other hother
              by_cases hl : other = lay
              · subst hl
                have hif : (if lay = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, (values, path, root).1, (values, path, root).2.1) else rest lay) =
                    (counter, values, path) := if_pos rfl
                simp only [hif]
                rw [hspec, hsearch]
                simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq,
                  true_and]
                refine ⟨hvalues.symm, ?_⟩
                rw [eval_treePath]
                funext level
                split_ifs with hlevel
                · exact (hpath level.val hlevel).symm
                · rfl
              · have hif : (if other = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, values, path) else rest other) = rest other := if_neg hl
                simp only [hif]
                exact hrest other (by
                  have : other.val ≠ remaining := fun h => hl (Fin.ext h)
                  omega)
theorem signAfterDigest_eq_signFrom (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signFrom key.parameter index (fun tree leaf => pure (key.ftsSecret index tree leaf))
        (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
        (fun level nodeIdx => pure (key.top level nodeIdx)) randomness leaves := by
  rw [signAfterDigest]
def signatureValue (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Option Signature :=
  (sequenceFin (m := Option) fun lay => evalWithAnswerFn f (signLayer key index lay)).map fun parts =>
    { randomness := randomness
      fts := evalWithAnswerFn f (ftsOpen key.parameter index leaves (key.ftsSecret index))
      layers := fun lay => LayerSignature.ofPadded lay (parts lay) }
theorem layerMessage_bottomLayer_eq (key : SecretKey) (index : Index) :
    (layerMessage key index bottomLayer : OracleComp HashSpec Digest) =
      ftsKey key.parameter index (key.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]
theorem eval_signFrom (key : SecretKey) (index : Index)
    (ftsGet : FtsTree → FtsLeaf → OracleComp HashSpec Digest)
    (otsGet : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hfts : ∀ tree leaf, evalWithAnswerFn f (ftsGet tree leaf) = key.ftsSecret index tree leaf)
    (hots : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (otsGet lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topGet : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topGet)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signFrom key.parameter index ftsGet otsGet topGet randomness leaves) =
      signatureValue f key randomness index leaves := by
  have hforest := eval_buildFtsTree_open f key.parameter index (ftsGet porsTree) leaves
  have htable : (fun (_ : FtsTree) leaf => evalWithAnswerFn f (ftsGet porsTree leaf)) = key.ftsSecret index := by
    funext tree leaf
    rw [Subsingleton.elim tree porsTree]
    exact hfts porsTree leaf
  rw [htable] at hforest
  unfold signFrom
  rw [evalWithAnswerFn_bind]
  revert hforest
  generalize evalWithAnswerFn f (buildFtsTree key.parameter index (ftsGet porsTree)) = built
  rcases built with ⟨secrets, table⟩
  rintro ⟨hopen, hkey⟩
  simp only at hopen hkey
  have hlayers := eval_signLayers f key index otsGet hots topGet htop numLayers le_rfl
      (table ftsTreeHeight 0) (by
    intro _
    rw [hkey]
    change _ = evalWithAnswerFn f (layerMessage key index bottomLayer)
    rw [layerMessage_bottomLayer_eq])
  simp only [evalWithAnswerFn_bind]
  unfold signatureValue
  rw [sequenceFin_option_eq]
  revert hlayers
  cases evalWithAnswerFn f (signLayers key.parameter index otsGet topGet numLayers (table ftsTreeHeight 0)) with
  | none =>
      rintro ⟨lay, _, hnone⟩
      rw [dif_neg (fun hall => by have := hall lay; rw [hnone] at this; simp at this)]
      rfl
  | some parts =>
      intro hparts
      have hall : ∀ lay, (evalWithAnswerFn f (signLayer key index lay)).isSome := fun lay => by
        rw [hparts lay lay.isLt]
        rfl
      rw [dif_pos hall]
      simp only [evalWithAnswerFn_pure, Option.map_some, Option.some.injEq]
      rw [hopen]
      congr 1
      funext lay
      rw [LayerOutput.toSignature_eq]
      congr 1
      simp only [hparts lay lay.isLt, Option.get_some]
theorem eval_signAfterDigest (key : SecretKey) (htop : KeyTopHonest f key) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signatureValue f key randomness index leaves := by
  rw [signAfterDigest_eq_signFrom]
  exact eval_signFrom f key index _ _ (fun _ _ => rfl) (fun _ _ _ _ => rfl) _ htop randomness leaves
def TopRegionEq {m : Type → Type} (topNode topNode' : Nat → Nat → m Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    topNode level nodeIdx = topNode' level nodeIdx
theorem signTopLayer_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (message : Digest) :
    signTopLayer parameter index secret topNode message = signTopLayer parameter index secret topNode' message := by
  have hpath : (fun level : Fin maxLayerHeight =>
      topNode level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) =
      (fun level : Fin maxLayerHeight =>
        topNode' level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) :=
    funext fun level => htop _ level.isLt _ (xor_div_lt (leafIndexAt_lt index topLayer) level.isLt)
  simp only [signTopLayer, hpath]
theorem signLayers_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (remaining : Nat) (message : Digest) :
    signLayers parameter index secret topNode remaining message =
      signLayers parameter index secret topNode' remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      rw [signLayers, signLayers]
      split
      · split
        · rw [signTopLayer_congr_top parameter index _ topNode topNode' htop]
        · simp only [ih]
      · rfl
theorem signAfterDigest_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx)))
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signAfterDigest key' randomness index leaves := by
  rw [signAfterDigest_eq_signFrom, signAfterDigest_eq_signFrom, ← hparameter, ← hots, ← hfts]
  unfold signFrom
  simp only [signLayers_congr_top key.parameter index _ _ _ htop]
end SphincsSecurity.Concrete
end
