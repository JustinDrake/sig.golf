import SigGolfCandidate.T3.BPORS

section

namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
def HonQ (answers : Answers) (q : Spec.Domain) : Prop :=
  ∃ pos : Extract.Pos, pos.Bounded ∧ q = .inl (.inr (Extract.honestInput answers pos))
theorem honQ_eq {answers : Answers} {pos : Extract.Pos} {input : HashInput} (hb : pos.Bounded)
    (hh : Extract.hdrBlock input = bytesLE 16 pos.hdr) (hq : HonQ answers (.inl (.inr input))) :
    input = Extract.honestInput answers pos := by
  obtain ⟨pos', hb', he⟩ := hq
  have hi : input = Extract.honestInput answers pos' := by
    simpa only [Sum.inl.injEq, Sum.inr.injEq] using he
  have hh' := Extract.hdrBlock_honestInput answers pos'
  rw [← hi, hh] at hh'
  rw [hi, Extract.Pos.hdr_injective hb hb' (bytesLE_injective hh')]
abbrev H (answers : Answers) (index coord level node : Nat) : Digest :=
  treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level node
abbrev S (answers : Answers) (index coord leaf : Nat) : Digest := Extract.ftsSecret answers index coord leaf
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (l p r : Digest) :
    Extract.hdrBlock (nodeInputP tag lay tree heap l p r) = bytesLE 16 (header tag lay tree 0 heap) := by
  unfold nodeInputP; exact Extract.hdrBlock_block4 _ _ _ _
theorem hdrBlock_ftsLeafInputP (index coord leaf : Nat) (a s b : Digest) :
    Extract.hdrBlock (ftsLeafInputP index coord leaf a s b) = bytesLE 16 (header 9 coord index 0 leaf) := by
  unfold ftsLeafInputP; exact Extract.hdrBlock_block4 _ _ _ _
theorem honQ_node {answers : Answers} {index coord level node : Nat} {left pad right : Digest}
    (hc : coord < 256) (hi : index < 2 ^ 40) (hl : level < 11) (hn : node < 2 ^ (11 - (level + 1)))
    (hq : HonQ answers (.inl (.inr (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node) left pad right)))) :
    left = H answers index coord level (2 * node) ∧ pad = 0 ∧ right = H answers index coord level (2 * node + 1) := by
  have hb : (Extract.Pos.ftsNode index coord level node).Bounded :=
    ⟨hc, hi, hl, by simpa only [Nat.sub_sub] using hn⟩
  have he := honQ_eq hb (by rw [hdrBlock_nodeInputP]; simp only [Extract.Pos.hdr, Nat.sub_sub]) hq
  rw [FtsExtract.honestInput_ftsNode answers index coord level node hl hn,
    show FtsExtract.builtSecret answers index coord =
      fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0 from rfl,
    FtsExtract.honInputL_built answers index coord level node hl hn] at he
  obtain ⟨h1, -, h2, h3⟩ := nodeInputP_fields he
  exact ⟨h1, h2, h3⟩
theorem honQ_leaf {answers : Answers} {index coord leaf : Nat} {p0 s p1 : Digest}
    (hc : coord < 256) (hi : index < 2 ^ 40) (hl : leaf < 2 ^ 32)
    (hq : HonQ answers (.inl (.inr (ftsLeafInputP index coord leaf p0 s p1)))) :
    p0 = 0 ∧ s = S answers index coord leaf ∧ p1 = 0 := by
  have hb : (Extract.Pos.ftsLeaf index coord leaf).Bounded := ⟨hc, hi, hl⟩
  have he := honQ_eq hb (by rw [hdrBlock_ftsLeafInputP]; rfl) hq
  simp only [Extract.honestInput, pad64_ftsLeafInputP] at he
  obtain ⟨h1, -, h2, h3⟩ := ftsLeafInputP_fields he
  exact ⟨h1, h2, h3⟩
theorem out_node_honest (answers : Answers) (index coord level node : Nat) (hl : level < 11)
    (hn : node < 2 ^ (11 - (level + 1))) :
    (answers (.inl (.inr (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
      (H answers index coord level (2 * node)) 0 (H answers index coord level (2 * node + 1)))))).extractLsb' 0 128 =
    H answers index coord (level + 1) node := by
  have ht := (Correctness.eval_buildFts_correct answers index coord).2.2.2 level hl node hn
  rw [nodeHash_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_nodeInputP] at ht
  exact ht.symm
theorem out_leaf_honest (answers : Answers) (index coord leaf : Nat) (hl : leaf < 2048) :
    (answers (.inl (.inr (ftsLeafInputP index coord leaf 0 (S answers index coord leaf) 0)))).extractLsb'
      0 128 = H answers index coord 0 leaf := by
  have ht := (Correctness.eval_buildFts_correct answers index coord).2.2.1 leaf hl
  rw [ftsLeaf_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_ftsLeafInputP] at ht
  exact ht.symm
theorem frontier_empty {leaves : List Nat} {level node : Nat} (h : hasLeaf leaves level node = false) :
    T3.frontier leaves level node = [(level, node)] := by
  cases level <;> simp [T3.frontier, h]
theorem frontier_leaf {leaves : List Nat} {node : Nat} (h : hasLeaf leaves 0 node = true) :
    T3.frontier leaves 0 node = [] := by
  simp [T3.frontier, h]
theorem frontier_node {leaves : List Nat} {level node : Nat} (h : hasLeaf leaves (level + 1) node = true) :
    T3.frontier leaves (level + 1) node =
      T3.frontier leaves level (2 * node) ++ T3.frontier leaves level (2 * node + 1) := by
  simp [T3.frontier, h]
theorem dfsP_honest (answers : Answers) (index coord : Nat) (hc : coord < 256) (hi : index < 2 ^ 40)
    (leaves : List Nat) (leafH : Nat → M Digest) (val pad : Nat × Nat → Digest)
    (hleaf : ∀ g, g < 2048 → (∀ q ∈ queried answers (leafH g), HonQ answers q) →
      evalWithAnswerFn answers (leafH g) = H answers index coord 0 g) :
    ∀ level node, level ≤ 11 → node < 2 ^ (11 - level) → hasLeaf leaves level node = true →
      (∀ q ∈ queried answers (dfsP index coord leaves leafH val pad level node), HonQ answers q) →
      evalWithAnswerFn answers (dfsP index coord leaves leafH val pad level node) = H answers index coord level node ∧
      ∀ p ∈ T3.frontier leaves level node, val p = H answers index coord p.1 p.2 := by
  intro level
  induction level with
  | zero =>
      intro node _ hn hh hq
      rw [dfsP_leaf hh] at hq ⊢
      exact ⟨hleaf node (by simpa using hn) hq, by rw [frontier_leaf hh]; simp⟩
  | succ level ih =>
      intro node hl hn hh hq
      have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
        rw [← pow_succ']; congr 1; omega
      have child : ∀ n', n' < 2 ^ (11 - level) →
          (∀ q ∈ queried answers (dfsP index coord leaves leafH val pad level n'), HonQ answers q) →
          evalWithAnswerFn answers (dfsP index coord leaves leafH val pad level n') = H answers index coord level n' →
          ∀ p ∈ T3.frontier leaves level n', val p = H answers index coord p.1 p.2 := by
        intro n' hn' hq' he'
        cases hh' : hasLeaf leaves level n' with
        | true => exact (ih n' (by omega) hn' hh' hq').2
        | false =>
            rw [dfsP_empty hh', evalWithAnswerFn_pure] at he'
            rw [frontier_empty hh']
            intro p hp
            rw [List.mem_singleton] at hp
            subst hp
            exact he'
      rw [dfsP_node hh] at hq ⊢
      simp only [queried_bind] at hq
      have hqN := hq _ (List.mem_append_right _ (List.mem_append_right _ (by
        rw [nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP]; exact List.mem_singleton_self _)))
      obtain ⟨hl1, hp0, hr1⟩ := honQ_node hc hi (by omega) hn hqN
      have fL := child (2 * node) (by omega) (fun q h => hq q (List.mem_append_left _ h)) hl1
      have fR := child (2 * node + 1) (by omega)
        (fun q h => hq q (List.mem_append_right _ (List.mem_append_left _ h))) hr1
      refine ⟨?_, ?_⟩
      · simp only [evalWithAnswerFn_bind]
        rw [nodeHashP_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_nodeInputP, hl1, hr1, hp0]
        exact out_node_honest answers index coord level node (by omega) hn
      · rw [frontier_node hh]
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact fL p hp
        · exact fR p hp
theorem climbStep_honest (answers : Answers) (index coord : Nat) (hc : coord < 256) (hi : index < 2 ^ 40)
    (val pad : Nat × Nat → Digest) (g : Nat) (hg : g < 2048) (k : Nat) (hk : k < 11) (v : Digest)
    (_hv : v = H answers index coord k (g / 2 ^ k))
    (hq : ∀ q ∈ queried answers (climbStep index coord val pad g k v), HonQ answers q) :
    evalWithAnswerFn answers (climbStep index coord val pad g k v) = H answers index coord (k + 1) (g / 2 ^ (k + 1)) ∧
      val (k, g / 2 ^ k ^^^ 1) = H answers index coord k (g / 2 ^ k ^^^ 1) := by
  have hd : g / 2 ^ (k + 1) = g / 2 ^ k / 2 := (Correctness.div_pow_succ g k).symm
  have hn : g / 2 ^ k / 2 < 2 ^ (11 - (k + 1)) := by
    rw [← hd, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show 11 - (k + 1) + (k + 1) = 11 by omega]
    exact lt_of_lt_of_le hg (by norm_num)
  have hx := xor_one_eq (g / 2 ^ k)
  unfold climbStep at hq ⊢
  by_cases hodd : g / 2 ^ k % 2 = 1
  · rw [if_pos hodd] at hq ⊢
    rw [nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP] at hq
    obtain ⟨h1, h2, h3⟩ := honQ_node hc hi hk hn (hq _ (List.mem_singleton_self _))
    refine ⟨?_, ?_⟩
    · rw [nodeHashP_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_nodeInputP, h1, h2, h3,
        out_node_honest answers index coord k _ hk hn, hd]
    · rw [h1, show 2 * (g / 2 ^ k / 2) = g / 2 ^ k ^^^ 1 by omega]
  · rw [if_neg hodd] at hq ⊢
    rw [nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP] at hq
    obtain ⟨h1, h2, h3⟩ := honQ_node hc hi hk hn (hq _ (List.mem_singleton_self _))
    refine ⟨?_, ?_⟩
    · rw [nodeHashP_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_nodeInputP, h1, h2, h3,
        out_node_honest answers index coord k _ hk hn, hd]
    · rw [h3, show 2 * (g / 2 ^ k / 2) + 1 = g / 2 ^ k ^^^ 1 by omega]
theorem climbV_honest (answers : Answers) (index coord : Nat) (hc : coord < 256) (hi : index < 2 ^ 40)
    (val pad : Nat × Nat → Digest) (g : Nat) (hg : g < 2048) :
    ∀ a lo (v : Digest), lo + a ≤ 11 → v = H answers index coord lo (g / 2 ^ lo) →
      (∀ q ∈ queried answers (climbV index coord val pad g lo a v), HonQ answers q) →
      evalWithAnswerFn answers (climbV index coord val pad g lo a v) =
        H answers index coord (lo + a) (g / 2 ^ (lo + a)) ∧
      ∀ k, lo ≤ k → k < lo + a → val (k, g / 2 ^ k ^^^ 1) = H answers index coord k (g / 2 ^ k ^^^ 1) := by
  intro a
  induction a with
  | zero =>
      intro lo v _ hv _
      refine ⟨by rw [climbV_zero, evalWithAnswerFn_pure, hv]; rfl, fun k h1 h2 => by omega⟩
  | succ a ih =>
      intro lo v hla hv hq
      rw [climbV_succ, queried_bind] at hq
      obtain ⟨hs1, hs2⟩ := climbStep_honest answers index coord hc hi val pad g hg lo (by omega) v hv
        (fun q h => hq q (List.mem_append_left _ h))
      have hrest := ih (lo + 1) _ (by omega) hs1 (fun q h => hq q (List.mem_append_right _ h))
      rw [climbV_succ, evalWithAnswerFn_bind, hrest.1, show lo + 1 + a = lo + (a + 1) by omega]
      refine ⟨rfl, fun k h1 h2 => ?_⟩
      by_cases hk : k = lo
      · subst hk; exact hs2
      · exact hrest.2 k (by omega) (by omega)
theorem leafHP_honest (answers : Answers) (index coord : Nat) (hc : coord < 256) (hi : index < 2 ^ 40)
    (leaves : List Nat) (values : List Digest) (pads : Pads) (g : Nat) (hg : g < 2048)
    (hq : ∀ q ∈ queried answers (leafHP index coord leaves values pads g), HonQ answers q) :
    evalWithAnswerFn answers (leafHP index coord leaves values pads g) = H answers index coord 0 g := by
  unfold leafHP at hq ⊢
  rw [ftsLeafP_eq_shortHash, queried_shortHash, pad64_ftsLeafInputP] at hq
  obtain ⟨h1, h2, h3⟩ := honQ_leaf hc hi (by omega) (hq _ (List.mem_singleton_self _))
  rw [ftsLeafP_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_ftsLeafInputP, h1, h2, h3]
  exact out_leaf_honest answers index coord g hg
theorem coord_honest (answers : Answers) (proof : Fin 115 → Digest) (pads : Pads) (index : Nat)
    (hi : index < 2 ^ 40) (c : Nat) (hc : c < 256) (sel : Selection) (hs : SelOk sel) (values : List Digest)
    (base : Nat)
    (hq : ∀ q ∈ queried answers (coordCanon index c (leafHP index c (selectedLeaves sel) values pads)
        (valOf proof base (slotPositions sel)) (valOf pads.fold base (slotPositions sel))
        (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2)), HonQ answers q) :
    ∀ p ∈ slotPositions sel, valOf proof base (slotPositions sel) p = H answers index c p.1 p.2 := by
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have hm0 : selLeaf sel 0 ∈ selectedLeaves sel := by rw [hs.selected]; simp
  have hm1 : selLeaf sel 1 ∈ selectedLeaves sel := by rw [hs.selected]; simp
  have hm2 : selLeaf sel 2 ∈ selectedLeaves sel := by rw [hs.selected]; simp
  have hb0 := hs.bucket_div hm0
  have hb1 := hs.bucket_div hm1
  have hb2 := hs.bucket_div hm2
  have hg2 : selLeaf sel 2 < 2048 := by unfold selLeaf; have := hs.l2; have := hs.b; omega
  rw [← dfsP_bucket g01 g12 hb0 hb1 hb2, queried_bind] at hq
  have hD := dfsP_honest answers index c hc hi [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2]
    (leafHP index c (selectedLeaves sel) values pads) (valOf proof base (slotPositions sel))
    (valOf pads.fold base (slotPositions sel))
    (fun g hg hq' => leafHP_honest answers index c hc hi _ values pads g hg hq') 7 sel.bucket (by decide)
    (by have := hs.b; simpa using this)
    ((hasLeaf_iff _ _ _).mpr ⟨selLeaf sel 0, by simp, hb0⟩) (fun q h => hq q (List.mem_append_left _ h))
  have hC := climbV_honest answers index c hc hi (valOf proof base (slotPositions sel))
    (valOf pads.fold base (slotPositions sel)) (selLeaf sel 2) hg2 4 7 _ (by decide)
    (by rw [hD.1, hb2]) (fun q h => hq q (List.mem_append_right _ h))
  intro p hp
  unfold slotPositions at hp
  rcases List.mem_append.mp hp with hp | hp
  · rw [hs.selected] at hp
    exact hD.2 p hp
  · simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have e : selLeaf sel 2 / 2 ^ (7 + j) = sel.bucket / 2 ^ j := bucket_div_outer hs.l2
    have := hC.2 (7 + j) (by omega) (by omega)
    rw [e] at this
    exact this
theorem queried_canon_fold (answers : Answers) (P : Nat → M Digest) :
    ∀ (l : List Nat) (init : List Digest) (c : Nat), c ∈ l → ∀ q ∈ queried answers (P c),
      q ∈ queried answers (l.foldlM (fun roots c => (fun v => roots ++ [v]) <$> P c) init) := by
  intro l
  induction l with
  | nil => intro _ _ h; simp at h
  | cons x xs ih =>
      intro init c hc q hq
      rw [List.foldlM_cons, queried_bind]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_append_left _ (by rwa [Extract.queried_map])
      · exact List.mem_append_right _ (ih _ c hc q hq)
theorem slot_coord (chosen : List Selection) : ∀ n k, k < slotBase chosen n →
    ∃ c < n, slotBase chosen c ≤ k ∧ k < slotBase chosen (c + 1) := by
  intro n
  induction n with
  | zero => intro k hk; simp [slotBase] at hk
  | succ n ih =>
      intro k hk
      by_cases h : k < slotBase chosen n
      · obtain ⟨c, hc, h1, h2⟩ := ih k h
        exact ⟨c, by omega, h1, h2⟩
      · exact ⟨n, by omega, by omega, hk⟩
theorem forest_block (answers : Answers) (index c : Nat) (sel : Selection) :
    Correctness.forestInner answers index c sel ++ Correctness.forestOuter answers index c sel =
      (slotPositions sel).map (fun p => H answers index c p.1 p.2) := by
  simp only [Correctness.forestInner, Correctness.forestOuter, slotPositions, selectedLeaves, List.map_append,
    List.map_map]
  rfl
theorem forestProofPrefix_eq (answers : Answers) (index : Nat) (chosen : List Selection) (n : Nat) :
    Correctness.forestProofPrefix answers index chosen n =
      (List.range n).flatMap fun c => (slotPositions (chosen.getD c ⟨0, []⟩)).map
        (fun p => H answers index c p.1 p.2) := by
  unfold Correctness.forestProofPrefix
  congr 1
  funext c
  exact forest_block answers index c _
theorem length_proof_blocks (answers : Answers) (index : Nat) (chosen : List Selection) (n : Nat) :
    ((List.range n).flatMap fun c => (slotPositions (chosen.getD c ⟨0, []⟩)).map
      (fun p => H answers index c p.1 p.2)).length = slotBase chosen n := by
  rw [List.length_flatMap]
  unfold slotBase
  congr 1
  apply List.map_congr_left
  intro c _
  simp
theorem queried_recoverFtsP_coord (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 115) (c : Nat) (hc7 : c < 7) :
    ∀ q ∈ queried answers (coordCanon index c (leafHP index c (selectedLeaves (chosen.getD c ⟨0, []⟩))
          ((List.range 3).map (fun j => sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
        (valOf sig.proof (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
        (valOf pads.fold (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
        (selLeaf (chosen.getD c ⟨0, []⟩) 0) (selLeaf (chosen.getD c ⟨0, []⟩) 1)
        (selLeaf (chosen.getD c ⟨0, []⟩) 2)),
      q ∈ queried answers (recoverFtsP sig pads index chosen) := by
  intro q hq
  rw [recoverFtsP_canon sig pads index chosen hc hle, queried_bind]
  apply List.mem_append_left
  have key := queried_canon_fold answers (fun c => coordCanon index c
      (leafHP index c (selectedLeaves (chosen.getD c ⟨0, []⟩))
        ((List.range 3).map (fun j => sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
      (valOf sig.proof (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
      (valOf pads.fold (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
      (selLeaf (chosen.getD c ⟨0, []⟩) 0) (selLeaf (chosen.getD c ⟨0, []⟩) 1)
      (selLeaf (chosen.getD c ⟨0, []⟩) 2)) (List.range 7) [] c (List.mem_range.mpr hc7) q hq
  exact key
theorem fts_proof_honest (answers : Answers) (σ : Signature) (N : HashOutput) (root : Digest)
    (hadm : admissible (selections N) = true)
    (hroot : evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some root)
    (hq : ∀ q ∈ queried answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)), HonQ answers q) :
    ∀ k : Fin 115, σ.proof k =
      (Correctness.forestProofPrefix answers (N.toNat % 2 ^ 31) (selections N) 7).getD k.val 0 := by
  have hsel := selectionsOk_of_admissible N hadm
  have hc := chosenOk_of N hsel
  have hle := slotBase_seven_le N hc hadm
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
  have htail := eval_recoverFtsP_tail answers σ 0 _ _ hc hle root (by rw [recoverFtsP_zero]; exact hroot)
  rw [← recoverFtsP_zero] at hq
  have hcoord : ∀ c < 7, ∀ p ∈ slotPositions ((selections N).getD c ⟨0, []⟩),
      valOf σ.proof (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩)) p =
        H answers (N.toNat % 2 ^ 31) c p.1 p.2 := by
    intro c hc7
    exact coord_honest answers σ.proof 0 _ hidx c (by omega) _ (hc c hc7) _ _
      (fun q h => hq q (queried_recoverFtsP_coord answers σ 0 _ _ hc hle c hc7 q h))
  rw [forestProofPrefix_eq]
  intro k
  by_cases hk : k.val < slotBase (selections N) 7
  · obtain ⟨c, hc7, hlo, hhi⟩ := slot_coord (selections N) 7 k.val hk
    rw [slotBase_succ] at hhi
    have hx : k.val - slotBase (selections N) c < (slotPositions ((selections N).getD c ⟨0, []⟩)).length := by
      omega
    have hv := hcoord c hc7 _ (List.getElem_mem hx)
    unfold valOf at hv
    have hfin : (⟨(slotBase (selections N) c + (slotPositions ((selections N).getD c ⟨0, []⟩)).idxOf
        (slotPositions ((selections N).getD c ⟨0, []⟩))[k.val - slotBase (selections N) c]) % 115,
        Nat.mod_lt _ (by decide)⟩ : Fin 115) = k := by
      ext
      simp only
      rw [List.Nodup.idxOf_getElem (slotPositions_nodup _) _ hx, Nat.add_sub_cancel' hlo, Nat.mod_eq_of_lt k.isLt]
    rw [hfin] at hv
    rw [hv]
    have hb := Correctness.flatMap_range_getD (fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).map
        (fun p => H answers (N.toNat % 2 ^ 31) c p.1 p.2)) 7 c (k.val - slotBase (selections N) c) hc7
      (by rw [List.length_map]; exact hx)
    rw [length_proof_blocks, Nat.add_sub_cancel' hlo] at hb
    rw [hb, List.getD_eq_getElem ((slotPositions ((selections N).getD c ⟨0, []⟩)).map
      (fun p => H answers (N.toNat % 2 ^ 31) c p.1 p.2)) 0 (by rw [List.length_map]; exact hx), List.getElem_map]
  · rw [htail k (by omega)]
    symm
    apply List.getD_eq_default
    rw [length_proof_blocks]
    omega
theorem fts_secrets_honest (answers : Answers) (σ : Signature) (N : HashOutput)
    (hs : ∀ (c : Fin 7) (j : Fin 3), σ.secrets ⟨3 * c.val + j.val, by omega⟩ =
      S answers (N.toNat % 2 ^ 31) c.val (selLeaf ((selections N).getD c.val ⟨0, []⟩) j.val)) :
    ∀ i : Fin 21, σ.secrets i =
      (Correctness.forestOpenPrefix answers (N.toNat % 2 ^ 31) (selections N) 7).getD i.val 0 := by
  intro i
  have hdummy := SigningRecords.secret_at_coordinate answers
    ⟨0, fun i => (Correctness.forestOpenPrefix answers (N.toNat % 2 ^ 31) (selections N) 7).getD i.val 0,
      fun _ => 0, fun _ => ⟨fun _ => 0, fun _ => 0⟩⟩ N (fun _ => rfl) ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩
  have hi : 3 * (i.val / 3) + i.val % 3 = i.val := by omega
  have hsi := hs ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩
  have hfin : (⟨3 * (i.val / 3) + i.val % 3, by omega⟩ : Fin 21) = i := Fin.ext hi
  simp only [hfin] at hsi
  rw [hsi]
  change (Correctness.forestOpenPrefix answers (N.toNat % 2 ^ 31) (selections N) 7).getD
    (3 * (i.val / 3) + i.val % 3) 0 = _ at hdummy
  rw [hi] at hdummy
  rw [hdummy]
  rfl
end SigGolfCandidate.T3.Security.BSuf
end

section

namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
theorem expandN_unfold (answers : Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (wit : Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, wit)) :
    ∃ counter rootF cs,
      evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) = some (counter, N) ∧
      evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some rootF ∧
      evalWithAnswerFn answers (expandLayers σ (N.toNat % 2 ^ 31) 4 rootF) = some (pk, cs) ∧
      wit = ⟨σ, counter, fun lay => cs.getD lay.val 0⟩ := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hf : evalWithAnswerFn answers (recoverFts σ (output.toNat % 2 ^ 31) (selections output)) with
      | none => simp only [hf, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some rootF =>
          simp only [hf, evalWithAnswerFn_bind] at he
          cases hl : evalWithAnswerFn answers (expandLayers σ (output.toNat % 2 ^ 31) 4 rootF) with
          | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some layers =>
              obtain ⟨root, cs⟩ := layers
              simp only [hl] at he
              split at he
              · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
              · rename_i hne
                simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                have hroot : root = pk := by simpa using hne
                subst hroot
                exact ⟨counter, rootF, cs, rfl, hf, hl, rfl⟩
theorem expandLayers_length (answers : Answers) (σ : Signature) (index : Nat) :
    ∀ n (value root : Digest) (cs : List (BitVec 32)),
      evalWithAnswerFn answers (expandLayers σ index n value) = some (root, cs) → cs.length = n := by
  intro n
  induction n with
  | zero =>
      intro value root cs h
      simp only [expandLayers, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; rfl
  | succ n ih =>
      intro value root cs h
      simp only [expandLayers, evalWithAnswerFn_bind] at h
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at h
      | some found =>
          obtain ⟨counter, digits⟩ := found
          simp only [hs, evalWithAnswerFn_bind] at h
          cases hr : evalWithAnswerFn answers (expandLayers σ index n
              (evalWithAnswerFn answers (recoverLayer σ index (Fin.ofNat 4 n) digits))) with
          | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at h
          | some res =>
              obtain ⟨root', cs'⟩ := res
              simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2, List.length_append, ih _ _ _ hr]
              rfl
theorem layer_of_shaped (answers : Answers) (N : HashOutput) (wit : Witness) (lay : Layer) (digits : List Nat)
    (hs : Extract.LayerShaped answers (witEnc N wit) (N.toNat % 2 ^ 31) lay digits) :
    wit.signature.layers lay = piecesSignature lay (Correctness.honestPieces answers lay
      (route (N.toNat % 2 ^ 31) lay).2 (route (N.toNat % 2 ^ 31) lay).1 digits) := by
  apply LayerSignature.ext'
  · funext i
    rw [← wvalue_witEnc N wit lay i, (hs.2 i.val i.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]
  · funext j
    rw [← wpath_witEnc N wit lay j, (hs.1 j.val j.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]
theorem honestMsg_lower (answers : Answers) (index n : Nat) (hn : n + 1 < 4) :
    Extract.honestMsg answers index (Fin.ofNat 4 n) =
      treeValue (Correctness.builtTree answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2)
        (height (Fin.ofNat 4 (n + 1))) 0 := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
  have hl : (⟨n + 1, by omega⟩ : Layer) = Fin.ofNat 4 (n + 1) := Fin.ext (by simp; omega)
  simp only [Extract.honestMsg, hv, dif_pos (show n < 3 by omega), Extract.honestRoot, hl]
theorem layers_payload (answers : Answers) (published : T3.Cache)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (N : HashOutput) (wit : Witness)
    (hgood : ∀ lay : Layer, Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay) :
    ∀ n, n ≤ 4 → ∀ (value root : Digest) (cs : List (BitVec 32)),
      (∀ k, n = k + 1 → value = Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k)) →
      evalWithAnswerFn answers (expandLayers wit.signature (N.toNat % 2 ^ 31) n value) = some (root, cs) →
      (∀ lay : Layer, lay.val < n → wit.counters lay = cs.getD lay.val 0) →
      ∃ pieces, evalWithAnswerFn answers (signLayers published (N.toNat % 2 ^ 31) n value) = some pieces ∧
        pieces.length = n ∧ ∀ lay : Layer, lay.val < n →
          wit.signature.layers lay = piecesSignature lay (pieces.getD lay.val ([], [])) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  intro n
  induction n with
  | zero =>
      intro _ value root cs _ _ _
      refine ⟨[], by simp [signLayers], rfl, fun lay h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
      intro hn value root cs hval hexp hctr
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      have hmsg := hval n rfl
      simp only [expandLayers, evalWithAnswerFn_bind] at hexp
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2
          (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at hexp
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hsome := Correctness.counterSearch_some answers (Fin.ofNat 4 n) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2
            (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 value counterLimit 0 counter digits (by decide) hs
          have hvalid := Cost.validDigits_decode hsome.2.2
          simp only [hs, evalWithAnswerFn_bind] at hexp
          cases hr : evalWithAnswerFn answers (expandLayers wit.signature (N.toNat % 2 ^ 31) n
              (evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 n) digits))) with
          | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at hexp
          | some res =>
              obtain ⟨root', cs'⟩ := res
              simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
              obtain ⟨-, hcs⟩ := hexp
              have hlen := expandLayers_length answers wit.signature (N.toNat % 2 ^ 31) n _ _ _ hr
              have hcounter : wit.counters (Fin.ofNat 4 n) = counter := by
                rw [hctr _ (by rw [hv]; omega), ← hcs, hv, List.getD_append_right _ _ _ _ (by omega), hlen]
                simp
              obtain ⟨digitsG, ⟨_, hdec⟩, hshape⟩ := hgood (Fin.ofNat 4 n)
              rw [wctr_witEnc, hcounter, ← hmsg, hsome.2.2, Option.some.injEq] at hdec
              subst hdec
              rename' digits => digitsG
              have hlayer := layer_of_shaped answers N wit (Fin.ofNat 4 n) digitsG hshape
              have hrec := Correctness.recoverLayer_honestPieces answers wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 n) digitsG
                hvalid hlayer
              by_cases hn0 : n = 0
              · subst hn0
                have ht : (route (N.toNat % 2 ^ 31) 0).2 = 0 := route_top_tree (N.toNat % 2 ^ 31) hidx
                have htop := Correctness.eval_signTop_honest answers published (route (N.toNat % 2 ^ 31) 0).1 digitsG hcache
                  (route_leaf_bound (N.toNat % 2 ^ 31) 0) hvalid
                refine ⟨[Correctness.honestPieces answers 0 0 (route (N.toNat % 2 ^ 31) 0).1 digitsG], ?_, rfl, ?_⟩
                · simp only [signLayers, evalWithAnswerFn_bind, hs, ite_true, evalWithAnswerFn_pure]
                  rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, htop]
                · intro lay hlay
                  have hl0 : lay = 0 := Fin.ext (by simp at hlay ⊢; omega)
                  subst hl0
                  rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, ht] at hlayer
                  exact hlayer
              · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
                have hnext : evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1)) digitsG) =
                    Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k) := by
                  rw [hrec, honestMsg_lower answers (N.toNat % 2 ^ 31) k (by omega)]
                obtain ⟨pieces, hpieces, hplen, hpagree⟩ := ih (by omega) _ root' cs'
                  (fun k' hk' => by rw [hnext]; congr; omega) hr
                  (fun lay hlay => by
                    rw [hctr lay (by omega), ← hcs, List.getD_append _ _ _ _ (by omega)])
                have htree := Correctness.eval_buildTree_result answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG hvalid
                  (route_leaf_bound (N.toNat % 2 ^ 31) _)
                refine ⟨pieces ++ [Correctness.honestPieces answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG], ?_,
                  by simp [hplen], ?_⟩
                · rw [signLayers]
                  simp only [evalWithAnswerFn_bind, hs, htree, show k + 1 ≠ 0 by omega, ite_false]
                  have hroot : ((Correctness.builtTree answers (Fin.ofNat 4 (k + 1))
                      (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).getD (height (Fin.ofNat 4 (k + 1))) []).getD 0 0 =
                      evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1)) digitsG) := by
                    rw [hrec]; rfl
                  rw [hroot, hpieces]
                  rfl
                · intro lay hlay
                  by_cases hlt : lay.val < k + 1
                  · rw [hpagree lay hlt, List.getD_append _ _ _ _ (by omega)]
                  · have hle : lay = Fin.ofNat 4 (k + 1) := Fin.ext (by rw [hv]; omega)
                    subst hle
                    rw [hlayer, hv, List.getD_append_right _ _ _ _ (by omega), hplen]
                    simp
theorem fts_queries_honest (answers : Answers) (σ : Signature) (N : HashOutput) (wit : Witness)
    (hsig : wit.signature = σ) (hc : ChosenOk (selections N)) (hle : slotBase (selections N) 7 ≤ 115)
    (htail : ∀ k : Fin 115, slotBase (selections N) 7 ≤ k.val → wit.signature.proof k = 0)
    (hfts : FtsExtract.FtsShaped answers N (witEnc N wit)) :
    ∀ q ∈ queried answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)), HonQ answers q := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
  intro q hq
  have h := hfts.1 q (by
    rw [witDecP_witEnc N wit hc hle htail, padDecP_witEnc N wit hc hle, recoverFtsP_zero, hsig]
    exact hq)
  rcases h with h | ⟨c, hc7, ⟨leaf, hleaf, h⟩ | ⟨level, hlevel, node, hnode, h⟩⟩
  · exact ⟨.forest _, hidx, h⟩
  · exact ⟨.ftsLeaf _ c leaf, ⟨by omega, hidx, by omega⟩, h⟩
  · exact ⟨.ftsNode _ c level node, ⟨by omega, hidx, hlevel, by simpa only [Nat.sub_sub] using hnode⟩, h⟩
theorem ftsRootsHonest_eq (answers : Answers) (index : Nat) :
    Extract.ftsRootsHonest answers index = Correctness.forestRoots answers index 7 := by
  have h := FtsExtract.honestInput_forest answers index
  rw [show Extract.honestInput answers (.forest index) =
    pad64 (Extract.forestInput index (Extract.ftsRootsHonest answers index)) from rfl] at h
  exact FtsExtract.forestInput_injective (Extract.ftsRootsHonest_length answers index)
    (by simp [Correctness.forestRoots]) h
theorem caseC_expansion_is_payload (answers : Answers) (published : T3.Cache)
    (message : Message) (pk : Digest) (signature : Signature) (N : HashOutput) (wit : Witness)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (_hpk : pk = Extract.honestRoot answers 0 0)
    (he : evalWithAnswerFn answers (expandN message pk signature) = some (N, wit))
    (hgood : ∀ lay : Layer, Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay)
    (hfts : FtsExtract.FtsShaped answers N (witEnc N wit)) :
    (evalWithAnswerFn answers (payloadRecordForNonce published signature.rho message)).1 = some signature := by
  have F := expandN_facts answers message pk signature N wit he
  obtain ⟨counter, rootF, cs, hds, hrf, hel, hwit⟩ := expandN_unfold answers message pk signature N wit he
  have hsel := selectionsOk_of_admissible N F.adm
  have hc := chosenOk_of N hsel
  have hle := slotBase_seven_le N hc F.adm
  have htail : ∀ k : Fin 115, slotBase (selections N) 7 ≤ k.val → wit.signature.proof k = 0 := by
    rw [F.sig]
    exact eval_recoverFtsP_tail answers signature 0 _ _ hc hle rootF (by rw [recoverFtsP_zero]; exact hrf)
  have hq := fts_queries_honest answers signature N wit F.sig hc hle htail hfts
  have hproof := fts_proof_honest answers signature N rootF F.adm hrf hq
  have hsec := fts_secrets_honest answers signature N (fun c j => by
    have h := (hfts.2 c.val c.isLt j.val j.isLt).1
    rw [wsecret_witEnc N wit _ (by omega), F.sig] at h
    exact h)
  have hrf' := Correctness.recoverFts_from_signer_lists answers signature (N.toNat % 2 ^ 31) N F.adm hsec hproof
  have hrootF : rootF = evalWithAnswerFn answers (forestPk (N.toNat % 2 ^ 31)
      (Correctness.forestRoots answers (N.toNat % 2 ^ 31) 7)) := by
    rw [hrf] at hrf'; exact Option.some.inj hrf'
  have hmsg3 : rootF = Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 3) := by
    rw [hrootF, show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
    simp only [Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false, Extract.honestForest,
      ftsRootsHonest_eq]
  obtain ⟨pieces, hpieces, -, hpagree⟩ := layers_payload answers published hcache N wit hgood 4 le_rfl rootF pk cs
    (fun k hk => by obtain rfl : k = 3 := by omega
                    exact hmsg3)
    (by rw [F.sig]; exact hel)
    (fun lay _ => by rw [hwit])
  unfold payloadRecordForNonce
  simp only [evalWithAnswerFn_bind, hds]
  rw [SigningRecords.payloadAfterDigest_forestRows]
  simp only [evalWithAnswerFn_bind, Correctness.eval_forestRows, evalWithAnswerFn_pure]
  rw [← hrootF, hpieces]
  simp only [evalWithAnswerFn_pure, Option.some.injEq]
  have hlay : ∀ lay : Layer, piecesSignature lay (pieces.getD lay.val ([], [])) = signature.layers lay := by
    intro lay
    have := hpagree lay lay.isLt
    rw [F.sig] at this
    exact this.symm
  rcases signature with ⟨rho, secrets, proof, layers⟩
  simp only [Signature.mk.injEq]
  exact ⟨trivial, funext fun i => (hsec i).symm, funext fun k => (hproof k).symm, funext hlay⟩
end SigGolfCandidate.T3.Security.BSuf
end
