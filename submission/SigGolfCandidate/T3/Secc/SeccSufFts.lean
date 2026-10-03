import SigGolfCandidate.T3.BPORS

/-! # B-SUF (1/4): the FTS part of a case-(C) expansion is the honest signing payload

Case (C) of `PaddedExtraction.Conclusion` gives `FtsExtract.FtsShaped answers N w`: every query of the padded FTS
recovery is the honest input of *some* bounded reference position (forest pk, FTS leaf, FTS node), and the 21
opened secrets are honest. PEX-F does not export which position each query sits at, nor that the proof slots read
at the folds are honest nodes. Here we re-derive both from the definitions:

* `honQ_eq`: a query whose header block is that of a bounded position `pos` and that is honest at some bounded
  position is honest at `pos` itself (`Pos.hdr_injective`);
* `dfsP_honest` / `climbV_honest`: in Core's slot-free DFS (`dfsP`) and the outer climbs (`climbV`), all-honest
  queries force the value, and the valuation of every empty position (= proof slot), to the honest tree node;
* `fts_proof_honest`: for a successful Core FTS recovery `recoverFts σ index (selections N)` whose queries are all
  honest, every one of the 118 proof slots equals the signer's `forestProofPrefix` entry (used slots: honest nodes
  in Core's consumption order, through `recoverFtsP_canon`; unused slots: zero, from Core's tail check,
  Core.lean:366, `eval_recoverFtsP_tail`);
* `fts_secrets_honest`: the secrets equal the signer's `forestOpenPrefix` entries.

Kernel hygiene. `Extract.ftsLevels answers index coord` is *defined* as `(evalWithAnswerFn answers (buildFts index
coord)).1`; the kernel compares the two forms by unfolding `ftsLevels` and then reducing the projection, which
evaluates `buildFts` (~35 s per comparison, also hidden in the lazily realized equation lemma
`Extract.ftsLevels.eq_1`). We therefore state honest FTS values on `buildFts` directly (`H`) and convert honest
inputs with PEX-F's already checked `honestInput_ftsNode` / `honInputL_built`. -/

namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree

/-! ## Honest queries are honest at their own header position -/

/-- A query is the honest (padded) input of some bounded reference position. -/
def HonQ (answers : Answers) (q : Spec.Domain) : Prop :=
  ∃ pos : Extract.Pos, pos.Bounded ∧ q = .inl (.inr (Extract.honestInput answers pos))

/-- An honest query whose header block names the bounded position `pos` is the honest input at `pos`. -/
theorem honQ_eq {answers : Answers} {pos : Extract.Pos} {input : HashInput} (hb : pos.Bounded)
    (hh : Extract.hdrBlock input = bytesLE 16 pos.hdr) (hq : HonQ answers (.inl (.inr input))) :
    input = Extract.honestInput answers pos := by
  obtain ⟨pos', hb', he⟩ := hq
  have hi : input = Extract.honestInput answers pos' := by
    simpa only [Sum.inl.injEq, Sum.inr.injEq] using he
  have hh' := Extract.hdrBlock_honestInput answers pos'
  rw [← hi, hh] at hh'
  rw [hi, Extract.Pos.hdr_injective hb hb' (bytesLE_injective hh')]

/-- Honest value of node `(level, node)` of the FTS tree `(index, coord)` (Core's `buildFts` levels). -/
abbrev H (answers : Answers) (index coord level node : Nat) : Digest :=
  treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level node

/-- Honest secret of global leaf `leaf` of the FTS tree `(index, coord)` (`Extract.ftsSecret`; unfolding it is
kernel-safe: its body is headed by `List.getD`, not by a projection). -/
abbrev S (answers : Answers) (index coord leaf : Nat) : Digest := Extract.ftsSecret answers index coord leaf

theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (l p r : Digest) :
    Extract.hdrBlock (nodeInputP tag lay tree heap l p r) = bytesLE 16 (header tag lay tree 0 heap) := by
  unfold nodeInputP; exact Extract.hdrBlock_block4 _ _ _ _

theorem hdrBlock_ftsLeafInputP (index coord leaf : Nat) (a s b : Digest) :
    Extract.hdrBlock (ftsLeafInputP index coord leaf a s b) = bytesLE 16 (header 9 coord index 0 leaf) := by
  unfold ftsLeafInputP; exact Extract.hdrBlock_block4 _ _ _ _

/-- An honest FTS fold/merge query has the honest children and a zero pad. -/
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

/-- An honest FTS leaf query has zero pads and the honest secret. -/
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

/-! ## The slot-free DFS and the outer climbs -/

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

/-- **DFS honesty.** If every query of Core's slot-free DFS at a non-empty node is honest (and honest leaf queries
give honest leaf values), the DFS returns the honest node and every empty frontier position is valued honestly. -/
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

/-- One honest climb step from level `k` on the root path of `g`. -/
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

/-- **Climb honesty.** `a` honest folds on the root path of `g` from an honest node value at level `lo`. -/
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

/-! ## One coordinate -/

/-- An honest leaf query of `recoverChildP`'s leaf hash gives the honest leaf value. -/
theorem leafHP_honest (answers : Answers) (index coord : Nat) (hc : coord < 256) (hi : index < 2 ^ 40)
    (leaves : List Nat) (values : List Digest) (pads : Pads) (g : Nat) (hg : g < 2048)
    (hq : ∀ q ∈ queried answers (leafHP index coord leaves values pads g), HonQ answers q) :
    evalWithAnswerFn answers (leafHP index coord leaves values pads g) = H answers index coord 0 g := by
  unfold leafHP at hq ⊢
  rw [ftsLeafP_eq_shortHash, queried_shortHash, pad64_ftsLeafInputP] at hq
  obtain ⟨h1, h2, h3⟩ := honQ_leaf hc hi (by omega) (hq _ (List.mem_singleton_self _))
  rw [ftsLeafP_eq_shortHash, SecurityExtraction.eval_shortHash, pad64_ftsLeafInputP, h1, h2, h3]
  exact out_leaf_honest answers index coord g hg

/-- **Coordinate honesty.** All-honest queries of Core's canonical coordinate program (`recoverFtsP_canon`) value
every proof position of the coordinate (bucket frontier, then the four outer siblings) honestly. -/
theorem coord_honest (answers : Answers) (proof : Fin 118 → Digest) (pads : Pads) (index : Nat)
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

/-! ## Seven coordinates -/

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

/-- Every proof slot below `slotBase chosen n` belongs to a coordinate `c < n`. -/
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

/-- The signer's per-coordinate proof block is the honest valuation of the coordinate's proof positions. -/
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

/-- The queries of coordinate `c`'s canonical program are queries of Core's padded FTS recovery. -/
theorem queried_recoverFtsP_coord (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 118) (c : Nat) (hc7 : c < 7) :
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

/-- **Proof-slot honesty.** A successful Core FTS recovery all of whose queries are honest carries exactly the
signer's proof list: honest nodes in Core's consumption order on the used slots, zero on the unused ones. -/
theorem fts_proof_honest (answers : Answers) (σ : Signature) (N : HashOutput) (root : Digest)
    (hadm : admissible (selections N) = true)
    (hroot : evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some root)
    (hq : ∀ q ∈ queried answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)), HonQ answers q) :
    ∀ k : Fin 118, σ.proof k =
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
        (slotPositions ((selections N).getD c ⟨0, []⟩))[k.val - slotBase (selections N) c]) % 118,
        Nat.mod_lt _ (by decide)⟩ : Fin 118) = k := by
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

/-- **Secret honesty.** Secrets matching the honest opened leaves are the signer's opened list. -/
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
