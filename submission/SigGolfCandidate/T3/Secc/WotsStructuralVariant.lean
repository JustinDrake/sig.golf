import SigGolfCandidate.T3.Secc.WotsStructuralHonest

/-!
# Stream S (2): R3 does not read the structural rows

A *structural row* (w.r.t. secrets and labels) is a public input that parses (PEX `posOf`) to a source node of G's
canonical graph without being that node's cell. `Variant labels T T'`: `T` agrees with `labels` (G's `Agrees`), and
`T'` coincides with `T` on coins, private coordinates and every public input that is not a structural row.

* `congr_of_queried`: tables agreeing on every query of a deterministic run evaluate it alike and issue the same queries
  (adaptive congruence; the queried inputs may depend on earlier answers).
* `Variant.honest`: an `HonestQuery` (stream S (1)) is answered alike by structural variants (an honest input at a
  source position is the cell, G's `honestInput_eq`).
* Hence R3's whole source program (`referenceGame_variant`: honest key generation, the offline signer, both honest
  charges) and every reference word / frontier depth at a source-sized leaf (`depth_variant`) are unchanged.
* The honest roots read by the reference search of a layer-0 leaf may lie at a child tree index `≥ 2^40`; headers keep
  `tree mod 2^40`, so those roots are the roots of the aliased bounded tree (`builtTree_alias`).
-/

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf

/-! ## Adaptive congruence -/

theorem eval_query_bind {α : Type} (T : Answers) (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) :
    evalWithAnswerFn T (liftM (T3.Spec.query input) >>= next) = evalWithAnswerFn T (next (T input)) := by
  rw [evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn T (liftM (T3.Spec.query input)) = T input from simulateQ_spec_query T input]

/-- **Adaptive congruence**: two tables that agree on every query of the deterministic run of `program` under `T`
evaluate it alike and issue the same queries. -/
theorem congr_of_queried {α : Type} (T T' : Answers) (program : M α)
    (h : ∀ q ∈ SourceReplay.queried T program, T q = T' q) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program := by
  induction program using OracleComp.inductionOn with
  | pure x => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have h0 : T input = T' input := h input List.mem_cons_self
      have ih' := ih (T input) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      refine ⟨?_, ?_⟩
      · rw [eval_query_bind, eval_query_bind, ← h0]
        exact ih'.1
      · rw [SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, ← h0, ih'.2]

/-! ## Structural variants -/

/-- `T'` coincides with `T` except possibly on structural rows: public inputs parsed at a source node of G's graph
that are not that node's cell (for `T`'s secrets and the labels `T` agrees with). -/
structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))

theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    Extract.posOf (Extract.honestInput T p) = some p :=
  Extract.posOf_eq hp (Extract.hdrBlock_honestInput T p)

/-- Honest queries are answered alike by structural variants. -/
theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr ⟨p, hp, hx⟩ => hv.pub x (fun node h => by
      rw [hx, posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact CanonGraph.honestInput_eq hv.agrees node)

/-- A program whose queries under `T` are honest evaluates alike (and issues the same queries) under every structural
variant of `T`. -/
theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))

/-! ## R3's source program -/

section Game
variable {labels : CanonGraph.Labels} {T T' : Answers}

theorem keygenCharge_variant (hv : Variant labels T T') : keygenCharge T = keygenCharge T' := by
  unfold keygenCharge
  rw [(hv.congr (sat_keygen T)).2]

theorem eval_keygen_variant (hv : Variant labels T T') :
    evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen :=
  (hv.congr (sat_keygen T)).1

theorem signCharge_variant (hv : Variant labels T T') (published : T3.Cache) (request : Request) :
    signCharge T published request = signCharge T' published request := by
  unfold signCharge
  rw [(hv.congr (sat_authenticatedSign T published request)).2]

theorem eval_sign_variant (hv : Variant labels T T') (published : T3.Cache) (request : Request) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      evalWithAnswerFn T' (FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).1

theorem offlineSign_variant (hv : Variant labels T T') (published : T3.Cache) (request : Request) :
    offlineSign T published request = offlineSign T' published request := by
  unfold offlineSign
  rw [signCharge_variant hv, eval_sign_variant hv]

theorem offlineImpl_variant (hv : Variant labels T T') (published : T3.Cache) :
    offlineImpl T published = offlineImpl T' published := by
  unfold offlineImpl
  have h : offlineSign T published = offlineSign T' published := funext (offlineSign_variant hv published)
  rw [h]

theorem offlineGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) :
    offlineGame T adversary = offlineGame T' adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_variant hv, eval_keygen_variant hv, offlineImpl_variant hv]

/-- **R3's capped source program does not read the structural rows.** -/
theorem referenceGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) (q : Nat) :
    referenceGame T adversary q = referenceGame T' adversary q := by
  unfold referenceGame
  rw [offlineGame_variant hv]

/-- The honest public key is unchanged. -/
theorem publicKey_variant (hv : Variant labels T T') :
    (evalWithAnswerFn T keygen).1 = (evalWithAnswerFn T' keygen).1 := by
  rw [eval_keygen_variant hv]

end Game

/-! ## Tree aliasing (headers keep `tree mod 2^40`) -/

section Alias
variable (T : Answers) (lay : Layer) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40)
include h

theorem leafEnd_alias (leaf i : Nat) : leafEnd T lay tree leaf i = leafEnd T lay tree' leaf i := by
  have hal : Mask.LeafAlias lay tree leaf ⟨lay, tree', leaf⟩ := ⟨rfl, h, rfl⟩
  unfold Correctness.leafEnd
  rw [Mask.chain_alias hal, Mask.leafSeed_alias T hal]

theorem leafRoot_alias (leaf : Nat) : leafRoot T lay tree leaf = leafRoot T lay tree' leaf := by
  unfold Correctness.leafRoot
  have hends : (List.range (chainCount lay)).map (leafEnd T lay tree leaf) =
      (List.range (chainCount lay)).map (leafEnd T lay tree' leaf) :=
    List.map_congr_left fun i _ => leafEnd_alias T lay h leaf i
  rw [hends]
  unfold leafHash
  rw [Mask.header_congr (t := 2) (p := 0) rfl h rfl]

omit h in
theorem buildLevels_alias (tag lay' : Nat) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40) (height : Nat)
    (leaves : List Digest) :
    T3.buildLevels tag lay' tree height leaves = T3.buildLevels tag lay' tree' height leaves := by
  have hn : T3.nodeHash tag lay' tree = T3.nodeHash tag lay' tree' := by
    funext heap left right
    unfold T3.nodeHash
    rw [Mask.header_congr (t := tag) (p := 0) rfl h rfl]
  have hl : T3.buildLevel tag lay' tree = T3.buildLevel tag lay' tree' := by
    funext height level nodes
    unfold T3.buildLevel
    rw [hn]
  unfold T3.buildLevels
  rw [hl]

theorem builtTree_alias : builtTree T lay tree = builtTree T lay tree' := by
  unfold Correctness.builtTree
  have hr : leafRoot T lay tree = leafRoot T lay tree' := funext (leafRoot_alias T lay h)
  rw [hr, buildLevels_alias 3 lay.val h]

theorem honestRoot_alias : Extract.honestRoot T lay tree = Extract.honestRoot T lay tree' := by
  unfold Extract.honestRoot
  rw [builtTree_alias T lay h]

end Alias

/-! ## Reference words and depths -/

section Depth
variable {labels : CanonGraph.Labels} {T T' : Answers}

theorem builtTree_variant_bounded (hv : Variant labels T T') (lay : Layer) (tree : Nat) (htree : tree < 2 ^ 40) :
    builtTree T lay tree = builtTree T' lay tree := by
  rw [← Correctness.eval_buildTree_levels T lay tree 0 [] (Cost.validDigits_nil lay),
    ← Correctness.eval_buildTree_levels T' lay tree 0 [] (Cost.validDigits_nil lay),
    (hv.congr (sat_buildTree T lay tree 0 [] (Cost.validDigits_nil lay) htree)).1]

theorem builtTree_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat) :
    builtTree T lay tree = builtTree T' lay tree := by
  have hmod : tree % 2 ^ 40 = tree % 2 ^ 40 % 2 ^ 40 := (Nat.mod_mod _ _).symm
  rw [builtTree_alias T lay hmod, builtTree_alias T' lay hmod]
  exact builtTree_variant_bounded hv lay _ (Nat.mod_lt _ (by decide))

theorem honestRoot_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat) :
    Extract.honestRoot T lay tree = Extract.honestRoot T' lay tree := by
  unfold Extract.honestRoot
  rw [builtTree_variant hv]

theorem honestForest_variant (hv : Variant labels T T') (index : Nat) (hindex : index < 2 ^ 40) :
    Extract.honestForest T index = Extract.honestForest T' index := by
  rw [Mask.honestForest_eq T, Mask.honestForest_eq T']
  have hfts : ∀ c ∈ List.range 7, evalWithAnswerFn T (buildFts index c) = evalWithAnswerFn T' (buildFts index c) :=
    fun c hc => (hv.congr (sat_buildFts T index c hindex (List.mem_range.mp hc))).1
  have hroots : ((List.range 7).map fun c => treeValue (evalWithAnswerFn T' (buildFts index c)).1 11 0) =
      Correctness.forestRoots T index 7 :=
    List.map_congr_left fun c hc => by rw [hfts c hc]
  rw [hroots]
  exact (hv.congr (sat_forestPk T index hindex)).1

/-- The honest message of a source-sized leaf (tree `< 2^31`, leaf `< 2^height`) is unchanged. -/
theorem leafMsg_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ 31)
    (hleaf : L.leaf < 2 ^ height L.lay) : leafMsg T L = leafMsg T' L := by
  unfold leafMsg
  split
  · exact honestRoot_variant hv _ _
  · rename_i hl
    have h3 : L.lay = 3 := by
      apply Fin.ext
      have := L.lay.isLt
      change L.lay.val = 3
      omega
    have hh : height L.lay = 6 := by rw [h3]; rfl
    rw [hh] at hleaf ⊢
    exact honestForest_variant hv _ (by
      have : L.tree * 2 ^ 6 < 2 ^ 31 * 2 ^ 6 := Nat.mul_lt_mul_of_pos_right htree (by decide)
      have : (2 : Nat) ^ 31 * 2 ^ 6 + 2 ^ 6 ≤ 2 ^ 40 := by norm_num
      omega)

theorem referenceSearch_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ 31)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceSearch T L = referenceSearch T' L := by
  unfold referenceSearch
  rw [leafMsg_variant hv L htree hleaf]
  exact (hv.congr (sat_counterSearch T _ _ _ _ _ _)).1

theorem referenceDigits_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ 31)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceDigits T L = referenceDigits T' L := by
  unfold referenceDigits
  rw [referenceSearch_variant hv L htree hleaf]

/-- **The frontier depth of a source-sized chain is unchanged.** -/
theorem depth_variant (hv : Variant labels T T') (a : ChainAddr) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 2 ^ height a.key.lay) : depth T a = depth T' a := by
  unfold depth
  rw [referenceDigits_variant hv a.key htree hleaf]

end Depth

end SigGolfCandidate.T3.Security.Wots.Structural
