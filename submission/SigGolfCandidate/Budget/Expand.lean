import SigGolfCandidate.Budget.Bridge
import SigGolfCandidate.Final.Abstract
import SigGolfCandidate.Final.RO
import SigGolfCandidate.Equiv.Sign

/-!
# Budget: the expansion is pathwise cheaper than signing

The expansion searches each layer's counter; under the lazy random oracle of the honest pipeline its
encoding queries were all made (and answered) by the signer, so a moment bound from fresh queries does
not apply. Instead, on every path of the honest pipeline the expansion costs fewer compressions than
the signing before it:

* every reachable state of the lazy random oracle is an evaluation under a fixed answer function
  (`eval_of_mem_support_roRun`: answer every query by its cached value);
* under a fixed answer function the expansion of an honest signature finds the signer's counters
  (`Final.eval_aExpand_sign'`), so it costs at most `3356 + Σ (c_lay + 1)` compressions
  (`blocksF_expandList_le`: digest, PORS stack machine, per layer the search and the chains, leaf and
  fold), while the signer costs at least `2^13 + Σ (c_lay + 1)` (`bR_sign_ge`: the PORS tree's secret
  derivations and the same counter searches);
* hence `E[2^(N_expand / 2^20)] ≤ E[2^(N_sign / 2^17)] ≤ 2` (`expand_bound_of_sign`).
-/

open OracleComp OracleSpec ENNReal OracleComp.EvalDist

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

/-! ## Compressions along the path of a fixed answer function -/

section blocks
variable (f : Hash)

/-- The compressions of `oa`'s queries along the path of the answer function `f`. -/
def blocksF {α : Type} (oa : OracleComp HashSpec α) : Nat := (evalWithAnswerFn f (countBlocks oa)).2

theorem eval_countBlocks_fst {α : Type} (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn f (countBlocks oa)).1 = evalWithAnswerFn f oa := by
  conv_rhs => rw [← fst_countWith Query.blocks oa]
  rw [evalWithAnswerFn_map]
  rfl

@[simp] theorem blocksF_pure {α : Type} (a : α) : blocksF f (pure a : OracleComp HashSpec α) = 0 := rfl

theorem blocksF_bind {α β : Type} (oa : OracleComp HashSpec α) (g : α → OracleComp HashSpec β) :
    blocksF f (oa >>= g) = blocksF f oa + blocksF f (g (evalWithAnswerFn f oa)) := by
  unfold blocksF countBlocks
  rw [countWith_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map]
  simp only
  rw [show (evalWithAnswerFn f (countWith Query.blocks oa)).1 = evalWithAnswerFn f oa from
    eval_countBlocks_fst f oa]

theorem blocksF_query (q : Query) : blocksF f (qry q) = q.blocks := by
  unfold blocksF countBlocks
  rw [countWith_query, evalWithAnswerFn_map]

theorem blocksF_map {α β : Type} (h : α → β) (oa : OracleComp HashSpec α) :
    blocksF f (h <$> oa) = blocksF f oa := by
  rw [map_eq_bind_pure_comp, blocksF_bind]
  simp

/-- `Spec` bounds the compressions of every path. -/
theorem Spec.blocksF_le {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat}
    {oa : OracleComp HashSpec α} (h : Spec P Post k oa) : blocksF f oa ≤ k := by
  induction h with
  | pure a k _ => simp
  | query q g k _ _ ih =>
    rw [blocksF_bind, blocksF_query]
    exact Nat.add_le_add_left (ih _) _

/-- `Spec` gives the result's property on every path. -/
theorem Spec.eval_post {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat}
    {oa : OracleComp HashSpec α} (h : Spec P Post k oa) : Post (evalWithAnswerFn f oa) := by
  induction h with
  | pure a k hp => exact hp
  | query q g k _ _ ih =>
    rw [evalWithAnswerFn_bind]
    exact ih _

end blocks

/-! ## Compressions of relabelled abstract computations -/

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

section relabel
variable (f : Hash)

/-- The answer function a computation relabelled by `fmtQ` sees. -/
def gF : QueryImpl SphincsSecurity.HashSpec Id := fun x => f (Equiv.fmtQ x)

theorem eval_relabel {α : Type} (X : Equiv.AComp α) :
    evalWithAnswerFn f (Bridge.relabel Equiv.fmtQ X) = evalWithAnswerFn (gF f) X :=
  Final.evalWithAnswerFn_relabel Equiv.fmtQ f X

/-- The compressions of the abstract computation `X` (relabelled by `fmtQ`) along `f`'s path. -/
def bR {α : Type} (X : Equiv.AComp α) : Nat := blocksF f (Bridge.relabel Equiv.fmtQ X)

@[simp] theorem bR_pure {α : Type} (a : α) : bR f (pure a : Equiv.AComp α) = 0 := rfl

theorem bR_bind {α β : Type} (X : Equiv.AComp α) (K : α → Equiv.AComp β) :
    bR f (X >>= K) = bR f X + bR f (K (evalWithAnswerFn (gF f) X)) := by
  unfold bR
  rw [Bridge.relabel_bind, blocksF_bind, eval_relabel]

theorem bR_map {α β : Type} (h : α → β) (X : Equiv.AComp α) : bR f (h <$> X) = bR f X := by
  rw [map_eq_bind_pure_comp, bR_bind]
  simp

theorem bR_oracleHash_ge (x : SphincsSecurity.HashInput) :
    1 ≤ bR f (SphincsSecurity.Concrete.oracleHash (m := Equiv.AComp) x) := by
  unfold bR
  rw [Equiv.relabel_oracleHash]
  unfold Ref.H
  rw [show (HashSpec.query (addrFmt (Equiv.toB x)) : OracleComp HashSpec _) = qry (addrFmt (Equiv.toB x)) from rfl,
    blocksF_query]
  unfold Query.blocks; omega

theorem bR_tweakableHash_ge (p : SphincsSecurity.PublicParameter) (d : SphincsSecurity.HashDomain)
    (pl : SphincsSecurity.HashInput) :
    1 ≤ bR f (SphincsSecurity.Concrete.tweakableHash (m := Equiv.AComp) p d pl) := by
  unfold SphincsSecurity.Concrete.tweakableHash
  rw [bR_bind]
  have := bR_oracleHash_ge f (SphincsSecurity.tweakableHashInput p d pl)
  omega

open SphincsSecurity SphincsSecurity.Concrete in
/-- A successful least-counter search from `start` tried every counter up to the one it returns. -/
theorem bR_encodingSearch_ge (p : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (M : SphincsSecurity.EncMessage) : ∀ (attempts start : Nat) (c : Counter) (enc : Encoding), start + attempts ≤ 2 ^ 32 →
      evalWithAnswerFn (gF f) (encodingSearch (m := Equiv.AComp) p lay tree leaf M attempts start)
        = some (c, enc) →
      c.toNat + 1 ≤ start + bR f (encodingSearch (m := Equiv.AComp) p lay tree leaf M attempts start) := by
  intro attempts
  induction attempts with
  | zero => intro start c enc _ h; simp [encodingSearch] at h
  | succ n ih =>
    intro start c enc hb h
    unfold encodingSearch at h ⊢
    rw [bR_bind]
    rw [evalWithAnswerFn_bind] at h
    have he : 1 ≤ bR f (encode (m := Equiv.AComp) p lay tree leaf M (BitVec.ofNat counterBits start)) := by
      unfold encode
      rw [bR_bind]
      have := bR_oracleHash_ge f (tweakableHashInput M.1 (.encoding lay tree leaf)
        (bytesLE 16 M.2 ++ bytesLE 4 (BitVec.ofNat counterBits start)))
      omega
    cases hr : evalWithAnswerFn (gF f) (encode (m := Equiv.AComp) p lay tree leaf M
        (BitVec.ofNat counterBits start)) with
    | some e =>
      rw [hr] at h
      simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [bR_pure, Nat.add_zero]
      have hc : (BitVec.ofNat counterBits start).toNat = start := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by show start < 2 ^ 32; omega)
      rw [hc]
      omega
    | none =>
      rw [hr] at h
      have := ih (start + 1) c enc (by omega) h
      simp only
      omega

open SphincsSecurity SphincsSecurity.Concrete in
theorem bR_sequenceFin_ge {α : Type} : ∀ {n : Nat} (c : Fin n → Equiv.AComp α) (k : Nat),
    (∀ j, k ≤ bR f (c j)) → n * k ≤ bR f (sequenceFin (m := Equiv.AComp) c)
  | 0, _, _, _ => by simp
  | n + 1, c, k, hc => by
    unfold sequenceFin
    rw [bR_bind, bR_bind]
    simp only [bR_pure, Nat.add_zero]
    have h1 := hc 0
    have h2 := bR_sequenceFin_ge (fun i : Fin n => c i.succ) k (fun j => hc j.succ)
    rw [Nat.succ_mul]
    omega

open SphincsSecurity SphincsSecurity.Concrete in
/-- The PORS tree derives at least one secret per leaf pair. -/
theorem bR_buildFtsTreePaired_ge (p : PublicParameter) (index : Index)
    (secret : FtsPair → Equiv.AComp (Digest × Digest)) (hs : ∀ pair, 1 ≤ bR f (secret pair)) :
    2 ^ 13 ≤ bR f (buildFtsTreePaired (m := Equiv.AComp) p index secret) := by
  unfold buildFtsTreePaired
  rw [bR_bind]
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (le_of_eq ?_) (bR_sequenceFin_ge f _ 1 (fun pair => ?_))
  · simp [ftsTreeHeight]
  · rw [bR_bind]; have := hs pair; omega

/-- The counters a signer's layer outputs carry, plus one per layer (the searches' trial counts). -/
def trialsOf (parts : SphincsSecurity.Layer → SphincsSecurity.Concrete.LayerOutput) (n : Nat) : Nat :=
  ((List.range n).map fun j =>
    if h : j < SphincsSecurity.numLayers then (parts ⟨j, h⟩).1.toNat + 1 else 0).sum

open SphincsSecurity SphincsSecurity.Concrete in
/-- The signer's layers search every counter up to the ones they sign. -/
theorem bR_signLayersPaired_ge (p : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → Equiv.AComp (Digest × Digest))
    (topNode : Nat → Nat → Equiv.AComp Digest) :
    ∀ (n : Nat) (M : SphincsSecurity.EncMessage) (parts : Layer → LayerOutput), n ≤ numLayers →
      evalWithAnswerFn (gF f) (signLayersPaired (m := Equiv.AComp) p index secret topNode n M) = some parts →
      trialsOf parts n ≤ bR f (signLayersPaired (m := Equiv.AComp) p index secret topNode n M) := by
  intro n
  induction n with
  | zero => intro M parts _ _; simp [trialsOf]
  | succ r ih =>
    intro M parts hn h
    have hlayer : r < numLayers := by omega
    unfold signLayersPaired at h ⊢
    rw [dif_pos hlayer] at h ⊢
    by_cases h0 : r = 0
    · subst h0
      rw [if_pos rfl] at h ⊢
      rw [bR_bind]
      rw [evalWithAnswerFn_bind] at h
      unfold signTopLayerPaired at h ⊢
      rw [bR_bind]
      rw [evalWithAnswerFn_bind] at h
      cases hs : evalWithAnswerFn (gF f) (encodingSearch (m := Equiv.AComp) p topLayer
          (treeIndexAt index topLayer) (leafIndexAt index topLayer) M encodingAttemptLimit 0) with
      | none => rw [hs] at h; simp at h
      | some ce =>
        obtain ⟨counter, encoding⟩ := ce
        have hb := bR_encodingSearch_ge f p topLayer (treeIndexAt index topLayer) (leafIndexAt index topLayer)
          M encodingAttemptLimit 0 counter encoding (by simp [encodingAttemptLimit]) hs
        rw [hs] at h
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at h
        subst h
        rw [show (0 + 1 : Nat) = 1 from rfl]
        unfold trialsOf
        rw [show List.range 1 = [0] from rfl]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [dif_pos (show 0 < numLayers by decide), if_pos (show (⟨0, _⟩ : Layer) = topLayer from rfl)]
        dsimp only
        omega
    · rw [if_neg h0] at h ⊢
      rw [bR_bind]
      rw [evalWithAnswerFn_bind] at h
      cases hs : evalWithAnswerFn (gF f) (encodingSearch (m := Equiv.AComp) p ⟨r, hlayer⟩
          (treeIndexAt index ⟨r, hlayer⟩) (leafIndexAt index ⟨r, hlayer⟩) M encodingAttemptLimit 0) with
      | none => rw [hs] at h; simp at h
      | some ce =>
        obtain ⟨counter, encoding⟩ := ce
        have hb := bR_encodingSearch_ge f p ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)
          (leafIndexAt index ⟨r, hlayer⟩) M encodingAttemptLimit 0 counter encoding
          (by simp [encodingAttemptLimit]) hs
        rw [hs] at h
        simp only at h ⊢
        rw [bR_bind]
        rw [evalWithAnswerFn_bind] at h
        generalize evalWithAnswerFn (gF f) (buildLayerTreePaired (m := Equiv.AComp) p ⟨r, hlayer⟩
          (treeIndexAt index ⟨r, hlayer⟩) (secret ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩))
          (leafIndexAt index ⟨r, hlayer⟩) encoding) = t at h ⊢
        obtain ⟨values, path, root⟩ := t
        simp only at h ⊢
        rw [bR_bind]
        rw [evalWithAnswerFn_bind] at h
        cases hrest : evalWithAnswerFn (gF f) (signLayersPaired (m := Equiv.AComp) p index secret topNode r root) with
        | none => rw [hrest] at h; simp at h
        | some rest =>
          rw [hrest] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          subst h
          have hi := ih root rest (by omega) hrest
          simp only [bR_pure, Nat.add_zero]
          have ht : trialsOf (fun other => if other = ⟨r, hlayer⟩ then (counter, values, path) else rest other)
              (r + 1) = trialsOf rest r + (counter.toNat + 1) := by
            unfold trialsOf
            rw [List.range_succ, List.map_append, List.sum_append]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
              dif_pos hlayer, if_pos rfl]
            congr 1
            refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
            rw [List.mem_range] at hj
            by_cases hjl : j < numLayers
            · rw [dif_pos hjl, dif_pos hjl, if_neg (fun e => by
                have := congrArg Fin.val e; simp at this; omega)]
            · rw [dif_neg hjl, dif_neg hjl]
          rw [ht]
          omega

open SphincsSecurity SphincsSecurity.Concrete in
/-- **The signer's compressions**: at least one per PORS leaf pair, plus every counter search. -/
theorem bR_sign_ge (sk : Seeded.SecretKey) (cache : TopCache) (msg : SphincsSecurity.Message) (S : Signature)
    (h : evalWithAnswerFn (gF f) (Seeded.sign (m := Equiv.AComp) sk cache msg) = some S) :
    2 ^ 13 + ((List.range numLayers).map fun j => Final.ctrOf S j + 1).sum ≤
      bR f (Seeded.sign (m := Equiv.AComp) sk cache msg) := by
  unfold Seeded.sign at h ⊢
  rw [bR_bind]
  rw [evalWithAnswerFn_bind] at h
  split at h
  swap
  · simp at h
  rename_i htag
  rw [if_pos htag]
  refine le_trans ?_ (Nat.le_add_left _ _)
  unfold Seeded.signChecked at h ⊢
  rw [bR_bind]
  rw [evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn (gF f) (Seeded.signDigestPairs (m := Equiv.AComp) sk msg digestPairLimit 0) with
  | none => rw [hd] at h; simp at h
  | some r =>
    obtain ⟨randomness, index, leaves⟩ := r
    rw [hd] at h
    simp only at h ⊢
    refine le_trans ?_ (Nat.le_add_left _ _)
    unfold signFromPaired at h ⊢
    rw [bR_bind]
    rw [evalWithAnswerFn_bind] at h
    have hfts := bR_buildFtsTreePaired_ge f sk.parameter index
      (Seeded.ftsSecret (m := Equiv.AComp) sk.parameter sk.seed index porsTree) (fun pair => by
        unfold Seeded.ftsSecret
        rw [bR_bind]
        have := bR_oracleHash_ge f (keygenHashInput sk.parameter (.fts index porsTree pair) sk.seed)
        omega)
    generalize evalWithAnswerFn (gF f) (buildFtsTreePaired (m := Equiv.AComp) sk.parameter index
      (Seeded.ftsSecret (m := Equiv.AComp) sk.parameter sk.seed index porsTree)) = t at h ⊢
    obtain ⟨secrets, table⟩ := t
    simp only at h ⊢
    rw [bR_bind]
    rw [evalWithAnswerFn_bind] at h
    cases hl : evalWithAnswerFn (gF f) (signLayersPaired (m := Equiv.AComp) sk.parameter index
        (Seeded.otsSecret sk.parameter sk.seed) (Seeded.cachedTopNode sk.parameter sk.seed cache)
        numLayers (0, table ftsTreeHeight 0)) with
    | none => rw [hl] at h; simp at h
    | some parts =>
      rw [hl] at h
      simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      have hL := bR_signLayersPaired_ge f sk.parameter index (Seeded.otsSecret sk.parameter sk.seed)
        (Seeded.cachedTopNode sk.parameter sk.seed cache) numLayers (0, table ftsTreeHeight 0) parts le_rfl hl
      have ht : ((List.range numLayers).map fun j => Final.ctrOf ⟨randomness, honestFts leaves secrets table,
          fun lay => LayerOutput.toSignature lay (parts lay)⟩ j + 1).sum = trialsOf parts numLayers := by
        unfold trialsOf
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        rw [List.mem_range] at hj
        unfold Final.ctrOf
        rw [dif_pos hj, dif_pos hj]
        rfl
      rw [ht]
      simp only [bR_pure, Nat.add_zero]
      omega

end relabel

/-! ## The expansion's compressions (reference level) -/

theorem slice_length_le (l : List Byte) (a n : Nat) : (Ref.slice l a n).length ≤ n := by
  simp [Ref.slice]

theorem spec_chainFrom (lay tau e i x : Nat) (v : Val) (hv : v.length ≤ 16) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) 7 (chainFrom lay tau e i x v) := by
  unfold chainFrom
  refine Spec.foldlM_range'_le (P := fun _ => True) (x + 1) (7 - x) _ (fun _ (w : Val) => w.length ≤ 16)
    (fun _ => 1) v hv (fun i' _ w hw => ?_) (fun _ h => h) (by (try simp) <;> omega)
  exact spec_hash16_bind (chainInput lay tau e i (x + 1 + i') w) trivial
    (blocksFmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl

/-- The chains (at most 7 steps each) and the 704-byte leaf. -/
theorem spec_verifyLeaf (w : List Byte) (lay tau e : Nat) (x : List Nat) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) 305 (verifyLeaf w lay tau e x) := by
  unfold verifyLeaf
  refine Spec.bind' (l := 11) (Spec.foldlM_range_le (P := fun _ => True) nChains _
    (fun i (ends : List Val) => AllShort ends ∧ ends.length = i) (fun _ => 7) []
    ⟨AllShort.nil, rfl⟩ (fun i _ ends hends => ?_) (fun acc h => h) le_rfl) (fun ends hends => ?_)
    (by (try simp [nChains]))
  · refine Spec.bind' (spec_chainFrom lay tau e i _ _ (slice_length_le _ _ _)) (fun v hv => ?_)
      (Nat.add_zero 7).le
    exact Spec.pure _ 0 ⟨hends.1.append hv, by simp [hends.2]⟩
  · refine spec_hash16 _ 11 trivial (blocksFmt_le _ 11 ?_ (by omega)) |>.mono (fun _ h => h)
      (fun v hv => by omega)
    have hl : ends.flatten.length ≤ 16 * 42 := by
      rw [List.length_flatten]
      have : ∀ v ∈ ends, v.length ≤ 16 := hends.1
      calc (ends.map List.length).sum ≤ (ends.map fun _ => 16).sum :=
            List.sum_le_sum (fun v hv => this v hv)
        _ = 16 * 42 := by simp [hends.2, nChains]
    simp only [leafInput, thInput, List.length_append, length_tweak, P, length_zeros]
    omega

/-- A fold over a path of 16-byte siblings: one compression per level. -/
theorem spec_foldPath (lay tau leaf : Nat) (v : Val) (hv : v.length ≤ 16) (path : List Val)
    (hp : AllShort path) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) path.length
      (foldPath (nodeInput lay tau) leaf v path) := by
  unfold foldPath
  refine Spec.foldlM_range_le (P := fun _ => True) path.length _ (fun _ (w : Val) => w.length ≤ 16)
    (fun _ => 1) v hv (fun i _ w hw => ?_) (fun _ h => h) (by simp)
  have hs : (path[i]?.getD []).length ≤ 16 := by
    cases h : path[i]? with
    | none => simp
    | some u => simp only [Option.getD_some]; exact hp u (List.mem_of_getElem? h)
  have hs' : (path.getD i []).length ≤ 16 := by rw [List.getD_eq_getElem?_getD]; exact hs
  dsimp only
  split
  · exact spec_hash16_bind _ trivial (blocksFmt_le _ 1 (by simp [nodeInput, thInput]; omega) le_rfl)
      (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl
  · exact spec_hash16_bind _ trivial (blocksFmt_le _ 1 (by simp [nodeInput, thInput]; omega) le_rfl)
      (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl

theorem allShort_witPath (w : List Byte) (lay : Nat) : AllShort (witPath w lay) := by
  intro u hu
  simp only [witPath, List.mem_map, List.mem_range] at hu
  obtain ⟨l, -, rfl⟩ := hu
  exact slice_length_le _ _ _

theorem length_witPath (w : List Byte) (lay : Nat) : (witPath w lay).length = height lay := by
  simp [witPath]

/-! ### The PORS stack machine -/

/-- The stack holds 16-byte nodes. -/
def StackOk (stack : List (Val × Nat)) : Prop := ∀ p ∈ stack, p.1.length ≤ 16

/-- The pending hash's input value is a 16-byte node. -/
def PendingOk : Pending → Prop
  | .leaf _ s => s.length ≤ 16
  | .merge _ l => l.length ≤ 16

theorem spec_segment (idx : Nat) (w : List Byte) (ptr E folds : Nat) (pending : Pending)
    (hp : PendingOk pending) (node : Val) (hn : node.length ≤ 16) :
    Spec (fun _ => True) (fun r : Option (Nat × Nat × Nat × Val × Bool) =>
        ∀ q ∈ r, q.2.2.2.1.length ≤ 16) 15 (Ref.segment idx w ptr E folds pending node) := by
  unfold Ref.segment
  dsimp only
  split
  · exact Spec.pure _ _ (by simp)
  split
  · exact Spec.pure _ _ (by simp)
  rename_i ha _
  have ha' : wbyte w ptr % 16 ≤ 14 := by unfold porsH at ha; omega
  refine Spec.bind' (Q := fun v : Val => v.length ≤ 16) (k := 1) (l := 14) ?_ (fun v hv => ?_) le_rfl
  · cases pending with
    | leaf x s =>
      exact spec_hash16 _ 1 trivial (blocksFmt_le _ 1 (by
        simp only [porsLeafInput, thInput, List.length_append, length_tweak, P, length_zeros]
        simp only [PendingOk] at hp; omega) le_rfl) |>.mono (fun _ h => h) (fun v h => by omega)
    | merge H l =>
      exact spec_hash16 _ 1 trivial (blocksFmt_le _ 1 (by
        simp only [porsNodeInput, thInput, List.length_append, length_tweak, P, length_zeros]
        simp only [PendingOk] at hp; omega) le_rfl) |>.mono (fun _ h => h) (fun v h => by omega)
  · refine Spec.bind' (Q := fun st : Val × Nat => st.1.length ≤ 16) (k := 14) (l := 0) ?_
      (fun st hst => Spec.pure _ _ ?_) le_rfl
    · unfold segFolds
      refine Spec.foldlM_range_le (P := fun _ => True) (wbyte w ptr % 16) _
        (fun _ (st : Val × Nat) => st.1.length ≤ 16) (fun _ => 1) (v, E) hv (fun i _ st hst => ?_)
        (fun _ h => h) (by simp; omega)
      dsimp only
      split
      · exact spec_hash16_bind _ trivial (blocksFmt_le _ 1 (by
          simp [porsNodeInput, thInput, wbytes]; omega) le_rfl)
          (fun w' hw' => Spec.pure _ 0 (by simp; omega)) le_rfl
      · exact spec_hash16_bind _ trivial (blocksFmt_le _ 1 (by
          simp [porsNodeInput, thInput, wbytes]; omega) le_rfl)
          (fun w' hw' => Spec.pure _ 0 (by simp; omega)) le_rfl
    · intro q hq
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact hst

theorem spec_segLoop (idx : Nat) (w : List Byte) :
    ∀ (stack : List (Val × Nat)) (ptr E folds : Nat) (pending : Pending) (node : Val),
      PendingOk pending → node.length ≤ 16 → StackOk stack →
      Spec (fun _ => True) (fun r : Option (Nat × Nat × Nat × Val × List (Val × Nat)) =>
          ∀ q ∈ r, q.2.2.2.1.length ≤ 16 ∧ StackOk q.2.2.2.2 ∧ q.2.2.2.2.length ≤ stack.length)
        (15 * (stack.length + 1)) (segLoop idx w ptr E folds pending node stack)
  | [], ptr, E, folds, pending, node, hp, hn, _ => by
    unfold segLoop
    refine Spec.bind' (l := 0) (spec_segment idx w ptr E folds pending hp node hn) (fun r hr => ?_) (by simp)
    rcases r with _ | ⟨ptr', E', folds', node', merge⟩
    · exact Spec.pure _ _ (by simp)
    · dsimp only
      split
      · exact Spec.pure _ _ (by simp)
      · refine Spec.pure _ _ ?_
        intro q hq
        simp only [Option.mem_def, Option.some.injEq] at hq
        subst hq
        exact ⟨hr _ rfl, fun _ h => by simp at h, le_rfl⟩
  | (pnode, Q) :: rest, ptr, E, folds, pending, node, hp, hn, hs => by
    unfold segLoop
    refine Spec.bind' (l := 15 * (rest.length + 1)) (spec_segment idx w ptr E folds pending hp node hn)
      (fun r hr => ?_) (by simp; omega)
    rcases r with _ | ⟨ptr', E', folds', node', merge⟩
    · exact Spec.pure _ _ (by simp)
    · dsimp only
      split
      · refine Spec.pure _ _ ?_
        intro q hq
        simp only [Option.mem_def, Option.some.injEq] at hq
        subst hq
        exact ⟨hr _ rfl, hs, le_rfl⟩
      · split
        · exact Spec.pure _ _ (by simp)
        · refine (spec_segLoop idx w rest ptr' (E' / 2) folds' (.merge (E' / 2) pnode) node'
            (hs (pnode, Q) (by simp)) (hr _ rfl) (fun p hp' => hs p (List.mem_cons_of_mem _ hp'))).mono
            (fun _ h => h) (fun r hr' q hq => ?_)
          obtain ⟨h1, h2, h3⟩ := hr' q hq
          exact ⟨h1, h2, by simp only [List.length_cons]; omega⟩

/-- The block bound of the leaf loop from `n` leaves on with a stack of `k` nodes. -/
def porsBound : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => 15 * (k + 1) + porsBound n (k + 1)

theorem porsBound_mono : ∀ (n : Nat) {k k' : Nat}, k ≤ k' → porsBound n k ≤ porsBound n k'
  | 0, _, _, _ => le_rfl
  | n + 1, k, k', h => by
    unfold porsBound
    have := porsBound_mono n (show k + 1 ≤ k' + 1 by omega)
    omega

theorem spec_porsLeaves (idx : Nat) (v : List Nat) (w : List Byte) :
    ∀ (slots : List Nat) (st : PorsState), st.node.length ≤ 16 → StackOk st.stack →
      Spec (fun _ => True) (fun r : Option PorsState => ∀ q ∈ r, q.node.length ≤ 16)
        (porsBound slots.length st.stack.length) (porsLeaves idx v w slots st)
  | [], st, hn, _ => by
    unfold porsLeaves
    exact Spec.pure _ _ (fun q hq => by simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact hn)
  | s :: rest, st, hn, hs => by
    unfold porsLeaves
    dsimp only
    split
    · exact Spec.pure _ _ (by simp)
    split
    · exact Spec.pure _ _ (by simp)
    refine Spec.bind' (l := porsBound rest.length (st.stack.length + 1))
      (spec_segLoop idx w st.stack st.ptr _ st.folds _ st.node
      (by simp only [PendingOk]; exact slice_length_le _ _ _) hn hs) (fun r hr => ?_)
      (by simp only [List.length_cons, porsBound]; omega)
    rcases r with _ | ⟨ptr', E', folds', node', stack'⟩
    · exact (Spec.pure _ _ (by simp)).mono_k (Nat.zero_le _)
    · obtain ⟨h1, h2, h3⟩ := hr _ rfl
      dsimp only at h1 h2 h3 ⊢
      have hs' : StackOk (if s < porsK - 1 then (node', E' ^^^ 1) :: stack' else stack') := by
        split
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact h1
          · exact h2 p hp
        · exact h2
      have hl : (if s < porsK - 1 then (node', E' ^^^ 1) :: stack' else stack').length ≤
          st.stack.length + 1 := by
        split
        · simp only [List.length_cons]; omega
        · omega
      exact (spec_porsLeaves idx v w rest ⟨ptr', _, E', folds', node', _⟩ h1 hs').mono_k
        (porsBound_mono _ hl)

/-- The PORS stack machine makes at most `1800` compressions. -/
theorem spec_porsRoot (idx : Nat) (v : List Nat) (w : List Byte) :
    Spec (fun _ => True) (fun r : Option Val => ∀ q ∈ r, q.length ≤ 16) 1800 (porsRoot idx v w) := by
  unfold porsRoot
  refine Spec.bind' (l := 0) (spec_porsLeaves idx v w (List.range porsK) ⟨wStream, 0, 0, 0, [], []⟩
    (by simp) (by simp [StackOk])) (fun r hr => ?_) (by simp [porsK, porsBound])
  rcases r with _ | st
  · exact Spec.pure _ _ (by simp)
  · dsimp only
    split
    · exact Spec.pure _ _ (by simp)
    · exact Spec.pure _ _ (fun q hq => by
        simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact hr _ rfl)

/-! ### The counter phase and the whole expansion -/

theorem blocksF_hash16_bind (f : Hash) {β : Type} (x : List Byte) (K : Val → OracleComp HashSpec β) :
    blocksF f (hash16 x >>= K) = (addrFmt x).blocks + blocksF f (K (answerBytes 16 (f (addrFmt x)))) := by
  rw [hash16_bind_eq, blocksF_bind, blocksF_query]
  congr 2

theorem eval_hash16_bind (f : Hash) {β : Type} (x : List Byte) (K : Val → OracleComp HashSpec β) :
    evalWithAnswerFn f (hash16 x >>= K) = evalWithAnswerFn f (K (answerBytes 16 (f (addrFmt x)))) := by
  rw [hash16_bind_eq, evalWithAnswerFn_bind]
  rfl

theorem blocksF_encodingHash_bind (f : Hash) {β : Type} (x : List Byte) (K : Val → OracleComp HashSpec β) :
    blocksF f (encodingHash x >>= K) = (addrFmt x).blocks + blocksF f (K (encodingBytes (f (addrFmt x)))) := by
  rw [encodingHash_bind_eq, blocksF_bind, blocksF_query]
  congr 2

theorem eval_encodingHash_bind (f : Hash) {β : Type} (x : List Byte) (K : Val → OracleComp HashSpec β) :
    evalWithAnswerFn f (encodingHash x >>= K) = evalWithAnswerFn f (K (encodingBytes (f (addrFmt x)))) := by
  rw [encodingHash_bind_eq, evalWithAnswerFn_bind]
  rfl

/-- A successful least-counter search from `c` costs one compression per trial. -/
theorem blocksF_searchCounter (f : Hash) (lay tau e : Nat) (M : Val) (hM : M.length ≤ 32) :
    ∀ fuel c c' x, evalWithAnswerFn f (searchCounter lay tau e M c fuel) = some (c', x) →
      blocksF f (searchCounter lay tau e M c fuel) + c ≤ c' + 1 ∧ c ≤ c' ∧ c' < c + fuel := by
  intro fuel
  induction fuel with
  | zero => intro c c' x h; simp [searchCounter] at h
  | succ n ih =>
    intro c c' x
    have hb : (addrFmt (encInput lay tau e M c)).blocks ≤ 1 :=
      blocksFmt_le _ 1 (by simp [encInput]; omega) le_rfl
    unfold searchCounter
    rw [blocksF_encodingHash_bind, eval_encodingHash_bind]
    generalize encodingBytes (f (addrFmt (encInput lay tau e M c))) = d
    cases decodeDigits lay d with
    | some x' =>
      intro h
      have h' : some (c, x') = some (c', x) := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      show (addrFmt (encInput lay tau e M c)).blocks + 0 + c ≤ c + 1 ∧ c ≤ c ∧ c < c + (n + 1)
      omega
    | none =>
      intro h
      have := ih (c + 1) c' x h
      show (addrFmt (encInput lay tau e M c)).blocks + blocksF f (searchCounter lay tau e M (c + 1) n) + c ≤ c' + 1 ∧
        c ≤ c' ∧ c' < c + (n + 1)
      omega

/-- The counter phase: one compression per counter trial, at most `311` others per layer; it returns
one counter below `C_max` per layer. -/
theorem blocksF_expandLayers (f : Hash) (w : List Byte) (idx : Nat) :
    ∀ n (M : Val) (cs : List Nat), n ≤ 5 → M.length ≤ 32 →
      evalWithAnswerFn f (expandLayers w idx n M) = some cs →
      blocksF f (expandLayers w idx n M) ≤ 311 * n + (cs.map (· + 1)).sum ∧ cs.length = n ∧
        ∀ c ∈ cs, c < 2 ^ 22 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro M cs hn hM
  rcases n with _ | _ | k
  · intro h
    have h' : some [] = some cs := h
    simp only [Option.some.injEq] at h'
    subst h'
    exact ⟨by simp [expandLayers], rfl, by simp⟩
  · intro h
    unfold expandLayers at h ⊢
    generalize route idx 0 = p at h ⊢
    obtain ⟨e, tau⟩ := p
    rw [blocksF_bind]
    rw [evalWithAnswerFn_bind] at h
    have hsearch := blocksF_searchCounter f 0 tau e M hM cMax 0
    generalize hs : evalWithAnswerFn f (searchCounter 0 tau e M 0 cMax) = r at h ⊢
    rcases r with _ | ⟨c, x⟩
    · exact absurd h (by simp)
    · obtain ⟨hb1, -, hb3⟩ := hsearch c x hs
      have h' : some [c] = some cs := h
      simp only [Option.some.injEq] at h'
      subst h'
      refine ⟨?_, rfl, ?_⟩
      · show blocksF f (searchCounter 0 tau e M 0 cMax) + 0 ≤ 311 * 1 + (c + 1 + 0)
        omega
      · intro c' hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
        subst hc'; unfold cMax at hb3; omega
  · intro h
    have hk := hn
    unfold expandLayers at h ⊢
    generalize hp : route idx (k + 1) = p at h ⊢
    obtain ⟨e, tau⟩ := p
    rw [blocksF_bind]
    rw [evalWithAnswerFn_bind] at h
    have hsearch := blocksF_searchCounter f (k + 1) tau e M hM cMax 0
    generalize hs : evalWithAnswerFn f (searchCounter (k + 1) tau e M 0 cMax) = r at h ⊢
    rcases r with _ | ⟨c, x⟩
    · exact absurd h (by simp)
    · obtain ⟨hb1, -, hb3⟩ := hsearch c x hs
      have hv := spec_verifyLeaf w (k + 1) tau e x
      have hvl := Spec.eval_post f hv
      have hvb := Spec.blocksF_le f hv
      change blocksF f (searchCounter (k + 1) tau e M 0 cMax) +
          blocksF f (verifyLeaf w (k + 1) tau e x >>= fun leaf =>
            foldPath (nodeInput (k + 1) tau) e leaf
                ((witPath w (k + 1)).take (height (k + 1) - 1)) >>= fun node =>
              hash16 (nodeInput (k + 1) tau (height (k + 1)) 0
                  ((topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))).take 16)
                  ((topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))).drop 16))
                >>= fun _ =>
              expandLayers w idx (k + 1)
                  (topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))) >>= fun r =>
                match r with
                | none => pure none
                | some cs => pure (some (cs ++ [c]))) ≤ _ ∧ _
      change evalWithAnswerFn f (verifyLeaf w (k + 1) tau e x >>= fun leaf =>
            foldPath (nodeInput (k + 1) tau) e leaf
                ((witPath w (k + 1)).take (height (k + 1) - 1)) >>= fun node =>
              hash16 (nodeInput (k + 1) tau (height (k + 1)) 0
                  ((topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))).take 16)
                  ((topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))).drop 16))
                >>= fun _ =>
              expandLayers w idx (k + 1)
                  (topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))) >>= fun r =>
                match r with
                | none => pure none
                | some cs => pure (some (cs ++ [c]))) = _ at h
      rw [blocksF_bind]
      rw [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn f (verifyLeaf w (k + 1) tau e x) = leaf at h hvl ⊢
      have hshort : AllShort ((witPath w (k + 1)).take (height (k + 1) - 1)) := fun u hu =>
        allShort_witPath w (k + 1) u (List.mem_of_mem_take hu)
      have hfd := spec_foldPath (k + 1) tau e leaf hvl _ hshort
      have hfl := Spec.eval_post f hfd
      have hfb := Spec.blocksF_le f hfd
      rw [List.length_take, length_witPath] at hfb
      have hh : height (k + 1) ≤ 6 := by
        have hk4 : k < 4 := by omega
        interval_cases k <;> decide
      rw [blocksF_bind]
      rw [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn f (foldPath (nodeInput (k + 1) tau) e leaf
        ((witPath w (k + 1)).take (height (k + 1) - 1))) = node at h hfl ⊢
      have hsib : (witSib w (k + 1) (height (k + 1) - 1)).length ≤ 16 := slice_length_le _ _ _
      have htop : (topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1))).length ≤ 32 := by
        unfold topPair
        split <;> rw [List.length_append] <;> omega
      generalize topPair e (height (k + 1)) node (witSib w (k + 1) (height (k + 1) - 1)) = top at h htop ⊢
      have hnb : (addrFmt (nodeInput (k + 1) tau (height (k + 1)) 0 (top.take 16) (top.drop 16))).blocks ≤ 1 := by
        refine blocksFmt_le _ 1 ?_ le_rfl
        have h1 : (top.take 16).length ≤ 16 := List.length_take_le _ _
        have h2 : (top.drop 16).length ≤ 16 := by rw [List.length_drop]; omega
        simp only [nodeInput, thInput, tweak, P, zeros, le32, leBytes, List.length_append, List.length_cons,
          List.length_nil, List.length_map, List.length_range, List.length_replicate]
        omega
      rw [blocksF_hash16_bind]
      rw [eval_hash16_bind] at h
      rw [blocksF_bind]
      rw [evalWithAnswerFn_bind] at h
      have hrec := ih (k + 1) (by omega) top
      generalize hr : evalWithAnswerFn f (expandLayers w idx (k + 1) top) = r2 at h ⊢
      rcases r2 with _ | cs'
      · exact absurd h (by simp)
      · obtain ⟨i1, i2, i3⟩ := hrec cs' (by omega) htop hr
        have h' : some (cs' ++ [c]) = some cs := h
        simp only [Option.some.injEq] at h'
        subst h'
        refine ⟨?_, by simp [i2], fun c' hc' => ?_⟩
        · show blocksF f (searchCounter (k + 1) tau e M 0 cMax) + (blocksF f (verifyLeaf w (k + 1) tau e x) +
            (blocksF f (foldPath (nodeInput (k + 1) tau) e leaf
                ((witPath w (k + 1)).take (height (k + 1) - 1))) +
              ((addrFmt (nodeInput (k + 1) tau (height (k + 1)) 0 (top.take 16) (top.drop 16))).blocks +
                (blocksF f (expandLayers w idx (k + 1) top) + 0)))) ≤ _
          simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil]
          omega
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
          rcases hc' with hc' | rfl
          · exact i3 c' hc'
          · unfold cMax at hb3; omega

/-- The counter sum a witness carries: its five `LE32` counters (at `Ref.ctrOff`), plus one each. -/
def ctrSum (wit : List Byte) : Nat :=
  ((List.range 5).map fun j => leNat (slice wit (ctrOff j) 4) + 1).sum

theorem ctrSum_withCounters (w0 : List Byte) (hw : 2960 ≤ w0.length) (cs : List Nat) (hl : cs.length = 5)
    (hc : ∀ c ∈ cs, c < 2 ^ 32) : ctrSum (withCounters w0 cs) = (cs.map (· + 1)).sum := by
  unfold ctrSum
  have e : ∀ j, j < 5 → leNat (slice (withCounters w0 cs) (ctrOff j) 4) = cs.getD j 0 := by
    intro j hj
    rw [Equiv.slice_withCounters_ctrOff w0 cs hw j hj, Ref.leNat_le32]
    apply Nat.mod_eq_of_lt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hc _ (List.getElem_mem _)
  rw [List.map_congr_left (fun j hj => by rw [e j (List.mem_range.mp hj)])]
  rw [← hl]
  exact congrArg List.sum (Equiv.map_range_getD cs (· + 1) 0)

/-- **The expansion's compressions**: the digest, the PORS stack machine, then per layer the counter
trials and at most `311` more. -/
theorem blocksF_expandList_le (f : Hash) (m sig : List Byte) (hm : m.length = 32) (hsig : sig.length = 6032)
    (wit : List Byte) (h : evalWithAnswerFn f (expandList m sig) = some wit) :
    wit.length = 16384 ∧ wit.take witLead = zeros witLead ∧
      blocksF f (expandList m sig) ≤ 3356 + ctrSum wit := by
  unfold expandList at h ⊢
  unfold digest at h ⊢
  simp only [bind_assoc, pure_bind] at h ⊢
  rw [H, show (HashSpec.query (addrFmt (digestInput (sigRho sig) m)) : OracleComp HashSpec _) =
    qry (addrFmt (digestInput (sigRho sig) m)) from rfl] at h ⊢
  rw [blocksF_bind, blocksF_query]
  rw [evalWithAnswerFn_bind] at h
  have hr : (sigRho sig).length = 16 := by simp [sigRho, slice, hsig]
  have hdb : (addrFmt (digestInput (sigRho sig) m)).blocks ≤ 1 := (dig_ok (sigRho sig) m hr hm).2
  generalize evalWithAnswerFn f (qry (addrFmt (digestInput (sigRho sig) m))) = a at h ⊢
  generalize hx : expandOf sig a.toNat = ox at h ⊢
  rcases ox with _ | w0
  · exact absurd h (by simp)
  · have hl0 := length_of_expandOf sig hsig _ _ hx
    change evalWithAnswerFn f (porsRoot (idxOf a.toNat) (leavesOf a.toNat) w0 >>= fun r =>
      match r with
      | none => pure none
      | some M => expandLayers w0 (idxOf a.toNat) nLayers (P ++ M) >>= fun r =>
        match r with
        | none => pure none
        | some cs => pure (some (withCounters w0 cs))) = _ at h
    change _ ∧ _ ∧ _ + blocksF f (porsRoot (idxOf a.toNat) (leavesOf a.toNat) w0 >>= fun r =>
      match r with
      | none => pure none
      | some M => expandLayers w0 (idxOf a.toNat) nLayers (P ++ M) >>= fun r =>
        match r with
        | none => pure none
        | some cs => pure (some (withCounters w0 cs))) ≤ _
    rw [blocksF_bind]
    rw [evalWithAnswerFn_bind] at h
    have hp := spec_porsRoot (idxOf a.toNat) (leavesOf a.toNat) w0
    have hpb := Spec.blocksF_le f hp
    have hpl := Spec.eval_post f hp
    generalize evalWithAnswerFn f (porsRoot (idxOf a.toNat) (leavesOf a.toNat) w0) = r at h hpl ⊢
    rcases r with _ | M
    · exact absurd h (by simp)
    · change evalWithAnswerFn f (expandLayers w0 (idxOf a.toNat) nLayers (P ++ M) >>= fun r =>
        match r with
        | none => pure none
        | some cs => pure (some (withCounters w0 cs))) = _ at h
      change _ ∧ _ ∧ _ + (_ + blocksF f (expandLayers w0 (idxOf a.toNat) nLayers (P ++ M) >>= fun r =>
        match r with
        | none => pure none
        | some cs => pure (some (withCounters w0 cs)))) ≤ _
      rw [blocksF_bind]
      rw [evalWithAnswerFn_bind] at h
      have hL := blocksF_expandLayers f w0 (idxOf a.toNat) nLayers (P ++ M)
      generalize hLe : evalWithAnswerFn f (expandLayers w0 (idxOf a.toNat) nLayers (P ++ M)) = r2 at h ⊢
      rcases r2 with _ | cs
      · exact absurd h (by simp)
      · have hPM : (P ++ M).length ≤ 32 := by
          have hlen := hpl M rfl
          simp only [List.length_append, P, zeros, List.length_replicate]
          omega
        obtain ⟨b1, b2, b3⟩ := hL cs le_rfl hPM hLe
        have h' : some (withCounters w0 cs) = some wit := h
        simp only [Option.some.injEq] at h'
        subst h'
        refine ⟨by rw [Equiv.length_withCounters _ _ (by rw [hl0]; decide), hl0]; rfl, ?_, ?_⟩
        · obtain ⟨-, -, -, hwl⟩ := Equiv.expandOf_some _ _ _ hx
          rw [take_withCounters w0 cs (by rw [hl0]; decide), hwl]
          exact take_witnessList _ _ _ _
        rw [ctrSum_withCounters w0 (by rw [hl0]; decide) cs b2 (fun c hc => by have := b3 c hc; omega)]
        show _ + (_ + (_ + 0)) ≤ _
        rw [show (311 : Nat) * nLayers = 1555 from rfl] at b1
        omega

/-! ## The pathwise comparison -/

theorem eval_countBoth_fst (f : Hash) {α : Type} (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn f (Sign.countBoth oa)).1 = evalWithAnswerFn f oa := by
  have := congrArg (evalWithAnswerFn f) (Sign.countBoth_blocks oa)
  rw [evalWithAnswerFn_map] at this
  have h2 := congrArg Prod.fst this
  simp only at h2
  rw [h2, eval_countBlocks_fst]

theorem eval_countBoth_blocks (f : Hash) {α : Type} (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn f (Sign.countBoth oa)).2.2 = blocksF f oa := by
  have := congrArg (evalWithAnswerFn f) (Sign.countBoth_blocks oa)
  rw [evalWithAnswerFn_map] at this
  have h2 := congrArg Prod.snd this
  simp only at h2
  rw [h2]; rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- **Under every answer function, the expansion of the signature costs fewer compressions than
the signing**, for the key pair of key generation. -/
theorem expand_le_sign (f : Hash) (sk : Bytes 32) (m : Bytes 32) (σ : Bytes 6032)
    (hσ : evalWithAnswerFn f (signRef sk (evalWithAnswerFn f (keygenRef sk)).2 m) = some σ) :
    blocksF f (expandRef m (evalWithAnswerFn f (keygenRef sk)).1 σ) ≤
      blocksF f (signRef sk (evalWithAnswerFn f (keygenRef sk)).2 m) := by
  -- the keys
  obtain ⟨⟨pkA, cA, skA⟩, hkp⟩ : ∃ kp, evalWithAnswerFn (gF f) (SphincsSecurity.Seeded.keygenFromSeed sk) = kp :=
    ⟨_, rfl⟩
  have hk : evalWithAnswerFn f (keygenRef sk) = ((pkA.root : Bytes 16), Equiv.cacheEnc cA) := by
    rw [Equiv.keygenRef_eq, evalWithAnswerFn_map, eval_relabel, hkp]
  have hskA : skA = ⟨sk, 0, skA.root⟩ := by
    have := hkp
    rw [SphincsSecurity.Completeness.eval_keygenFromSeed] at this
    simp only [Prod.mk.injEq] at this
    rw [← this.2.2]
  rw [hk] at hσ ⊢
  simp only at hσ ⊢
  -- the signer
  have hS := Equiv.signRef_eq skA (by rw [hskA]) (Equiv.cacheEnc cA) m
  rw [Equiv.cacheDec_cacheEnc, show skA.seed = sk by rw [hskA]] at hS
  rw [hS, evalWithAnswerFn_map, eval_relabel] at hσ
  cases hs : evalWithAnswerFn (gF f) (SphincsSecurity.Seeded.sign (m := Equiv.AComp) skA cA m) with
  | none => rw [hs] at hσ; simp at hσ
  | some S =>
    rw [hs] at hσ
    simp only [Option.map_some, Option.some.injEq] at hσ
    subst hσ
    have hsb := bR_sign_ge f skA cA m S hs
    have hsign : blocksF f (signRef sk (Equiv.cacheEnc cA) m) =
        bR f (SphincsSecurity.Seeded.sign (m := Equiv.AComp) skA cA m) := by
      rw [hS, blocksF_map]; rfl
    rw [hsign]
    -- the expansion
    obtain ⟨wl, hwl, hwz, hexp, -⟩ := Final.eval_aExpand_sign' (gF f) sk m hkp hs
    have hE := Equiv.expandRef_eq m (pkA.root : Bytes 16) pkA (Equiv.compress S)
    have hev : evalWithAnswerFn f (expandRef m (pkA.root : Bytes 16) (Equiv.compress S)) =
        some (Ref.ofList 15872
          (Ref.cutW (Ref.withCounters wl ((List.range SphincsSecurity.numLayers).map (Final.ctrOf S))))) := by
      rw [hE, eval_relabel, hexp]
    unfold expandRef at hev ⊢
    rw [blocksF_bind, evalWithAnswerFn_bind] at *
    simp only [blocksF_pure, Nat.add_zero]
    cases hl : evalWithAnswerFn f (expandList (toList m) (toList (Equiv.compress S))) with
    | none => rw [hl] at hev; simp at hev
    | some wit =>
      rw [hl] at hev
      simp only [evalWithAnswerFn_pure, Option.map_some, Option.some.injEq] at hev
      obtain ⟨hwit, hwitz, hb⟩ := blocksF_expandList_le f _ _ (length_toList m) (length_toList _) wit hl
      have hcs : ((List.range SphincsSecurity.numLayers).map (Final.ctrOf S)).length = 5 := by
        simp [SphincsSecurity.numLayers]
      have hwc : (Ref.withCounters wl ((List.range SphincsSecurity.numLayers).map (Final.ctrOf S))).length = 16384 := by
        rw [Equiv.length_withCounters _ _ (by rw [hwl]; decide), hwl]
      -- W1: both views have the zero lead, so they agree when their witnesses (the views without the
      -- lead) do
      have hweq : wit = Ref.withCounters wl ((List.range SphincsSecurity.numLayers).map (Final.ctrOf S)) := by
        rw [← extW_toList_cutW wit hwit hwitz, hev,
          extW_toList_cutW_withCounters wl _ hwc (by rw [hwl]; decide) hwz]
      rw [hweq, ctrSum_withCounters wl (by rw [hwl]; decide) _ hcs (fun c hc => by
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        unfold Final.ctrOf; rw [dif_pos hj]; exact BitVec.isLt _)] at hb
      have : ((List.range SphincsSecurity.numLayers).map (Final.ctrOf S)).map (· + 1) =
          (List.range SphincsSecurity.numLayers).map fun j => Final.ctrOf S j + 1 := by
        rw [List.map_map]; rfl
      rw [this] at hb
      omega

/-! ## The honest pipeline -/

section pipeline
open SigGolfCandidate.Legacy

/-- `ExpandBelowSign` from a phase-level comparison (any submission). -/
theorem expandBelowSign_of (sub : Submission)
    (hle : ∀ (f : Hash) (sk : SecretKey) (m : Message) pk cache σ,
      (evalWithAnswerFn f (sub.run .keygen sk)).value = some (pk, cache) →
      (evalWithAnswerFn f (sub.run .sign (sk, cache, m))).value = some σ →
      (evalWithAnswerFn f (sub.run .expand (m, pk, σ))).hashCompressions ≤
        (evalWithAnswerFn f (sub.run .sign (sk, cache, m))).hashCompressions) :
    ExpandBelowSign sub := by
  intro f sk m
  unfold Submission.honest
  simp only [evalWithAnswerFn_bind]
  generalize hk : evalWithAnswerFn f (sub.run .keygen sk) = k
  rcases hkv : k.value with _ | ⟨pk, cache⟩
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize hs : evalWithAnswerFn f (sub.run .sign (sk, cache, m)) = sgn
  rcases hsv : sgn.value with _ | σ
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  have h := hle f sk m pk cache σ (by rw [hk]; exact hkv) (by rw [hs]; exact hsv)
  rw [hs] at h
  generalize he : evalWithAnswerFn f (sub.run .expand (m, pk, σ)) = ex at h ⊢
  rcases ex.value with _ | w
  · simp only [evalWithAnswerFn_pure]
    simp only [recordCost, if_true, show Phase.expand ≠ Phase.sign by decide,
      show Phase.sign ≠ Phase.expand by decide, if_false]
    exact h
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    simp only [recordCost, if_true, show Phase.expand ≠ Phase.sign by decide,
      show Phase.sign ≠ Phase.expand by decide, show Phase.expand ≠ Phase.verify by decide,
      show Phase.sign ≠ Phase.verify by decide, if_false]
    exact h

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Legacy.Input

set_option maxRecDepth 100000 in
/-- The phase-level comparison for the submission, from its keygen, sign and expand refinements
(in the form of `Sign.Sim.run_eq`) and `expand_le_sign`. -/
theorem expand_run_le
    (hK : ∀ sk, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some p.1, p.2.1, p.2.2)) <$> Sign.countBoth (keygenRef sk))
    (hS : ∀ sk cache m, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      submission.run .sign (sk, cache, m) = Sign.countBoth (signRef sk cache m))
    (hE : ∀ m pk σ, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      submission.run .expand (m, pk, σ) = (fun p => (p.1, p.2.1, p.2.2)) <$> Sign.countBoth (expandRef m pk σ))
    (f : Hash) (sk : SecretKey) (m : Message) (pk : PublicKey) (cache : Cache) (σ : Bytes 6032)
    (hk : (evalWithAnswerFn f (submission.run .keygen sk)).value = some (pk, cache))
    (hs : (evalWithAnswerFn f (submission.run .sign (sk, cache, m))).value = some σ) :
    (evalWithAnswerFn f (submission.run .expand (m, pk, σ))).hashCompressions ≤
      (evalWithAnswerFn f (submission.run .sign (sk, cache, m))).hashCompressions := by
  have hKv : (fun r => r.value) <$> submission.run .keygen sk = some <$> keygenRef sk := by
    have h := congrArg (fun x => Prod.fst <$> x) (hK sk)
    simp only [Functor.map_map] at h
    refine h.trans ?_
    have e : (fun a : (SigGolfCandidate.Legacy.PublicKey × SigGolfCandidate.Cache) × Nat × Nat => some a.1) <$>
        Sign.countBoth (keygenRef sk) = some <$> (Prod.fst <$> Sign.countBoth (keygenRef sk)) :=
      (Functor.map_map _ _ _).symm
    rw [e, Sign.fst_countBoth]
  have hkp : evalWithAnswerFn f (keygenRef sk) = (pk, cache) := by
    have := congrArg (evalWithAnswerFn f) hKv
    rw [evalWithAnswerFn_map, evalWithAnswerFn_map, hk] at this
    exact (Option.some.inj this).symm
  have hSv : (fun r => r.value) <$> submission.run .sign (sk, cache, m) = signRef sk cache m := by
    have h := congrArg (fun x => Prod.fst <$> x) (hS sk cache m)
    simp only [Functor.map_map] at h
    exact h.trans (Sign.fst_countBoth _)
  have hsσ : evalWithAnswerFn f (signRef sk cache m) = some σ := by
    have := congrArg (evalWithAnswerFn f) hSv
    rw [evalWithAnswerFn_map, hs] at this
    exact this.symm
  have hSc : (fun r => r.hashCompressions) <$> submission.run .sign (sk, cache, m) =
      Prod.snd <$> countBlocks (signRef sk cache m) := by
    have h := congrArg (fun x => (fun p => p.2.2) <$> x) (hS sk cache m)
    simp only [Functor.map_map] at h
    refine h.trans ?_
    rw [← Sign.countBoth_blocks, Functor.map_map]
  have hEc : (fun r => r.hashCompressions) <$> submission.run .expand (m, pk, σ) =
      Prod.snd <$> countBlocks (expandRef m pk σ) := by
    have h := congrArg (fun x => (fun p => p.2.2) <$> x) (hE m pk σ)
    simp only [Functor.map_map] at h
    refine h.trans ?_
    rw [← Sign.countBoth_blocks, Functor.map_map]
  have hsb : (evalWithAnswerFn f (submission.run .sign (sk, cache, m))).hashCompressions =
      blocksF f (signRef sk cache m) := by
    have := congrArg (evalWithAnswerFn f) hSc
    rw [evalWithAnswerFn_map, evalWithAnswerFn_map] at this
    exact this
  have heb : (evalWithAnswerFn f (submission.run .expand (m, pk, σ))).hashCompressions =
      blocksF f (expandRef m pk σ) := by
    have := congrArg (evalWithAnswerFn f) hEc
    rw [evalWithAnswerFn_map, evalWithAnswerFn_map] at this
    exact this
  rw [heb, hsb]
  have hle := expand_le_sign f sk m σ (by rw [hkp]; exact hsσ)
  rw [hkp] at hle
  exact hle

set_option maxRecDepth 100000 in
/-- **`ExpandBelowSign` for the submission**, from its keygen, sign and expand refinements. -/
theorem expandBelowSign_submission
    (hK : ∀ sk, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some p.1, p.2.1, p.2.2)) <$> Sign.countBoth (keygenRef sk))
    (hS : ∀ sk cache m, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      submission.run .sign (sk, cache, m) = Sign.countBoth (signRef sk cache m))
    (hE : ∀ m pk σ, (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      submission.run .expand (m, pk, σ) = (fun p => (p.1, p.2.1, p.2.2)) <$> Sign.countBoth (expandRef m pk σ)) :
    ExpandBelowSign submission :=
  expandBelowSign_of submission fun f sk m pk cache σ hk hs =>
    expand_run_le hK hS hE f sk m pk cache σ hk hs

end pipeline

end SigGolfCandidate.Budget
