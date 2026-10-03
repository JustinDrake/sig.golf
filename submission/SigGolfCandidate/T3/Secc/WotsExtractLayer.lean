import SigGolfCandidate.T3.Secc.WotsExtractWord

/-!
# Stream W, part 3: one layer of the verifier (BP-A §1.4)

* `WotsPrimitiveSrc` is `Wots.WotsPrimitive` with every leaf / chain address and every structural position source-sized
  (`toPrimitive`; `SourceLeaf`, `SourceChain`, `PosSource` in `WotsExtractChain`). The verifier only reaches route
  positions of an index `< 2^31`.
* Trace monotonicity of every event (`structuralHit_mono`, …, `WotsPrimitiveSrc.mono`).
* `layerP_wots` (layer-level refinement of PEX's `layerP_extract`): a layer reaching the honest root of its tree gives
  a (source-sized) `StructuralHit` among its queries (Merkle node, leaf pk, padded chain row, or canonical chain row at or
  above the frontier), or honest Merkle bytes and, per chain `i`: frontier at or below the decoded digit ⇒ honest value at the
  digit (zero pads if it hashes a step); frontier above the digit ⇒ `ContactAt` and, if the chain starts at least
  two below the frontier, `TwoEdgeAt`.
* `layer_wots`: with the layer's frame (message, counter, decoded digits) and the word analysis (`word_cases` against
  the reference word): a source-sized WOTS primitive event, or the layer is `Good` on its honest message.
-/

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-! ## The source-sized primitive event -/

/-- `WotsPrimitive` with every address and position source-sized (`SourceLeaf`, `SourceChain`, `PosSource` of
`WotsExtractChain`): what the verifier produces; the finite sums / canonical graphs of streams C/E/S need it. -/
def WotsPrimitiveSrc (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, SourceLeaf L ∧ EncodingMatchAt answers trace L) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)

theorem WotsPrimitiveSrc.toPrimitive {answers : Answers} {trace : List Entry} (h : WotsPrimitiveSrc answers trace) :
    WotsPrimitive answers trace := by
  rcases h with ⟨L, -, h⟩ | h | ⟨a, -, h⟩ | ⟨a, b, -, -, hab, ha, hb⟩ | ⟨a, -, hm, hc⟩
  · exact Or.inl ⟨L, h⟩
  · exact Or.inr (Or.inl h.toStructuralHit)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, ha, hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hm, hc⟩)))

/-! ## Trace monotonicity -/

section mono
variable {answers : Answers} {trace trace' : List Entry}

theorem seenRow_mono {a : ChainAddr} {step : Nat} {value out : Digest} (h : SeenRow trace a step value out)
    (hsub : ∀ e ∈ trace, e ∈ trace') : SeenRow trace' a step value out := by
  obtain ⟨answer, hm, hl⟩ := h
  exact ⟨answer, hsub _ hm, hl⟩

theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, seenRow_mono hs hsub⟩

theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, seenRow_mono h1 hsub, seenRow_mono h2 hsub⟩

theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, answer, hm, hne, hd⟩ := h
  exact ⟨message, counter, answer, hsub _ hm, hne, hd⟩

theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, answer, digits, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, answer, digits, hsub _ hm, hne, hd, hl, hu⟩

theorem structuralHit_mono (h : StructuralHit answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    StructuralHit answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hc, hh⟩

theorem WotsPrimitiveSrc.mono (h : WotsPrimitiveSrc answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveSrc answers trace' := by
  rcases h with ⟨L, hL, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨L, hL, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))

end mono

/-! ## One layer (E8: the walk hands over `layerNextP`) -/

/-- A node hit of PEX's Merkle extraction is a source-sized structural hit. -/
theorem nodeHit_src (answers : Answers) (qs : List Spec.Domain) (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31)
    (h : Extract.NodeHitIn answers qs lay (route index lay).2 (route index lay).1) :
    StructuralHitSrc answers (entriesOf answers qs) := by
  obtain ⟨step, input, hstep, hq, hhit, hsame⟩ := h
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have htree31 : (route index lay).2 < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hnb := Extract.node_bound lay (route index lay).1 step hleafB hstep
  exact structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1))) input
    ⟨htreeB, hstep, hnb⟩ ⟨htree31, hstep, hnb⟩ hq hhit hsame trivial

/-- The leaf pk and chains of a layer from the honest leaf pk (`layerLeafP`'s queries among `qs`): a source-sized
structural hit, or per chain (frontier `≤` digit ⇒ honest value, zero pads if it hashes a step) ∧ (digit `<`
frontier ⇒ `ContactAt` ∧ (digit `+ 2 ≤` frontier ⇒ `TwoEdgeAt`)). -/
theorem leafChains_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (qs : List Spec.Domain)
    (hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ qs)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
      ∀ i, i < chainCount lay →
        (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i → wchainPads w lay i = (0, 0))) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
          ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
              TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩)) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have htree31 : (route index lay).2 < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hleaf32 : (route index lay).1 < 2 ^ 32 :=
    lt_of_lt_of_le hleafB (le_trans (Nat.pow_le_pow_right (by decide) (Extract.height_le lay)) (by norm_num))
  have hqC : ∀ q ∈ queried answers (Extract.layerChains w index lay digits), q ∈ qs := by
    intro q hq
    apply hqL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  -- leaf pk
  rw [Correctness.builtTree_leaf answers lay _ _ hleafB, Extract.layerLeafP_eq, evalWithAnswerFn_bind] at hv0
  have hends : evalWithAnswerFn answers (Extract.layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wvalue w lay i))) := by
    rw [Extract.layerChains, Correctness.eval_mapM]
    exact Extract.map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wvalue w lay i)))
  rcases Extract.leafHash_extract answers lay (route index lay).2 (route index lay).1
      (evalWithAnswerFn answers (Extract.layerChains w index lay digits))
      ((List.range (chainCount lay)).map (leafEnd answers lay (route index lay).2 (route index lay).1))
      (by rw [hends]; simp) (by simpa using Extract.chainCount_pos lay) hv0 with hE | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.leaf lay (route index lay).2 (route index lay).1) _ ⟨htreeB, hleaf32⟩
      ⟨htree31, hleafB⟩ ?_ hhit hsame trivial
    apply hqL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_right _ hq
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  -- chains
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
  have hc := Extract.chainCount_le lay
  have hreach : evalWithAnswerFn answers
      (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
        (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i)) =
      honestChainValue answers lay (route index lay).2 (route index lay).1 i
        (leafSeed answers lay (route index lay).2 (route index lay).1 i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  have hdepth : depth answers ⟨routeLeaf index lay, i⟩ ≤ maxDigit lay i := depth_le answers ⟨routeLeaf index lay, i⟩ hi
  have hsrcC : SourceChain ⟨routeLeaf index lay, i⟩ := ⟨routeLeaf_source index lay hidx, hi⟩
  have hcount : digits.getD i 0 + (maxDigit lay i - digits.getD i 0) < 2 ^ width lay i := by
    have hm := Nonbinary.maxDigit_lt_pow_width lay i
    omega
  rcases chain_cases answers ⟨routeLeaf index lay, i⟩ (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
      (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i) qs
      (fun q hq => hqC q (Extract.layerChains_queried answers w index lay digits (route index lay).1
        (route index lay).2 rfl rfl i hi q hq))
      hsrcC hcount (by omega) hreach with
    hS' | ⟨hhon, hlow⟩
  · exact (hS hS').elim
  refine ⟨fun hle => ?_, hlow⟩
  obtain ⟨hval, hpads⟩ := hhon hle
  refine ⟨hval, fun hlt => ?_⟩
  obtain ⟨h0, h1⟩ := hpads (by omega)
  exact Prod.ext h0 h1

/-- **Layer-level refinement** of PEX's `layerNextP_extract`. A layer handover reaching the walk target (the honest
root at the top, the honest root children below it; its queries among `qs`): a `StructuralHit` among `qs`, or
honest Merkle bytes (`Extract.MerkleShaped`) and, per chain, (frontier `≤` digit ⇒ honest value, zero pads if it
hashes a step) ∧ (digit `<` frontier ⇒ `ContactAt` ∧ (digit `+ 2 ≤` frontier ⇒ `TwoEdgeAt`)). -/
theorem layerNextP_wots (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits (Fin.ofNat 4 n) digits) (qs : List Spec.Domain)
    (hsub : ∀ q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) =
      Extract.walkTarget answers index n) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
    (Extract.MerkleShaped answers w index (Fin.ofNat 4 n) ∧
      ∀ i, i < chainCount (Fin.ofNat 4 n) →
        (depth answers ⟨routeLeaf index (Fin.ofNat 4 n), i⟩ ≤ digits.getD i 0 →
          wvalue w (Fin.ofNat 4 n) i =
              leafValue answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
                digits i ∧
            (digits.getD i 0 < maxDigit (Fin.ofNat 4 n) i → wchainPads w (Fin.ofNat 4 n) i = (0, 0))) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index (Fin.ofNat 4 n), i⟩ →
          ContactAt answers (entriesOf answers qs) ⟨routeLeaf index (Fin.ofNat 4 n), i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index (Fin.ofNat 4 n), i⟩ →
              TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index (Fin.ofNat 4 n), i⟩))) := by
  rcases Extract.layerNextP_merkle answers w index n hn digits reaches with hnode | ⟨hm, hv0, hqL⟩
  · exact Or.inl (nodeHit_src answers qs index (Fin.ofNat 4 n) hidx (hnode.mono hsub))
  rcases leafChains_wots answers w index (Fin.ofNat 4 n) digits hidx hvalid qs (fun q hq => hsub q (hqL q hq)) hv0
    with hS | hc
  · exact Or.inl hS
  · exact Or.inr ⟨hm, hc⟩

/-- **One layer of the walk** (BP-A §1.4, every layer reaching its honest root): with the layer's frame (message
`msg`, the witness counter, decoded digits) and its encoding query among `qs`, a source-sized WOTS primitive event
on `qs`, or the layer signs its honest message and is `Good`. -/
theorem layer_wots (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (msg : Digest × BitVec 96 × Digest)
    (digits : List Nat)
    (hidx : index < 2 ^ 31) (hframe : Extract.Frame answers w index (Fin.ofNat 4 n) msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index (Fin.ofNat 4 n) msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) =
      Extract.walkTarget answers index n) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index (Fin.ofNat 4 n) ∧ Extract.Good answers w index (Fin.ofNat 4 n)) := by
  classical
  have hW := layerNextP_wots answers w index n hn digits hidx (Cost.validDigits_decode hframe.2) qs hsub reaches
  set lay : Layer := Fin.ofNat 4 n with hlay
  have hdec : decode (routeLeaf index lay).lay
      (low (answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay)))))) = some digits := hframe.2
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  have hencE : (encodingRow (routeLeaf index lay) msg (wctr w lay),
      answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay))))) ∈ entriesOf answers qs :=
    mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  rcases hW with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl hS))
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  · -- the reference word: honest-shaped layer
    have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · exact Or.inr ⟨hm, digits, hm ▸ hframe, hshape⟩
    · refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wctr w lay, _, hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ hdec (Or.inl (by rw [leafMsg_route]; exact hm))
      · rw [← heq]; exact hdec
  · -- a unit neighbor at `i`: marker and contact at `i`
    have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wctr w lay, _, digits, hencE, referenceInput_ne answers _ msg _ hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · -- a chain lowered by at least two: two-edge at `i`
    refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact ((hchains i.val i.isLt).2 hlt).2 h2
  · -- two lowered chains: two contacts
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)

end SigGolfCandidate.T3.Security.WotsExtract
