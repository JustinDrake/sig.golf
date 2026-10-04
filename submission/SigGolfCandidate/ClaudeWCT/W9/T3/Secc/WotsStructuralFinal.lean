import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsStructuralHonest
import SigGolfCandidate.T3.Secc.WotsStructuralVariant
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.ExtractSrc
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layer
import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReferenceInputs
import SigGolfCandidate.T3.Secc.WotsStructuralFinal

section


namespace ClaudeWCT.W9.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))
theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    Extract.posOf (Extract.honestInput T p) = some p :=
  Extract.posOf_eq hp (Extract.hdrBlock_honestInput T p)
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
theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))
section Game
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem keygenCharge_variant (hv : Variant labels T T') : keygenCharge T = keygenCharge T' := by
  unfold keygenCharge
  rw [(hv.congr (sat_keygen T)).2]
theorem eval_keygen_variant (hv : Variant labels T T') :
    evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen :=
  (hv.congr (sat_keygen T)).1
theorem signCharge_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    signCharge T published request = signCharge T' published request := by
  unfold signCharge
  rw [(hv.congr (sat_authenticatedSign T published request)).2]
theorem eval_sign_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      evalWithAnswerFn T' (FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).1
theorem offlineSign_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    offlineSign T published request = offlineSign T' published request := by
  unfold offlineSign
  rw [signCharge_variant hv, eval_sign_variant hv]
theorem offlineImpl_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) :
    offlineImpl T published = offlineImpl T' published := by
  unfold offlineImpl
  have h : offlineSign T published = offlineSign T' published := funext (offlineSign_variant hv published)
  rw [h]
theorem offlineGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) :
    offlineGame T adversary = offlineGame T' adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_variant hv, eval_keygen_variant hv, offlineImpl_variant hv]
theorem referenceGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) (q : Nat) :
    referenceGame T adversary q = referenceGame T' adversary q := by
  unfold referenceGame
  rw [offlineGame_variant hv]
theorem publicKey_variant (hv : Variant labels T T') :
    (evalWithAnswerFn T keygen).1 = (evalWithAnswerFn T' keygen).1 := by
  rw [eval_keygen_variant hv]
end Game
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
theorem honestForest_variant (hv : Variant labels T T') (index : Nat) (hindex : index < 2 ^ 31) :
    Extract.honestForest T index = Extract.honestForest T' index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9,
    ← ClaudeWCT.WCT9.signForest_root T index 0, ← ClaudeWCT.WCT9.signForest_root T' index 0,
    (hv.congr (sat_signForest T index hindex 0)).1]
theorem leafMsg_variant (hv : Variant labels T T') (L : LeafAddr) : leafMsg T L = leafMsg T' L := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [builtTree_variant hv]
  · rw [honestForest_variant hv _ (Nat.mod_lt _ (by decide))]
theorem referenceSearch_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ 31)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceSearch T L = referenceSearch T' L := by
  unfold referenceSearch
  rw [leafMsg_variant hv L]
  exact (hv.congr (sat_layerCounterSearch T _ _ _ _ _ _)).1
theorem referenceDigits_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ 31)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceDigits T L = referenceDigits T' L := by
  unfold referenceDigits
  rw [referenceSearch_variant hv L htree hleaf]
theorem depth_variant (hv : Variant labels T T') (a : ChainAddr) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 2 ^ height a.key.lay) : depth T a = depth T' a := by
  unfold depth
  rw [referenceDigits_variant hv a.key htree hleaf]
end Depth
end ClaudeWCT.W9.T3.Security.Wots.Structural
end

section




namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ position.Bounded ∧ WotsExtract.PosSource position ∧
    StructuralClass answers input position
def OtherQuery (answers : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False
noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (OtherQuery sample.answers (.inl (.inr e.1)))).length
def TraceInUniverse (adversary : AdversaryP) (q : Nat) : Prop :=
  ∀ sample ∈ (referenceExperiment adversary q).support, ∀ entry ∈ sample.trace,
    entry.1 ∈ referenceInputs adversary
def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ WotsExtract.PosSource position ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
namespace Structural
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3.Security.CanonGraph (Node Labels Secrets OtherHalves cell programmed canonInputs privateEquiv)
theorem exists_node_of_posSource {p : Extract.Pos} (h : WotsExtract.PosSource p) : ∃ node : Node, node.toPos = p := by
  apply CanonGraph.exists_toPos
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 :=
        Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      have hw : 2 ^ width lay i ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
      have hc := Extract.chainCount_le lay
      exact ⟨h1, by omega, by omega, by omega⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 :=
        Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      exact ⟨h1, by omega⟩
  | node lay tree level nd => exact h
  | forest index => exact h
  | wctChain index coord child t step => exact h
  | wctLeaf index coord child => exact h
  | wctNode index coord level nd => exact h
theorem structuralClass_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') {x : HashInput}
    {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    StructuralClass T x p ↔ StructuralClass T' x p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨htree, hleaf, -, -⟩ := hsrc
      have key : ∀ (a : ChainAddr) (step' : Nat),
          Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step') → depth T a = depth T' a := by
        intro a step' h
        rw [hpos] at h
        simp only [Option.some.injEq, Extract.Pos.chain.injEq] at h
        obtain ⟨hl, ht, hlf, -, -⟩ := h
        exact depth_variant hv a (by rw [← ht]; exact htree) (by rw [← hlf, ← hl]; exact hleaf)
      change OtherChainRow T x ↔ OtherChainRow T' x
      constructor
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [← key a step' h]; exact hd)⟩
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [key a step' h]; exact hd)⟩
  | leaf => exact Iff.rfl
  | node => exact Iff.rfl
  | forest => exact Iff.rfl
  | wctChain => exact Iff.rfl
  | wctLeaf => exact Iff.rfl
  | wctNode => exact Iff.rfl
theorem otherInput_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') (x : HashInput) :
    OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mpr hc⟩
section Fixed
variable (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels
theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels :=
  Finset.mem_filter
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : Node) : x ≠ cell s node labels := by
  obtain ⟨-, node₀, hpos, hne⟩ := (mem_strRows V s labels x).mp hx
  intro heq
  have := CanonGraph.cell_eq_of_posOf s labels hpos heq
  subst this
  exact hne heq
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩
theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput
noncomputable def strTable (rest : Rest V s labels) (ρ : strRows V s labels → HashOutput) : Answers :=
  eagerAnswers V (privateEquiv.symm (s, o))
    (programmed V hU s labels
      (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest))
variable (rest : Rest V s labels)
theorem strTable_eq_canon (ρ : strRows V s labels → HashOutput) :
    strTable V hU s o labels rest ρ = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) V
      (programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)) := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem strTable_agrees (ρ : strRows V s labels → HashOutput) :
    CanonGraph.Agrees (strTable V hU s o labels rest ρ) labels := by
  rw [strTable_eq_canon]
  exact CanonGraph.eager_programmed_agrees V hU s o labels _
theorem secretsOf_strTable (ρ : strRows V s labels → HashOutput) :
    CanonGraph.secretsOf (strTable V hU s o labels rest ρ) = s := by
  rw [strTable_eq_canon, CanonGraph.secretsOf_eager, CanonGraph.privateSecrets_symm]
theorem strTable_public_mem (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ V) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) =
      programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)
        ⟨x, hx⟩ :=
  SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x hx rfl
theorem strTable_str (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = ρ ⟨x, hx⟩ := by
  have hV := ((mem_strRows V s labels x).mp hx).1
  rw [strTable_public_mem V hU s o labels rest ρ x hV,
    CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ (strRows_not_cell V s labels hx)]
  exact SphincsSecurity.Concrete.UniformTableSplit.join_embed (strEmbed V s labels) (strEmbed_injective V s labels)
    ρ rest ⟨x, hx⟩
theorem strTable_out (ρ ρ' : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∉ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = strTable V hU s o labels rest ρ' (.inl (.inr x)) := by
  by_cases hV : x ∈ V
  · rw [strTable_public_mem V hU s o labels rest ρ x hV, strTable_public_mem V hU s o labels rest ρ' x hV]
    by_cases hcell : ∃ node, x = cell s node labels
    · obtain ⟨node, rfl⟩ := hcell
      have he : (⟨cell s node labels, hV⟩ : V) = CanonGraph.cellIn V hU s node labels := rfl
      rw [he, CanonGraph.programmed_at, CanonGraph.programmed_at]
    · have hn : ∀ node, x ≠ cell s node labels := fun node h => hcell ⟨node, h⟩
      rw [CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn,
        CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn]
      have hout : (⟨x, hV⟩ : V) ∉ Set.range (strEmbed V s labels) := by
        rintro ⟨y, hy⟩
        apply hx
        have : y.val = x := congrArg Subtype.val hy
        rw [← this]
        exact y.property
      exact (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ rest ⟨⟨x, hV⟩, hout⟩).trans
        (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ' rest ⟨⟨x, hV⟩, hout⟩).symm
  · change SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x
    simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hV]
theorem strTable_variant (ρ ρ' : strRows V s labels → HashOutput) :
    Variant labels (strTable V hU s o labels rest ρ) (strTable V hU s o labels rest ρ') where
  agrees := strTable_agrees V hU s o labels rest ρ
  coin := fun _ => rfl
  priv := fun _ => rfl
  pub := fun x hx => by
    apply strTable_out V hU s o labels rest ρ ρ' x
    intro hmem
    obtain ⟨-, node, hpos, hne⟩ := (mem_strRows V s labels x).mp hmem
    have := hx node hpos
    rw [secretsOf_strTable] at this
    exact hne this
def strHit (T0 : Answers) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ OtherInput T0 x ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ low a = low (labels node)
theorem strHit_kernel (T0 : Answers) (x : HashInput) (hx : x ∈ strRows V s labels) :
    Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (if OtherInput T0 x then 1 else 0 : ℝ≥0∞) := by
  by_cases hO : OtherInput T0 x
  · rw [if_pos hO, mul_one]
    obtain ⟨-, node₀, hpos₀, -⟩ := (mem_strRows V s labels x).mp hx
    calc Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)]
        ≤ Pr[fun a : HashOutput => SphincsSecurity.truncateHash a = low (labels node₀) |
            PMF.uniformOfFintype HashOutput] := by
          apply probEvent_mono
          rintro a - ⟨-, -, node, hpos, hlow⟩
          have hn : node = node₀ :=
            CanonGraph.toPos_injective (Option.some.inj (hpos.symm.trans hpos₀))
          subst hn
          exact hlow
      _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
          have h := SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq (low (labels node₀))
          rw [card_digest] at h
          exact h
  · have hz : Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => hO h.2.1
    rw [hz]
    exact bot_le
theorem hit_bridge (ρ : strRows V s labels → HashOutput) (qs : List RefWorld.Domain)
    (h : StructuralHitIn V (strTable V hU s o labels rest ρ) (traceOf (strTable V hU s o labels rest ρ) qs)) :
    ∃ e ∈ traceOf (strTable V hU s o labels rest ρ) qs,
      strHit V s labels (strTable V hU s o labels rest (fun _ => 0)) e.1 e.2 := by
  obtain ⟨p, x, a, hmem, hxV, hpos, hb, hsrc, hc, hne, hlow⟩ := h
  refine ⟨(x, a), hmem, ?_, ?_, ?_⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    rw [CanonGraph.honestInput_eq (strTable_agrees V hU s o labels rest ρ), secretsOf_strTable] at hne
    exact (mem_strRows V s labels x).mpr ⟨hxV, node, hpos, hne⟩
  · exact ⟨p, hpos, hb, hsrc, (structuralClass_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0))
      hpos hsrc).mp hc⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    refine ⟨node, hpos, ?_⟩
    have ha : a = strTable V hU s o labels rest ρ (.inl (.inr x)) := mem_traceOf hmem
    rw [CanonGraph.honest_answer (strTable_agrees V hU s o labels rest ρ)] at hlow
    change low a = low (labels node)
    rw [ha]
    exact hlow
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)
end Fixed
noncomputable def sampleComp (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> offlineRun T adversary q
section Bound
variable (adversary : AdversaryP) (q : Nat) (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]
theorem fixed_bound :
    Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (otherCount sample : ℝ≥0∞) := by
  set T := strTable V hU s o labels rest with hT
  set G0 := referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (T fun _ => 0) with hHit
  set Charged := OtherInput (T fun _ => 0) with hCharged
  have hlazy := lazy_seen_le (strRows V s labels) T (fun ρ x hx => strTable_str V hU s o labels rest ρ x hx)
    (fun ρ x hx => strTable_out V hU s o labels rest ρ (fun _ => 0) x hx) Hit Charged (2 ^ 128 : ℝ≥0∞)⁻¹
    (fun x a h => h.1) (fun x hx => strHit_kernel V s labels (T fun _ => 0) x hx) G0
  have hevent : Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] ≤
      Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, probEvent_map]
    have hpair := recorded_pair adversary q V hU s o labels rest ρ
    have hseen : Pr[fun r => Seen Hit r.2 |
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] =
        Pr[fun z => ∃ e ∈ z.2, Hit e.1 e.2 | (fun run => (run.1, traceOf (T ρ) run.2)) <$>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryCap.recorded G0)]] := by
      rw [hpair, probEvent_map]
      rfl
    rw [hseen, probEvent_map]
    apply probEvent_mono
    intro run _ h
    exact hit_bridge V hU s o labels rest ρ run.2 h
  have hcount : (∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] * (otherCount sample : ℝ≥0∞)) =
      ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] *
            (chargedCount Charged r.2 : ℝ≥0∞) := by
    rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
    refine tsum_congr fun ρ => congrArg _ ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    have hA : ∀ run : Option (Bool × Nat) × List RefWorld.Domain,
        (otherCount (⟨T ρ, (evalWithAnswerFn (T ρ) keygen).1, traceOf (T ρ) run.2⟩ : RefSample) : ℝ≥0∞) =
          (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞))
            ((fun run => (run.1, traceOf (T ρ) run.2)) run) := by
      intro run
      rw [count_bridge V hU s o labels rest ρ]
    refine (tsum_congr fun run => congrArg _ (hA run)).trans ?_
    rw [← tsum_probOutput_map_mul _ (fun run : Option (Bool × Nat) × List RefWorld.Domain =>
        (run.1, traceOf (T ρ) run.2))
      (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞)),
      recorded_pair adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    rfl
  rw [hcount]
  exact hevent.trans hlazy
end Bound
def BoundOn (V : Finset HashInput) (p : SPMF RefSample) : Prop :=
  Pr[fun sample => StructuralHitIn V sample.answers sample.trace | p] ≤
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | p] * (otherCount sample : ℝ≥0∞)
theorem boundOn_bind {X : Type} (V : Finset HashInput) (μ : SPMF X) (K : X → SPMF RefSample)
    (h : ∀ x, BoundOn V (K x)) : BoundOn V (μ >>= K) := by
  unfold BoundOn
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  calc (∑' x, Pr[= x | μ] * Pr[fun sample => StructuralHitIn V sample.answers sample.trace | K x])
      ≤ ∑' x, Pr[= x | μ] * ((2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | K x] * (otherCount sample : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by simp only [mul_left_comm _ (2 ^ 128 : ℝ≥0∞)⁻¹, ENNReal.tsum_mul_left]
section Assembly
noncomputable local instance instFintypeCoordinate_wotsStructural : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsStructural : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
theorem referenceInputs_canon (adversary : AdversaryP) : canonInputs ⊆ referenceInputs adversary := by
  unfold referenceInputs
  exact CanonGraph.canonInputs_subset_publicUniverse.trans Finset.subset_union_left
theorem tables_bind_spmf {R : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp R) :
    ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun pub => 𝒮[next pt pub]) =
    ((liftM (PMF.uniformOfFintype Secrets) : SPMF _) >>= fun s =>
      (liftM (PMF.uniformOfFintype OtherHalves) : SPMF _) >>= fun o =>
      (liftM (PMF.uniformOfFintype Labels) : SPMF _) >>= fun labels =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun r =>
        𝒮[next (privateEquiv.symm (s, o)) (programmed U hU s labels r)]) := by
  have h := CanonGraph.tables_bind U hU next
  simp only [evalSPMF_bind, evalSPMF_uniformSample] at h
  exact h
theorem referenceComp_spmf (adversary : AdversaryP) (q : Nat) :
    𝒮[referenceComp adversary q] =
      ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
        (liftM (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)) : SPMF _) >>= fun pub =>
          𝒮[sampleComp adversary q (eagerAnswers (referenceInputs adversary) pt pub)]) := by
  unfold referenceComp
  simp only [evalSPMF_bind, evalSPMF_uniformSample]
  rfl
theorem referenceComp_bound (adversary : AdversaryP) (q : Nat) :
    BoundOn (referenceInputs adversary) 𝒮[referenceComp adversary q] := by
  rw [referenceComp_spmf, tables_bind_spmf _ (referenceInputs_canon adversary)]
  refine boundOn_bind _ _ _ fun s => boundOn_bind _ _ _ fun o => boundOn_bind _ _ _ fun labels => ?_
  rw [uniform_split_bind (strEmbed (referenceInputs adversary) s labels)
    (strEmbed_injective (referenceInputs adversary) s labels)]
  refine boundOn_bind _ _ _ fun rest => ?_
  exact fixed_bound adversary q (referenceInputs adversary) (referenceInputs_canon adversary) s o labels rest
end Assembly
end Structural
theorem referenceExperiment_eq (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl
theorem reference_structural_in_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  have h := Structural.referenceComp_bound adversary q
  unfold Structural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h
theorem reference_structural_le (adversary : AdversaryP) (q : Nat) (hV : TraceInUniverse adversary q) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  refine le_trans ?_ (reference_structural_in_le adversary q)
  rw [referenceExperiment_eq, probEvent_liftM_pmf', probEvent_liftM_pmf']
  apply probEvent_mono
  intro sample hs h
  have hsupp : sample ∈ (referenceExperiment adversary q).support := by
    rw [referenceExperiment_eq]
    exact mem_support_liftM_pmf _ sample hs
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, hc, hhit⟩ := h
  exact ⟨position, input, answer, hmem, hV sample hsupp (input, answer) hmem, hpos, hb, hsrc, hc, hhit⟩
end ClaudeWCT.W9.T3.Security.Wots
end

section



namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
theorem traceInUniverse (adversary : AdversaryP) (q : Nat) : TraceInUniverse adversary q :=
  fun sample hs entry he => reference_trace_mem adversary q sample hs entry he
theorem reference_structural_src_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) :=
  reference_structural_le adversary q (traceInUniverse adversary q)
end ClaudeWCT.W9.T3.Security.Wots
end
