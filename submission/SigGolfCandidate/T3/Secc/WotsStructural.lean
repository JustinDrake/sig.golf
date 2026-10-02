import SigGolfCandidate.T3.Secc.WotsStructuralLazy
import SigGolfCandidate.T3.Secc.WotsExtractChain

/-!
# Stream S: `reference_structural_le` (BP-A §3/§4 S)

In R3, the probability that the trace holds a structural hit (W's `StructuralHitSrc`: an O-class query at a parsed
bounded source-sized position hitting the low half of the honest answer there) is at most `2^-128` times the expected
number of O-class queries.

Route (BP-A §1.5 "Structural"):
1. G's `tables_bind`: R3's eager tables = (secrets, other private halves, labels, residual), the public table being the
   residual with every canonical cell programmed to its label.
2. For fixed `(secrets, other, labels)`, split the residual into the *structural rows* `strRows` (inputs of the
   universe parsed at a source node that are not its cell) and the rest (`UniformTableSplit`); fix the rest.
3. Stream S (1)/(2): R3's source program (honest key generation, offline signer, honest charges) and every frontier
   depth do not read the structural rows (`referenceGame_variant`, `depth_variant`).
4. Stream S (3): the structural rows are lazily sampled; a fresh O-class one hits its label with probability `2^-128`;
   the potential argument gives the bound for every fixed rest (`lazy_seen_le`); average.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The O class, its count, and the endpoint's events (`plan/S-INTERFACE.md`) -/

/-- O-class input (BP-A §1.2): at a parsed (PEX `posOf`), bounded, source-sized (W's `PosSource`) position, and not a
canonical prefix row (`StructuralClass`: at chain positions a padded row or a canonical row at/above the frontier; at
leaf / Merkle / FTS leaf / FTS node / forest positions every input). -/
def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ position.Bounded ∧ WotsExtract.PosSource position ∧
    StructuralClass answers input position

/-- O-class on `T3.Spec.Domain` (F2's `refCount` class form). -/
def OtherQuery (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False

/-- Number of O-class entries of an R3 sample; definitionally F2's `refCount OtherQuery sample`. -/
noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (OtherQuery sample.answers (.inl (.inr e.1)))).length

/-- R3's recorded trace stays in R3's eager public universe (F2 fact, requested in `plan/REQUESTS.md` S-1). -/
def TraceInUniverse (adversary : AdversaryP) (q : Nat) : Prop :=
  ∀ sample ∈ (referenceExperiment adversary q).support, ∀ entry ∈ sample.trace,
    entry.1 ∈ referenceInputs adversary

/-- `StructuralHitSrc` with the hit input inside a given universe. -/
def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ WotsExtract.PosSource position ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input

namespace Structural
open CanonGraph (Node Labels Secrets OtherHalves cell programmed canonInputs privateEquiv)

/-! ## Classes under structural variants -/

/-- W's source-sized positions are source nodes of G's graph. -/
theorem exists_node_of_posSource {p : Extract.Pos} (h : WotsExtract.PosSource p) : ∃ node : Node, node.toPos = p := by
  apply CanonGraph.exists_toPos
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
      have hc := Extract.chainCount_le lay
      exact ⟨h1, by omega, by omega, by omega⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      exact ⟨h1, by omega⟩
  | node lay tree level nd => exact h
  | forest index => exact h
  | ftsLeaf index coord leaf => exact h
  | ftsNode index coord level nd => exact h

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
  | ftsLeaf => exact Iff.rfl
  | ftsNode => exact Iff.rfl

theorem otherInput_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') (x : HashInput) :
    OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mpr hc⟩

/-! ## The structural rows of R3's universe for fixed secrets and labels -/

section Fixed
variable (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)

/-- Inputs of the universe parsed at a source node of G's graph that are not that node's cell. -/
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels

theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels :=
  Finset.mem_filter

/-- A structural row is no cell at all. -/
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : Node) : x ≠ cell s node labels := by
  obtain ⟨-, node₀, hpos, hne⟩ := (mem_strRows V s labels x).mp hx
  intro heq
  have := CanonGraph.cell_eq_of_posOf s labels hpos heq
  subst this
  exact hne heq

/-- The structural rows inside the universe. -/
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩

theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)

/-- The rest of the residual table. -/
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput

/-- R3's eager table with residual public table `join ρ rest`. -/
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

/-- Two residuals differing only on the structural rows give structural variants. -/
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

/-! ### The hit predicate and its kernel -/

/-- A structural O-class row whose answer has the low half of its position's label. -/
def strHit (T0 : Answers) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ OtherInput T0 x ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ low a = low (labels node)

theorem card_digest : (Fintype.card SphincsSecurity.Digest : ℝ≥0∞) = 2 ^ 128 := by
  simp [SphincsSecurity.digestBits]
  norm_num

/-- **Kernel**: a uniform answer of a structural row hits its label with probability `2^-128`. -/
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

/-! ### The trace bridges -/

theorem mem_traceOf {T : Answers} {qs : List RefWorld.Domain} {e : Entry} (he : e ∈ traceOf T qs) :
    e.2 = T (.inl (.inr e.1)) := by
  unfold traceOf at he
  obtain ⟨query, -, hq⟩ := List.mem_filterMap.mp he
  rcases query with (n | x) | u
  · simp at hq
  · simp only [Option.some.injEq] at hq
    rw [← hq]
  · simp at hq

/-- **Event bridge**: an R3 structural hit is a hit of the potential (with the honest answer read off the labels). -/
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

/-- **Count bridge**: the O-class count of an R3 sample is the charged count of the potential. -/
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)

end Fixed

/-! ## The bound for fixed secrets, labels and rest -/

/-- R3's sample computation on a fixed table (the body of `referenceComp`). -/
noncomputable def sampleComp (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> offlineRun T adversary q

section Bound
variable (adversary : AdversaryP) (q : Nat) (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)

/-- The sample computation in recorded form: the source program does not depend on the structural rows. -/
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]

/-- The recorded run's (value, trace) pair is the observed run's. -/
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]

/-- **Fixed secrets, labels and rest**: the structural bound over the uniform structural rows. -/
theorem fixed_bound :
    Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (otherCount sample : ℝ≥0∞) := by
  -- abbreviations
  set T := strTable V hU s o labels rest with hT
  set G0 := referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (T fun _ => 0) with hHit
  set Charged := OtherInput (T fun _ => 0) with hCharged
  have hlazy := lazy_seen_le (strRows V s labels) T (fun ρ x hx => strTable_str V hU s o labels rest ρ x hx)
    (fun ρ x hx => strTable_out V hU s o labels rest ρ (fun _ => 0) x hx) Hit Charged (2 ^ 128 : ℝ≥0∞)⁻¹
    (fun x a h => h.1) (fun x hx => strHit_kernel V s labels (T fun _ => 0) x hx) G0
  -- the event
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
  -- the count
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

/-! ## Averaging over secrets, labels and rest -/

/-- The structural bound on a law of R3 samples. -/
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

/-- `UniformTableSplit` in SPMF form, the rest sampled first. -/
theorem uniform_split_bind {Index Cell R : Type} [Fintype Index] [Fintype Cell] [DecidableEq Index]
    [DecidableEq Cell] (embed : Index → Cell) (hinj : Function.Injective embed) (g : (Cell → HashOutput) → SPMF R) :
    ((liftM (PMF.uniformOfFintype (Cell → HashOutput)) : SPMF (Cell → HashOutput)) >>= g) =
      ((liftM (PMF.uniformOfFintype (SphincsSecurity.Concrete.UniformTableSplit.Outside embed → HashOutput)) :
          SPMF _) >>= fun rest =>
        (liftM (PMF.uniformOfFintype (Index → HashOutput)) : SPMF (Index → HashOutput)) >>= fun ρ =>
          g (SphincsSecurity.Concrete.UniformTableSplit.join embed hinj ρ rest)) := by
  rw [SphincsSecurity.Concrete.UniformTableSplit.uniform_join embed hinj, ← PMF.monad_bind_eq_bind, liftM_bind]
  simp only [← PMF.monad_map_eq_map, liftM_map, bind_assoc, bind_map_left]
  exact SphincsSecurity.Concrete.RetainedObservation.bind_comm _ _ _

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

/-- **The structural bound on R3's whole law.** -/
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

/-! ## The endpoint -/

theorem liftM_pmf_apply {α : Type} (p : ProbComp α) (x : α) : (liftM p : PMF α) x = Pr[= x | 𝒮[p]] := by
  rw [← PMF.probOutput_eq_apply]
  rfl

theorem probEvent_liftM_pmf {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | 𝒮[p]] := rfl

theorem probEvent_liftM_pmf' {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | p] := rfl

theorem mem_support_liftM_pmf {α : Type} (p : ProbComp α) (x : α) (hx : x ∈ support p) :
    x ∈ (liftM p : PMF α).support := by
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply]
  change Pr[= x | p] ≠ 0
  exact (mem_support_iff _ _).mp hx

theorem referenceExperiment_eq (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl

/-- **Core structural bound** (no hypothesis): hits whose input lies in R3's eager universe. -/
theorem reference_structural_in_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  have h := Structural.referenceComp_bound adversary q
  unfold Structural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h

/-- **`reference_structural_le`** (BP-A §3/§4 S): the source-sized structural hit of W's `WotsPrimitiveSrc` on R3's
trace has probability at most `2^-128` times the expected number of O-class queries (given that R3's trace stays in
its eager universe, `TraceInUniverse`, F2). -/
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

end SigGolfCandidate.T3.Security.Wots
