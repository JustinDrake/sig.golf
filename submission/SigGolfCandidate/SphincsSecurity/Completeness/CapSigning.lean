import SigGolfCandidate.SphincsSecurity.Completeness.Caps
import SigGolfCandidate.SphincsSecurity.Completeness.Assembly

/-!
# The signer returns a representable counter tuple

The abstract signer and its query behavior are unchanged. This file charges
exhaustion or an unrepresentable counter tuple to the five checked prefix events.
The total byte codec may emit its reserved rejected tail outside this event.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete SigGolfCandidate.Ref.CounterPack

attribute [local irreducible] Seeded.signDigestLoop Concrete.buildLayerTreePaired Concrete.buildFtsTreePaired
  Concrete.encodingSearch digestAttemptLimit encodingAttemptLimit SphincsSecurity.deriveKey
  Seeded.signChecked

/-- A failed computation or an output outside the specified good set. -/
def capBad {α : Type} (good : α → Prop) (result : Option α) : Prop :=
  result.elim True (fun v => ¬ good v)

instance capBad_decidable {α : Type} (good : α → Prop) [DecidablePred good] (result : Option α) :
    Decidable (capBad good result) := by
  cases result with
  | none => exact isTrue trivial
  | some value => exact inferInstanceAs (Decidable (¬ good value))

theorem not_capBad_iff {α : Type} (good : α → Prop) (result : Option α) :
    ¬ capBad good result ↔ ∃ value, result = some value ∧ good value := by
  cases result <;> simp [capBad]

def capGoodLayer (lay : Layer) (out : LayerOutput) : Prop :=
  out.1.toNat < counterCap lay.val

def capGoodLayers (remaining : Nat) (out : Layer → LayerOutput) : Prop :=
  ∀ lay, lay.val < remaining → capGoodLayer lay (out lay)

def capGoodSignature (signature : Signature) : Prop :=
  ∀ lay, (signature.layers lay).counter.toNat < counterCap lay.val

instance capGoodSignature_decidable (signature : Signature) : Decidable (capGoodSignature signature) :=
  inferInstanceAs (Decidable (∀ lay, (signature.layers lay).counter.toNat < counterCap lay.val))

/-- The top layer fails or exceeds its cap only through its counter search. -/
theorem probEvent_signTopLayer_cap (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh parameter (fun l => l.val < 1) cache) :
    Pr[fun r => capBad (capGoodLayer topLayer) r.1 |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signTopLayerPaired parameter index secret topNode message
          : OracleComp HashSpec (Option LayerOutput))).run cache]
      ≤ capFailureBound := by
  rw [signTopLayerPaired]
  refine le_trans (probEvent_bind_le_add _ _
    (fun r => capBad (fun v => v.1.toNat < counterCap topLayer.val) r.1) _ cache 0 ?_) ?_
  · rintro ⟨result, c1⟩ _ hsome
    obtain ⟨⟨counter, word⟩, rfl, hcounter⟩ := (not_capBad_iff _ _).mp hsome
    dsimp only
    refine probEvent_bind_le _ _ _ c1 0 (fun r1 _ => ?_)
    refine probEvent_bind_le _ _ _ r1.2 0 (fun r2 _ => ?_)
    simp [capBad, capGoodLayer, hcounter]
  · rw [add_zero]
    simpa only [capBad, Nat.not_lt] using
      probEvent_encodingSearch_cap_uniform parameter topLayer _ _ message cache
        (fun c _ => hfresh topLayer (by decide) _ _ _)

/-- A union bound through the unchanged bottom-up signing recursion. -/
theorem probEvent_signLayers_cap (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ (remaining : Nat), remaining ≤ numLayers → ∀ (message : Digest) (cache : QueryCache HashSpec),
      EncodingFresh sk.parameter (fun l => l.val < remaining) cache →
      Pr[fun r => capBad (capGoodLayers remaining) r.1 |
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (signLayersPaired sk.parameter index (Seeded.otsSecret sk.parameter sk.seed) topNode remaining message
            : OracleComp HashSpec (Option (Layer → LayerOutput)))).run cache]
        ≤ (remaining : ℝ≥0∞) * capFailureBound := by
  intro remaining
  induction remaining with
  | zero => intro _ message cache _; simp [signLayersPaired, capBad, capGoodLayers]
  | succ r ih =>
      intro hrem message cache hfresh
      rw [signLayersPaired]
      split
      next hlayer =>
        by_cases hzero : r = 0
        · subst hzero
          rw [if_pos rfl]
          refine le_trans (probEvent_bind_le_add _ _
            (fun r => capBad (capGoodLayer topLayer) r.1) _ cache 0 ?_) ?_
          · rintro ⟨result, c1⟩ _ hsome
            obtain ⟨output, rfl, houtput⟩ := (not_capBad_iff _ _).mp hsome
            have hgood : capGoodLayers 1
                (fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)) := by
              intro lay hlay
              have he : lay = topLayer := Fin.ext (by simp only [topLayer]; omega)
              subst lay
              simpa [capGoodLayer] using houtput
            simpa [capBad] using hgood
          · rw [add_zero, Nat.zero_add, Nat.cast_one, one_mul]
            exact probEvent_signTopLayer_cap sk.parameter index _ topNode message cache hfresh
        rw [if_neg hzero]
        refine le_trans (probEvent_bind_le_add _ _
          (fun result => capBad (fun v => v.1.toNat < counterCap r) result.1) _ cache
          ((r : ℝ≥0∞) * capFailureBound) ?_) ?_
        · rintro ⟨result, c1⟩ hr hsome
          obtain ⟨⟨counter, word⟩, rfl, hcounter⟩ := (not_capBad_iff _ _).mp hsome
          dsimp only
          have h1 : EncodingFresh sk.parameter (fun l => l.val < r) c1 :=
            (hfresh.mono fun l hl => Nat.lt_succ_of_lt hl).step _ ⟨_, c1⟩ hr
              (fun f l hl tree leaf payload => Avoids.encodingSearch f _ _ _ _ _ _
                (fun _ => encodingInput_ne_of_layer_ne _
                  (fun h => by rw [← h] at hl; exact absurd hl (Nat.lt_irrefl _)) _ _ _ _ _ _) _ _)
          refine probEvent_bind_le _ _ _ c1 _ (fun built hbuilt => ?_)
          have h2 := h1.step _ built hbuilt (fun f l _ tree leaf payload =>
            Avoids.buildLayerTreePaired_of_structural f _ _ _ _ _ _ _
              (structural_encoding sk.parameter sk.seed l tree leaf payload))
          obtain ⟨⟨values, path, root⟩, c2⟩ := built
          dsimp only
          refine le_trans (probEvent_bind_le_add _ _
            (fun result => capBad (capGoodLayers r) result.1) _ c2 0 ?_) ?_
          · rintro ⟨result3, c3⟩ _ hsome3
            obtain ⟨rest, rfl, hrest⟩ := (not_capBad_iff _ _).mp hsome3
            have hgood : capGoodLayers (r + 1)
                (fun other => if other = ⟨r, hlayer⟩ then (counter, values, path) else rest other) := by
              intro lay hlay
              by_cases he : lay = ⟨r, hlayer⟩
              · subst lay
                simpa [capGoodLayer] using hcounter
              · dsimp only
                rw [if_neg he]
                apply hrest lay
                have hne : lay.val ≠ r := fun h => he (Fin.ext h)
                omega
            simpa [capBad] using hgood
          · rw [add_zero]
            exact ih (Nat.le_of_succ_le hrem) root c2 h2
        · calc _ ≤ capFailureBound + (r : ℝ≥0∞) * capFailureBound := by
                refine add_le_add ?_ le_rfl
                simpa only [capBad, Nat.not_lt] using
                  probEvent_encodingSearch_cap_uniform sk.parameter ⟨r, hlayer⟩ _ _ message cache
                    (fun c _ => hfresh _ (Nat.lt_succ_self r) _ _ _)
            _ = ((r + 1 : Nat) : ℝ≥0∞) * capFailureBound := by push_cast; ring
      next hlayer => exact absurd (Nat.lt_of_succ_le hrem) hlayer

/-- The PORS tree never fails; its five layer counters satisfy the same union bound. -/
theorem probEvent_signFrom_cap (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => capBad capGoodSignature r.1 | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signFromPaired sk.parameter index (Seeded.ftsSecret sk.parameter sk.seed index)
        (Seeded.otsSecret sk.parameter sk.seed) topNode randomness leaves
        : OracleComp HashSpec (Option Signature))).run cache]
      ≤ (numLayers : ℝ≥0∞) * capFailureBound := by
  rw [signFromPaired]
  refine probEvent_bind_le _ _ _ cache _ (fun tree htree => ?_)
  have h1 := hfresh.step _ tree htree (fun f l _ t leaf payload =>
    Avoids.buildFtsTreePaired_of_structural f _ _ _ _
      (structural_encoding sk.parameter sk.seed l t leaf payload))
  obtain ⟨⟨secrets, table⟩, c1⟩ := tree
  dsimp only
  refine le_trans (probEvent_bind_le_add _ _ (fun r => capBad (capGoodLayers numLayers) r.1) _ c1 0 ?_) ?_
  · rintro ⟨result, c2⟩ _ hsome
    obtain ⟨parts, rfl, hparts⟩ := (not_capBad_iff _ _).mp hsome
    have hgood : capGoodSignature ⟨randomness, honestFts leaves secrets table,
        fun lay => LayerOutput.toSignature lay (parts lay)⟩ := by
      intro lay
      exact hparts lay lay.isLt
    simpa [capBad] using hgood
  · rw [add_zero]
    exact probEvent_signLayers_cap sk index topNode numLayers le_rfl (table ftsTreeHeight 0) c1
      (h1.mono fun _ _ => trivial)

/-- Digest exhaustion and the five counter prefix events cover all failures of compact representation. -/
theorem probEvent_signChecked_cap (sk : Seeded.SecretKey) (topCache : TopCache) (message : Message)
    (cache : QueryCache HashSpec)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => capBad capGoodSignature r.1 | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.signChecked sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * capFailureBound := by
  rw [Seeded.signChecked]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache
    ((numLayers : ℝ≥0∞) * capFailureBound) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨⟨randomness, index, leaves⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun _ => True) c1 :=
      henc.step _ ⟨_, c1⟩ hr (fun f l _ tree leaf payload =>
        Avoids.signDigestLoop_of_structural f _ sk message
          (structural_encoding sk.parameter sk.seed l tree leaf payload) _ _)
    exact probEvent_signFrom_cap sk index _ randomness leaves c1 h1
  · exact add_le_add (probEvent_signDigestLoop sk message digestAttemptLimit 0 cache ∅
      (by rw [digestAttemptLimit]; omega) (by simp) (fun s _ _ => hrand s) (fun ρ _ => hmsg ρ)) le_rfl

/-- The cached MAC check passes for honest key generation and adds no cap event. -/
theorem probEvent_sign_cap (sk : Seeded.SecretKey) (topCache : TopCache) (message : Message)
    (cache : QueryCache HashSpec)
    (hmac : cache (macHashInput sk.parameter sk.seed topCache.region) = some topCache.tag)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => capBad capGoodSignature r.1 | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.sign sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * capFailureBound := by
  rw [Seeded.sign]
  simp only [oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [cached_run _ _ _ hmac, pure_bind, if_pos rfl]
  exact probEvent_signChecked_cap sk topCache message cache hrand hmsg henc

/-- Fresh key generation supplies exactly the freshness and cached-MAC hypotheses above. -/
theorem probEvent_signedWithKeys_cap (seed : MasterSeed) (message : Message) :
    Pr[fun r => capBad capGoodSignature r.1.2 |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signedWithKeys seed message)).run ∅]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * capFailureBound := by
  rw [signedWithKeys]
  refine probEvent_bind_le _ _ _ ∅ _ (fun r hr => ?_)
  obtain ⟨hrand, hmsg, henc⟩ := keygen_fresh seed r hr message
  have hmac := keygen_mac_cached seed r hr
  refine le_trans (probEvent_bind_le_add _ _ (fun r => capBad capGoodSignature r.1) _ r.2 0 ?_) ?_
  · rintro ⟨result, c⟩ _ hgood
    simpa [capBad] using hgood
  · rw [add_zero]
    exact probEvent_sign_cap r.1.2.2 r.1.2.1 message r.2 hmac hrand hmsg henc

/-- Whether the optional signature is representable by the compact codec. -/
def capSuccess : Option Signature → Bool
  | none => false
  | some signature => decide (capGoodSignature signature)

theorem capSuccess_false_iff (result : Option Signature) :
    capSuccess result = false ↔ capBad capGoodSignature result := by
  cases result with
  | none => simp [capSuccess, capBad]
  | some signature => exact decide_eq_false_iff_not

/-- The representability experiment, retaining every abstract signing query. -/
def capGame (seed : MasterSeed) (message : Message) : OracleComp HashSpec Bool :=
  (fun r => capSuccess r.2) <$> signedWithKeys seed message

noncomputable def capExperiment (seed : MasterSeed) (message : Message) : ProbComp Bool :=
  (simulateQ (randomOracle : QueryImpl HashSpec _) (capGame seed message)).run' ∅

/-- One message fails representation only through the six bounded searches. -/
theorem cap_seeded_failure_le (seed : MasterSeed) (message : Message) :
    Pr[= false | capExperiment seed message]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 699 + 5 * capFailureBound := by
  rw [capExperiment, capGame, simulateQ_map, StateT.run'_eq, StateT.run_map,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  simp only [Function.comp_def, capSuccess_false_iff]
  exact (probEvent_signedWithKeys_cap seed message).trans
    (add_le_add digestFactor_pow_le (by rfl))


/-- The genuine all-message cap bound; the existing stronger uncapped theorem is unchanged. -/
theorem cap_complete_seeded (seed : MasterSeed) :
    ∑' message : Message, Pr[= false | capExperiment seed message]
      ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    ∑' message : Message, Pr[= false | capExperiment seed message]
        ≤ ∑' _message : Message, ((2⁻¹ : ℝ≥0∞) ^ 699 + 5 * capFailureBound) :=
          ENNReal.tsum_le_tsum fun message => cap_seeded_failure_le seed message
    _ = (2 : ℝ≥0∞) ^ 256 * ((2⁻¹ : ℝ≥0∞) ^ 699 + 5 * capFailureBound) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := closing_sum_caps_uniform

end SphincsSecurity.Completeness
