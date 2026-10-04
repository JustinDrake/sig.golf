import SigGolfCandidate.ClaudeWCT.W9.T3.Gate6.SourceBudget
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.PairRows
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets

section


namespace ClaudeWCT.W9.T3.LayerBudget
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Budgets (signingZ encodingRate encodingRate_bounds encoding_failMass signing_z_le
  EncodingFreshBelow SourceFreshness V_bind_bounded post_of_roRun)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow layerTrial V_layerCounterSearch bound_layerCounterSearch
  avoids_layerCounterSearch preserves_pairBelow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
structure Envelopes where
  b : Layer → ℚ
  ge_one : ∀ lay, 1 ≤ b lay
  step : ∀ lay, (SigGolfCandidate.T3.BaseAudit.zU : ℝ) * ((1 - encodingRate lay) * (b lay : ℝ) + encodingRate lay) ≤
    (b lay : ℝ)
namespace Envelopes
variable (E : Envelopes)
noncomputable def envelope (lay : Layer) : ENNReal := ENNReal.ofReal (E.b lay : ℝ)
theorem envelope_ge_one (lay : Layer) : 1 ≤ E.envelope lay := by
  rw [envelope, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast E.ge_one lay)
theorem moment_step (lay : Layer) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass (Sampling.encodingDecode lay) * E.envelope lay +
        (1 - failMass (Sampling.encodingDecode lay))) ≤ E.envelope lay := by
  have hp0 : 0 ≤ encodingRate lay := by linarith [(encodingRate_bounds lay).1]
  have hp1 : 0 ≤ 1 - encodingRate lay := by linarith [(encodingRate_bounds lay).2]
  have hb0 : 0 ≤ (E.b lay : ℝ) := by have := E.ge_one lay; exact_mod_cast (by linarith : (0 : ℚ) ≤ E.b lay)
  have hz0 : 0 ≤ (SigGolfCandidate.T3.BaseAudit.zU : ℝ) := by norm_num [SigGolfCandidate.T3.BaseAudit.zU]
  have hs : 1 - (1 - encodingRate lay) = encodingRate lay := by ring
  rw [encoding_failMass, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp1, hs, envelope]
  calc
    _ ≤ ENNReal.ofReal (SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1 - encodingRate lay) * ENNReal.ofReal (E.b lay : ℝ) +
        ENNReal.ofReal (encodingRate lay)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
        ((1 - encodingRate lay) * (E.b lay : ℝ) + encodingRate lay)) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (E.step lay)
theorem V_counterSearch_fresh (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (message : Digest) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (Sampling.encodingTrial lay tree leaf message c) = none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (counterSearch lay tree leaf message counter fuel) cache ≤ E.envelope lay :=
  Sampling.V_counterSearch secret _ _ (E.envelope_ge_one lay)
    lay tree leaf message (E.moment_step lay) fuel counter hlimit cache hfresh
noncomputable def layerMomentBound : Nat → ENNReal
  | 0 => 1
  | n + 1 => E.envelope (Fin.ofNat 4 n) *
      (if n = 0 then signingZ ^ 165 else signingZ ^ (treeCost (Fin.ofNat 4 n)) * layerMomentBound n)
theorem layerMomentBound_ge_one : ∀ n, 1 ≤ E.layerMomentBound n := by
  intro n; induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [layerMomentBound]
      apply one_le_mul (E.envelope_ge_one _)
      split
      · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
      · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) ih
theorem V_signLayers_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (index : Nat) : ∀ n, n ≤ 4 → ∀ message rcache, EncodingFreshBelow n rcache →
    V secret signingZ (signLayers cache index n message) rcache ≤ E.layerMomentBound n := by
  intro n
  induction n with
  | zero => intro _ message rcache _; simp only [signLayers, V_pure, layerMomentBound, le_refl]
  | succ n ih =>
      intro hn message rcache hc
      have hnv : (Fin.ofNat 4 n).val = n := Nat.mod_eq_of_lt (by omega)
      have heFresh : EncodingFreshBelow ((Fin.ofNat 4 n).val + 1) rcache := by rwa [hnv]
      have hs := E.V_counterSearch_fresh secret (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 message
        counterLimit 0 (by decide) rcache
        (fun c _ hlim => hc _ (by rw [hnv]; omega) _ _ _ _ hlim)
      simp only [signLayers, layerMomentBound]
      refine V_bind_bounded secret signingZ _ _ rcache _ _ hs ?_
      intro result hr
      have hpost := post_of_roRun (bound_counterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 message counterLimit 0)
        secret rcache result hr
      have hnext := hf.counter (Fin.ofNat 4 n) _ _ message rcache heFresh result hr
      cases hx : result.1 with
      | none =>
          simp only [hx, V_pure]
          split
          · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
          · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (E.layerMomentBound_ge_one n)
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hpost counter digits hx
          simp only [hx]
          by_cases hn0 : n = 0
          · subst n
            simp only [ite_true]
            refine V_bind_bounded secret signingZ _ _ result.2 _ 1
              (V_of_bound (bound_signTop cache _ digits hd.1 hd.2.1) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_ |>.trans_eq (mul_one _)
            intro out _; rw [V_pure]
          · simp only [hn0, ite_false]
            refine V_bind_bounded secret signingZ _ _ result.2 _ _
              (V_of_bound (bound_buildTree (Fin.ofNat 4 n) _ _ digits hd.2.2) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_
            intro treeResult htree
            have ht := hf.tree (Fin.ofNat 4 n) _ _ digits result.2 hnext treeResult htree
            rw [hnv] at ht
            refine V_bind_bounded secret signingZ _ _ treeResult.2 _ 1
              (ih (by omega) _ _ ht) ?_ |>.trans_eq (mul_one _)
            intro previous _
            cases previous.1 <;> rw [V_pure]
theorem V_layerCounterSearch_fresh (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) cache ≤ E.envelope lay :=
  V_layerCounterSearch secret _ _ (E.envelope_ge_one lay) lay tree leaf msg (E.moment_step lay) fuel counter
    hlimit cache hfresh
theorem V_signLayersBC (secret : BitVec 256) (cache : Cache) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg rcache, PairFreshBelow n rcache →
      V secret signingZ (ClaudeWCT.WCT9.signLayersBC cache index n msg) rcache ≤ E.layerMomentBound n := by
  intro n
  induction n with
  | zero =>
      intro _ msg rcache _
      simp only [ClaudeWCT.WCT9.signLayersBC, V_pure, layerMomentBound, le_refl]
  | succ n ih =>
      intro hn msg rcache hc
      have hnv : (Fin.ofNat 4 n).val = n := Nat.mod_eq_of_lt (by omega)
      have hs := E.V_layerCounterSearch_fresh secret (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
        counterLimit 0 (by decide) rcache
        (fun c _ hlim => hc.layerTrial _ (by rw [hnv]; omega) _ _ _ _ hlim)
      simp only [ClaudeWCT.WCT9.signLayersBC, layerMomentBound]
      refine V_bind_bounded secret signingZ _ _ rcache _ _ hs ?_
      intro result hr
      have hpost := post_of_roRun (bound_layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg counterLimit 0)
        secret rcache result hr
      have hnext : PairFreshBelow n result.2 := by
        intro other ho tree' leaf' left' right' c hlt
        have hne : Fin.ofNat 4 n ≠ other := by intro he; subst other; omega
        rw [SigGolfCandidate.T3.Freshness.preserves secret _ _ (avoids_layerCounterSearch secret hne
          (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit
          tree' leaf' left' right' c) rcache result hr]
        exact hc other (by omega) tree' leaf' left' right' c hlt
      cases hx : result.1 with
      | none =>
          simp only [hx, V_pure]
          split
          · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
          · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (E.layerMomentBound_ge_one n)
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hpost counter digits hx
          simp only [hx]
          by_cases hn0 : n = 0
          · subst n
            simp only [ite_true]
            refine V_bind_bounded secret signingZ _ _ result.2 _ 1
              (V_of_bound (bound_signTop cache _ digits hd.1 hd.2.1) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_ |>.trans_eq (mul_one _)
            intro out _; rw [V_pure]
          · simp only [hn0, ite_false]
            refine V_bind_bounded secret signingZ _ _ result.2 _ _
              (V_of_bound (bound_buildTree (Fin.ofNat 4 n) _ _ digits hd.2.2) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_
            intro treeResult htree
            have ht : PairFreshBelow n treeResult.2 :=
              preserves_pairBelow secret _ (fun target htag =>
                SigGolfCandidate.T3.Freshness.avoids_buildTree secret target (Or.inl htag) _ _ _ digits)
                n result.2 hnext treeResult htree
            refine V_bind_bounded secret signingZ _ _ treeResult.2 _ 1
              (ih (by omega) _ _ ht) ?_ |>.trans_eq (mul_one _)
            intro previous _
            cases previous.1 <;> rw [V_pure]
theorem layerMomentBound_four :
    E.layerMomentBound 4 = signingZ ^ 85922 * E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 := by
  change E.envelope 3 * (signingZ ^ 21439 * (E.envelope 2 *
    (signingZ ^ 21439 * (E.envelope 1 * (signingZ ^ 42879 * (E.envelope 0 * signingZ ^ 165)))))) = _
  ring
theorem envelope_prod :
    E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 =
      ENNReal.ofReal ((E.b 0 : ℝ) * (E.b 1 : ℝ) * (E.b 2 : ℝ) * (E.b 3 : ℝ)) := by
  have h0 : 0 ≤ (E.b 0 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 0] : (0 : ℚ) ≤ E.b 0)
  have h1 : 0 ≤ (E.b 1 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 1] : (0 : ℚ) ≤ E.b 1)
  have h2 : 0 ≤ (E.b 2 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 2] : (0 : ℚ) ≤ E.b 2)
  simp only [envelope]
  rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (mul_nonneg h0 h1),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h0 h1) h2)]
end Envelopes
open ClaudeWCT.W9.T3.BaseAudit in
noncomputable def Envelopes.v2b : Envelopes where
  b := ![V2b.b1, V2b.b2, V2b.b3, V2b.b4]
  ge_one := by intro lay; fin_cases lay <;> norm_num [V2b.b1, V2b.b2, V2b.b3, V2b.b4]
  step := by
    intro lay
    fin_cases lay <;> norm_num [encodingRate, EncodingCounting.acceptedCount, SigGolfCandidate.T3.BaseAudit.zU,
      V2b.b1, V2b.b2, V2b.b3, V2b.b4]
noncomputable abbrev Envelopes.v3 : Envelopes := Envelopes.v2b
end ClaudeWCT.W9.T3.LayerBudget
end

section


namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V V_pure V_of_bound)
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le V_bind_bounded post_of_roRun signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow AllSearchesFreshBC digestSearch_preserves_pairBelow
  privateMac_preserves_fresh privateNonce_preserves_fresh)
open SigGolfCandidate.T3.BaseAudit (zU)
open SigGolfCandidate.T3.Cost (bound_privateNonce bound_privateMac)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable abbrev layerEnvelopes : ClaudeWCT.W9.T3.LayerBudget.Envelopes :=
  ClaudeWCT.W9.T3.LayerBudget.Envelopes.v2b
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.V2b.b0 : ℝ)
theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.V2b.b0]
theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V2b.p0 : ℝ)) :
    failMass digestDecode = ENNReal.ofReal (1 - (BaseAudit.V2b.p0 : ℝ)) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, haccept,
    ENNReal.ofReal_sub 1 (by norm_num [BaseAudit.V2b.p0])]
  simp
theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V2b.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (BaseAudit.V2b.p0 : ℝ) := by norm_num [BaseAudit.V2b.p0]
  have hp1 : 0 ≤ 1 - (BaseAudit.V2b.p0 : ℝ) := by norm_num [BaseAudit.V2b.p0]
  have hb0 : 0 ≤ (BaseAudit.V2b.b0 : ℝ) := by norm_num [BaseAudit.V2b.b0]
  have hz0 : 0 ≤ (zU : ℝ) := by norm_num [zU]
  have hs : 1 - (1 - (BaseAudit.V2b.p0 : ℝ)) = (BaseAudit.V2b.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1, hs, digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (zU : ℝ) *
      (ENNReal.ofReal (1 - (BaseAudit.V2b.p0 : ℝ)) * ENNReal.ofReal (BaseAudit.V2b.b0 : ℝ) +
        ENNReal.ofReal (BaseAudit.V2b.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((zU : ℝ) *
        ((1 - (BaseAudit.V2b.p0 : ℝ)) * (BaseAudit.V2b.b0 : ℝ) + (BaseAudit.V2b.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := BaseAudit.V2b.step_0
      have h' : ((zU * ((1 - BaseAudit.V2b.p0) * BaseAudit.V2b.b0 + BaseAudit.V2b.p0) : ℚ) : ℝ) ≤
          (BaseAudit.V2b.b0 : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V2b.p0 : ℝ)) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  ClaudeWCT.W9.T3.Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh
theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance digest_probability_eq_p0
theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    digest_probability_eq_p0
structure SourceFreshness (secret : BitVec 256) : Prop where
  forest : ∀ index output cache, PairFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (ClaudeWCT.WCT9.signForest index output) cache),
      PairFreshBelow 4 result.2
noncomputable def postDigestMomentFor (fts : ℕ) : ENNReal := signingZ ^ fts * layerEnvelopes.layerMomentBound 4
noncomputable def payloadMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * (digestEnvelope * postDigestMomentFor fts)
noncomputable def signingMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * payloadMomentFor fts
noncomputable def signingMoment : ENNReal := signingMomentFor BaseAudit.V3.ftsSign
theorem postDigestMomentFor_ge_one (fts : ℕ) : 1 ≤ postDigestMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerEnvelopes.layerMomentBound_ge_one 4)
theorem payloadMomentFor_ge_one (fts : ℕ) : 1 ≤ payloadMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestEnvelope_ge_one (postDigestMomentFor_ge_one fts))
theorem V_signPayload_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (signPayload cache message) rcache ≤ payloadMomentFor fts := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateNonce message) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro nonce hn
  have hnFresh := privateNonce_preserves_fresh secret message rcache hc nonce hn
  refine V_bind_bounded secret signingZ _ _ nonce.2 _ _
    (V_digestSearch_fresh secret nonce.1 message digestAttemptLimit 0
      (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega) nonce.2
      (fun c _ hlim => hnFresh.1 _ _ _ hlim)) ?_
  intro found hd
  have hdFresh := digestSearch_preserves_pairBelow secret nonce.1 message 0 digestAttemptLimit nonce.2 hnFresh
    found hd
  cases hx : found.1 with
  | none => simp only [V_pure]; exact postDigestMomentFor_ge_one fts
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      obtain ⟨post, hbound⟩ := hforest (output.toNat % 2 ^ 31) output
      refine V_bind_bounded secret signingZ _ _ found.2 _ _
        (V_of_bound hbound secret signingZ (SigGolfCandidate.Budget.one_le_zOf _) found.2) ?_
      intro forest hforestRun
      have hforestFresh := hf.forest _ _ found.2 hdFresh forest hforestRun
      refine V_bind_bounded secret signingZ _ _ forest.2 _ 1
        (layerEnvelopes.V_signLayersBC secret cache (output.toNat % 2 ^ 31) 4 (by decide)
          (.forest forest.1.2) forest.2 hforestFresh) ?_ |>.trans_eq (mul_one _)
      intro pieces _
      cases pieces.1 <;> rw [V_pure]
theorem V_sign_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ signingMomentFor fts := by
  show V secret signingZ (ClaudeWCT.WCT9.signWith digestAttemptLimit cache message) rcache ≤
    signingMomentFor fts
  unfold ClaudeWCT.WCT9.signWith
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateMac cache.region) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro result hr
  have hmac := privateMac_preserves_fresh secret cache.region rcache hc result hr
  split
  · rw [V_pure]; exact payloadMomentFor_ge_one fts
  · exact V_signPayload_of_freshness_for secret hf fts hforest cache message result.2 hmac
theorem signingMomentFor_eq (fts : ℕ) : signingMomentFor fts = signingZ ^ (4 + fts + 85922) *
    (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
      layerEnvelopes.envelope 3) := by
  rw [signingMomentFor, payloadMomentFor, postDigestMomentFor, layerEnvelopes.layerMomentBound_four]
  ring
theorem signingMomentFor_mono {a b : ℕ} (h : a ≤ b) : signingMomentFor a ≤ signingMomentFor b := by
  have hz : signingZ ^ a ≤ signingZ ^ b := pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) h
  unfold signingMomentFor payloadMomentFor postDigestMomentFor
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hz le_rfl)))
theorem envelope_product_eq : digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
    layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3 =
    ENNReal.ofReal ((BaseAudit.V2b.b0 : ℝ) * (BaseAudit.V2b.b1 : ℝ) * (BaseAudit.V2b.b2 : ℝ) *
      (BaseAudit.V2b.b3 : ℝ) * (BaseAudit.V2b.b4 : ℝ)) := by
  change ENNReal.ofReal (BaseAudit.V2b.b0 : ℝ) * ENNReal.ofReal (BaseAudit.V2b.b1 : ℝ) *
    ENNReal.ofReal (BaseAudit.V2b.b2 : ℝ) * ENNReal.ofReal (BaseAudit.V2b.b3 : ℝ) *
    ENNReal.ofReal (BaseAudit.V2b.b4 : ℝ) = _
  rw [← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V2b.b0 : ℝ) by norm_num [BaseAudit.V2b.b0]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V2b.b0 : ℝ) * (BaseAudit.V2b.b1 : ℝ) by
      norm_num [BaseAudit.V2b.b0, BaseAudit.V2b.b1]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V2b.b0 : ℝ) * (BaseAudit.V2b.b1 : ℝ) * (BaseAudit.V2b.b2 : ℝ) by
      norm_num [BaseAudit.V2b.b0, BaseAudit.V2b.b1, BaseAudit.V2b.b2]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V2b.b0 : ℝ) * (BaseAudit.V2b.b1 : ℝ) * (BaseAudit.V2b.b2 : ℝ) *
      (BaseAudit.V2b.b3 : ℝ) by
      norm_num [BaseAudit.V2b.b0, BaseAudit.V2b.b1, BaseAudit.V2b.b2, BaseAudit.V2b.b3])]
theorem signingMoment_eq : signingMoment = signingZ ^ 118169 *
    (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
      layerEnvelopes.envelope 3) := by
  rw [signingMoment, signingMomentFor_eq]
  norm_num [BaseAudit.V3.ftsSign]
theorem signingMoment_le_two : signingMoment ≤ 2 := by
  rw [signingMoment_eq, SigGolfCandidate.Budget.zOf_pow, envelope_product_eq]
  have hcast := ENNReal.ofReal_le_ofReal BaseAudit.V3.signing_envelope
  rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((118169 : ℝ) / 131072) by positivity)] at hcast
  norm_num only [ENNReal.ofReal_ofNat] at hcast
  convert hcast using 1
  norm_num
theorem signingMomentFor_v2b_le_two : signingMomentFor 32250 ≤ 2 := by
  rw [signingMomentFor_eq, SigGolfCandidate.Budget.zOf_pow, envelope_product_eq]
  have hcast := ENNReal.ofReal_le_ofReal BaseAudit.V2b.signing_envelope
  rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((118176 : ℝ) / 131072) by positivity)] at hcast
  norm_num only [ENNReal.ofReal_ofNat] at hcast
  convert hcast using 1
  norm_num
theorem signingMomentFor_le_two_of_le {fts : ℕ} (h : fts ≤ 32250) : signingMomentFor fts ≤ 2 :=
  (signingMomentFor_mono h).trans signingMomentFor_v2b_le_two
theorem V_sign_le_two_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) {fts : ℕ}
    (hfts : fts ≤ 32250)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness_for secret hf fts hforest cache message rcache hc).trans
    (signingMomentFor_le_two_of_le hfts)
theorem realized_sign_exponential_budget_of_freshness_for (secret : BitVec 256)
    (hf : SourceFreshness secret) {fts : ℕ} (hfts : fts ≤ 32250)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (SigGolfCandidate.T3.Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  have h := V_sign_le_two_of_freshness_for secret hf hfts hforest cache message rcache hc
  rw [SigGolfCandidate.T3.Sampling.V_realized] at h
  simp only [signingZ_pow] at h
  rw [StateT.run'_eq, expectedValue_map]
  exact h
end ClaudeWCT.W9.T3.Budgets
end
