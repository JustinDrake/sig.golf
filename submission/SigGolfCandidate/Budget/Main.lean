import SigGolfCandidate.Budget.Numeric
import SigGolfCandidate.Submission

/-!
# Budget: `Submission.CompressionBounds` from refinement hypotheses

`compressionBounds_of_refinement`: any submission whose programs have the compressions of the
reference spec satisfies the organizer's `CompressionBounds`. The hypotheses are about the
`OracleComp`s of the programs (their query trees), mapped to what is needed:

* keygen: `(value, hashCompressions)` is `countBlocks (keygenRef sk)` with the value some function
  `G` of the public key;
* sign: `hashCompressions` is `countBlocks (signRef sk cache m)`'s count, for every cache input
  (the bound holds for every cache, in particular the honest one from keygen);
* expand: on every path of the honest pipeline (under every fixed answer function) expand costs
  at most as many compressions as sign (`ExpandBelowSign`; for the submission: `Budget/Expand`,
  the expansion's counter searches replay the signer's). Every reachable state of the lazy random
  oracle is such an evaluation (`eval_of_mem_support_roRun`), so the expand moment is at most the
  sign moment (`2^(1/2^20) ≤ 2^(1/2^17)`).

These follow from bytecode refinement theorems of the form
`(fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input = ...` by
mapping (`Functor.map_map`).
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist

/-! ## `honest`, split after each phase -/

section Tails
variable (sub : Submission)

def tailE (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (expand : RunResult (Output sub.sizes .expand)) : OracleComp HashSpec HonestResult :=
  let costs := recordCost costs .expand expand.hashCompressions
  match expand.value with
  | some witness => do
    let verify ← sub.run .verify (m, pk, witness)
    let costs := recordCost costs .verify verify.hashCompressions
    pure ⟨verify.value.isSome, costs, verify.cycles + witnessCycles sub.sizes.witness⟩
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

def tailS (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (sign : RunResult (Output sub.sizes .sign)) : OracleComp HashSpec HonestResult :=
  let costs := recordCost costs .sign sign.hashCompressions
  match sign.value with
  | some signature => do
    let expand ← sub.run .expand (m, pk, signature)
    tailE sub m pk costs expand
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

def tailK (sk : SecretKey) (m : Message) (keygen : RunResult (Output sub.sizes .keygen)) :
    OracleComp HashSpec HonestResult :=
  let costs := recordCost (fun _ => 0) .keygen keygen.hashCompressions
  match keygen.value with
  | some (pk, cache) => do
    let sign ← sub.run .sign (sk, cache, m)
    tailS sub m pk costs sign
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

theorem honest_eq (sk : SecretKey) (m : Message) :
    sub.honest sk m = sub.run .keygen sk >>= tailK sub sk m := rfl

theorem tailE_costs (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (e : RunResult (Output sub.sizes .expand)) :
    ∀ r ∈ support (tailE sub m pk costs e), ∀ ph, ph ≠ .verify →
      r.costs ph = recordCost costs .expand e.hashCompressions ph := by
  intro r hr ph hph
  unfold tailE at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨v, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [recordCost, hph]
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

theorem tailS_costs (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (s : RunResult (Output sub.sizes .sign)) :
    ∀ r ∈ support (tailS sub m pk costs s), ∀ ph, ph ≠ .verify → ph ≠ .expand →
      r.costs ph = recordCost costs .sign s.hashCompressions ph := by
  intro r hr ph hph hph'
  unfold tailS at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨e, -, hr⟩ := hr
    rw [tailE_costs sub m pk _ e r hr ph hph]
    simp [recordCost, hph']
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

theorem tailK_costs (sk : SecretKey) (m : Message) (k : RunResult (Output sub.sizes .keygen)) :
    ∀ r ∈ support (tailK sub sk m k), r.costs .keygen = k.hashCompressions := by
  intro r hr
  unfold tailK at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨s, -, hr⟩ := hr
    rw [tailS_costs sub m _ _ s r hr .keygen (by decide) (by decide)]
    simp [recordCost]
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; simp [recordCost]

end Tails

/-! ## Expectations over the random oracle -/

theorem ev_withRandomOracle {α : Type} (oa : OracleComp HashSpec α) (f : α → ℝ≥0∞) :
    expectedValue (withRandomOracle oa) f = expectedValue (roRun oa ∅) (fun x => f x.1) := by
  unfold withRandomOracle roRun
  rw [StateT.run'_eq, expectedValue_map]

theorem ev_roRun_le_of_support {α : Type} (oa : OracleComp HashSpec α) (c : RCache)
    (g : α → ℝ≥0∞) (v : ℝ≥0∞) (h : ∀ r ∈ support oa, g r ≤ v) :
    expectedValue (roRun oa c) (fun x => g x.1) ≤ v := by
  refine expectedValue_le_of_support fun x hx => h _ ?_
  apply support_simulateQ_run'_subset randomOracle oa c
  rw [StateT.run'_eq, support_map]
  exact ⟨x, hx, rfl⟩

/-- The expectation of `z ^ n` over a count computation is `V`. -/
theorem ev_count_eq_V {α : Type} (z : ℝ≥0∞) (oa : OracleComp HashSpec α) (c : RCache) :
    expectedValue (roRun (Prod.snd <$> countBlocks oa) c) (fun x => z ^ x.1) = V z oa c := by
  rw [roRun_map, expectedValue_map]; rfl

/-- The organizer's cost functional is `zOf budget ^ cost`. -/
theorem costFun_eq (n B : Nat) :
    ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (B : ℝ))) = zOf B ^ n := by
  rw [zOf_pow, Real.rpow_eq_pow]

theorem ofReal_rpow_zero (B : Nat) : ENNReal.ofReal (Real.rpow 2 ((0 : Nat) / (B : ℝ))) = 1 := by
  simp [Real.rpow_eq_pow]

/-! ## Reachable states of the lazy random oracle are answer-function evaluations -/

/-- A reachable result of the lazy random oracle extends the start cache and is the evaluation of the
computation under every answer function agreeing with the final cache. -/
theorem eval_of_mem_support_roRun {α : Type} (oa : OracleComp HashSpec α) :
    ∀ (c : RCache) (x : α × RCache), x ∈ support (roRun oa c) →
      (∀ q u, c q = some u → x.2 q = some u) ∧
      ∀ f : Hash, (∀ q u, x.2 q = some u → f q = u) → evalWithAnswerFn f oa = x.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c x hx
    rw [roRun_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨fun _ _ h => h, fun _ _ => rfl⟩
  | query_bind q k ih =>
    intro c x hx
    rw [roRun_bind, support_bind] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [show (liftM (OracleSpec.query q) : OracleComp HashSpec _) = qry q from rfl, roRun_qry] at hy
    obtain ⟨h1, h2⟩ := ih y.1 y.2 x hx
    have hyq : y.2 q = some y.1 ∧ ∀ q' u, c q' = some u → y.2 q' = some u := by
      rcases mem_support_ro q c y hy with ⟨hc, he⟩ | ⟨hc, he⟩
      · rw [he]; exact ⟨hc, fun _ _ h => h⟩
      · rw [he]
        refine ⟨QueryCache.cacheQuery_self _ _ _, fun q' u hq' => ?_⟩
        by_cases hqq : q' = q
        · subst hqq; rw [hc] at hq'; cases hq'
        · rw [QueryCache.cacheQuery_of_ne _ _ hqq]; exact hq'
    refine ⟨fun q' u h => h1 q' u (hyq.2 q' u h), fun f hf => ?_⟩
    rw [evalWithAnswerFn_bind]
    have e : evalWithAnswerFn f (liftM (OracleSpec.query q) : OracleComp HashSpec _) = f q := by
      simp [evalWithAnswerFn, simulateQ_spec_query]
    rw [e, hf q y.1 (h1 q y.1 hyq.1)]
    exact h2 f hf

/-- The answer function reading the final cache (`0` elsewhere). -/
def cacheFn (c : RCache) : Hash := fun q => (c q).getD 0

theorem eval_cacheFn {α : Type} (oa : OracleComp HashSpec α) (x : α × RCache)
    (hx : x ∈ support (roRun oa ∅)) : evalWithAnswerFn (cacheFn x.2) oa = x.1 :=
  (eval_of_mem_support_roRun oa ∅ x hx).2 (cacheFn x.2) fun q u h => by
    simp only [cacheFn, h, Option.getD_some]

/-! ## The three phases -/

section Phases
variable (sub : Submission)

/-- The keygen refinement hypothesis (compressions and value). -/
def KeygenRefines : Prop :=
  ∀ sk, ∃ G : Bytes 16 × Cache → Option (Output sub.sizes .keygen),
    (fun r => (r.value, r.hashCompressions)) <$> sub.run .keygen sk =
      (fun p => (G p.1, p.2)) <$> countBlocks (keygenRef sk)

/-- A sign-input cache read as a reference cache, for a submission whose cache size `K` is the
reference `CACHE_BYTES`. -/
abbrev refCache {sub : Submission} (hc : sub.sizes.cache = CACHE_BYTES) (cache : Bytes sub.sizes.cache) :
    Cache :=
  cast (congrArg Bytes hc) cache

/-- The sign refinement hypothesis (compressions), for every cache input. -/
def SignRefines (hc : sub.sizes.cache = CACHE_BYTES) : Prop :=
  ∀ sk cache m, (fun r => r.hashCompressions) <$> sub.run .sign (sk, cache, m) =
    Prod.snd <$> countBlocks (signRef sk (refCache hc cache) m)

theorem keygen_count (hK : KeygenRefines sub) (sk : SecretKey) :
    (fun r => r.hashCompressions) <$> sub.run .keygen sk = Prod.snd <$> countBlocks (keygenRef sk) := by
  obtain ⟨G, hG⟩ := hK sk
  have h := congrArg (fun oa => Prod.snd <$> oa) hG
  simp only [Functor.map_map] at h
  exact h

set_option maxRecDepth 100000 in
/-- States after keygen satisfy sign's cache invariant. -/
theorem keygen_cacheInv (hK : KeygenRefines sub) (sk : SecretKey)
    (x : RunResult (Output sub.sizes .keygen) × RCache)
    (hx : x ∈ support (roRun (sub.run .keygen sk) ∅)) : CacheInv Inv0 x.2 := by
  obtain ⟨G, hG⟩ := hK sk
  have h1 : ((x.1.value, x.1.hashCompressions), x.2) ∈
      support (roRun ((fun r => (r.value, r.hashCompressions)) <$> sub.run .keygen sk) ∅) := by
    rw [roRun_map, support_map]; exact ⟨x, hx, rfl⟩
  rw [hG, roRun_map, support_map] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  have hy' := mem_support_roRun_of_count _ _ _ y hy
  have := (spec_keygenRef sk).support (I := Inv0)
    (fun q hq => by unfold PK at hq; unfold Inv0; omega) ∅ (fun q u h => by simp at h) _ hy'
  have h2 : x.2 = y.2 := (congrArg Prod.snd hyx).symm
  rw [h2]; exact this.2

theorem keygen_bound (hK : KeygenRefines sub) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  rw [ev_withRandomOracle, honest_eq, roRun_bind, expectedValue_bind]
  calc expectedValue (roRun (sub.run .keygen sk) ∅) (fun x =>
        expectedValue (roRun (tailK sub sk m x.1) x.2) (fun y => ENNReal.ofReal
          (Real.rpow 2 ((y.1.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))))
      ≤ expectedValue (roRun (sub.run .keygen sk) ∅)
          (fun x => zOf (2 ^ 20) ^ x.1.hashCompressions) := by
        refine expectedValue_mono _ fun x => ?_
        apply ev_roRun_le_of_support (tailK sub sk m x.1) x.2 (fun r => ENNReal.ofReal
          (Real.rpow 2 ((r.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
        intro r hr
        rw [tailK_costs sub sk m x.1 r hr, show Phase.keygen.budget = 2 ^ 20 from rfl, costFun_eq]
    _ = V (zOf (2 ^ 20)) (keygenRef sk) ∅ := by
        rw [← ev_count_eq_V, ← keygen_count sub hK sk, roRun_map, expectedValue_map]
    _ ≤ 2 := V_keygenRef_le_two sk ∅

theorem sign_bound (hK : KeygenRefines sub) (hc : sub.sizes.cache = CACHE_BYTES)
    (hS : SignRefines sub hc) (sk : SecretKey)
    (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  rw [ev_withRandomOracle, honest_eq, roRun_bind, expectedValue_bind]
  refine expectedValue_le_of_support fun x hx => ?_
  have hinv := keygen_cacheInv sub hK sk x hx
  obtain ⟨k, c⟩ := x
  dsimp only at hinv ⊢
  unfold tailK
  split
  · next pk cache _ =>
    rw [roRun_bind, expectedValue_bind]
    calc expectedValue (roRun (sub.run .sign (sk, cache, m)) c) (fun y =>
          expectedValue (roRun (tailS sub m pk _ y.1) y.2) (fun w => ENNReal.ofReal
            (Real.rpow 2 ((w.1.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))))
        ≤ expectedValue (roRun (sub.run .sign (sk, cache, m)) c)
            (fun y => zOf (2 ^ 17) ^ y.1.hashCompressions) := by
          refine expectedValue_mono _ fun y => ?_
          apply ev_roRun_le_of_support (tailS sub m pk _ y.1) y.2 (fun r => ENNReal.ofReal
            (Real.rpow 2 ((r.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
          intro r hr
          rw [tailS_costs sub m pk _ y.1 r hr .sign (by decide) (by decide),
            show Phase.sign.budget = 2 ^ 17 from rfl]
          simp only [recordCost, if_true]
          rw [costFun_eq]
      _ = V (zOf (2 ^ 17)) (signRef sk (refCache hc cache) m) c := by
          rw [← ev_count_eq_V, ← hS sk cache m, roRun_map, expectedValue_map]
      _ ≤ 2 := V_signRef_le_two sk (refCache hc cache) m c hinv
  · simp only [roRun_pure, expectedValue_pure]
    simp only [recordCost, show Phase.sign ≠ Phase.keygen by decide, if_false]
    rw [ofReal_rpow_zero]; norm_num

/-- Expand costs at most as many compressions as sign on every path of the honest pipeline. -/
def ExpandBelowSign : Prop :=
  ∀ (f : Hash) (sk : SecretKey) (m : Message),
    (evalWithAnswerFn f (sub.honest sk m)).costs .expand ≤ (evalWithAnswerFn f (sub.honest sk m)).costs .sign

theorem zOf_mono {B B' : Nat} (hB : 0 < B') (h : B' ≤ B) : zOf B ≤ zOf B' := by
  unfold zOf
  refine ENNReal.ofReal_le_ofReal ?_
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h1 : (0 : ℝ) < B' := by exact_mod_cast hB
  have h2 : (B' : ℝ) ≤ B := by exact_mod_cast h
  exact one_div_le_one_div_of_le h1 h2

theorem expand_bound (hK : KeygenRefines sub) (hc : sub.sizes.cache = CACHE_BYTES)
    (hS : SignRefines sub hc) (hE : ExpandBelowSign sub) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  refine le_trans ?_ (sign_bound sub hK hc hS sk m)
  rw [ev_withRandomOracle, ev_withRandomOracle]
  refine expectedValue_mono_of_support fun x hx => ?_
  have hx1 := eval_cacheFn _ x hx
  have hle := hE (cacheFn x.2) sk m
  rw [hx1] at hle
  rw [show Phase.expand.budget = 2 ^ 20 from rfl, show Phase.sign.budget = 2 ^ 17 from rfl,
    costFun_eq, costFun_eq]
  calc zOf (2 ^ 20) ^ x.1.costs .expand ≤ zOf (2 ^ 20) ^ x.1.costs .sign :=
        pow_le_pow_right₀ (one_le_zOf _) hle
    _ ≤ zOf (2 ^ 17) ^ x.1.costs .sign :=
        pow_le_pow_left₀ (zero_le) (zOf_mono (by norm_num) (by norm_num)) _

/-- **Compression bounds** for any submission refining the reference spec. -/
theorem compressionBounds_of_refinement (hK : KeygenRefines sub)
    (hc : sub.sizes.cache = CACHE_BYTES) (hS : SignRefines sub hc)
    (hE : ExpandBelowSign sub) : sub.CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m => ?_
  simp only [Phase.budgeted, List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with rfl | rfl | rfl
  · exact keygen_bound sub hK sk m
  · exact sign_bound sub hK hc hS sk m
  · exact expand_bound sub hK hc hS hE sk m

end Phases

/-- The competition statement for `SigGolfCandidate.submission`, modulo the refinement facts. -/
theorem submission_compressionBounds_of_refines (hK : KeygenRefines submission)
    (hS : SignRefines submission rfl) (hE : ExpandBelowSign submission) :
    submission.CompressionBounds :=
  compressionBounds_of_refinement submission hK rfl hS hE

end SigGolfCandidate.Budget
