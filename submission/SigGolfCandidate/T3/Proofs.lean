import SigGolfCandidate.SphincsSecurity.Completeness.Search
import SigGolfCandidate.SphincsSecurity.Completeness.Octopus.Split
import SigGolfCandidate.T3.Core
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.SeedHitProbability
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.EvalDist.Monad.Disagreement
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Memoize
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Erasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.FiniteTable
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Presampling
import SigGolfCandidate.SphincsSecurity.Proof.Event.Erasure

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3
open OracleComp OracleSpec ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem digest_list_bytes_length (values : List Digest) :
    (values.flatMap (bytesLE 16)).length = 16 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.flatMap_cons,List.length_append,bytesLE_length,List.length_cons,ih]
      omega

theorem serializeLayer_length {lay : Layer} (sig : LayerSignature lay) :
    (serializeLayer sig).length = 16*(chainCount lay+height lay) := by
  simp only [serializeLayer,List.length_append,digest_list_bytes_length,List.length_ofFn]
  omega

theorem serialize_length (sig : Signature) : (serialize sig).length = 5728 := by
  simp only [serialize,List.length_append,bytesLE_length,digest_list_bytes_length,
    List.length_ofFn,List.length_flatten,List.map_ofFn,Function.comp_def]
  simp_rw [serializeLayer_length]
  decide

theorem cacheBytes_length (cache : Cache) : (cacheBytes cache).length = 32768 := by
  simp only [cacheBytes,List.length_append,bytesLE_length,List.length_ofFn]

theorem serializeLayer_injective (lay : Layer) : Function.Injective (@serializeLayer lay) := by
  rintro ⟨lv,lp⟩ ⟨rv,rp⟩ h
  simp only [serializeLayer] at h
  obtain ⟨hv,hp⟩ := List.append_inj h (by simp only [digest_list_bytes_length,List.length_ofFn])
  have hv := SphincsSecurity.flatMap_bytesLE_ofFn_injective hv
  have hp := SphincsSecurity.flatMap_bytesLE_ofFn_injective hp
  subst rv rp
  rfl

/-- Counter omission introduces no byte aliases: a compact signature contains
exactly the structural values whose freshness the source game records. -/
theorem serialize_injective : Function.Injective serialize := by
  rintro ⟨lr,ls,lp,ll⟩ ⟨rr,rs,rp,rl⟩ h
  simp only [serialize] at h
  obtain ⟨hhead,hlayers⟩ := List.append_inj h (by
    simp only [List.length_append,bytesLE_length,digest_list_bytes_length,List.length_ofFn])
  obtain ⟨hhead,hproof⟩ := List.append_inj hhead (by
    simp only [List.length_append,bytesLE_length,digest_list_bytes_length,List.length_ofFn])
  obtain ⟨hrho,hsecrets⟩ := List.append_inj hhead (by simp only [bytesLE_length])
  have hrho := bytesLE_injective hrho
  have hs := SphincsSecurity.flatMap_bytesLE_ofFn_injective hsecrets
  have hp := SphincsSecurity.flatMap_bytesLE_ofFn_injective hproof
  have hl := SphincsSecurity.length_flatten_ofFn_eq _ _
    (fun lay => by rw [serializeLayer_length,serializeLayer_length]) hlayers
  have hl' : ll=rl := funext fun lay => serializeLayer_injective lay (congrFun hl lay)
  subst rr rs rp rl
  rfl

theorem dataDigits_length (lay : Layer) (value : Digest) :
    (dataDigits lay value).length = dataCount lay := by simp [dataDigits]

theorem decode_length_sum {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value = some digits) :
    digits.length=chainCount lay ∧ digits.sum=target lay := by
  unfold decode at h
  split at h
  · simp at h
  · split at h
    · rename_i hl
      dsimp only at h
      split at h
      · rename_i hs
        have he := Option.some.inj h
        subst digits
        subst lay
        simpa [dataDigits_length,dataCount,chainCount] using And.intro (dataDigits_length 0 value) hs
      · simp at h
    · rename_i hl
      dsimp only at h
      split at h
      · rename_i hs
        have he := Option.some.inj h
        subst digits
        constructor
        · simp only [List.length_append,List.length_singleton,dataDigits_length]
          fin_cases lay <;> simp_all [dataCount,chainCount]
        · simp only [List.sum_append,List.sum_singleton]
          omega
      · simp at h

theorem route_leaf_bound (index : Nat) (lay : Layer) : (route index lay).1 < 2^height lay :=
  Nat.mod_lt _ (by positivity)

theorem route_top_tree (index : Nat) (hindex : index < 2^31) : (route index 0).2=0 := by
  exact Nat.div_eq_of_lt hindex

/-- Every retained-cache read is in the MAC-authenticated region without wrapping. -/
theorem topPath_offset_bound (leaf level byte : Nat) (hleaf : leaf<4096)
    (hlo : 2≤level) (hhi : level<12) (hb : byte<16) :
    16*(2048-2^(13-level)+(leaf/2^level ^^^ 1))+byte<32736 := by
  have hdiv : leaf/2^level < 2^(12-level) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity),← Nat.pow_add,Nat.sub_add_cancel (by omega)]
    exact hleaf
  have hsib := Nat.xor_lt_two_pow hdiv (Nat.one_lt_two_pow (by omega))
  interval_cases level <;> norm_num at hsib ⊢ <;> omega

theorem topPath_offset_mod (leaf level byte : Nat) (hleaf : leaf<4096)
    (hlo : 2≤level) (hhi : level<12) (hb : byte<16) :
    (16*(2048-2^(13-level)+(leaf/2^level ^^^ 1))+byte)%32736 =
      16*(2048-2^(13-level)+(leaf/2^level ^^^ 1))+byte :=
  Nat.mod_eq_of_lt (topPath_offset_bound leaf level byte hleaf hlo hhi hb)

@[simp] theorem privateInput_short (secret : BitVec 256) (h : BitVec 128) :
    privateInput secret (.inl h) =
      bytesLE 16 (secret.extractLsb' 0 128) ++ bytesLE 16 h ++
        bytesLE 16 (secret.extractLsb' 128 128) ++ zero16 := by
  simp [privateInput,pad64,bytesLE_length,zero16]

@[simp] theorem privateInput_nonce (secret : BitVec 256) (m : Message) :
    privateInput secret (.inr (.inl m)) =
      bytesLE 16 (secret.extractLsb' 0 128) ++ bytesLE 16 (header 7 0 0 0 0) ++
        bytesLE 16 (secret.extractLsb' 128 128) ++ zero16 ++ bytesLE 32 m ++ List.replicate 32 0 := by
  simp only [privateInput,pad64,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn]

@[simp] theorem privateInput_mac (secret : BitVec 256) (region : Region) :
    privateInput secret (.inr (.inr region)) =
      bytesLE 16 (secret.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
        bytesLE 16 (secret.extractLsb' 128 128) ++ zero16 ++ List.ofFn region ++ List.replicate 32 0 := by
  simp only [privateInput,pad64,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn]

theorem privateInput_injective (secret : BitVec 256) : Function.Injective (privateInput secret) := by
  rintro (left|left) (right|right) h
  · apply congrArg Sum.inl
    apply bytesLE_injective (n := 16)
    simpa only [privateInput_short,List.append_assoc,List.append_cancel_left_eq,
      List.append_cancel_right_eq] using h
  · have hl := congrArg List.length h
    cases right <;> simp only [privateInput_short,privateInput_nonce,privateInput_mac,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn] at hl
    all_goals omega
  · have hl := congrArg List.length h
    cases left <;> simp only [privateInput_short,privateInput_nonce,privateInput_mac,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn] at hl
    all_goals omega
  · apply congrArg Sum.inr
    rcases left with message|region <;> rcases right with message'|region'
    · apply congrArg Sum.inl
      apply bytesLE_injective (n := 32)
      simpa only [privateInput_nonce,List.append_assoc,List.append_cancel_left_eq,
        List.append_cancel_right_eq] using h
    · have hl := congrArg List.length h
      simp only [privateInput_short,privateInput_nonce,privateInput_mac,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn] at hl
      omega
    · have hl := congrArg List.length h
      simp only [privateInput_short,privateInput_nonce,privateInput_mac,List.length_append,bytesLE_length,zero16,List.length_replicate,List.length_ofFn] at hl
      omega
    · apply congrArg Sum.inr
      apply List.ofFn_injective
      simpa only [privateInput_mac,List.append_assoc,List.append_cancel_left_eq,
        List.append_cancel_right_eq] using h

end SigGolfCandidate.T3

namespace SigGolfCandidate.T3.FullSecret
open OracleComp OracleSpec ENNReal
open SphincsSecurity (MasterSeed OracleWorld sampleMasterSeed romImpl HashQueryBound)
open SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false

def Hit (input : HashInput) (secret : MasterSeed) : Prop :=
  input.take 16 = SphincsSecurity.bytesLE 16 (secret.extractLsb' 0 128) ∧
  (input.drop 32).take 16 = SphincsSecurity.bytesLE 16 (secret.extractLsb' 128 128)

def HitLog (inputs : List HashInput) (secret : MasterSeed) : Prop :=
  ∃ input ∈ inputs, Hit input secret

theorem hit_probability (input : HashInput) :
    Pr[Hit input | sampleMasterSeed] ≤ 1 / ((2 ^ 256 : Nat) : ENNReal) :=
by
  classical
  have hunique : ∀ a b, Hit input a → Hit input b → a=b := by
    intro a b ha hb
    apply SphincsSecurity.hashOutput_eq_of_extract (width := 128) (by decide)
    · exact SphincsSecurity.bytesLE_injective (ha.1.symm.trans hb.1)
    · exact SphincsSecurity.bytesLE_injective (ha.2.symm.trans hb.2)
  by_cases hexists : ∃ secret, Hit input secret
  · obtain ⟨secret,hsecret⟩ := hexists
    have hevent : Hit input = fun other => other=secret := by
      funext other
      exact propext ⟨fun h => hunique other secret h hsecret,fun h => h ▸ hsecret⟩
    rw [hevent]
    simp [sampleMasterSeed,MasterSeed]
  · have hevent : Hit input = fun _ => False := by
      funext secret
      exact propext ⟨fun h => hexists ⟨secret,h⟩,False.elim⟩
    rw [hevent]
    simp

theorem hitLog_probability (inputs : List HashInput) :
    Pr[HitLog inputs | sampleMasterSeed] ≤ inputs.length / ((2 ^ 256 : Nat) : ENNReal) := by
  induction inputs with
  | nil => simp [HitLog]
  | cons input inputs ih =>
    have hevent : HitLog (input :: inputs) = fun secret => Hit input secret ∨ HitLog inputs secret := by
      funext secret; simp [HitLog]
    rw [hevent]
    exact (probEvent_or_le _ _ _).trans ((add_le_add (hit_probability input) ih).trans_eq (by
      simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]))

open scoped Classical in
theorem adaptive_hit_probability {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : HashQueryBound computation cache q) :
    Pr[= none | sampleMasterSeed >>= fun secret =>
      (simulateQ romImpl (stopBefore (hashBad (fun input => Hit input secret)) computation)).run' cache] ≤
        q / ((2 ^ 256 : Nat) : ENNReal) := by
  classical
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun secret =>
        (fun result => decide (HitLog result.2 secret)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map,
        decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun secret => decide (HitLog result.2 secret)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (hitLog_probability result.2).trans
        (ENNReal.div_le_div
          (by exact_mod_cast traceHashes_length_le computation cache q hbound result hresult) le_rfl)

open scoped Classical in
theorem cache_change_bound {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ secret, AgreeOutside (fun input => Hit input secret) (initial secret) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun secret => (simulateQ romImpl computation).run' (initial secret)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] + q / ((2 ^ 256 : Nat) : ENNReal) := by
  classical
  let stopped := fun secret =>
    (simulateQ romImpl (stopBefore (hashBad (fun input => Hit input secret)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secret =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (fun input => Hit input secret)
          computation (initial secret) cache (hagree secret) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add
        (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (adaptive_hit_probability computation cache q hbound)

theorem exists_secret_not_hit (inputs : List HashInput) (hsize : inputs.length < 2 ^ 256) :
    ∃ secret, ¬HitLog inputs secret := by
  classical
  by_contra h
  have hall : ∀ secret, HitLog inputs secret := by simpa using h
  have hone : Pr[HitLog inputs | sampleMasterSeed] = 1 := by simp [hall]
  have hlt : (inputs.length : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) < 1 :=
    ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact_mod_cast hsize)
  exact (not_lt_of_ge (hone ▸ hitLog_probability inputs)) hlt

/-- Query bounds transfer too; erasing private queries never manufactures a
budget assumption about the ideal experiment. -/
theorem queryBound_of_secret_caches {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec)
    (cache : QueryCache HashSpec) (hsize : inputs.length + q < 2 ^ 256)
    (hagree : ∀ secret, ¬HitLog inputs secret →
      AgreeOutside (fun input => Hit input secret) (caches secret) cache)
    (hbound : ∀ secret, ¬HitLog inputs secret → HashQueryBound computation (caches secret) q) :
    HashQueryBound computation cache q := by
  induction computation using OracleComp.inductionOn generalizing q inputs caches cache with
  | pure value =>
    intro result hresult
    simp only [SphincsSecurity.countHashQueries_pure, simulateQ_pure, StateT.run'_eq,
      StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Nat.zero_le q
  | query_bind input next ih =>
    obtain ⟨secret, hsecret⟩ := exists_secret_not_hit inputs (by omega)
    obtain ⟨step, hstep⟩ := SphincsSecurity.probComp_support_nonempty ((romImpl input).run (caches secret))
    have hcost := (SphincsSecurity.hashQueryBound_query_bind input next (caches secret) q
      (hbound secret hsecret) step hstep).1
    apply hashQueryBound_query_bind_of input next cache q hcost
    intro result hresult
    have hcache := romImpl_support_cacheAfter input cache result hresult
    rcases result with ⟨answer, nextCache⟩
    dsimp at hcache
    subst nextCache
    have havoid (secret : MasterSeed) (hsecret : ¬HitLog (prependHash input inputs) secret) :
        ¬hashBad (fun input => Hit input secret) input ∧ ¬HitLog inputs secret := by
      change ¬TraceHits (fun input => Hit input secret) (prependHash input inputs) at hsecret
      rw [traceHits_prepend] at hsecret
      exact not_or.mp hsecret
    have htransfer (secret : MasterSeed) (hsecret : ¬HitLog (prependHash input inputs) secret) :=
      romImpl_support_transfer (fun input => Hit input secret) (caches secret) cache
        (hagree secret (havoid secret hsecret).2) input (havoid secret hsecret).1 answer hresult
    apply ih answer
      (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0))
      (prependHash input inputs) (fun secret => cacheAfter (caches secret) input answer)
      (cacheAfter cache input answer)
    · cases input <;> simp_all [prependHash]
    · intro secret hsecret; exact (htransfer secret hsecret).2
    · intro secret hsecret
      exact (SphincsSecurity.hashQueryBound_query_bind input next (caches secret) q
        (hbound secret (havoid secret hsecret).2) _ (htransfer secret hsecret).1).2

end SigGolfCandidate.T3.FullSecret

namespace SigGolfCandidate.T3.Derivation
open OracleComp OracleSpec ENNReal
open SphincsSecurity (MasterSeed OracleWorld sampleMasterSeed romImpl HashQueryBound)
open SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false

abbrev HashOutput := SphincsSecurity.HashOutput
abbrev HashSpec := SphincsSecurity.HashSpec

/-- Private coordinates may include attacker-chosen MAC regions and messages.
The program itself has no access to the master secret. -/
abbrev Spec (J : Type) := OracleWorld + (J →ₒ HashOutput)

def realHandler {J : Type} (inputs : J → HashInput) : QueryImpl (Spec J) (OracleComp OracleWorld)
  | .inl input => liftM (OracleWorld.query input)
  | .inr index => liftM (OracleWorld.query (.inr (inputs index)))

def tableHandler {J : Type} (outputs : J → HashOutput) : QueryImpl (Spec J) (OracleComp OracleWorld)
  | .inl input => liftM (OracleWorld.query input)
  | .inr index => pure (outputs index)

def realize {J α : Type} (inputs : J → HashInput) (program : OracleComp (Spec J) α) :
    OracleComp OracleWorld α := simulateQ (realHandler inputs) program

def tableRun {J α : Type} (outputs : J → HashOutput) (program : OracleComp (Spec J) α) :
    OracleComp OracleWorld α := simulateQ (tableHandler outputs) program

theorem erases {J α : Type} (inputs : J → HashInput) (outputs : J → HashOutput)
    (known : QueryCache HashSpec) (hknown : ∀ j, known (inputs j) = some (outputs j))
    (program : OracleComp (Spec J) α) :
    Erases (worldKnown known) (realize inputs program) (tableRun outputs program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
    simp only [realize, tableRun, simulateQ_bind, simulateQ_spec_query]
    cases input with
    | inl input => exact .query input _ _ ih
    | inr j =>
      change Erases _ (liftM (OracleWorld.query (.inr (inputs j))) >>= _)
        (pure (outputs j) >>= _)
      rw [pure_bind]
      exact Erases.skip (known := worldKnown known) (Sum.inr (inputs j))
        (outputs j) (hknown j) _ _ (ih (outputs j))

@[irreducible] noncomputable def outputSampler (J : Type) [Fintype J] : SampleableType (J → HashOutput) := by
  classical
  exact SampleableType.ofFintype _

variable {J : Type} [Fintype J]
noncomputable local instance : SampleableType (J → HashOutput) := outputSampler J

noncomputable def preparedCache (inputs : J → HashInput) (outputs : J → HashOutput) :
    QueryCache HashSpec := cacheTable ∅ inputs outputs

theorem preparedCache_agree (inputs : MasterSeed → J → HashInput)
    (hhit : ∀ secret j, FullSecret.Hit (inputs secret j) secret) (outputs : J → HashOutput)
    (secret : MasterSeed) :
    AgreeOutside (fun input => FullSecret.Hit input secret) (preparedCache (inputs secret) outputs) ∅ := by
  intro input hinput
  apply cacheTable_apply_of_not_mem
  intro j heq
  exact hinput (heq ▸ hhit secret j)

/-- Presampling is exact, including arbitrary repeated private requests.
Public queries are still answered by the same consistent random oracle. -/
theorem evalDist_realize {α : Type} (inputs : J → HashInput) (hinj : Function.Injective inputs)
    (program : OracleComp (Spec J) α) :
    𝒮[(simulateQ romImpl (realize inputs program)).run' ∅] =
      𝒮[do
        let outputs ← ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput))
        (simulateQ romImpl (tableRun outputs program)).run' (preparedCache inputs outputs)] := by
  let preparation : OracleComp OracleWorld (J → HashOutput) := liftM (queryTable (R := HashOutput) inputs)
  have hprep : (simulateQ romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := HashOutput) inputs)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
        (randomOracle (spec := HashSpec)) (queryTable (R := HashOutput) inputs))
  rw [evalDist_presample_computation (realize inputs program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := HashOutput) inputs hinj ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
  funext outputs
  have he := (erases inputs outputs (preparedCache inputs outputs)
    (cacheTable_apply ∅ inputs hinj outputs) program).evalDist_run
      (preparedCache inputs outputs) le_rfl
  simpa only [preparedCache, StateT.run'_eq, evalSPMF_map] using congrArg (Functor.map Prod.fst) he

/-- A concrete query bound implies the same bound after private-query erasure
from every programmed cache. -/
theorem prepared_queryBound {α : Type} (inputs : J → HashInput) (hinj : Function.Injective inputs)
    (program : OracleComp (Spec J) α) (q : Nat)
    (hbound : HashQueryBound (realize inputs program) ∅ q) (outputs : J → HashOutput) :
    HashQueryBound (tableRun outputs program) (preparedCache inputs outputs) q := by
  let preparation : OracleComp OracleWorld (J → HashOutput) := liftM (queryTable (R := HashOutput) inputs)
  have hprep : (simulateQ romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := HashOutput) inputs)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
        (randomOracle (spec := HashSpec)) (queryTable (R := HashOutput) inputs))
  have hsupport : (outputs, preparedCache inputs outputs) ∈
      support ((simulateQ romImpl preparation).run ∅) := by
    rw [hprep, mem_support_iff_of_evalSPMF_eq
      (evalDist_queryTable_fresh (R := HashOutput) inputs hinj ∅ (fun _ => rfl)), support_map]
    exact ⟨outputs, mem_support_uniformSample (J → HashOutput), rfl⟩
  exact (erases inputs outputs (preparedCache inputs outputs)
    (cacheTable_apply ∅ inputs hinj outputs) program).hashQueryBound
      (preparedCache inputs outputs) le_rfl q
      (hashQueryBound_after_preparation _ preparation ∅ q hbound _ hsupport)

/-- One global reduction for all secret-bearing domains, with query-bound
transfer proved from the real experiment. This quantifies over the whole
adaptive program, so it includes malicious caches and repeated requests. -/
theorem game_hop {α : Type} (inputs : MasterSeed → J → HashInput)
    (hinj : ∀ secret, Function.Injective (inputs secret))
    (hhit : ∀ secret j, FullSecret.Hit (inputs secret j) secret)
    (program : OracleComp (Spec J) α) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : ∀ secret, HashQueryBound (realize (inputs secret) program) ∅ q)
    (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun secret =>
        (simulateQ romImpl (realize (inputs secret) program)).run' ∅] ≤
      Pr[event | ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput)) >>= fun outputs =>
        (simulateQ romImpl (tableRun outputs program)).run' ∅] +
          q / ((2 ^ 256 : Nat) : ENNReal) := by
  have htable (outputs : J → HashOutput) : HashQueryBound (tableRun outputs program) ∅ q := by
    apply FullSecret.queryBound_of_secret_caches (tableRun outputs program) q []
      (fun secret => preparedCache (inputs secret) outputs) ∅ (by simpa using hq)
    · intro secret _; exact preparedCache_agree inputs hhit outputs secret
    · intro secret _; exact prepared_queryBound _ (hinj secret) program q (hbound secret) outputs
  calc
    _ = Pr[event | sampleMasterSeed >>= fun secret => do
        let outputs ← ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput))
        (simulateQ romImpl (tableRun outputs program)).run' (preparedCache (inputs secret) outputs)] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalSPMF_bind_congr' _ (fun secret => evalDist_realize _ (hinj secret) program)
    _ = Pr[event | ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput)) >>= fun outputs =>
        sampleMasterSeed >>= fun secret =>
        (simulateQ romImpl (tableRun outputs program)).run' (preparedCache (inputs secret) outputs)] :=
      probEvent_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      calc
        _ ≤ ∑' outputs, Pr[= outputs | ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput))] *
            (Pr[event | (simulateQ romImpl (tableRun outputs program)).run' ∅] +
              q / ((2 ^ 256 : Nat) : ENNReal)) := by
          exact ENNReal.tsum_le_tsum fun outputs => mul_le_mul' le_rfl
            (FullSecret.cache_change_bound (tableRun outputs program)
              (fun secret => preparedCache (inputs secret) outputs) ∅
              (preparedCache_agree inputs hhit outputs) q (htable outputs) event)
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
          rw [tsum_probOutput_eq_sub]
          simp

end SigGolfCandidate.T3.Derivation
namespace SigGolfCandidate.T3.Derivation
open OracleComp OracleSpec ENNReal
open SphincsSecurity (MasterSeed OracleWorld sampleMasterSeed romImpl HashQueryBound)
open SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false

def charged {J : Type} : (Spec J).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True

instance {J : Type} : DecidablePred (charged (J := J)) := fun input => by
  rcases input with (sample | hash) | privateInput <;> dsimp [charged] <;> infer_instance

noncomputable def cap {J α : Type} (program : OracleComp (Spec J) α) (q : Nat) :=
  SphincsSecurity.QueryCap.run charged program q

theorem realize_cap {J α : Type} (inputs : J → HashInput) (program : OracleComp (Spec J) α) (q : Nat) :
    realize inputs (cap program q) =
      SphincsSecurity.QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _)
        (realize inputs program) q := by
  induction program using OracleComp.inductionOn generalizing q with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [cap, SphincsSecurity.QueryCap.run_query_bind, realize,
      simulateQ_bind, simulateQ_spec_query]
    rcases input with (sample | hash) | privateInput
    · simp only [charged, if_false, realHandler, SphincsSecurity.QueryCap.run_query_bind]
      exact congrArg (fun k => liftM (OracleWorld.query (.inl sample)) >>= k) (funext fun answer => ih answer q)
    · cases q <;>
        simp only [charged, if_true, realHandler, SphincsSecurity.QueryCap.run_query_bind,
          simulateQ_pure, simulateQ_bind, simulateQ_spec_query]
      rename_i q
      exact congrArg (fun k => liftM (OracleWorld.query (.inr hash)) >>= k) (funext fun answer => ih answer q)
    · cases q <;>
        simp only [charged, if_true, realHandler, SphincsSecurity.QueryCap.run_query_bind,
          simulateQ_pure, simulateQ_bind, simulateQ_spec_query]
      rename_i q
      exact congrArg (fun k => liftM (OracleWorld.query (.inr (inputs privateInput))) >>= k)
        (funext fun answer => ih answer q)

variable {J : Type} [Fintype J]
noncomputable local instance : SampleableType (J → HashOutput) := outputSampler J

/-- The event form required by the competition: no global bound is assumed
on the adversary. The cap counts private calls and public hash calls, and
preserves precisely the successful runs that use at most `q` calls. -/
theorem event_game_hop {α : Type} (inputs : MasterSeed → J → HashInput)
    (hinj : ∀ secret, Function.Injective (inputs secret))
    (hhit : ∀ secret j, FullSecret.Hit (inputs secret j) secret)
    (program : OracleComp (Spec J) α) (q : Nat) (hq : q < 2 ^ 256) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ q | sampleMasterSeed >>= fun secret =>
        (simulateQ romImpl (SphincsSecurity.countHashQueries (realize (inputs secret) program))).run' ∅] ≤
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 |
        ($ᵗ (J → HashOutput) : ProbComp (J → HashOutput)) >>= fun outputs =>
          (simulateQ romImpl (tableRun outputs (cap program q))).run' ∅] +
        q / ((2 ^ 256 : Nat) : ENNReal) := by
  have heq : Pr[fun result => event result.1 ∧ result.2 ≤ q | sampleMasterSeed >>= fun secret =>
        (simulateQ romImpl (SphincsSecurity.countHashQueries (realize (inputs secret) program))).run' ∅] =
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 |
        sampleMasterSeed >>= fun secret =>
          (simulateQ romImpl (realize (inputs secret) (cap program q))).run' ∅] := by
    simp only [probEvent_bind_eq_tsum, realize_cap]
    exact tsum_congr fun secret => congrArg _ (romRun_cap_event _ ∅ q event)
  rw [heq]
  apply game_hop inputs hinj hhit (cap program q) q hq
  intro secret
  rw [realize_cap]
  exact hashQueryBound_cap _ ∅ q

end SigGolfCandidate.T3.Derivation

namespace SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
@[irreducible] noncomputable def coordinateFintype : Fintype Coordinate := by
  classical
  exact inferInstance

theorem private_hit_serialization (secret : BitVec 256) (headBlock suffix : HashInput)
    (hlen : headBlock.length=16) :
    FullSecret.Hit (bytesLE 16 (secret.extractLsb' 0 128) ++ headBlock ++
      bytesLE 16 (secret.extractLsb' 128 128) ++ suffix) secret := by
  constructor
  · simp only [List.append_assoc,List.take_append,bytesLE_length,Nat.sub_self,
      List.take_zero,List.append_nil,Nat.zero_sub,List.nil_append]
    exact List.take_of_length_le (by rw [bytesLE_length])
  · rw [show (bytesLE 16 (secret.extractLsb' 0 128) ++ headBlock ++
        bytesLE 16 (secret.extractLsb' 128 128) ++ suffix).drop 32 =
          bytesLE 16 (secret.extractLsb' 128 128) ++ suffix from by
        rw [List.append_assoc (bytesLE 16 (secret.extractLsb' 0 128) ++ headBlock)]
        have hp : (bytesLE 16 (secret.extractLsb' 0 128) ++ headBlock).length=32 := by
          simp only [List.length_append,bytesLE_length,hlen]
        rw [← hp,List.drop_left]]
    simp only [List.take_append,bytesLE_length,Nat.sub_self,List.take_zero,List.append_nil]
    exact List.take_of_length_le (by rw [bytesLE_length])

theorem privateInput_hit (secret : BitVec 256) (coordinate : Coordinate) :
    FullSecret.Hit (privateInput secret coordinate) secret := by
  rcases coordinate with tweak|message|region
  · rw [privateInput_short]
    exact private_hit_serialization secret (bytesLE 16 tweak) zero16 (bytesLE_length _ _)
  · rw [privateInput_nonce]
    rw [List.append_assoc _ zero16 (bytesLE 32 message),
      List.append_assoc _ (zero16 ++ bytesLE 32 message) (List.replicate 32 0)]
    exact private_hit_serialization secret (bytesLE 16 (header 7 0 0 0 0))
      (zero16 ++ bytesLE 32 message ++ List.replicate 32 0) (bytesLE_length _ _)
  · rw [privateInput_mac]
    rw [List.append_assoc _ zero16 (List.ofFn region),
      List.append_assoc _ (zero16 ++ List.ofFn region) (List.replicate 32 0)]
    exact private_hit_serialization secret (bytesLE 16 (header 14 0 0 0 0))
      (zero16 ++ List.ofFn region ++ List.replicate 32 0) (bytesLE_length _ _)

namespace Security
open OracleComp OracleSpec ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

structure Request where
  message : Message
  cache : Cache

inductive Forgery where
  | witness (message : Message) (witness : Witness)
  | signature (message : Message) (signature : Signature)

abbrev Requests := Request →ₒ Option Signature
abbrev Adversary := Digest → Cache → OracleComp (OracleWorld + Requests) (Option Forgery)

def forwardWorld : QueryImpl OracleWorld M := fun input => Spec.query (.inl input)

def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M) :=
  QueryImpl.withLogging fun request => liftM (sign request.cache request.message)

/-- Both organizer forgery forms. Failed signing responses do not enter the
freshness relation, but still count toward the lifetime limit. -/
noncomputable def checkForgery (publicKey : Digest) (log : QueryLog Requests) : Forgery → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message witness =>
        let verified ← verify message publicKey witness
        pure (decide (¬∃ entry ∈ log, entry.1.message=message ∧ entry.2.isSome=true) && verified)
    | .signature message signature =>
        let witness ← expand message publicKey signature
        let some witness := witness | return false
        let verified ← verify message publicKey witness
        pure (decide (¬∃ entry ∈ log, entry.1.message=message ∧ entry.2=some signature) && verified)

noncomputable def game (adversary : Adversary) : M Bool := do
    let (publicKey, cache) ← keygen
    let (forgery, log) ← (simulateQ
      ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
        signingOracle) (adversary publicKey cache)).run
    let some forgery := forgery | return false
    let verified ← checkForgery publicKey log forgery
    pure (decide (log.length ≤ 2^32) && verified)

noncomputable def realExperiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (Derivation.realize (privateInput secret) (game adversary)))).run' ∅

noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType (Coordinate → Derivation.HashOutput) :=
  Derivation.outputSampler Coordinate

noncomputable def tableExperiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option (Bool × Nat)) :=
  ($ᵗ (Coordinate → Derivation.HashOutput) : ProbComp _) >>= fun outputs =>
    (simulateQ romImpl (Derivation.tableRun outputs (Derivation.cap (game adversary) q))).run' ∅

/-- All secret-dependent calls are replaced together; no adversary-wide
query assumption or authenticated-cache assumption is required. -/
theorem private_derivation_event_bound (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun outcome => ∃ result, outcome=some result ∧ result.1=true |
        tableExperiment adversary q] + q / ((2^256 : Nat) : ENNReal) := by
  classical
  exact Derivation.event_game_hop privateInput privateInput_injective
    privateInput_hit (game adversary) q hq (· = true)

end Security
end SigGolfCandidate.T3

namespace SigGolfCandidate.T3.MixedCode
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure Code where
  n : Nat
  width : Fin n → Nat
  target : Nat

abbrev Encoding (code : Code) := (i : Fin code.n) → Fin (2 ^ code.width i)
variable {code : Code}

def digitSum (word : Encoding code) : Nat := ∑ i, (word i).val

def Valid (word : Encoding code) : Prop := digitSum word = code.target

instance validDecidable (word : Encoding code) : Decidable (Valid word) :=
  inferInstanceAs (Decidable (digitSum word = code.target))

/-- Two valid words cannot be ordered componentwise unless they are equal: walking chains forward from a revealed word never reaches another valid word. -/
theorem eq_of_le_of_valid {x y : (Encoding code)} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  simp only [Valid] at hx hy
  have hsum : digitSum x = digitSum y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : digitSum x < digitSum y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

/-! ### Unit neighbors

A valid word one backward step below the reference at one chain and nowhere else below it. This is the only way a forgery can reuse a one-time key with a single inverted chain step. -/

def UnitNeighborAt (reference candidate : (Encoding code)) (lowered : (Fin code.n)) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val

theorem UnitNeighborAt.ne {reference candidate : (Encoding code)} {lowered : (Fin code.n)}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega

theorem UnitNeighborAt.lowered_unique {reference candidate : (Encoding code)} {left right : (Fin code.n)}
    (hleft : UnitNeighborAt reference candidate left) (hright : UnitNeighborAt reference candidate right) : left = right := by
  by_contra hne
  have hle := hleft.2.2.2 right (Ne.symm hne)
  have hd := hright.2.2.1
  omega

noncomputable def unitNeighbors (reference : (Encoding code)) (lowered : (Fin code.n)) : Finset (Encoding code) :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

theorem mem_unitNeighbors {reference candidate : (Encoding code)} {lowered : (Fin code.n)} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def allUnitNeighbors (reference : (Encoding code)) : Finset (Encoding code) :=
  Finset.univ.biUnion (unitNeighbors reference)

theorem mem_allUnitNeighbors {reference candidate : (Encoding code)} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

private theorem two_terms_le_sum (f : (Fin code.n) → Nat) {left right : (Fin code.n)} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset (Fin code.n)))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

private theorem single_of_sum_one (f : (Fin code.n) → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, fun other hne => ?_⟩
  have hpair := two_terms_le_sum f hne
  omega

/-- For the target-sum code a unit neighbor moves exactly one step from the lowered chain to one other chain. -/
private theorem UnitNeighborAt.raised {reference candidate : (Encoding code)} {lowered : (Fin code.n)}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ raised, raised ≠ lowered ∧ (reference raised).val + 1 = (candidate raised).val ∧
      ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index := by
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  simp only [Valid] at hreference hcandidate
  have hpoint : ∀ index : (Fin code.n),
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val := fun index => by omega
  have hsum := congrArg (fun f : (Fin code.n) → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, ((reference index).val - (candidate index).val) = 1 := by
    rw [Finset.sum_eq_single lowered]
    · omega
    · intro index _ hne
      have := hup index hne
      omega
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change _ + digitSum candidate = _ + digitSum reference at hsum
  have hsums : digitSum candidate = digitSum reference := hcandidate.trans hreference.symm
  have hforward : ∑ index, ((candidate index).val - (reference index).val) = 1 := by omega
  obtain ⟨raised, hraise, hothers⟩ := single_of_sum_one _ hforward
  refine ⟨raised, fun he => ?_, by omega, fun index hl hr => ?_⟩
  · subst raised
    omega
  · have hdown := hothers index hr
    have hle := hup index hl
    apply Fin.ext
    omega

theorem unitNeighbors_card_le (reference : (Encoding code)) (lowered : (Fin code.n)) :
    (unitNeighbors reference lowered).card ≤ (code.n - 1) := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} → {raised : (Fin code.n) // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.raised.choose, candidate.property.raised.choose_spec.1⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' : left.property.raised.choose = right.property.raised.choose := congrArg Subtype.val he
    obtain ⟨_, hup, hrest⟩ := left.property.raised.choose_spec
    obtain ⟨_, hup', hrest'⟩ := right.property.raised.choose_spec
    rw [he'] at hup hrest
    funext index
    by_cases hl : index = lowered
    · subst index
      apply Fin.ext
      have := left.property.2.2.1
      have := right.property.2.2.1
      omega
    · by_cases hr : index = right.property.raised.choose
      · subst index
        apply Fin.ext
        omega
      · exact (hrest index hl hr).trans (hrest' index hl hr).symm
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : (Fin code.n) => raised ≠ lowered) = Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ, Fintype.card_fin] at hcard
  simpa only [unitNeighbors] using hcard

theorem allUnitNeighbors_card_le (reference : (Encoding code)) : (allUnitNeighbors reference).card ≤ (code.n * (code.n - 1)) := by
  calc
    _ ≤ ∑ lowered : (Fin code.n), (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : (Fin code.n), (code.n - 1) :=
      Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = (code.n * (code.n - 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]


end SigGolfCandidate.T3.MixedCode

namespace SigGolfCandidate.T3
open OracleComp OracleSpec ENNReal
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def code (lay : Layer) : MixedCode.Code where
  n := chainCount lay
  width i := width lay i.val
  target := target lay

abbrev Encoding (lay : Layer) := MixedCode.Encoding (code lay)
abbrev ChainIndex (lay : Layer) := Fin (chainCount lay)

theorem chainCount_bound (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide

theorem unit_neighbors_bound (lay : Layer) (word : Encoding lay) (i : ChainIndex lay) :
    (MixedCode.unitNeighbors word i).card ≤ 57 :=
  (MixedCode.unitNeighbors_card_le word i).trans (Nat.sub_le_sub_right (chainCount_bound lay) 1)

theorem all_neighbors_bound (lay : Layer) (word : Encoding lay) :
    (MixedCode.allUnitNeighbors word).card ≤ 3306 := by
  refine (MixedCode.allUnitNeighbors_card_le word).trans ?_
  exact Nat.mul_le_mul (chainCount_bound lay) (Nat.sub_le_sub_right (chainCount_bound lay) 1)

def digitOffset (lay : Layer) (i : Nat) : Nat :=
  if lay=0 then (if i<49 then 2*i else 98+3*(i-49)) else 3*i

theorem dataDigits_getD (lay : Layer) (value : Digest) (i : Nat) (hi : i<dataCount lay) :
    (dataDigits lay value).getD i 0 = value.toNat / 2^digitOffset lay i % 2^width lay i := by
  simp [dataDigits,digitOffset,List.getD_eq_getElem,hi]

theorem decode_data {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) :
    value.toNat<2^encodedBits lay ∧ digits.take (dataCount lay)=dataDigits lay value := by
  unfold decode at h
  split at h
  · simp at h
  · rename_i hbits
    constructor
    · omega
    · split at h <;> dsimp only at h <;> split at h
      · have he := Option.some.inj h
        subst digits
        exact List.take_of_length_le (by rw [dataDigits_length])
      · simp at h
      · have he := Option.some.inj h
        subst digits
        rw [← dataDigits_length lay value,List.take_left]
      · simp at h

theorem decode_digit_bound {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) (i : Nat) (hi : i<chainCount lay) :
    digits.getD i 0 < 2^width lay i := by
  unfold decode at h
  split at h
  · simp at h
  · split at h <;> dsimp only at h <;> split at h
    · rename_i hbits hl hs
      have he := Option.some.inj h
      subst digits
      have hdata : i<dataCount lay := by subst lay; exact hi
      rw [dataDigits_getD lay value i hdata]
      exact Nat.mod_lt _ (by positivity)
    · simp at h
    · rename_i hbits hl hs
      have he := Option.some.inj h
      subst digits
      by_cases hid : i<dataCount lay
      · rw [List.getD_append _ _ _ _ (by simpa only [dataDigits_length] using hid),dataDigits_getD lay value i hid]
        exact Nat.mod_lt _ (by positivity)
      · have hieq : i=dataCount lay := by
          fin_cases lay <;> simp_all [dataCount,chainCount] <;> omega
        subst i
        rw [← dataDigits_length lay value,List.getD_append_right _ _ _ _ (by omega)]
        simpa only [Nat.sub_self,List.getD_cons_zero,width,hl,false_and,ite_false,show (2:Nat)^3=8 by decide] using hs.2
    · simp at h


def decodedWord {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) : Encoding lay := fun i =>
  ⟨digits.getD i.val 0,decode_digit_bound h i.val i.isLt⟩

theorem decodedWord_list {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) :
    (List.ofFn fun i => (decodedWord h i).val)=digits := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn,code] using (decode_length_sum h).1.symm
  · intro i hleft hright
    simp only [List.getElem_ofFn,decodedWord,List.getD_eq_getElem _ _ hright]

theorem decodedWord_valid {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) : MixedCode.Valid (decodedWord h) := by
  change (∑ i, (decodedWord h i).val)=target lay
  rw [← List.sum_ofFn,decodedWord_list h]
  exact (decode_length_sum h).2

/-- The list-valued source decoder inherits the target-sum antichain theorem. -/
theorem decode_antichain {lay : Layer} {left right : Digest} {xs ys : List Nat}
    (hx : decode lay left=some xs) (hy : decode lay right=some ys)
    (hle : ∀ i, i<chainCount lay → xs.getD i 0 ≤ ys.getD i 0) : xs=ys := by
  have he := MixedCode.eq_of_le_of_valid (decodedWord_valid hx) (decodedWord_valid hy)
    (fun i => hle i.val i.isLt)
  rw [← decodedWord_list hx,← decodedWord_list hy,he]

theorem encodedBits_lt (lay : Layer) : encodedBits lay<128 := by fin_cases lay <;> decide

theorem digest_eq_of_dataDigits_eq {lay : Layer} {left right : Digest}
    (h : dataDigits lay left=dataDigits lay right)
    (hl : left.toNat<2^encodedBits lay) (hr : right.toNat<2^encodedBits lay) : left=right := by
  have hextract (i : Nat) (hi : i<dataCount lay) :
      left.extractLsb' (digitOffset lay i) (width lay i)=
        right.extractLsb' (digitOffset lay i) (width lay i) := by
    apply BitVec.eq_of_toNat_eq
    simpa only [dataDigits_getD lay left i hi,dataDigits_getD lay right i hi,
      BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow] using
      congrArg (fun xs : List Nat => xs.getD i 0) h
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  by_cases hb : bit<encodedBits lay
  · by_cases ht : lay=0
    · subst lay
      by_cases hsmall : bit<98
      · have hd := hextract (bit/2) (by simp [dataCount]; omega)
        have hw : width 0 (bit/2)=2 := by simp [width];omega
        have ho : digitOffset 0 (bit/2)=2*(bit/2) := by simp [digitOffset];omega
        rw [hw] at hd
        have he := congrArg (fun d : BitVec 2 => d.getLsbD (bit%2)) hd
        simpa only [ho,BitVec.getLsbD_extractLsb',show bit%2<2 by omega,decide_true,
          Bool.true_and,show 2*(bit/2)+bit%2=bit by omega] using he
      · have hi : 49+(bit-98)/3<58 := by simp [encodedBits] at hb;omega
        have hd := hextract (49+(bit-98)/3) (by simpa [dataCount] using hi)
        have hw : width 0 (49+(bit-98)/3)=3 := by simp [width]
        have ho : digitOffset 0 (49+(bit-98)/3)=98+3*((bit-98)/3) := by simp [digitOffset]
        rw [hw] at hd
        have he := congrArg (fun d : BitVec 3 => d.getLsbD ((bit-98)%3)) hd
        simpa only [ho,BitVec.getLsbD_extractLsb',show (bit-98)%3<3 by omega,decide_true,
          Bool.true_and,show 98+3*((bit-98)/3)+(bit-98)%3=bit by omega] using he
    · have hi : bit/3<dataCount lay := by simp [encodedBits,ht] at hb;simp [dataCount,ht];omega
      have hd := hextract (bit/3) hi
      have hw : width lay (bit/3)=3 := by simp [width,ht]
      have ho : digitOffset lay (bit/3)=3*(bit/3) := by simp [digitOffset,ht]
      rw [hw] at hd
      have he := congrArg (fun d : BitVec 3 => d.getLsbD (bit%3)) hd
      simpa only [ho,BitVec.getLsbD_extractLsb',show bit%3<3 by omega,decide_true,
        Bool.true_and,show 3*(bit/3)+bit%3=bit by omega] using he
  · have hleft := (BitVec.toNat_lt_iff_getLsbD_eq_false (encodedBits lay) (encodedBits_lt lay)).mp hl
    have hright := (BitVec.toNat_lt_iff_getLsbD_eq_false (encodedBits lay) (encodedBits_lt lay)).mp hr
    have hbit : encodedBits lay+(bit-encodedBits lay)=bit := by omega
    simpa only [hbit] using (hleft (bit-encodedBits lay)).trans (hright (bit-encodedBits lay)).symm

theorem decode_some_injective {lay : Layer} {left right : Digest} {word : List Nat}
    (hl : decode lay left=some word) (hr : decode lay right=some word) : left=right := by
  have hdleft := decode_data hl
  have hdright := decode_data hr
  exact digest_eq_of_dataDigits_eq (hdleft.2.symm.trans hdright.2) hdleft.1 hdright.1

/-- A particular valid mixed/checksum word has at most one digest preimage. -/
theorem decode_probability_le (lay : Layer) (word : List Nat) :
    Pr[fun digest => decode lay digest=some word | ($ᵗ Digest : ProbComp Digest)] ≤
      1/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  have hcard : (Finset.univ.filter fun digest => decode lay digest=some word).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact decode_some_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast hcard


/-- No field of the 16-byte public tweak overflows into another field. -/
theorem header_toNat (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat =
      1+tag%256*2^8+lay%256*2^16+(tree/2^32%256)*2^24+
        (if packedNodeTag tag then tree%2^32*2^32+index%2^32*2^64+position%2^32*2^96
         else position%2^32*2^32+tree%2^32*2^64+index%2^32*2^96) := by
  unfold header
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have ht := Nat.mod_lt tag (by decide : 0<256)
  have hl := Nat.mod_lt lay (by decide : 0<256)
  have hth := Nat.mod_lt (tree/2^32) (by decide : 0<256)
  have hp := Nat.mod_lt position (by decide : 0<2^32)
  have htl := Nat.mod_lt tree (by decide : 0<2^32)
  have hi := Nat.mod_lt index (by decide : 0<2^32)
  split <;> norm_num only [Nat.reducePow] at * <;> omega

theorem pack_nat_injective {a a' b b' base : Nat} (ha : a<base) (ha' : a'<base)
    (he : a+base*b=a'+base*b') : a=a' ∧ b=b' := by
  have haeq := congrArg (fun n => n%base) he
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt ha'] at haeq
  subst a'
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt ha) (Nat.add_left_cancel he)⟩

theorem header_injective {tag lay tree position index tag' lay' tree' position' index' : Nat}
    (ht : tag<256) (hl : lay<256) (htr : tree<2^40) (hp : position<2^32) (hi : index<2^32)
    (ht' : tag'<256) (hl' : lay'<256) (htr' : tree'<2^40) (hp' : position'<2^32) (hi' : index'<2^32)
    (h : header tag lay tree position index=header tag' lay' tree' position' index') :
    tag=tag' ∧ lay=lay' ∧ tree=tree' ∧ position=position' ∧ index=index' := by
  have hh : tree/2^32<256 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num at htr ⊢;exact htr)
  have hh' : tree'/2^32<256 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num at htr' ⊢;exact htr')
  have he := (header_toNat tag lay tree position index).symm.trans
    ((congrArg (fun x : BitVec 128 => x.toNat) h).trans (header_toNat tag' lay' tree' position' index'))
  simp only [Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt ht',Nat.mod_eq_of_lt hl',Nat.mod_eq_of_lt hp',Nat.mod_eq_of_lt hi',
    Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt hh'] at he
  have htag : tag = tag' := by
    split_ifs at he <;> norm_num only [Nat.reducePow] at * <;> omega
  subst tag'
  by_cases hpack : packedNodeTag tag
  · simp only [if_pos hpack] at he
    have hpacked : lay+256*(tree/2^32+256*(tree%2^32+2^32*(index+2^32*position))) =
        lay'+256*(tree'/2^32+256*(tree'%2^32+2^32*(index'+2^32*position'))) := by
      norm_num only [Nat.reducePow] at he ⊢
      omega
    obtain ⟨hlay,hpacked⟩ := pack_nat_injective hl hl' hpacked
    obtain ⟨hhigh,hpacked⟩ := pack_nat_injective hh hh' hpacked
    obtain ⟨hlow,hpacked⟩ := pack_nat_injective (Nat.mod_lt tree (by positivity))
      (Nat.mod_lt tree' (by positivity)) hpacked
    obtain ⟨hindex,hposition⟩ := pack_nat_injective hi hi' hpacked
    exact ⟨rfl,hlay,by omega,hposition,hindex⟩
  · simp only [if_neg hpack] at he
    have hpacked : lay+256*(tree/2^32+256*(position+2^32*(tree%2^32+2^32*index))) =
        lay'+256*(tree'/2^32+256*(position'+2^32*(tree'%2^32+2^32*index'))) := by
      norm_num only [Nat.reducePow] at he ⊢
      omega
    obtain ⟨hlay,hpacked⟩ := pack_nat_injective hl hl' hpacked
    obtain ⟨hhigh,hpacked⟩ := pack_nat_injective hh hh' hpacked
    obtain ⟨hposition,hpacked⟩ := pack_nat_injective hp hp' hpacked
    obtain ⟨hlow,hindex⟩ := pack_nat_injective (Nat.mod_lt tree (by positivity))
      (Nat.mod_lt tree' (by positivity)) hpacked
    exact ⟨rfl,hlay,by omega,hposition,hindex⟩

open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)

theorem digestInput_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : BitVec 32}
    (h : digestInput rho message counter=digestInput rho' message' counter') :
    rho=rho' ∧ message=message' ∧ counter=counter' := by
  unfold digestInput at h
  obtain ⟨hhead,hm⟩ := List.append_inj h (by simp only [List.length_append,bytesLE_length])
  obtain ⟨hr,hh⟩ := List.append_inj hhead (by simp only [bytesLE_length])
  have ht := header_injective (by decide : 12<256) (by decide : 0<256)
    (by decide : 0<2^40) (by decide : 0<2^32) counter.isLt
    (by decide : 12<256) (by decide : 0<256)
    (by decide : 0<2^40) (by decide : 0<2^32) counter'.isLt (bytesLE_injective hh)
  exact ⟨bytesLE_injective hr,bytesLE_injective hm,BitVec.eq_of_toNat_eq ht.2.2.2.2⟩

/-- Admissibility tests only the within-bucket leaves. Rejection sampling does
not inspect the index or bucket bits of a fresh digest. -/
theorem admissible_bucket_map (chosen : List Selection) (f : Selection → Nat) :
    admissible (chosen.map fun s => {s with bucket := f s})=admissible chosen := by
  simp only [admissible,List.all_map,List.map_map,Function.comp_def]

theorem selections_length (output : HashOutput) : (selections output).length=7 := by
  simp only [selections,List.length_map,List.length_range]

theorem selection_leaves_length (output : HashOutput) (selected : Selection)
    (h : selected ∈ selections output) : selected.leaves.length=3 := by
  simp only [selections,List.mem_map] at h
  obtain ⟨i,_,rfl⟩ := h
  simp only [List.length_mergeSort,List.length_map,List.length_range]

theorem selection_bucket_bound (output : HashOutput) (selected : Selection)
    (h : selected ∈ selections output) : selected.bucket<16 := by
  simp only [selections,List.mem_map] at h
  obtain ⟨i,_,rfl⟩ := h
  exact Nat.mod_lt _ (by decide)

theorem selection_leaf_bound (output : HashOutput) (selected : Selection) (leaf : Nat)
    (h : selected ∈ selections output) (hl : leaf ∈ selected.leaves) : leaf<128 := by
  simp only [selections,List.mem_map] at h
  obtain ⟨i,_,rfl⟩ := h
  simp only [List.mem_mergeSort,List.mem_map] at hl
  obtain ⟨j,_,rfl⟩ := hl
  exact Nat.mod_lt _ (by decide)


end SigGolfCandidate.T3


namespace SigGolfCandidate.T3.Cost
open OracleComp OracleSpec Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

abbrev Query := T3.Spec.Domain

def weight : Query → Nat
  | .inl (.inl _) => 0
  | .inl (.inr input) => input.length/64
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 513

abbrev qry (q : Query) : M (T3.Spec.Range q) := T3.Spec.query q

inductive Bound (P : Query → Prop) {α : Type} (Post : α → Prop) :
    Nat → M α → Prop
  | pure (a : α) (k : Nat) : Post a → Bound P Post k (pure a)
  | query (q : Query) (f : T3.Spec.Range q → M α) (k : Nat) :
      P q → (∀ u, Bound P Post k (f u)) → Bound P Post (weight q + k) (qry q >>= f)

namespace Bound

variable {P : Query → Prop} {α β : Type}

theorem mono_k {Post : α → Prop} {k k' : Nat} {oa : M α}
    (h : Bound P Post k oa) (hk : k  ≤  k') : Bound P Post k' oa := by
  induction h generalizing k' with
  | pure a k hp => exact .pure a k' hp
  | query q f k hq _ ih =>
    have : k' = weight q + (k' - weight q) := by omega
    rw [this]
    exact .query q f _ hq fun u => ih u (by omega)

theorem mono {P' : Query → Prop} {Post Post' : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) (hP : ∀ q, P q → P' q) (hQ : ∀ a, Post a → Post' a) :
    Bound P' Post' k oa := by
  induction h with
  | pure a k hp => exact .pure a k (hQ a hp)
  | query q f k hq _ ih => exact .query q f k (hP q hq) ih

theorem bind {Q : α → Prop} {R : β → Prop} {k l : Nat} {oa : M α}
    {f : α → M β} (h : Bound P Q k oa) (hf : ∀ a, Q a → Bound P R l (f a)) :
    Bound P R (k + l) (oa >>= f) := by
  induction h with
  | pure a k hp => rw [pure_bind]; exact (hf a hp).mono_k (by omega)
  | query q g k hq _ ih =>
    rw [bind_assoc, Nat.add_assoc]
    exact .query q _ _ hq ih

theorem bind' {Q : α → Prop} {R : β → Prop} {k l n : Nat} {oa : M α}
    {f : α → M β} (h : Bound P Q k oa) (hf : ∀ a, Q a → Bound P R l (f a))
    (hn : k + l  ≤  n) : Bound P R n (oa >>= f) :=
  (h.bind hf).mono_k hn

theorem map {Q : α → Prop} {R : β → Prop} {k : Nat} {oa : M α} (g : α → β)
    (h : Bound P Q k oa) (hg : ∀ a, Q a → R (g a)) : Bound P R k (g <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact (h.bind (l := 0) fun a ha => .pure _ 0 (hg a ha))

theorem qry_bind {R : β → Prop} {q : Query} {f : T3.Spec.Range q → M β} {k n : Nat}
    (hq : P q) (hf : ∀ u, Bound P R k (f u)) (hn : weight q + k  ≤  n) :
    Bound P R n (qry q >>= f) :=
  (Bound.query q f k hq hf).mono_k hn

end Bound

theorem Bound.foldlM_list {P : Query → Prop} {γ β : Type} (l : List β)
    (f : γ → β → M γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i (hi : i < l.length) acc, Inv i acc → Bound P (Inv (i + 1)) (cost i) (f acc l[i])) :
    Bound P (Inv l.length) (∑ i ∈ range l.length, cost i) (l.foldlM f init) := by
  induction l generalizing Inv cost init with
  | nil => exact Bound.pure _ _ h0
  | cons x l ih =>
    rw [List.foldlM_cons, List.length_cons]
    have h0' := hs 0 (by simp) init h0
    simp only [List.getElem_cons_zero] at h0'
    refine Bound.bind' h0' (fun a ha => ih (fun i => Inv (i + 1)) (fun i => cost (i + 1)) a ha
      (fun i hi acc hacc => hs (i + 1) (by simp; omega) acc hacc)) ?_
    rw [Finset.sum_range_succ' _ l.length]; omega

theorem Bound.foldlM_range {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Bound P (Inv (i + 1)) (cost i) (f acc i)) :
    Bound P (Inv n) (∑ i ∈ range n, cost i) ((List.range n).foldlM f init) := by
  have h := Bound.foldlM_list (P := P) (List.range n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range]; exact hs i (by simpa using hi) acc hacc)
  simpa using h

theorem Bound.foldlM_range' {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Bound P (Inv (i + 1)) (cost i) (f acc (a + i))) :
    Bound P (Inv n) (∑ i ∈ range n, cost i) ((List.range' a n).foldlM f init) := by
  have h := Bound.foldlM_list (P := P) (List.range' a n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range', Nat.one_mul]; exact hs i (by simpa using hi) acc hacc)
  simpa using h

theorem Bound.foldlM_range_le {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Bound P (Inv (i + 1)) (cost i) (f acc i))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i  ≤  k) :
    Bound P Post k ((List.range n).foldlM f init) :=
  ((Bound.foldlM_range n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk

theorem Bound.foldlM_range'_le {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Bound P (Inv (i + 1)) (cost i) (f acc (a + i)))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i  ≤  k) :
    Bound P Post k ((List.range' a n).foldlM f init) :=
  ((Bound.foldlM_range' a n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk

theorem sum_const_range (n c : Nat) : ∑ _i ∈ range n, c = n * c := by simp

theorem sum_levels (h : Nat) : ∑ i ∈ range h, 2 ^ (h - i) / 2 = 2 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ range h, 2 ^ (h + 1 - (i + 1)) / 2 = 2 ^ (h - i) / 2 := by
      intro i _; rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl this, ih]
    simp only [Nat.sub_zero, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    have : 1  ≤  2 ^ h := Nat.one_le_two_pow
    omega

/-- Forward a query and add its weight to the counter. -/
def countImpl (wt : Query → Nat) : QueryImpl T3.Spec (StateT Nat (OracleComp T3.Spec)) :=
  fun q => do
    modify (· + wt q)
    liftM (T3.Spec.query q)

def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp T3.Spec α) :
    OracleComp T3.Spec (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0

/-- The result and the number of oracle calls. -/
def countCalls {α : Type} (oa : OracleComp T3.Spec α) : OracleComp T3.Spec (α × Nat) :=
  countWith (fun _ => 1) oa

/-- The result and the number of compressions (64-byte blocks). -/
def countBlocks {α : Type} (oa : OracleComp T3.Spec α) : OracleComp T3.Spec (α × Nat) :=
  countWith weight oa

section
variable (wt : Query → Nat) {α β : Type}

/-- Running from counter `n` adds `n` to the count. -/
theorem countImpl_run (oa : OracleComp T3.Spec α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp T3.Spec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp T3.Spec _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp T3.Spec α) = pure (a, 0) :=
  rfl

/-- Counts add up along a bind. -/
theorem countWith_bind (oa : OracleComp T3.Spec α) (f : α → OracleComp T3.Spec β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)

@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (T3.Spec.query q) : OracleComp T3.Spec _) =
      (fun a => (a, wt q)) <$> (liftM (T3.Spec.query q) : OracleComp T3.Spec _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

/-- Dropping the count gives back the computation. -/
@[simp] theorem fst_countWith (oa : OracleComp T3.Spec α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a

end



/-- Soundness of the cost/postcondition calculus against the counted source
query tree, including every possible oracle response sequence. -/
theorem Bound.count_support {P : Query → Prop} {α : Type} {Post : α → Prop}
    {k : Nat} {oa : M α} (h : Bound P Post k oa) :
    ∀ result ∈ support (countWith weight oa), Post result.1 ∧ result.2 ≤ k := by
  induction h with
  | pure a k hp =>
      intro result hr
      simp only [countWith_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact ⟨hp,Nat.zero_le _⟩
  | query q f k hq h ih =>
      intro result hr
      rw [countWith_bind,mem_support_bind_iff] at hr
      obtain ⟨answer,ha,hr⟩ := hr
      rw [countWith_query,support_map] at ha
      obtain ⟨value,_,rfl⟩ := ha
      rw [support_map] at hr
      obtain ⟨rest,hrest,rfl⟩ := hr
      have ht := ih value rest hrest
      exact ⟨ht.1,Nat.add_le_add_left ht.2 _⟩

theorem Bound.mapM_list {P : Query → Prop} {α β : Type} (l : List α)
    (f : α → M β) (cost : α → Nat)
    (h : ∀ x ∈ l, Bound P (fun _ => True) (cost x) (f x)) :
    Bound P (fun out => out.length=l.length) (l.map cost).sum (l.mapM f) := by
  induction l with
  | nil => exact .pure [] 0 rfl
  | cons a l ih =>
      rw [List.mapM_cons]
      simp only [List.map_cons,List.sum_cons]
      refine (h a (by simp)).bind fun value _ => ?_
      refine (ih (fun x hx => h x (by simp [hx]))).bind' (l := 0) (fun tail ht => ?_) (by omega)
      exact .pure (value::tail) 0 (by simp [ht])

def GoodQuery : Query → Prop
  | .inl (.inr input) => 0 < input.length ∧ input.length%64=0
  | _ => True

abbrev CBound {α : Type} (Post : α → Prop) (k : Nat) (program : M α) :=
  Bound GoodQuery Post k program

theorem pad64_length (input : HashInput) :
    (pad64 input).length=input.length+(64-input.length%64)%64 := by
  simp only [pad64,List.length_append,List.length_replicate]

theorem private_realization_weight (secret : BitVec 256) (coordinate : Coordinate) :
    (privateInput secret coordinate).length/64=weight (.inr coordinate) := by
  rcases coordinate with tweak | message | region
  · simp only [privateInput_short,zero16,weight,SphincsSecurity.bytesLE_length,List.length_append,List.length_replicate,List.length_ofFn]
  · simp only [privateInput_nonce,zero16,weight,SphincsSecurity.bytesLE_length,List.length_append,List.length_replicate,List.length_ofFn]
  · simp only [privateInput_mac,zero16,weight,SphincsSecurity.bytesLE_length,List.length_append,List.length_replicate,List.length_ofFn]

theorem pad64_aligned (input : HashInput) : (pad64 input).length%64=0 := by
  rw [pad64_length]
  omega

theorem pad64_positive (input : HashInput) (hpos : 0 < input.length) : 0 < (pad64 input).length := by
  rw [pad64_length]
  omega

theorem bound_shortHash (input : HashInput) (k : Nat) (hpos : 0 < input.length)
    (hlen : (pad64 input).length/64 ≤ k) : CBound (fun _ => True) k (shortHash input) := by
  unfold shortHash publicHash
  apply Bound.qry_bind (k := 0) ⟨pad64_positive input hpos,pad64_aligned input⟩ (fun _ => .pure _ 0 trivial)
  simpa only [weight,Nat.add_zero] using hlen

theorem bound_privatePair (tag lay tree position index : Nat) :
    CBound (fun _ => True) 1 (privatePair tag lay tree position index) := by
  unfold privatePair privateHash
  exact Bound.qry_bind (k := 0) trivial (fun _ => .pure _ 0 trivial) (by simp only [weight];omega)

theorem bound_privateMac (region : Region) : CBound (fun _ => True) 513 (privateMac region) := by
  change CBound _ _ (qry (.inr (.inr (.inr region))))
  rw [← bind_pure (qry _)]
  exact Bound.qry_bind (k := 0) trivial (fun _ => .pure _ 0 trivial) (by simp only [weight];omega)

theorem bound_mask (level index : Nat) : CBound (fun _ => True) 1 (mask level index) := by
  unfold mask
  exact (bound_privatePair 13 0 0 level index).bind' (fun _ _ => .pure _ 0 trivial) (by decide)

theorem bound_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    CBound (fun _ => True) count (chain lay tree leaf i start count value) := by
  unfold chain
  refine Bound.foldlM_range'_le start count _ (fun _ _ => True) (fun _ => 1) value trivial
    (fun n _ value _ => ?_) (fun _ _ => trivial) (by simp)
  apply bound_shortHash <;> simp [chainInput,pad64_length,zero16,SphincsSecurity.bytesLE_length]

theorem bound_nodeHash (tag lay tree heap : Nat) (left right : Digest) :
    CBound (fun _ => True) 1 (nodeHash tag lay tree heap left right) := by
  apply bound_shortHash <;> simp [nodeHash,pad64_length,zero16,SphincsSecurity.bytesLE_length]



theorem bound_top_leafHash (tree leaf : Nat) (ends : List Digest) (hlen : ends.length=58) :
    CBound (fun _ => True) 15 (leafHash 0 tree leaf ends) := by
  apply bound_shortHash <;> simp only [leafHash,pad64_length,List.length_append,SphincsSecurity.bytesLE_length,
    digest_list_bytes_length,List.length_drop,hlen] <;> norm_num

def topPairCost (pair : Nat) : Nat :=
  1+∑ half ∈ range 2, (2^width 0 (2*pair+half)-1)

theorem topPairCost_sum : (∑ pair ∈ range 29,topPairCost pair)=239 := by decide +kernel

/-- The top leaf has 58 mixed-radix chains: 49 of radix four, nine of radix
 eight, and 29 paired seed queries. Its leaf hash takes 15 blocks. -/
theorem bound_buildTopLeaf (tree leaf : Nat) :
    CBound (fun result => result.2.length=58) 254 (buildLeaf 0 tree leaf []) := by
  unfold buildLeaf
  refine Bound.bind' (l := 15) (Bound.foldlM_range 29 _
    (fun pair (state : List Digest × List Digest) => state.1.length=2*pair ∧ state.2.length=2*pair)
    topPairCost ([],[]) ⟨rfl,rfl⟩ (fun pair hpair state hstate => ?_))
    (fun state hstate => ?_) ?_
  · unfold topPairCost
    refine (bound_privatePair 0 0 tree pair leaf).bind (fun seeds _ => ?_)
    change CBound _ (∑ half ∈ range 2,(2^width 0 (2*pair+half)-1)) _
    refine (Bound.foldlM_range 2 _
      (fun half (acc : List Digest × List Digest) => acc.1.length=2*pair+half ∧ acc.2.length=2*pair+half)
      (fun half => 2^width 0 (2*pair+half)-1) state
      ⟨by simpa using hstate.1,by simpa using hstate.2⟩ (fun half hhalf acc hacc => ?_)).mono
      (fun _ h => h) (fun acc h => ⟨by omega,by omega⟩)
    have hi : ¬chainCount (0 : Layer) ≤ 2*pair+half := by
      change ¬58 ≤ 2*pair+half
      omega
    simp only [hi,ite_false,List.getD_nil,Bool.false_eq_true,Nat.sub_zero]
    refine (bound_chain 0 tree leaf (2*pair+half) 0 0 _).bind' (l := 2^width 0 (2*pair+half)-1)
      (fun value _ => ?_) (by omega)
    refine (bound_chain 0 tree leaf (2*pair+half) 0 (2^width 0 (2*pair+half)-1) value).bind'
      (l := 0) (fun last _ => ?_) (by omega)
    exact .pure _ 0 ⟨by simp [hacc.1];omega,by simp [hacc.2];omega⟩
  · simp only [Bool.false_eq_true,ite_false]
    refine (bound_top_leafHash tree leaf state.1 (by omega)).bind' (l := 0) (fun root _ => ?_) (by omega)
    exact .pure (root,state.2) 0 (by simpa using hstate.2)
  · rw [topPairCost_sum]



theorem bound_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) :
    CBound (fun result => result.length=nodes.length/2) (nodes.length/2)
      (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel
  have hc := Bound.mapM_list (P := GoodQuery) (List.range (nodes.length/2))
    (fun i => nodeHash tag lay tree (2^(h-level)+i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0))
    (fun _ => 1) (fun _ _ => bound_nodeHash _ _ _ _ _ _)
  simpa using hc

def LevelShape (height completed : Nat) (levels : List (List Digest)) : Prop :=
  levels.length=completed+1 ∧ ∀ j, j ≤ completed → (levels.getD j []).length=2^(height-j)

theorem bound_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (hlen : leaves.length=2^h) :
    CBound (LevelShape h h) (2^h-1) (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  refine Bound.foldlM_range'_le 1 h _ (LevelShape h) (fun i => 2^(h-i)/2) [leaves]
    ⟨rfl,fun j hj => by
      have he : j=0 := by omega
      subst j
      simpa using hlen⟩
    (fun i hi levels hlevels => ?_) (fun _ h => h) (by rw [sum_levels])
  have hprevious : (levels.getD (1+i-1) []).length=2^(h-i) := by
    simpa using hlevels.2 i le_rfl
  refine (bound_buildLevel tag lay tree h (1+i) (levels.getD (1+i-1) [])).bind' (l := 0)
    (fun nodes hnodes => ?_) (by rw [hprevious];omega)
  have hnext : nodes.length=2^(h-(i+1)) := by
    rw [hprevious,show h-i=h-(i+1)+1 by omega,pow_succ,Nat.mul_div_cancel _ (by decide : 0 < 2)] at hnodes
    exact hnodes
  refine .pure (levels++[nodes]) 0 ⟨by simp [hlevels.1],?_⟩
  intro j hj
  by_cases hold : j ≤ i
  · rw [List.getD_append levels [nodes] [] j (by have := hlevels.1;omega)]
    exact hlevels.2 j hold
  · have he : j=i+1 := by omega
    subst j
    rw [List.getD_append_right levels [nodes] [] (i+1) (by have := hlevels.1;omega)]
    simp only [hlevels.1,Nat.sub_self,List.getD_cons_zero]
    exact hnext

theorem bound_buildTopTree (tree selected : Nat) :
    CBound (fun result => LevelShape 12 12 result.1) 1044479 (buildTree 0 tree selected []) := by
  unfold buildTree
  simp only [ite_self]
  refine Bound.bind' (l := 4095) (Bound.foldlM_range 4096 _
    (fun i (state : List Digest × List Digest) => state.1.length=i) (fun _ => 254) ([],[]) rfl
    (fun leaf _ state hstate => ?_)) (fun state hstate => ?_) (by rw [sum_const_range])
  · refine (bound_buildTopLeaf tree leaf).bind' (l := 0) (fun result _ => ?_) (by omega)
    exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevels 3 0 tree 12 state.1 hstate).bind' (l := 0)
      (fun levels hlevels => .pure (levels,state.2) 0 hlevels) (by decide)

theorem bound_keygenPayload : CBound (fun _ => True) 1046525 keygenPayload := by
  unfold keygenPayload
  refine (bound_buildTopTree 0 0).bind' (l := 2046) (fun result _ => ?_) (by decide)
  refine (Bound.mapM_list (P := GoodQuery) (List.range' 2 10) _
    (fun level => 2^(12-level)) (fun level _ => ?_)).bind' (l := 0)
    (fun masked _ => .pure _ 0 trivial) ?_
  · have hm := Bound.mapM_list (P := GoodQuery) (List.range (2^(12-level)))
      (fun i => do let value ← mask level i;pure ((result.1.getD level []).getD i 0 ^^^ value))
      (fun _ => 1) (fun i _ => (bound_mask level i).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide))
    exact (hm.mono (fun _ h => h) (fun _ _ => trivial)).mono_k (by simp)
  · decide +kernel

/-- Source keygen fits the organizer's compression budget for every possible
oracle response sequence, including the 513-block cache authentication. -/
theorem bound_keygen : CBound (fun _ => True) 1047038 keygen := by
  unfold keygen
  refine bound_keygenPayload.bind' (l := 513) (fun result _ => ?_) (by decide)
  exact (bound_privateMac result.2).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide)

theorem keygen_compression_bound :
    ∀ result ∈ support (countBlocks keygen), result.2 ≤ 2^20 := by
  intro result hr
  exact (bound_keygen.count_support result hr).2.trans (by decide)

end SigGolfCandidate.T3.Cost


namespace SigGolfCandidate.T3.Cost
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace World
abbrev Query := SphincsSecurity.OracleWorld.Domain

def weight : Query → Nat
  | .inl _ => 0
  | .inr input => input.length/64

/-- Forward a query and add its weight to the counter. -/
def countImpl (wt : Query → Nat) : QueryImpl SphincsSecurity.OracleWorld (StateT Nat (OracleComp SphincsSecurity.OracleWorld)) :=
  fun q => do
    modify (· + wt q)
    liftM (SphincsSecurity.OracleWorld.query q)

def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp SphincsSecurity.OracleWorld α) :
    OracleComp SphincsSecurity.OracleWorld (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0

/-- The result and the number of oracle calls. -/
def countCalls {α : Type} (oa : OracleComp SphincsSecurity.OracleWorld α) : OracleComp SphincsSecurity.OracleWorld (α × Nat) :=
  countWith (fun _ => 1) oa

/-- The result and the number of compressions (64-byte blocks). -/
def countBlocks {α : Type} (oa : OracleComp SphincsSecurity.OracleWorld α) : OracleComp SphincsSecurity.OracleWorld (α × Nat) :=
  countWith weight oa

section
variable (wt : Query → Nat) {α β : Type}

/-- Running from counter `n` adds `n` to the count. -/
theorem countImpl_run (oa : OracleComp SphincsSecurity.OracleWorld α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp SphincsSecurity.OracleWorld) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp SphincsSecurity.OracleWorld _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp SphincsSecurity.OracleWorld α) = pure (a, 0) :=
  rfl

/-- Counts add up along a bind. -/
theorem countWith_bind (oa : OracleComp SphincsSecurity.OracleWorld α) (f : α → OracleComp SphincsSecurity.OracleWorld β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)

@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (SphincsSecurity.OracleWorld.query q) : OracleComp SphincsSecurity.OracleWorld _) =
      (fun a => (a, wt q)) <$> (liftM (SphincsSecurity.OracleWorld.query q) : OracleComp SphincsSecurity.OracleWorld _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

/-- Dropping the count gives back the computation. -/
@[simp] theorem fst_countWith (oa : OracleComp SphincsSecurity.OracleWorld α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a

end



end World

theorem realize_bind {α β : Type} (secret : BitVec 256) (oa : M α) (f : α → M β) :
    realize secret (oa >>= f)=realize secret oa >>= fun result => realize secret (f result) := by
  simp only [realize,simulateQ_bind]

theorem realize_map {α β : Type} (secret : BitVec 256) (f : α → β) (oa : M α) :
    realize secret (f <$> oa)=f <$> realize secret oa := by
  simp only [realize,simulateQ_map]

theorem realized_query_count (secret : BitVec 256) (q : Query) :
    World.countWith World.weight (realize secret (qry q))=
      (fun answer => (answer,weight q)) <$> realize secret (qry q) := by
  rcases q with (coin | input) | (tweak | (message | region))
  · exact World.countWith_query World.weight (.inl coin)
  · exact World.countWith_query World.weight (.inr input)
  · change World.countWith World.weight (liftM (SphincsSecurity.OracleWorld.query
      (.inr (privateInput secret (.inl tweak))))) = _
    rw [World.countWith_query,World.weight,private_realization_weight]
    rfl
  · change World.countWith World.weight (liftM (SphincsSecurity.OracleWorld.query
      (.inr (privateInput secret (.inr (.inl message)))))) = _
    rw [World.countWith_query,World.weight,private_realization_weight]
    rfl
  · change World.countWith World.weight (liftM (SphincsSecurity.OracleWorld.query
      (.inr (privateInput secret (.inr (.inr region)))))) = _
    rw [World.countWith_query,World.weight,private_realization_weight]
    rfl

/-- The private-coordinate cost is exactly the block count of its concrete
secret-dependent oracle input. The identity holds for the entire query tree. -/
theorem realize_count {α : Type} (secret : BitVec 256) (program : M α) :
    realize secret (countWith weight program)=World.countWith World.weight (realize secret program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [realize]
  | query_bind q next ih =>
      rw [countWith_bind,realize_bind,realize_bind,World.countWith_bind]
      rw [countWith_query,realize_map,realized_query_count]
      simp_rw [realize_map,ih]

/-- Realization only chooses among responses already admitted by the source
query tree. -/
theorem realize_support_subset {α : Type} (secret : BitVec 256) (program : M α) :
    support (realize secret program) ⊆ support program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [realize]
  | query_bind q next ih =>
      intro result hr
      rw [realize_bind,mem_support_bind_iff] at hr
      obtain ⟨value,_,hv⟩ := hr
      rw [mem_support_bind_iff]
      exact ⟨value,mem_support_query q value,ih value hv⟩

theorem realized_keygen_compression_bound (secret : BitVec 256) :
    ∀ result ∈ support (World.countBlocks (realize secret keygen)), result.2 ≤ 2^20 := by
  intro result hr
  rw [World.countBlocks,← realize_count] at hr
  exact keygen_compression_bound result (realize_support_subset secret _ hr)

end SigGolfCandidate.T3.Cost


namespace SigGolfCandidate.T3.Cost
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Keygen's exponential-moment bound holds from every initial random-oracle
cache, since its concrete compression count is bounded on every execution. -/
theorem realized_keygen_exponential_budget (secret : BitVec 256)
    (cache : QueryCache SphincsSecurity.HashSpec) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (World.countBlocks (realize secret keygen))).run' cache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / (2^20 : Nat))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro result hr
  have hc := realized_keygen_compression_bound secret result
    (support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache hr)
  calc (2 : ENNReal) ^ ((result.2 : ℝ) / (2^20 : Nat)) ≤ (2 : ENNReal) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [div_le_one (by norm_num : (0 : ℝ) < (2^20 : Nat))]
        exact_mod_cast hc
    _ = 2 := by simp

end SigGolfCandidate.T3.Cost


namespace SigGolfCandidate.T3.Cost
open OracleComp OracleSpec Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def ValidDigits (lay : Layer) (digits : List Nat) : Prop :=
  ∀ i, i < chainCount lay → digits.getD i 0 ≤ 2^width lay i-1

theorem validDigits_nil (lay : Layer) : ValidDigits lay [] := by
  intro i _
  simp

theorem validDigits_decode {lay : Layer} {value : Digest} {digits : List Nat}
    (h : decode lay value=some digits) : ValidDigits lay digits := by
  intro i hi
  have := decode_digit_bound h i hi
  omega

def leafHashCost (lay : Layer) : Nat := if lay=0 then 15 else 11
def fullLeafCost (lay : Layer) : Nat := if lay=0 then 254 else 334

theorem bound_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hlen : ends.length=chainCount lay) :
    CBound (fun _ => True) (leafHashCost lay) (leafHash lay tree leaf ends) := by
  apply bound_shortHash <;> simp only [leafHash,pad64_length,List.length_append,
    SphincsSecurity.bytesLE_length,digest_list_bytes_length,List.length_drop,hlen]
  · fin_cases lay <;> decide
  · fin_cases lay <;> decide

def fullPairCost (lay : Layer) (pair : Nat) : Nat :=
  1+∑ half ∈ range 2, if chainCount lay ≤ 2*pair+half then 0 else 2^width lay (2*pair+half)-1

theorem fullPairCost_sum (lay : Layer) :
    (∑ pair ∈ range ((chainCount lay+1)/2),fullPairCost lay pair)+leafHashCost lay=fullLeafCost lay := by
  fin_cases lay <;> decide +kernel

/-- A selected leaf has the same full traversal cost as an unselected leaf:
the walk to each disclosed digit and the walk from there to the endpoint
partition the chain. The odd lower-layer final pair discards its second half. -/
theorem bound_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hd : ValidDigits lay digits) :
    CBound (fun result => result.2.length=chainCount lay) (fullLeafCost lay)
      (buildLeaf lay tree leaf digits) := by
  unfold buildLeaf
  refine Bound.bind' (l := leafHashCost lay) (Bound.foldlM_range ((chainCount lay+1)/2) _
    (fun pair (state : List Digest × List Digest) =>
      state.1.length=min (2*pair) (chainCount lay) ∧ state.2.length=min (2*pair) (chainCount lay))
    (fullPairCost lay) ([],[]) ⟨by simp,by simp⟩ (fun pair hpair state hstate => ?_))
    (fun state hstate => ?_) (le_of_eq (fullPairCost_sum lay))
  · unfold fullPairCost
    refine (bound_privatePair 0 lay.val tree pair leaf).bind (fun seeds _ => ?_)
    refine (Bound.foldlM_range 2 _
      (fun half (acc : List Digest × List Digest) =>
        acc.1.length=min (2*pair+half) (chainCount lay) ∧
        acc.2.length=min (2*pair+half) (chainCount lay))
      (fun half => if chainCount lay ≤ 2*pair+half then 0 else 2^width lay (2*pair+half)-1)
      state ⟨by simpa using hstate.1,by simpa using hstate.2⟩
      (fun half hhalf acc hacc => ?_)).mono (fun _ h => h) (fun acc h => ⟨by omega,by omega⟩)
    by_cases hi : chainCount lay ≤ 2*pair+half
    · simp only [hi,ite_true]
      exact .pure acc 0 ⟨by omega,by omega⟩
    · simp only [hi,ite_false,Bool.false_eq_true]
      have hc := hd (2*pair+half) (by omega)
      refine (bound_chain lay tree leaf (2*pair+half) 0 (digits.getD (2*pair+half) 0) _).bind'
        (l := 2^width lay (2*pair+half)-1-digits.getD (2*pair+half) 0)
        (fun value _ => ?_) (by omega)
      refine (bound_chain lay tree leaf (2*pair+half) (digits.getD (2*pair+half) 0)
        (2^width lay (2*pair+half)-1-digits.getD (2*pair+half) 0) value).bind'
        (l := 0) (fun last _ => ?_) (by omega)
      exact .pure _ 0 ⟨by simp only [List.length_append,List.length_singleton];omega,
        by simp only [List.length_append,List.length_singleton];omega⟩
  · simp only [Bool.false_eq_true,ite_false]
    have hlen : state.1.length=chainCount lay := by have := hstate.1;omega
    refine (bound_leafHash lay tree leaf state.1 hlen).bind' (l := 0) (fun root _ => ?_) (by omega)
    exact .pure (root,state.2) 0 (by
      change state.2.length=chainCount lay
      have := hstate.2
      omega)

def treeCost (lay : Layer) : Nat := (fullLeafCost lay+1)*2^height lay-1

theorem bound_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hd : ValidDigits lay digits) :
    CBound (fun result => LevelShape (height lay) (height lay) result.1) (treeCost lay)
      (buildTree lay tree selected digits) := by
  unfold buildTree
  refine Bound.bind' (l := 2^height lay-1) (Bound.foldlM_range (2^height lay) _
    (fun i (state : List Digest × List Digest) => state.1.length=i)
    (fun _ => fullLeafCost lay) ([],[]) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) ?_
  · have hd' : ValidDigits lay (if leaf=selected then digits else []) := by
      split <;> first | exact hd | exact validDigits_nil lay
    refine (bound_buildLeaf lay tree leaf _ hd').bind' (l := 0) (fun result _ => ?_) (by omega)
    exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevels 3 lay.val tree (height lay) state.1 hstate).bind' (l := 0)
      (fun levels hlevels => .pure (levels,state.2) 0 hlevels) (by omega)
  · rw [sum_const_range]
    simp only [treeCost,Nat.add_mul,Nat.one_mul,Nat.mul_comm (fullLeafCost lay)]
    have := Nat.one_le_two_pow (n := height lay)
    omega

theorem lowerTreeCost : treeCost 1+treeCost 2+treeCost 3=85757 := by decide +kernel

theorem bound_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
    CBound (fun _ => True) 1 (ftsLeaf index coord leaf secret) := by
  apply bound_shortHash <;> simp [ftsLeaf,pad64_length,zero16,SphincsSecurity.bytesLE_length]

theorem bound_buildFts (index coord : Nat) :
    CBound (fun result => LevelShape 11 11 result.1 ∧ result.2.length=2048) 5119 (buildFts index coord) := by
  unfold buildFts
  refine Bound.bind' (l := 2047) (Bound.foldlM_range 1024 _
    (fun pair (state : List Digest × List Digest) => state.1.length=2*pair ∧ state.2.length=2*pair)
    (fun _ => 3) ([],[]) ⟨rfl,rfl⟩ (fun pair _ state hstate => ?_))
    (fun state hstate => ?_) (by rw [sum_const_range])
  · refine (bound_privatePair 8 coord index 0 pair).bind' (l := 2) (fun seeds _ => ?_) (by decide)
    refine (bound_ftsLeaf index coord (2*pair) seeds.1).bind' (l := 1) (fun left _ => ?_) (by decide)
    refine (bound_ftsLeaf index coord (2*pair+1) seeds.2).bind' (l := 0) (fun right _ => ?_) (by decide)
    exact .pure _ 0 ⟨by simp [hstate.1];omega,by simp [hstate.2];omega⟩
  · refine (bound_buildLevels 10 coord index 11 state.1 (by simpa using hstate.1)).bind'
      (l := 0) (fun levels hl => ?_) (by decide)
    exact .pure (levels,state.2) 0 ⟨hl,hstate.2⟩

theorem bound_forestPk (index : Nat) (roots : List Digest) (hlen : roots.length=7) :
    CBound (fun _ => True) 2 (forestPk index roots) := by
  apply bound_shortHash <;> simp [forestPk,pad64_length,List.length_append,
    SphincsSecurity.bytesLE_length,digest_list_bytes_length,List.length_drop,hlen]

theorem bound_topPath (cache : Cache) (leaf : Nat) :
    CBound (fun result => result.length=12) 773 (topPath cache leaf) := by
  unfold topPath
  refine (bound_buildTopLeaf 0 (leaf ^^^ 1)).bind' (l := 519) (fun sibling _ => ?_) (by decide)
  refine (bound_buildTopLeaf 0 _).bind' (l := 265) (fun left _ => ?_) (by decide)
  refine (bound_buildTopLeaf 0 _).bind' (l := 11) (fun right _ => ?_) (by decide)
  refine (bound_nodeHash 3 0 0 _ left.1 right.1).bind' (l := 10) (fun siblingPair _ => ?_) (by decide)
  refine (Bound.mapM_list (P := GoodQuery) (List.range' 2 10) _ (fun _ => 1)
    (fun level _ => (bound_mask level _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide))).bind'
    (l := 0) (fun rest hrest => ?_) (by simp)
  exact .pure ([sibling.1,siblingPair]++rest) 0 (by simpa using hrest)

theorem sum_getD (x : List Nat) : ∑ i ∈ range x.length,x.getD i 0=x.sum := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.length_cons,Finset.sum_range_succ',List.sum_cons]
    simp only [List.getD_cons_succ,List.getD_cons_zero,ih]
    omega

theorem sum_pairs (f : Nat → Nat) (n : Nat) :
    ∑ k ∈ range n,(f (2*k)+f (2*k+1))=∑ i ∈ range (2*n),f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,show 2*(n+1)=2*n+1+1 by ring,
      Finset.sum_range_succ,Finset.sum_range_succ,Nat.add_assoc]

def signaturePairCost (digits : List Nat) (pair : Nat) : Nat :=
  1+∑ half ∈ range 2,digits.getD (2*pair+half) 0

theorem signaturePairCost_sum (digits : List Nat) (hlen : digits.length=58) :
    ∑ pair ∈ range 29,signaturePairCost digits pair=29+digits.sum := by
  unfold signaturePairCost
  rw [Finset.sum_add_distrib,sum_const_range]
  simp only [Nat.mul_one]
  apply congrArg (fun n : Nat => 29+n)
  have htwo (pair : Nat) : (∑ half ∈ range 2,digits.getD (2*pair+half) 0)=
      digits.getD (2*pair) 0+digits.getD (2*pair+1) 0 := by simp [Finset.sum_range_succ]
  simp_rw [htwo]
  rw [sum_pairs (fun i => digits.getD i 0) 29,show 2*29=digits.length by omega,sum_getD]

theorem bound_topSignatureLeaf (tree leaf : Nat) (digits : List Nat) (hlen : digits.length=58) :
    CBound (fun result => result.2.length=58) (29+digits.sum) (buildLeaf 0 tree leaf digits true) := by
  unfold buildLeaf
  refine Bound.bind' (l := 0) (Bound.foldlM_range 29 _
    (fun pair (state : List Digest × List Digest) => state.2.length=2*pair)
    (signaturePairCost digits) ([],[]) rfl (fun pair hpair state hstate => ?_))
    (fun state hstate => ?_) (by rw [signaturePairCost_sum digits hlen];omega)
  · unfold signaturePairCost
    refine (bound_privatePair 0 0 tree pair leaf).bind (fun seeds _ => ?_)
    refine (Bound.foldlM_range 2 _
      (fun half (acc : List Digest × List Digest) => acc.2.length=2*pair+half)
      (fun half => digits.getD (2*pair+half) 0) state (by simpa using hstate)
      (fun half hhalf acc hacc => ?_)).mono (fun _ h => h) (fun acc h => by omega)
    have hi : ¬chainCount (0 : Layer) ≤ 2*pair+half := by change ¬58 ≤ 2*pair+half;omega
    simp only [hi,ite_false,ite_true]
    refine (bound_chain 0 tree leaf (2*pair+half) 0 (digits.getD (2*pair+half) 0) _).bind'
      (l := 0) (fun value _ => ?_) (by omega)
    exact .pure _ 0 (by simp [hacc];omega)
  · simp only [ite_true]
    exact .pure (0,state.2) 0 hstate

theorem bound_signTop (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hlen : digits.length=58) (hsum : digits.sum=125) :
    CBound (fun result => result.1.length=58 ∧ result.2.length=12) 928 (signTop cache leaf digits) := by
  unfold signTop
  refine (bound_topSignatureLeaf 0 leaf digits hlen).bind' (l := 773) (fun result hr => ?_)
    (by rw [hsum]; omega)
  refine (bound_topPath cache leaf).bind' (l := 0) (fun path hp => ?_) (by decide)
  exact .pure (result.2,path) 0 ⟨hr,hp⟩

def CounterResult (lay : Layer) (out : Option (BitVec 32 × List Nat)) : Prop :=
  ∀ counter digits,out=some (counter,digits) →
    digits.length=chainCount lay ∧ digits.sum=target lay ∧ ValidDigits lay digits

theorem bound_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter,CBound (CounterResult lay) fuel (counterSearch lay tree leaf message counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [CounterResult])
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      refine (bound_shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 counter)) 1
        (by simp [encodingInput,SphincsSecurity.bytesLE_length])
        (by simp [encodingInput,pad64_length,SphincsSecurity.bytesLE_length])).bind'
        (l := fuel) (fun answer _ => ?_) (by omega)
      cases hd : decode lay answer with
      | none => exact ih (counter+1)
      | some digits =>
          refine .pure (some (BitVec.ofNat 32 counter,digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1,(decode_length_sum hd).2,validDigits_decode hd⟩

theorem bound_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    CBound (fun _ => True) 1 (digest rho message counter) := by
  change CBound _ _ (qry (.inl (.inr (pad64 (digestInput rho message counter)))))
  rw [← bind_pure (qry _)]
  refine Bound.qry_bind (k := 0)
    ⟨pad64_positive _ (by simp [digestInput,SphincsSecurity.bytesLE_length]),pad64_aligned _⟩
    (fun _ => .pure _ 0 trivial) ?_
  simp [weight,pad64_length,digestInput,SphincsSecurity.bytesLE_length]

def DigestResult (out : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ counter output,out=some (counter,output) → admissible (selections output)=true

theorem bound_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter,CBound DigestResult fuel (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [DigestResult])
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      refine (bound_digest rho message (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun output _ => ?_) (by omega)
      split
      · rename_i hgood
        refine .pure (some (BitVec.ofNat 32 counter,output)) fuel ?_
        intro other value hv
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hv)
        exact (show admissible (selections _) = true ∧ digestGate _ = true by simpa only [digestAdmissible, Bool.and_eq_true] using hgood).1
      · exact ih (counter+1)

def layerFixedCost : Nat → Nat
  | 0 => 0
  | n+1 => if n=0 then 928 else treeCost (Fin.ofNat 4 n)+layerFixedCost n

theorem layerFixedCost_four : layerFixedCost 4=86685 := by decide +kernel

theorem bound_signLayers (cache : Cache) (index : Nat) :
    ∀ n message,CBound (fun _ => True) (n*counterLimit+layerFixedCost n)
      (signLayers cache index n message) := by
  intro n
  induction n with
  | zero =>
      intro message
      exact .pure _ _ trivial
  | succ n ih =>
      intro message
      unfold signLayers
      dsimp only
      refine (bound_counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 message counterLimit 0).bind'
        (l := n*counterLimit+layerFixedCost (n+1)) (fun out hout => ?_)
        (by simp only [Nat.add_mul,Nat.one_mul];omega)
      cases out with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter,digits⟩ := pair
          have hd := hout counter digits rfl
          dsimp only
          by_cases hn : n=0
          · subst n
            simp only [ite_true]
            refine (bound_signTop cache _ digits hd.1 hd.2.1).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCost])
          · simp only [hn,ite_false]
            refine (bound_buildTree (Fin.ofNat 4 n) _ _ digits hd.2.2).bind'
              (l := n*counterLimit+layerFixedCost n) (fun result _ => ?_)
              (by simp only [layerFixedCost,hn,ite_false];omega)
            refine (ih ((result.1.getD (height (Fin.ofNat 4 n)) []).getD 0 0)).bind'
              (l := 0) (fun previous _ => ?_) (by omega)
            cases previous <;> exact .pure _ 0 trivial

theorem bound_privateNonce (message : Message) :
    CBound (fun _ => True) 2 (privateNonce message) := by
  unfold privateNonce privateHash
  exact Bound.qry_bind (k := 0) trivial (fun _ => .pure _ 0 trivial) (by simp [weight])

/-- A deterministic ceiling on all source signing traces, including failures.
The probabilistic budget separately charges the two bounded searches. -/
theorem bound_signPayload (cache : Cache) (message : Message) :
    CBound (fun _ => True) (122522+attemptLimit+4*counterLimit) (signPayload cache message) := by
  unfold signPayload
  refine (bound_privateNonce message).bind' (l := 122520+attemptLimit+4*counterLimit)
    (fun rho _ => ?_) (by omega)
  refine (bound_digestSearch rho message attemptLimit 0).bind' (l := 122520+4*counterLimit)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter,output⟩ := pair
      dsimp only
      refine Bound.bind' (l := 86687+4*counterLimit) (Bound.foldlM_range 7 _
        (fun coord (state : List Digest × List Digest × List Digest) => state.2.2.length=coord)
        (fun _ => 5119) ([],[],[]) rfl (fun coord _ state hstate => ?_))
        (fun state hstate => ?_) (by rw [sum_const_range];omega)
      · refine (bound_buildFts _ coord).bind' (l := 0) (fun result _ => ?_) (by decide)
        exact .pure _ 0 (by simp [hstate])
      · refine (bound_forestPk _ state.2.2 hstate).bind' (l := 86685+4*counterLimit)
          (fun root _ => ?_) (by omega)
        refine (bound_signLayers cache _ 4 root).bind' (l := 0) (fun layers _ => ?_)
          (by rw [layerFixedCost_four];omega)
        cases layers <;> exact .pure _ 0 trivial

theorem bound_sign (cache : Cache) (message : Message) :
    CBound (fun _ => True) (123035+attemptLimit+4*counterLimit) (sign cache message) := by
  unfold sign
  refine (bound_privateMac cache.region).bind' (l := 122522+attemptLimit+4*counterLimit)
    (fun tag _ => ?_) (by omega)
  split
  · exact .pure _ _ trivial
  · exact bound_signPayload cache message

theorem sign_compression_ceiling (secret : BitVec 256) (cache : Cache) (message : Message) :
    ∀ result ∈ support (World.countBlocks (realize secret (sign cache message))),
      result.2 ≤ 17948827 := by
  intro result hr
  rw [World.countBlocks,← realize_count] at hr
  exact (bound_sign cache message).count_support result
    (realize_support_subset secret _ hr) |>.2

end SigGolfCandidate.T3.Cost


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

abbrev Answers := QueryImpl T3.Spec Id

theorem counterSearch_some (answers : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter found digits,counter+fuel ≤ 2^32 →
      evalWithAnswerFn answers (counterSearch lay tree leaf message counter fuel)=some (found,digits) →
      counter ≤ found.toNat ∧ found.toNat < counter+fuel ∧
        decode lay (evalWithAnswerFn answers (shortHash (encodingInput lay tree leaf message found)))=some digits := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits _ he
      simp [counterSearch] at he
  | succ fuel ih =>
      intro counter found digits hlimit he
      simp only [counterSearch,evalWithAnswerFn_bind] at he
      cases hd : decode lay (evalWithAnswerFn answers
        (shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo,hhi,hgood⟩ := ih (counter+1) found digits (by omega) he
          exact ⟨by omega,by omega,hgood⟩
      | some values =>
          simp only [hd,evalWithAnswerFn_pure,Option.some.injEq,Prod.mk.injEq] at he
          obtain ⟨rfl,rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat=counter := by
            rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount],by rw [hcount];omega,hd⟩

theorem digestSearch_some_good (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output,counter+fuel ≤ 2^32 →
      evalWithAnswerFn answers (digestSearch rho message counter fuel)=some (found,output) →
      counter ≤ found.toNat ∧ found.toNat < counter+fuel ∧
        evalWithAnswerFn answers (digest rho message found)=output ∧ digestAdmissible output=true := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found output _ he
      simp [digestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [digestSearch,evalWithAnswerFn_bind] at he
      split at he
      · rename_i hgood
        simp only [evalWithAnswerFn_pure,Option.some.injEq,Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        have hcount : (BitVec.ofNat 32 counter).toNat=counter := by
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hcount],by rw [hcount];omega,rfl,hgood⟩
      · obtain ⟨hlo,hhi,hrest⟩ := ih (counter+1) found output (by omega) he
        exact ⟨by omega,by omega,hrest⟩

theorem digestSearch_some (answers : Answers) (rho : Digest) (message : Message)
    (fuel counter : Nat) (found : BitVec 32) (output : HashOutput)
    (hlimit : counter+fuel ≤ 2^32)
    (he : evalWithAnswerFn answers (digestSearch rho message counter fuel)=some (found,output)) :
    counter ≤ found.toNat ∧ found.toNat < counter+fuel ∧
      evalWithAnswerFn answers (digest rho message found)=output ∧ admissible (selections output)=true := by
  obtain ⟨hlo,hhi,houtput,hgood⟩ := digestSearch_some_good answers rho message fuel counter found output hlimit he
  exact ⟨hlo,hhi,houtput,(show admissible (selections _) = true ∧ digestGate _ = true by simpa only [digestAdmissible, Bool.and_eq_true] using hgood).1⟩

theorem expandLayers_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n,n ≤ 4 → ∀ value root counters,
      evalWithAnswerFn answers (expandLayers sig index n value)=some (root,counters) →
      counters.length=n ∧ ∀ w : Witness,w.signature=sig →
        (∀ lay : Layer,lay.val < n → w.counters lay=counters.getD lay.val 0) →
        evalWithAnswerFn answers (verifyLayers w index n value)=some root := by
  intro n
  induction n with
  | zero =>
      intro _ value root counters he
      simp only [expandLayers,evalWithAnswerFn_pure,Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      exact ⟨rfl,fun _ _ _ => rfl⟩
  | succ n ih =>
      intro hn value root counters he
      simp only [expandLayers,evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some found =>
          obtain ⟨counter,digits⟩ := found
          simp only [hs,evalWithAnswerFn_bind] at he
          cases hr : evalWithAnswerFn answers (expandLayers sig index n
            (evalWithAnswerFn answers (recoverLayer sig index (Fin.ofNat 4 n) digits))) with
          | none => simp only [hr,evalWithAnswerFn_pure,reduceCtorEq] at he
          | some previous =>
              obtain ⟨previousRoot,previousCounters⟩ := previous
              simp only [hr,evalWithAnswerFn_pure,Option.some.injEq,Prod.mk.injEq] at he
              obtain ⟨rfl,rfl⟩ := he
              obtain ⟨hlen,hverify⟩ := ih (by omega) _ _ _ hr
              refine ⟨by simp [hlen],?_⟩
              intro w hw hc
              have hlay : (Fin.ofNat 4 n : Layer).val=n := by
                change n%4=n
                exact Nat.mod_eq_of_lt (by omega)
              have hcounter : w.counters (Fin.ofNat 4 n)=counter := by
                rw [hc _ (by rw [hlay];omega),hlay,
                  List.getD_append_right previousCounters [counter] 0 n (by omega),hlen]
                simp
              obtain ⟨_,hbound,hdecode⟩ := counterSearch_some answers (Fin.ofNat 4 n)
                (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value
                counterLimit 0 counter digits (by decide) hs
              have hnot : ¬counter.toNat ≥ counterLimit := by omega
              simp only [verifyLayers,hcounter,hnot,ite_false,evalWithAnswerFn_bind,hdecode,hw]
              apply hverify w hw
              intro lay hsmall
              rw [hc lay (by omega),List.getD_append previousCounters [counter] 0 lay.val (by omega)]

/-- The counter-recovering source expander is sound for every fixed oracle.
This includes arbitrary compact signatures, not only signer outputs. -/
theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig)=some w) :
    evalWithAnswerFn answers (verify message pk w)=true := by
  simp only [expand,evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at he
  | some found =>
      obtain ⟨counter,output⟩ := found
      simp only [hd,evalWithAnswerFn_bind] at he
      cases hf : evalWithAnswerFn answers (recoverFts sig (output.toNat%2^31) (selections output)) with
      | none => simp only [hf,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some forest =>
          simp only [hf,evalWithAnswerFn_bind] at he
          cases hl : evalWithAnswerFn answers (expandLayers sig (output.toNat%2^31) 4 forest) with
          | none => simp only [hl,evalWithAnswerFn_pure,reduceCtorEq] at he
          | some layers =>
              obtain ⟨root,counters⟩ := layers
              simp only [hl] at he
              split at he
              · simp only [evalWithAnswerFn_pure,reduceCtorEq] at he
              · rename_i hroot
                have hroot : root=pk := by simpa using hroot
                simp only [evalWithAnswerFn_pure,Option.some.injEq] at he
                subst w
                obtain ⟨_,hcounter,houtput,hadm⟩ := digestSearch_some_good answers sig.rho message
                  attemptLimit 0 counter output (by decide) hd
                have hnot : ¬counter.toNat ≥ attemptLimit := by omega
                have hverified := (expandLayers_verified answers sig (output.toNat%2^31) 4
                  (by decide) forest root counters hl).2
                  ⟨sig,counter,fun lay => counters.getD lay.val 0⟩ rfl (fun _ _ => rfl)
                simp only [verify,hnot,ite_false,evalWithAnswerFn_bind,houtput,hadm,
                  Bool.not_true,Bool.false_eq_true,hf,hverified,evalWithAnswerFn_pure,hroot,beq_self_eq_true]

theorem realize_eval {α : Type} (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (program : M α) :
    evalWithAnswerFn answers (realize secret program)=
      evalWithAnswerFn (answers.compose (realHandler secret)) program := by
  exact (QueryImpl.simulateQ_compose answers (realHandler secret) program).symm

theorem realized_expand_implies_verify (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (realize secret (expand message pk sig))=some w) :
    evalWithAnswerFn answers (realize secret (verify message pk w))=true := by
  rw [realize_eval] at he ⊢
  exact expand_implies_verify _ message pk sig w he

/-- Exhaustion means every counter in the searched interval failed the exact
source decoder. There is no probabilistic or independence assumption here. -/
theorem counterSearch_none_iff (answers : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter,
      evalWithAnswerFn answers (counterSearch lay tree leaf message counter fuel)=none ↔
      ∀ offset,offset < fuel → decode lay (evalWithAnswerFn answers
        (shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 (counter+offset)))))=none := by
  intro fuel
  induction fuel with
  | zero => intro counter;simp [counterSearch]
  | succ fuel ih =>
      intro counter
      simp only [counterSearch,evalWithAnswerFn_bind]
      cases hd : decode lay (evalWithAnswerFn answers
        (shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd,ih]
          constructor
          · intro hall offset hoff
            cases offset with
            | zero => simpa using hd
            | succ offset =>
                simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall offset (by omega)
          · intro hall offset hoff
            simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall (offset+1) (by omega)
      | some digits =>
          simp only [hd,evalWithAnswerFn_pure,reduceCtorEq,false_iff]
          intro hall
          have := hall 0 (by omega)
          simp only [Nat.add_zero,hd,reduceCtorEq] at this

/-- Digest exhaustion similarly means every counter in the interval failed the
actual source admissibility predicate. -/
theorem digestSearch_none_iff (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter,
      evalWithAnswerFn answers (digestSearch rho message counter fuel)=none ↔
      ∀ offset,offset < fuel → digestAdmissible (evalWithAnswerFn answers
        (digest rho message (BitVec.ofNat 32 (counter+offset))))=false := by
  intro fuel
  induction fuel with
  | zero => intro counter;simp [digestSearch]
  | succ fuel ih =>
      intro counter
      simp only [digestSearch,evalWithAnswerFn_bind]
      split
      · rename_i hgood
        simp only [evalWithAnswerFn_pure,reduceCtorEq,false_iff]
        intro hall
        have := hall 0 (by omega)
        simp only [Nat.add_zero,hgood,Bool.true_eq_false] at this
      · rename_i hbad
        have hbad : digestAdmissible (evalWithAnswerFn answers
          (digest rho message (BitVec.ofNat 32 counter)))=false := by simpa using hbad
        rw [ih]
        constructor
        · intro hall offset hoff
          cases offset with
          | zero => simpa using hbad
          | succ offset =>
              simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall offset (by omega)
        · intro hall offset hoff
          simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall (offset+1) (by omega)

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def Matches (proof : Fin 118 → Digest) (values : List Digest) (used : Nat) : Prop :=
  ∀ i,i < values.length → ∀ h : used+i < 118,proof ⟨used+i,h⟩=values.getD i 0

theorem Matches.left {proof : Fin 118 → Digest} {left right : List Digest} {used : Nat}
    (h : Matches proof (left++right) used) : Matches proof left used := by
  intro i hi hb
  rw [h i (by simp only [List.length_append];omega) hb,List.getD_append _ _ _ _ hi]

theorem Matches.right {proof : Fin 118 → Digest} {left right : List Digest} {used : Nat}
    (h : Matches proof (left++right) used) : Matches proof right (used+left.length) := by
  intro i hi hb
  have hbound : used+(left.length+i) < 118 := by omega
  have he := h (left.length+i) (by simp only [List.length_append];omega) hbound
  rw [List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left] at he
  simpa [Nat.add_assoc] using he

theorem hasLeaf_zero (leaves : List Nat) (node : Nat) :
    hasLeaf leaves 0 node=true ↔ node ∈ leaves := by
  simp only [hasLeaf,List.any_eq_true,decide_eq_true_eq,pow_zero,Nat.mul_one]
  constructor
  · rintro ⟨leaf,hleaf,hlo,hhi⟩
    have he : leaf=node := by omega
    simpa [he] using hleaf
  · intro h
    exact ⟨node,h,le_rfl,by omega⟩

theorem mapped_values_at_leaf (leaves : List Nat) (secrets : Nat → Digest)
    (node : Nat) (hnode : node ∈ leaves) :
    (leaves.map secrets).getD (leaves.idxOf node) 0=secrets node := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_idxOf hnode,
    Option.map_some,Option.getD_some]

/-- Recovering a subtree from its source frontier consumes exactly those
frontier values and returns the original node. Both the proof stream and
secret lookups are the ones used by `recoverChild`. -/
theorem recoverChild_correct (answers : Answers) (index coord : Nat)
    (nodes : Nat → Nat → Digest) (secrets : Nat → Digest)
    (hleaf : ∀ leaf,leaf < 2048 → nodes 0 leaf=evalWithAnswerFn answers (ftsLeaf index coord leaf (secrets leaf)))
    (hnode : ∀ level,level < 11 → ∀ node,node < 2^(11-(level+1)) →
      nodes (level+1) node=evalWithAnswerFn answers
        (nodeHash 10 coord index (2^(11-(level+1))+node) (nodes level (2*node)) (nodes level (2*node+1))))
    (leaves : List Nat) (values : List Digest)
    (hvalues : ∀ leaf,leaf ∈ leaves → values.getD (leaves.idxOf leaf) 0=secrets leaf)
    (proof : Fin 118 → Digest) :
    ∀ level,level ≤ 11 → ∀ node,node < 2^(11-level) → ∀ used,
      used+(frontier leaves level node).length ≤ 118 →
      Matches proof ((frontier leaves level node).map fun p => nodes p.1 p.2) used →
      evalWithAnswerFn answers (recoverChild index coord leaves values proof level node used)=
        some (nodes level node,used+(frontier leaves level node).length) := by
  intro level
  induction level with
  | zero =>
      intro _ node hn used hfit hmatch
      by_cases hh : hasLeaf leaves 0 node=true
      · have hm := (hasLeaf_zero leaves node).mp hh
        have hv := hvalues node hm
        simp only [recoverChild,hh,Bool.not_true,Bool.false_eq_true,ite_false,
          evalWithAnswerFn_bind,hv,evalWithAnswerFn_pure,← hleaf node hn,
          frontier,ite_true,List.length_nil,Nat.add_zero]
      · have hh : hasLeaf leaves 0 node=false := by simpa using hh
        simp only [frontier,hh,Bool.false_eq_true,ite_false,List.length_singleton] at hfit
        have hp := hmatch 0 (by simp [frontier,hh]) (by omega)
        simp only [frontier,hh,Bool.false_eq_true,ite_false,List.map_cons,List.map_nil,
          List.getD_cons_zero,Nat.add_zero] at hp
        simp only [recoverChild,hh,Bool.not_false,ite_true,dif_pos (show used < 118 by omega),
          evalWithAnswerFn_pure,hp,frontier,Bool.false_eq_true,ite_false,List.length_singleton]
  | succ level ih =>
      intro hl node hn used hfit hmatch
      by_cases hh : hasLeaf leaves (level+1) node=true
      · have hsplit : frontier leaves (level+1) node=
            frontier leaves level (2*node)++frontier leaves level (2*node+1) := by
          simp only [frontier,hh,ite_true]
        rw [hsplit,List.length_append] at hfit
        rw [hsplit,List.map_append] at hmatch
        have hpow : 2^(11-level)=2^(11-(level+1))*2 := by
          rw [show 11-level=(11-(level+1))+1 by omega,pow_succ]
        have hleft := ih (by omega) (2*node) (by rw [hpow];omega) used (by omega) hmatch.left
        have hright := ih (by omega) (2*node+1) (by rw [hpow];omega)
          (used+(frontier leaves level (2*node)).length) (by omega)
          (by simpa only [List.length_map] using hmatch.right)
        simp only [recoverChild,hh,Bool.not_true,Bool.false_eq_true,ite_false,
          evalWithAnswerFn_bind,hleft,hright,evalWithAnswerFn_pure,← hnode level (by omega) node hn,
          hsplit,List.length_append,Nat.add_assoc]
      · have hh : hasLeaf leaves (level+1) node=false := by simpa using hh
        simp only [frontier,hh,Bool.false_eq_true,ite_false,List.length_singleton] at hfit
        have hp := hmatch 0 (by simp [frontier,hh]) (by omega)
        simp only [frontier,hh,Bool.false_eq_true,ite_false,List.map_cons,List.map_nil,
          List.getD_cons_zero,Nat.add_zero] at hp
        simp only [recoverChild,hh,Bool.not_false,ite_true,dif_pos (show used < 118 by omega),
          evalWithAnswerFn_pure,hp,frontier,Bool.false_eq_true,ite_false,List.length_singleton]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem eval_mapM {α β : Type} (answers : Answers) (items : List α) (f : α → M β) :
    evalWithAnswerFn answers (items.mapM f)=items.map (fun x => evalWithAnswerFn answers (f x)) := by
  induction items with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure,ih,List.map_cons]

theorem eval_foldlM_list_inv {α β : Type} (answers : Answers) (items : List β)
    (f : α → β → M α) (Inv : Nat → α → Prop) (initial : α) (h0 : Inv 0 initial)
    (hs : ∀ i (hi : i < items.length) state,Inv i state →
      Inv (i+1) (evalWithAnswerFn answers (f state items[i]))) :
    Inv items.length (evalWithAnswerFn answers (items.foldlM f initial)) := by
  induction items generalizing Inv initial with
  | nil => exact h0
  | cons x xs ih =>
      rw [List.foldlM_cons,evalWithAnswerFn_bind,List.length_cons]
      exact ih (fun i => Inv (i+1)) _ (hs 0 (by simp) initial h0)
        (fun i hi state hstate => hs (i+1) (by simp;omega) state hstate)

theorem eval_foldlM_range'_inv {α : Type} (answers : Answers) (start n : Nat)
    (f : α → Nat → M α) (Inv : Nat → α → Prop) (initial : α) (h0 : Inv 0 initial)
    (hs : ∀ i,i < n → ∀ state,Inv i state →
      Inv (i+1) (evalWithAnswerFn answers (f state (start+i)))) :
    Inv n (evalWithAnswerFn answers ((List.range' start n).foldlM f initial)) := by
  have hi := eval_foldlM_list_inv answers (List.range' start n) f Inv initial h0
    (fun i hi state hstate => by
      simp only [List.getElem_range',Nat.one_mul]
      exact hs i (by simpa using hi) state hstate)
  simpa only [List.length_range'] using hi

theorem eval_buildLevel (answers : Answers) (tag lay tree h level : Nat) (nodes : List Digest) :
    evalWithAnswerFn answers (buildLevel tag lay tree h level nodes)=
      (List.range (nodes.length/2)).map fun i => evalWithAnswerFn answers
        (nodeHash tag lay tree (2^(h-level)+i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)) := by
  exact eval_mapM answers _ _

theorem eval_buildLevel_length (answers : Answers) (tag lay tree h level : Nat) (nodes : List Digest) :
    (evalWithAnswerFn answers (buildLevel tag lay tree h level nodes)).length=nodes.length/2 := by
  rw [eval_buildLevel,List.length_map,List.length_range]

theorem eval_buildLevel_getD (answers : Answers) (tag lay tree h level : Nat) (nodes : List Digest)
    (i : Nat) (hi : i < nodes.length/2) :
    (evalWithAnswerFn answers (buildLevel tag lay tree h level nodes)).getD i 0=
      evalWithAnswerFn answers (nodeHash tag lay tree (2^(h-level)+i)
        (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)) := by
  rw [eval_buildLevel]
  simp [List.getD_eq_getElem,hi]

/-- All stored levels have the expected width, preserve the initial leaves,
and satisfy the exact public node-hash recurrence. -/
def TreeLevels (answers : Answers) (tag lay tree h : Nat) (leaves : List Digest)
    (completed : Nat) (levels : List (List Digest)) : Prop :=
  Cost.LevelShape h completed levels ∧ levels.getD 0 []=leaves ∧
    ∀ level,level < completed → ∀ node,node < 2^(h-(level+1)) →
      (levels.getD (level+1) []).getD node 0=evalWithAnswerFn answers
        (nodeHash tag lay tree (2^(h-(level+1))+node)
          ((levels.getD level []).getD (2*node) 0) ((levels.getD level []).getD (2*node+1) 0))

theorem eval_buildLevels_correct (answers : Answers) (tag lay tree h : Nat)
    (leaves : List Digest) (hlen : leaves.length=2^h) :
    TreeLevels answers tag lay tree h leaves h (evalWithAnswerFn answers (buildLevels tag lay tree h leaves)) := by
  unfold buildLevels
  refine eval_foldlM_range'_inv answers 1 h _ (TreeLevels answers tag lay tree h leaves) [leaves]
    ⟨⟨rfl,?_⟩,rfl,?_⟩ (fun i hi levels hlevels => ?_)
  · intro j hj
    have he : j=0 := by omega
    subst j
    simpa using hlen
  · intro j hj
    omega
  · simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    let next := evalWithAnswerFn answers (buildLevel tag lay tree h (1+i) (levels.getD (1+i-1) []))
    have hlength : levels.length=i+1 := hlevels.1.1
    have hprevious : (levels.getD (1+i-1) []).length=2^(h-i) := by
      simpa using hlevels.1.2 i le_rfl
    have hnext : next.length=2^(h-(i+1)) := by
      rw [eval_buildLevel_length,hprevious,show h-i=h-(i+1)+1 by omega,pow_succ,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    change TreeLevels answers tag lay tree h leaves (i+1) (levels++[next])
    refine ⟨⟨by simp [hlength],?_⟩,?_,?_⟩
    · intro j hj
      by_cases hold : j ≤ i
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hlevels.1.2 j hold
      · have he : j=i+1 := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega),hlength]
        simp only [Nat.sub_self,List.getD_cons_zero]
        exact hnext
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hlevels.2.1
    · intro level hlevel node hnode
      by_cases hold : level < i
      · rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ level (by omega)]
        exact hlevels.2.2 level hold node hnode
      · have he : level=i := by omega
        subst level
        rw [List.getD_append_right _ _ _ _ (by omega),hlength]
        simp only [Nat.sub_self,List.getD_cons_zero]
        rw [List.getD_append _ _ _ i (by omega)]
        have hwidth : (levels.getD (1+i-1) []).length/2=2^(h-(i+1)) := by
          rw [hprevious,show h-i=h-(i+1)+1 by omega,pow_succ,
            Nat.mul_div_cancel _ (by decide : 0 < 2)]
        have hc := eval_buildLevel_getD answers tag lay tree h (1+i) (levels.getD (1+i-1) []) node
          (by rw [hwidth];exact hnode)
        simpa only [next,show 1+i=i+1 by omega,Nat.add_sub_cancel] using hc

theorem eval_foldlM_range_inv {α : Type} (answers : Answers) (n : Nat)
    (f : α → Nat → M α) (Inv : Nat → α → Prop) (initial : α) (h0 : Inv 0 initial)
    (hs : ∀ i,i < n → ∀ state,Inv i state →
      Inv (i+1) (evalWithAnswerFn answers (f state i))) :
    Inv n (evalWithAnswerFn answers ((List.range n).foldlM f initial)) := by
  have hi := eval_foldlM_list_inv answers (List.range n) f Inv initial h0
    (fun i hi state hstate => by
      simp only [List.getElem_range]
      exact hs i (by simpa using hi) state hstate)
  simpa only [List.length_range] using hi

def FtsRows (answers : Answers) (index coord pairs : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length=2*pairs ∧ rows.2.length=2*pairs ∧
    ∀ leaf,leaf < 2*pairs → rows.1.getD leaf 0=
      evalWithAnswerFn answers (ftsLeaf index coord leaf (rows.2.getD leaf 0))

theorem FtsRows.step (answers : Answers) (index coord pair : Nat) (rows : List Digest × List Digest)
    (hrows : FtsRows answers index coord pair rows) (left right : Digest) :
    FtsRows answers index coord (pair+1)
      (rows.1++[evalWithAnswerFn answers (ftsLeaf index coord (2*pair) left),
                 evalWithAnswerFn answers (ftsLeaf index coord (2*pair+1) right)],rows.2++[left,right]) := by
  refine ⟨by simp [hrows.1];omega,by simp [hrows.2.1];omega,?_⟩
  intro leaf hleaf
  change (rows.1++[_ , _]).getD leaf 0=evalWithAnswerFn answers
    (ftsLeaf index coord leaf ((rows.2++[left,right]).getD leaf 0))
  by_cases hold : leaf < 2*pair
  · rw [List.getD_append _ _ _ _ (by rw [hrows.1];exact hold),
      List.getD_append _ _ _ _ (by rw [hrows.2.1];exact hold)]
    exact hrows.2.2 leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hrows.1];omega),
      List.getD_append_right _ _ _ _ (by rw [hrows.2.1];omega),hrows.1,hrows.2.1]
    have he : leaf=2*pair ∨ leaf=2*pair+1 := by omega
    rcases he with rfl | rfl
    · simp
    · simp

def ftsRows (index coord : Nat) : M (List Digest × List Digest) :=
  (List.range 1024).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let (left,right) ← privatePair 8 coord index 0 pair
      let leftLeaf ← ftsLeaf index coord (2*pair) left
      let rightLeaf ← ftsLeaf index coord (2*pair+1) right
      pure (state.1++[leftLeaf,rightLeaf],state.2++[left,right])) ([],[])

theorem buildFts_eq (index coord : Nat) : buildFts index coord=(do
    let rows ← ftsRows index coord
    let levels ← buildLevels 10 coord index 11 rows.1
    pure (levels,rows.2)) := rfl

theorem eval_ftsRows_correct (answers : Answers) (index coord : Nat) :
    FtsRows answers index coord 1024 (evalWithAnswerFn answers (ftsRows index coord)) := by
  unfold ftsRows
  refine eval_foldlM_range_inv answers 1024 _ (FtsRows answers index coord) ([],[])
    ⟨rfl,rfl,by simp⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  exact FtsRows.step answers index coord pair rows hrows _ _

def treeValue (levels : List (List Digest)) (level node : Nat) : Digest :=
  (levels.getD level []).getD node 0

/-- The concrete forest builder supplies precisely the leaf and internal-node
relations used by subtree recovery. -/
theorem eval_buildFts_correct (answers : Answers) (index coord : Nat) :
    let result := evalWithAnswerFn answers (buildFts index coord)
    Cost.LevelShape 11 11 result.1 ∧ result.2.length=2048 ∧
      (∀ leaf,leaf < 2048 → treeValue result.1 0 leaf=
        evalWithAnswerFn answers (ftsLeaf index coord leaf (result.2.getD leaf 0))) ∧
      (∀ level,level < 11 → ∀ node,node < 2^(11-(level+1)) →
        treeValue result.1 (level+1) node=evalWithAnswerFn answers
          (nodeHash 10 coord index (2^(11-(level+1))+node)
            (treeValue result.1 level (2*node)) (treeValue result.1 level (2*node+1)))) := by
  rw [buildFts_eq]
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  let rows := evalWithAnswerFn answers (ftsRows index coord)
  have hr := eval_ftsRows_correct answers index coord
  have hl := eval_buildLevels_correct answers 10 coord index 11 rows.1 hr.1
  refine ⟨hl.1,hr.2.1,?_,hl.2.2⟩
  intro leaf hleaf
  change ((evalWithAnswerFn answers (buildLevels 10 coord index 11 rows.1)).getD 0 []).getD leaf 0=_
  rw [hl.2.1]
  exact hr.2.2 leaf hleaf

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Finset
open SphincsSecurity.Completeness.Octopus
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The selected leaves below a particular source tree node, in local coordinates. -/
def Located (leaves : List Nat) (level node : Nat) (selected : Finset Nat) : Prop :=
  ∀ offset,offset < 2^level → (node*2^level+offset ∈ leaves ↔ offset ∈ selected)

theorem hasLeaf_iff_nonempty {leaves : List Nat} {level node : Nat} {selected : Finset Nat}
    (hbelow : Below level selected) (hlocated : Located leaves level node selected) :
    hasLeaf leaves level node=true ↔ selected.Nonempty := by
  simp only [hasLeaf,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨leaf,hleaf,hlo,hhi⟩
    have hoff : leaf-node*2^level < 2^level := by
      rw [Nat.add_mul,Nat.one_mul] at hhi
      omega
    refine ⟨leaf-node*2^level,(hlocated _ hoff).mp ?_⟩
    simpa only [Nat.add_sub_of_le hlo] using hleaf
  · rintro ⟨offset,hoff⟩
    have hb := hbelow offset hoff
    refine ⟨node*2^level+offset,(hlocated offset hb).mpr hoff,by omega,?_⟩
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem Located.left {leaves : List Nat} {level node : Nat} {selected : Finset Nat}
    (h : Located leaves (level+1) node selected) :
    Located leaves level (2*node) (lo level selected) := by
  intro offset hoff
  have he : (2*node)*2^level+offset=node*2^(level+1)+offset := by rw [pow_succ];ring
  rw [he,h offset (by rw [pow_succ];omega)]
  simp only [lo,Finset.mem_filter]
  exact ⟨fun hm => ⟨hm,hoff⟩,And.left⟩

theorem Located.right {leaves : List Nat} {level node : Nat} {selected : Finset Nat}
    (h : Located leaves (level+1) node selected) :
    Located leaves level (2*node+1) (hi level selected) := by
  intro offset hoff
  have he : (2*node+1)*2^level+offset=node*2^(level+1)+(offset+2^level) := by rw [pow_succ];ring
  rw [he,h (offset+2^level) (by rw [pow_succ];omega)]
  simp only [hi,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro hm
    exact ⟨offset+2^level,⟨hm,by omega⟩,by omega⟩
  · rintro ⟨value,⟨hm,hv⟩,he⟩
    have he' : value=offset+2^level := by omega
    simpa only [he'] using hm

/-- The executable source frontier obeys the exact octopus formula. Empty
subtrees contribute one proof value; nonempty ones contribute `oc`. -/
theorem frontier_length_formula (leaves : List Nat) :
    ∀ level node selected,Below level selected → Located leaves level node selected →
      (frontier leaves level node).length=if selected=∅ then 1 else oc level selected := by
  intro level
  induction level with
  | zero =>
      intro node selected hb hl
      by_cases hempty : selected=∅
      · have hh : hasLeaf leaves 0 node=false := by
          have := hasLeaf_iff_nonempty hb hl
          simp [hempty] at this
          exact this
        simp [frontier,hh,hempty]
      · have hh : hasLeaf leaves 0 node=true := (hasLeaf_iff_nonempty hb hl).mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hs := below_zero hb hempty
        simp [frontier,hh,hempty,hs,oc,octH,xorSum]
  | succ level ih =>
      intro node selected hb hl
      by_cases hempty : selected=∅
      · have hh : hasLeaf leaves (level+1) node=false := by
          have := hasLeaf_iff_nonempty hb hl
          simp [hempty] at this
          exact this
        simp [frontier,hh,hempty]
      · have hh : hasLeaf leaves (level+1) node=true := (hasLeaf_iff_nonempty hb hl).mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hL := lo_below level selected
        have hR := hi_below hb
        rw [frontier,hh,if_pos rfl,List.length_append,ih _ _ hL hl.left,ih _ _ hR hl.right,if_neg hempty]
        have hsplit : glue level (lo level selected) (hi level selected)=selected := glue_lo_hi
        by_cases hleft : lo level selected=∅
        · have hright : hi level selected ≠ ∅ := by
            intro hr
            apply hempty
            rw [← hsplit,hleft,hr,glue_empty_empty]
          rw [if_pos hleft,if_neg hright]
          conv_rhs => rw [← hsplit,hleft,oc_glue_right hR hright]
          omega
        · by_cases hright : hi level selected=∅
          · rw [if_neg hleft,if_pos hright]
            conv_rhs => rw [← hsplit,hright,oc_glue_left hL hleft]
          · rw [if_neg hleft,if_neg hright]
            conv_rhs => rw [← hsplit,oc_glue_both hL hR hleft hright]

theorem authCount_eq_octH (leaves : List Nat) (hlen : leaves.length=3) (hn : leaves.Nodup) :
    authCount leaves=octH 7 leaves := by
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
  have hab : a ≠ b := by intro he;subst b;simp at hn
  have hbc : b ≠ c := by intro he;subst c;simp at hn
  have hx1 : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr hab
  have hx2 : b ^^^ c ≠ 0 := Nat.xor_ne_zero_iff.mpr hbc
  simp only [authCount,octH,xorSum,List.drop_succ_cons,List.drop_zero,List.tail_cons,
    List.zip_cons_cons,List.zip_nil_right,List.map_cons,List.map_nil,
    List.zipWith_cons_cons,List.zipWith_nil_right,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,SphincsSecurity.Concrete.bitLength,hx1,hx2,ite_false]
  omega

theorem located_bucket (leaves : List Nat) (bucket : Nat) :
    Located (leaves.map fun leaf => bucket*128+leaf) 7 bucket leaves.toFinset := by
  intro offset _
  simp only [show (2:Nat)^7=128 by decide,List.mem_map,List.mem_toFinset]
  constructor
  · rintro ⟨leaf,hleaf,he⟩
    have he' : leaf=offset := Nat.add_left_cancel he
    simpa only [he'] using hleaf
  · intro h
    exact ⟨offset,h,rfl⟩

theorem bucket_frontier_length (leaves : List Nat) (bucket : Nat)
    (hlen : leaves.length=3) (hn : leaves.Nodup) (hs : leaves.SortedLE)
    (hb : ∀ leaf,leaf ∈ leaves → leaf < 128) :
    (frontier (leaves.map fun leaf => bucket*128+leaf) 7 bucket).length=authCount leaves := by
  have hbelow : Below 7 leaves.toFinset := fun leaf hleaf => hb leaf (List.mem_toFinset.mp hleaf)
  have hne : leaves.toFinset ≠ ∅ := by
    intro he
    have hn : leaves=[] := by simpa using he
    rw [hn] at hlen
    contradiction
  rw [frontier_length_formula _ 7 bucket leaves.toFinset hbelow (located_bucket leaves bucket),
    if_neg hne,oc,(List.toFinset_sort (· ≤ ·) hn).mpr hs.pairwise]
  exact (authCount_eq_octH leaves hlen hn).symm

theorem selection_leaves_sorted (output : HashOutput) (selected : Selection)
    (h : selected ∈ selections output) : selected.leaves.SortedLE := by
  simp only [selections,List.mem_map] at h
  obtain ⟨i,_,rfl⟩ := h
  exact List.sortedLE_mergeSort

/-- The source admissibility predicate's arithmetic cap bounds the actual
recursive frontier lengths, including the three outer proof nodes per bucket. -/
theorem admissible_frontier_capacity (output : HashOutput)
    (h : admissible (selections output)=true) :
    28+((selections output).map fun selected =>
      (frontier (selected.leaves.map fun leaf => selected.bucket*128+leaf) 7 selected.bucket).length).sum ≤ 118 := by
  have hs : (∀ selected ∈ selections output,selected.leaves.Nodup) ∧
      28+((selections output).map fun selected => authCount selected.leaves).sum ≤ 118 := by
    simpa only [admissible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using h
  have hmap : ((selections output).map fun selected =>
      (frontier (selected.leaves.map fun leaf => selected.bucket*128+leaf) 7 selected.bucket).length)=
        (selections output).map (fun selected => authCount selected.leaves) := by
    apply List.map_congr_left
    intro selected hselected
    exact bucket_frontier_length selected.leaves selected.bucket
      (selection_leaves_length output selected hselected) (hs.1 selected hselected)
      (selection_leaves_sorted output selected hselected)
      (fun leaf hleaf => selection_leaf_bound output selected leaf hselected hleaf)
  rw [hmap]
  exact hs.2

/-- Direct source-level subtree reconstruction for a bucket in the actual
forest tree built by `buildFts`. -/
theorem built_bucket_recovery (answers : Answers) (index coord bucket used : Nat)
    (leaves : List Nat) (proof : Fin 118 → Digest)
    (hbucket : bucket < 16) (hlen : leaves.length=3) (hn : leaves.Nodup)
    (hs : leaves.SortedLE) (hb : ∀ leaf,leaf ∈ leaves → leaf < 128)
    (hfit : used+authCount leaves ≤ 118)
    (hproof : Matches proof ((frontier (leaves.map fun leaf => bucket*128+leaf) 7 bucket).map
      fun p => treeValue (evalWithAnswerFn answers (buildFts index coord)).1 p.1 p.2) used) :
    let built := evalWithAnswerFn answers (buildFts index coord)
    let selected := leaves.map fun leaf => bucket*128+leaf
    evalWithAnswerFn answers (recoverChild index coord selected
      (selected.map fun leaf => built.2.getD leaf 0) proof 7 bucket used)=
      some (treeValue built.1 7 bucket,used+authCount leaves) := by
  have htree := eval_buildFts_correct answers index coord
  have hcount := bucket_frontier_length leaves bucket hlen hn hs hb
  dsimp only
  rw [← hcount] at hfit ⊢
  exact recoverChild_correct answers index coord
    (treeValue (evalWithAnswerFn answers (buildFts index coord)).1)
    (fun leaf => (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0)
    htree.2.2.1 htree.2.2.2 _ _
    (fun leaf hm => mapped_values_at_leaf _ _ leaf hm) proof 7 (by decide) bucket hbucket used hfit hproof

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Cost
open OracleComp OracleSpec Finset
open Correctness SphincsSecurity.Completeness.Octopus
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def childCost (leaves : List Nat) : Nat → Nat → Nat
  | 0,node => if hasLeaf leaves 0 node then 1 else 0
  | level+1,node => if hasLeaf leaves (level+1) node then
      childCost leaves level (2*node)+childCost leaves level (2*node+1)+1 else 0

theorem bound_recoverChild (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 118 → Digest) : ∀ level node used,
    CBound (fun _ => True) (childCost leaves level node)
      (recoverChild index coord leaves values proof level node used) := by
  intro level
  induction level with
  | zero =>
      intro node used
      by_cases hh : hasLeaf leaves 0 node=true
      · simp only [childCost,recoverChild,hh,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
        exact (bound_ftsLeaf index coord node _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide)
      · have hh : hasLeaf leaves 0 node=false := by simpa using hh
        simp only [childCost,recoverChild,hh,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
        split <;> exact .pure _ 0 trivial
  | succ level ih =>
      intro node used
      by_cases hh : hasLeaf leaves (level+1) node=true
      · simp only [childCost,recoverChild,hh,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
        refine (ih (2*node) used).bind' (l := childCost leaves level (2*node+1)+1)
          (fun left _ => ?_) (by omega)
        cases left with
        | none => exact .pure _ _ trivial
        | some pair =>
            obtain ⟨left,next⟩ := pair
            refine (ih (2*node+1) next).bind' (l := 1) (fun right _ => ?_) (by omega)
            cases right with
            | none => exact .pure _ _ trivial
            | some pair =>
                obtain ⟨right,next⟩ := pair
                exact (bound_nodeHash 10 coord index _ left right).bind' (l := 0)
                  (fun _ _ => .pure _ 0 trivial) (by decide)
      · have hh : hasLeaf leaves (level+1) node=false := by simpa using hh
        simp only [childCost,recoverChild,hh,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
        split <;> exact .pure _ 0 trivial

/-- Each occupied leaf contributes two units; frontier leaves contribute one.
The minus-one convention is expressed without truncated subtraction. -/
theorem childCost_formula (leaves : List Nat) :
    ∀ level node selected,Below level selected → Located leaves level node selected →
      childCost leaves level node+1=2*selected.card+(frontier leaves level node).length := by
  intro level
  induction level with
  | zero =>
      intro node selected hb hl
      by_cases hempty : selected=∅
      · have hh : hasLeaf leaves 0 node=false := by
          have := hasLeaf_iff_nonempty hb hl
          simpa [hempty] using this
        simp [childCost,frontier,hh,hempty]
      · have hh : hasLeaf leaves 0 node=true := (hasLeaf_iff_nonempty hb hl).mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hs := below_zero hb hempty
        simp [childCost,frontier,hh,hs]
  | succ level ih =>
      intro node selected hb hl
      by_cases hempty : selected=∅
      · have hh : hasLeaf leaves (level+1) node=false := by
          have := hasLeaf_iff_nonempty hb hl
          simpa [hempty] using this
        simp [childCost,frontier,hh,hempty]
      · have hh : hasLeaf leaves (level+1) node=true := (hasLeaf_iff_nonempty hb hl).mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hL := lo_below level selected
        have hR := hi_below hb
        have hlc := ih _ _ hL hl.left
        have hrc := ih _ _ hR hl.right
        have hcard : (lo level selected).card+(hi level selected).card=selected.card := by
          rw [← card_glue hL,glue_lo_hi]
        simp only [childCost,frontier,hh,ite_true,List.length_append]
        omega

theorem bucket_childCost (leaves : List Nat) (bucket : Nat)
    (hlen : leaves.length=3) (hn : leaves.Nodup) (hs : leaves.SortedLE)
    (hb : ∀ leaf,leaf ∈ leaves → leaf < 128) :
    childCost (leaves.map fun leaf => bucket*128+leaf) 7 bucket=authCount leaves+5 := by
  have hc := childCost_formula (leaves.map fun leaf => bucket*128+leaf) 7 bucket leaves.toFinset
    (fun leaf hleaf => hb leaf (List.mem_toFinset.mp hleaf)) (located_bucket leaves bucket)
  rw [List.toFinset_card_of_nodup hn,hlen,bucket_frontier_length leaves bucket hlen hn hs hb] at hc
  omega

theorem capacity_sum (lay : Layer) :
    (∑ i ∈ range (chainCount lay),(2^width lay i-1))=capacity lay := by
  fin_cases lay <;> decide +kernel

theorem sum_finRange (n : Nat) (f : Nat → Nat) :
    ((List.finRange n).map fun i => f i.val).sum=∑ i ∈ range n,f i := by
  simp only [List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    Fin.sum_univ_eq_sum_range]

theorem remaining_steps (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length=chainCount lay) (hsum : digits.sum=target lay) :
    (∑ i ∈ range (chainCount lay),(2^width lay i-1-digits.getD i 0))=capacity lay-target lay := by
  rw [Finset.sum_tsub_distrib _ (fun i hi => hd i (Finset.mem_range.mp hi)),capacity_sum]
  rw [← hlen,sum_getD,hsum]

def recoverLayerCost (lay : Layer) : Nat := capacity lay-target lay+leafHashCost lay+height lay

theorem bound_recoverLayer (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length=chainCount lay) (hsum : digits.sum=target lay) :
    CBound (fun _ => True) (recoverLayerCost lay) (recoverLayer sig index lay digits) := by
  unfold recoverLayer
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => 2^width lay i.val-1-digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay+height lay) (fun ends hends => ?_) ?_
  · refine (bound_leafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k (by simp)
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => 2^width lay i-1-digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerCost]
    omega

def recoveryLayersCost : Nat → Nat
  | 0 => 0
  | n+1 => recoverLayerCost (Fin.ofNat 4 n)+recoveryLayersCost n

theorem recoveryLayersCost_four : recoveryLayersCost 4=485 := by decide +kernel

theorem bound_verifyLayers (w : Witness) (index : Nat) :
    ∀ n root,CBound (fun _ => True) (n+recoveryLayersCost n) (verifyLayers w index n root) := by
  intro n
  induction n with
  | zero => intro root;exact .pure _ _ trivial
  | succ n ih =>
      intro root
      unfold verifyLayers
      dsimp only
      split
      · exact .pure _ _ trivial
      · refine (bound_shortHash _ 1
          (by simp [encodingInput,SphincsSecurity.bytesLE_length])
          (by simp [encodingInput,pad64_length,SphincsSecurity.bytesLE_length])).bind'
          (l := recoverLayerCost (Fin.ofNat 4 n)+n+recoveryLayersCost n)
          (fun answer _ => ?_) (by simp only [recoveryLayersCost];omega)
        cases hd : decode (Fin.ofNat 4 n) answer with
        | none => exact .pure _ _ trivial
        | some digits =>
            exact (bound_recoverLayer w.signature index (Fin.ofNat 4 n) digits
              (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2).bind'
              (l := n+recoveryLayersCost n) (fun value _ => ih value) (by omega)

theorem bound_expandLayers (sig : Signature) (index : Nat) :
    ∀ n root,CBound (fun _ => True) (n*counterLimit+recoveryLayersCost n) (expandLayers sig index n root) := by
  intro n
  induction n with
  | zero => intro root;exact .pure _ _ trivial
  | succ n ih =>
      intro root
      unfold expandLayers
      dsimp only
      refine (bound_counterSearch (Fin.ofNat 4 n) _ _ root counterLimit 0).bind'
        (l := recoverLayerCost (Fin.ofNat 4 n)+n*counterLimit+recoveryLayersCost n)
        (fun found hf => ?_) (by simp only [recoveryLayersCost,Nat.add_mul,Nat.one_mul];omega)
      cases found with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter,digits⟩ := pair
          have hd := hf counter digits rfl
          refine (bound_recoverLayer sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
            (l := n*counterLimit+recoveryLayersCost n) (fun value _ => ?_) (by omega)
          refine (ih value).bind' (l := 0) (fun result _ => ?_) (by omega)
          cases result <;> exact .pure _ 0 trivial

def recoverOuter (sig : Signature) (index coord bucket : Nat) (initial : Option (Digest × Nat)) :
    M (Option (Digest × Nat)) :=
  (List.range 4).foldlM (fun (state : Option (Digest × Nat)) j => do
    let some (value,used) := state | pure none
    if h : used < 118 then
      let other := sig.proof ⟨used,h⟩
      let pair := if bucket/2^j%2=0 then (value,other) else (other,value)
      let parent ← nodeHash 10 coord index (2^(4-j-1)+bucket/2^(j+1)) pair.1 pair.2
      pure (some (parent,used+1))
    else pure none) initial

theorem bound_recoverOuter (sig : Signature) (index coord bucket : Nat) (initial : Option (Digest × Nat)) :
    CBound (fun _ => True) 4 (recoverOuter sig index coord bucket initial) := by
  unfold recoverOuter
  refine Bound.foldlM_range_le 4 _ (fun _ _ => True) (fun _ => 1) initial trivial
    (fun j _ state _ => ?_) (fun _ _ => trivial) (by simp)
  cases state with
  | none => exact .pure _ 1 trivial
  | some pair =>
      obtain ⟨value,used⟩ := pair
      dsimp only
      split
      · exact (bound_nodeHash _ _ _ _ _ _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide)
      · exact .pure _ 1 trivial

def forestStep (sig : Signature) (index : Nat) (chosen : List Selection) (coord : Nat)
    (state : Option (List Digest × Nat)) : M (Option (List Digest × Nat)) := do
  let some (roots,used) := state | pure none
  let sel := chosen.getD coord ⟨0,[]⟩
  let selected := sel.leaves.map (fun s => sel.bucket*128+s)
  let values := (List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)
  let some (value,next) ← recoverChild index coord selected values sig.proof 7 sel.bucket used | pure none
  let result ← recoverOuter sig index coord sel.bucket (some (value,next))
  let some (root,next) := result | pure none
  pure (some (roots++[root],next))

def forestStepCost (chosen : List Selection) (coord : Nat) : Nat :=
  let sel := chosen.getD coord ⟨0,[]⟩
  childCost (sel.leaves.map fun leaf => sel.bucket*128+leaf) 7 sel.bucket+4

def RootsLength (n : Nat) (state : Option (List Digest × Nat)) : Prop :=
  ∀ roots used,state=some (roots,used) → roots.length=n

theorem bound_forestStep (sig : Signature) (index : Nat) (chosen : List Selection) (coord : Nat)
    (state : Option (List Digest × Nat)) (hstate : RootsLength coord state) :
    CBound (RootsLength (coord+1)) (forestStepCost chosen coord) (forestStep sig index chosen coord state) := by
  unfold forestStep
  cases state with
  | none => exact .pure _ _ (by simp [RootsLength])
  | some pair =>
      obtain ⟨roots,used⟩ := pair
      have hroots := hstate roots used rfl
      dsimp only
      refine (bound_recoverChild index coord _ _ sig.proof 7 _ used).bind'
        (l := 4) (fun found _ => ?_) le_rfl
      cases found with
      | none => exact .pure _ _ (by simp [RootsLength])
      | some pair =>
          obtain ⟨value,next⟩ := pair
          refine (bound_recoverOuter sig index coord _ (some (value,next))).bind'
            (l := 0) (fun result _ => ?_) (by decide)
          cases result with
          | none => exact .pure _ 0 (by simp [RootsLength])
          | some pair =>
              obtain ⟨root,next⟩ := pair
              refine .pure _ 0 ?_
              intro otherRoots otherUsed he
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
              simp [hroots]

def forestRecoveryCost (chosen : List Selection) : Nat :=
  (∑ coord ∈ range 7,forestStepCost chosen coord)+2

theorem bound_recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) :
    CBound (fun _ => True) (forestRecoveryCost chosen) (recoverFts sig index chosen) := by
  change CBound _ _ (do
    let state ← (List.range 7).foldlM (fun state coord => forestStep sig index chosen coord state) (some ([],0))
    let some (roots,used) := state | pure none
    if !(List.range (118-used)).all (fun j =>
      decide (sig.proof ⟨(used+j)%118,Nat.mod_lt _ (by decide)⟩=0)) then return none
    pure (some (← forestPk index roots)))
  refine (Bound.foldlM_range 7 _ RootsLength (forestStepCost chosen) (some ([],0))
    (by simp [RootsLength]) (fun coord _ state hs => bound_forestStep sig index chosen coord state hs)).bind
    (fun result hr => ?_)
  cases result with
  | none => exact .pure _ 2 trivial
  | some pair =>
      obtain ⟨roots,used⟩ := pair
      have hroots := hr roots used rfl
      dsimp only
      split
      · exact .pure _ 2 trivial
      · exact (bound_forestPk index roots hroots).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by decide)

theorem sum_getD_apply {α : Type} (items : List α) (fallback : α) (f : α → Nat) :
    (∑ i ∈ range items.length,f (items.getD i fallback))=(items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons,Finset.sum_range_succ',List.map_cons,List.sum_cons]
      simp only [List.getD_cons_succ,List.getD_cons_zero,ih]
      omega

theorem forestRecoveryCost_le (output : HashOutput) (hadm : admissible (selections output)=true) :
    forestRecoveryCost (selections output) ≤ 158 := by
  have hs : (∀ selected ∈ selections output,selected.leaves.Nodup) ∧
      28+((selections output).map fun selected => authCount selected.leaves).sum ≤ 118 := by
    simpa only [admissible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using hadm
  have hstep : ∀ coord ∈ range 7,forestStepCost (selections output) coord=
      authCount ((selections output).getD coord ⟨0,[]⟩).leaves+9 := by
    intro coord hcoord
    have hc : coord < (selections output).length := by rw [selections_length];exact Finset.mem_range.mp hcoord
    have hm : (selections output).getD coord ⟨0,[]⟩ ∈ selections output := by
      rw [List.getD_eq_getElem _ _ hc]
      exact List.getElem_mem hc
    dsimp only [forestStepCost]
    rw [bucket_childCost _ _ (selection_leaves_length output _ hm) (hs.1 _ hm)
      (selection_leaves_sorted output _ hm) (fun leaf hl => selection_leaf_bound output _ leaf hm hl)]
  unfold forestRecoveryCost
  rw [Finset.sum_congr rfl hstep,Finset.sum_add_distrib,sum_const_range,
    ← selections_length output,sum_getD_apply (selections output) ⟨0,[]⟩ (fun selected => authCount selected.leaves)]
  have hc := hs.2
  rw [selections_length]
  omega

/-- All source verifier executions fit this bound, including malformed
witnesses and rejection paths. It is a compression count, not a cycle count. -/
theorem bound_verify (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 648 (verify message pk w) := by
  unfold verify
  split
  · exact .pure _ _ trivial
  · refine (bound_digest w.signature.rho message w.digestCounter).bind' (l := 647)
      (fun output _ => ?_) (by decide)
    dsimp only
    split
    · exact .pure _ _ trivial
    · rename_i hadm
      have hgood : digestAdmissible output=true := by simpa using hadm
      have hadm : admissible (selections output)=true :=
        (Bool.and_eq_true_iff.mp hgood).1
      refine ((bound_recoverFts w.signature (output.toNat%2^31) (selections output)).mono_k
        (forestRecoveryCost_le output hadm)).bind' (l := 489) (fun forest _ => ?_) (by decide)
      cases forest with
      | none => exact .pure _ _ trivial
      | some forest =>
          refine (bound_verifyLayers w (output.toNat%2^31) 4 forest).bind'
            (l := 0) (fun root _ => ?_) (by rw [recoveryLayersCost_four])
          cases root <;> exact .pure _ 0 trivial

theorem verify_compression_bound (secret : BitVec 256) (message : Message) (pk : Digest) (w : Witness) :
    ∀ result ∈ support (World.countBlocks (realize secret (verify message pk w))),result.2 ≤ 648 := by
  intro result hr
  rw [World.countBlocks,← realize_count] at hr
  exact (bound_verify message pk w).count_support result (realize_support_subset secret _ hr) |>.2

theorem bound_expand (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (attemptLimit+4*counterLimit+643) (expand message pk sig) := by
  unfold expand
  refine (bound_digestSearch sig.rho message attemptLimit 0).bind' (l := 4*counterLimit+643)
    (fun found hf => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter,output⟩ := pair
      have hadm := hf counter output rfl
      dsimp only
      refine ((bound_recoverFts sig (output.toNat%2^31) (selections output)).mono_k
        (forestRecoveryCost_le output hadm)).bind' (l := 4*counterLimit+485)
        (fun forest _ => ?_) (by omega)
      cases forest with
      | none => exact .pure _ _ trivial
      | some forest =>
          refine (bound_expandLayers sig (output.toNat%2^31) 4 forest).bind' (l := 0)
            (fun layers _ => ?_) (by rw [recoveryLayersCost_four])
          cases layers with
          | none => exact .pure _ 0 trivial
          | some pair =>
              obtain ⟨root,counters⟩ := pair
              dsimp only
              split <;> exact .pure _ 0 trivial

theorem expand_compression_ceiling (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) :
    ∀ result ∈ support (World.countBlocks (realize secret (expand message pk sig))),
      result.2 ≤ 17826435 := by
  intro result hr
  rw [World.countBlocks,← realize_count] at hr
  exact (bound_expand message pk sig).count_support result (realize_support_subset secret _ hr) |>.2

end SigGolfCandidate.T3.Cost


namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

abbrev RawM := OracleComp SphincsSecurity.HashSpec

def publicHandler : QueryImpl SphincsSecurity.HashSpec M :=
  fun input => T3.Spec.query (.inl (.inr input))

def publicProgram {α : Type} (program : RawM α) : M α := simulateQ publicHandler program

/-- Programs containing only public hash queries have exactly the raw random-
oracle semantics after private-input realization. -/
theorem public_randomOracle {α : Type} (secret : BitVec 256) (program : RawM α) :
    simulateQ SphincsSecurity.romImpl (realize secret (publicProgram program))=
      simulateQ (randomOracle (spec := SphincsSecurity.HashSpec)) program := by
  unfold realize publicProgram
  rw [← QueryImpl.simulateQ_compose,← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  simp only [QueryImpl.compose,publicHandler,simulateQ_spec_query,realHandler,SphincsSecurity.romImpl]
  rfl

def encodingTrial (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) : HashInput :=
  pad64 (encodingInput lay tree leaf message (BitVec.ofNat 32 counter))

def digestTrial (rho : Digest) (message : Message) (counter : Nat) : HashInput :=
  pad64 (digestInput rho message (BitVec.ofNat 32 counter))

def encodingDecode (lay : Layer) (answer : HashOutput) : Option (List Nat) :=
  decode lay (answer.extractLsb' 0 128)

def digestDecode (answer : HashOutput) : Option HashOutput :=
  if digestAdmissible answer then some answer else none

theorem counterSearch_public (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter,counterSearch lay tree leaf message counter fuel=
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (encodingTrial lay tree leaf message) (encodingDecode lay)
        (fun c digits => pure (BitVec.ofNat 32 c,digits)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter;rfl
  | succ fuel ih =>
      intro counter
      rw [counterSearch,SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram,simulateQ_bind,simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash,HasQuery.query,publicHandler,
        shortHash,publicHash,bind_assoc,pure_bind,encodingTrial,encodingDecode]
      apply bind_congr
      intro answer
      cases hd : decode lay (answer.extractLsb' 0 128) <;>
        simp only [simulateQ_map,simulateQ_pure,map_pure,ih,publicProgram]

theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter,digestSearch rho message counter fuel=
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (digestTrial rho message) digestDecode
        (fun c output => pure (BitVec.ofNat 32 c,output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter;rfl
  | succ fuel ih =>
      intro counter
      rw [digestSearch,SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram,simulateQ_bind,simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash,HasQuery.query,publicHandler,
        digest,publicHash,bind_assoc,pure_bind,digestTrial,digestDecode]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_map,simulateQ_pure,map_pure,ih,publicProgram]

theorem pad64_inj_of_length {left right : HashInput} (hlen : left.length=right.length)
    (he : pad64 left=pad64 right) : left=right :=
  (List.append_inj he hlen).1

theorem encodingTrial_injective (lay : Layer) (tree leaf : Nat) (message : Digest)
    {left right : Nat} (hl : left < 2^32) (hr : right < 2^32)
    (he : encodingTrial lay tree leaf message left=encodingTrial lay tree leaf message right) : left=right := by
  have he := pad64_inj_of_length (by simp [encodingInput,SphincsSecurity.bytesLE_length]) he
  simp only [encodingInput,List.append_cancel_left_eq] at he
  have hc := congrArg BitVec.toNat (SphincsSecurity.bytesLE_injective he)
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr] using hc

theorem digestTrial_injective (rho : Digest) (message : Message)
    {left right : Nat} (hl : left < 2^32) (hr : right < 2^32)
    (he : digestTrial rho message left=digestTrial rho message right) : left=right := by
  have he := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  have hc := congrArg BitVec.toNat (digestInput_injective he).2.2
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr] using hc

/-- Exact source counter search exhaustion is bounded by the fresh-answer
rejection mass to the number of trials. Freshness is an explicit obligation. -/
theorem counterSearch_failure (secret : BitVec 256) (lay : Layer) (tree leaf : Nat) (message : Digest)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (encodingTrial lay tree leaf message c)=none) :
    Pr[fun result => result.1=none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (counterSearch lay tree leaf message counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass (encodingDecode lay)^fuel := by
  rw [counterSearch_public,public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2^32)
    (fun _ _ hl hr he => encodingTrial_injective lay tree leaf message hl hr he)
    fuel counter hlimit cache hfresh

theorem digestSearch_failure (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none) :
    Pr[fun result => result.1=none |
      (simulateQ SphincsSecurity.romImpl (realize secret (digestSearch rho message counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass digestDecode^fuel := by
  rw [digestSearch_public,public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2^32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh

end SigGolfCandidate.T3.Sampling


namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

abbrev RCache := QueryCache SphincsSecurity.HashSpec

noncomputable def roRun {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) :
    ProbComp (α × RCache) := (simulateQ SphincsSecurity.romImpl (realize secret program)).run cache

theorem roRun_bind {α β : Type} (secret : BitVec 256) (program : M α) (next : α → M β) (cache : RCache) :
    roRun secret (program >>= next) cache=roRun secret program cache >>= fun result => roRun secret (next result.1) result.2 := by
  simp only [roRun,realize_bind,simulateQ_bind,StateT.run_bind]

theorem roRun_map {α β : Type} (secret : BitVec 256) (f : α → β) (program : M α) (cache : RCache) :
    roRun secret (f <$> program) cache=(fun result => (f result.1,result.2)) <$> roRun secret program cache := by
  simp only [roRun,realize_map,simulateQ_map,StateT.run_map]

@[simp] theorem roRun_pure {α : Type} (secret : BitVec 256) (value : α) (cache : RCache) :
    roRun secret (pure value : M α) cache=pure (value,cache) := by
  simp [roRun,realize]

/-- The source compression exponential moment, under concrete secret realization. -/
noncomputable def V {α : Type} (secret : BitVec 256) (z : ENNReal) (program : M α) (cache : RCache) : ENNReal :=
  expectedValue (roRun secret (countBlocks program) cache) (fun result => z^result.1.2)

/-- The moment is exactly that of the realized source's concrete compression
count, including private-call input blocks. -/
theorem V_realized {α : Type} (secret : BitVec 256) (z : ENNReal) (program : M α) (cache : RCache) :
    V secret z program cache=expectedValue
      ((simulateQ SphincsSecurity.romImpl (World.countBlocks (realize secret program))).run cache)
      (fun result => z^result.1.2) := by
  unfold V roRun countBlocks World.countBlocks
  rw [realize_count]

@[simp] theorem V_pure {α : Type} (secret : BitVec 256) (z : ENNReal) (value : α) (cache : RCache) :
    V secret z (pure value : M α) cache=1 := by simp [V,countBlocks]

theorem ev_const_mul {α : Type} (program : ProbComp α) (f : α → ENNReal) (a : ENNReal) :
    expectedValue program (fun value => a*f value)=a*expectedValue program f := by
  simp only [mul_comm a]
  exact expectedValue_mul_const program f a

theorem V_bind_eq {α β : Type} (secret : BitVec 256) (z : ENNReal) (program : M α) (next : α → M β)
    (cache : RCache) : V secret z (program >>= next) cache=
      expectedValue (roRun secret (countBlocks program) cache)
        (fun result => z^result.1.2*V secret z (next result.1.1) result.2) := by
  unfold V countBlocks
  rw [countWith_bind,roRun_bind,expectedValue_bind]
  congr 1
  funext result
  rw [roRun_map,expectedValue_map]
  simp only [pow_add]
  exact ev_const_mul _ _ _

theorem count_reaches {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache)
    (result : (α × Nat) × RCache) (hr : result ∈ support (roRun secret (countBlocks program) cache)) :
    (result.1.1,result.2) ∈ support (roRun secret program cache) := by
  have he : roRun secret program cache=(fun value => (value.1.1,value.2)) <$>
      roRun secret (countBlocks program) cache := by
    conv_lhs => rw [← fst_countWith weight program]
    rw [roRun_map]
    rfl
  rw [he,support_map]
  exact ⟨result,hr,rfl⟩

theorem V_bind_le {α β : Type} (secret : BitVec 256) (z : ENNReal) (program : M α) (next : α → M β)
    (cache : RCache) (bound : ENNReal)
    (h : ∀ result ∈ support (roRun secret program cache),V secret z (next result.1) result.2 ≤ bound) :
    V secret z (program >>= next) cache ≤ V secret z program cache*bound := by
  rw [V_bind_eq]
  change expectedValue (roRun secret (countBlocks program) cache) _ ≤
    expectedValue (roRun secret (countBlocks program) cache) _*bound
  rw [← expectedValue_mul_const]
  apply expectedValue_mono_of_support
  intro result hr
  have hc := count_reaches secret program cache result hr
  have hn : V secret z (next result.1.1) result.2 ≤ bound := h (result.1.1,result.2) hc
  exact mul_le_mul' (le_refl (z^result.1.2)) hn

theorem V_map {α β : Type} (secret : BitVec 256) (z : ENNReal) (f : α → β) (program : M α) (cache : RCache) :
    V secret z (f <$> program) cache=V secret z program cache := by
  rw [map_eq_bind_pure_comp,V_bind_eq,V]
  simp

theorem V_of_bound {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat} {program : M α}
    (h : Bound P Post k program) (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z) (cache : RCache) :
    V secret z program cache ≤ z^k := by
  apply expectedValue_le_of_support
  intro result hr
  have hs : result.1 ∈ support (realize secret (countBlocks program)) := by
    apply support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache
    rw [StateT.run'_eq,support_map]
    exact ⟨result,hr,rfl⟩
  have hc := (h.count_support result.1 (realize_support_subset secret _ hs)).2
  exact pow_le_pow_right₀ hz hc

abbrev publicQuery (input : HashInput) : M HashOutput := T3.Spec.query (.inl (.inr input))

theorem roRun_publicQuery (secret : BitVec 256) (input : HashInput) (cache : RCache) :
    roRun secret (publicQuery input) cache=(randomOracle (spec := SphincsSecurity.HashSpec) input).run cache := by
  change (simulateQ SphincsSecurity.romImpl
    (realize secret (publicProgram (SphincsSecurity.HashSpec.query input)))).run cache=_
  rw [public_randomOracle,simulateQ_spec_query]

theorem V_publicQuery {α : Type} (secret : BitVec 256) (z : ENNReal) (input : HashInput)
    (next : HashOutput → M α) (cache : RCache) :
    V secret z (publicQuery input >>= next) cache=z^(input.length/64)*
      expectedValue ((randomOracle (spec := SphincsSecurity.HashSpec) input).run cache)
        (fun result => V secret z (next result.1) result.2) := by
  rw [V_bind_eq]
  unfold countBlocks
  change expectedValue (roRun secret (countWith weight (qry (.inl (.inr input)))) cache) _=_
  rw [countWith_query,roRun_map,expectedValue_map]
  change expectedValue (roRun secret (publicQuery input) cache)
    (fun result => z^(input.length/64)*V secret z (next result.1) result.2)=_
  rw [roRun_publicQuery]
  exact ev_const_mul _ _ _

theorem expectedValue_fresh (input : HashInput) (cache : RCache) (hfresh : cache input=none)
    (f : HashOutput × RCache → ENNReal) :
    expectedValue ((randomOracle (spec := SphincsSecurity.HashSpec) input).run cache) f=
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => f (answer,cache.cacheQuery input answer)) := by
  rw [randomOracle.run_eq,hfresh]
  simp only
  rw [expectedValue_bind]
  simp
  rfl

end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Cost
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem ev_ite_le (P : HashOutput → Prop) [DecidablePred P] (a b : ENNReal)
    (g : HashOutput → ENNReal) (hg : ∀ answer,g answer ≤ if P answer then a else b) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g ≤
      Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]*a+
        Pr[fun answer => ¬P answer | ($ᵗ HashOutput : ProbComp HashOutput)]*b := by
  calc expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g
      ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun answer => (if P answer then 1 else 0)*a+(if ¬P answer then 1 else 0)*b) :=
        expectedValue_mono _ fun answer => (hg answer).trans (by by_cases h : P answer <;> simp [h])
    _ = _ := by
      rw [expectedValue_add,expectedValue_mul_const,expectedValue_mul_const,
        expectedValue_ite_one,expectedValue_ite_one]

theorem probEvent_not (P : HashOutput → Prop) [DecidablePred P] :
    Pr[fun answer => ¬P answer | ($ᵗ HashOutput : ProbComp HashOutput)]=
      1-Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  have hf : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)]=0 := by simp
  rw [hf,tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc)

theorem publicSearch_succ {β γ : Type} (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (fuel counter : Nat) :
    publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) (fuel+1) counter)=
      publicQuery (inputs counter) >>= fun answer => match decoder answer with
        | none => publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel (counter+1))
        | some value => pure (some (result counter value)) := by
  rw [searchLoop]
  simp only [publicProgram,simulateQ_bind,SphincsSecurity.Concrete.oracleHash,HasQuery.query,
    simulateQ_spec_query,publicHandler]
  apply bind_congr
  intro answer
  cases decoder answer <;> simp only [simulateQ_map,simulateQ_pure,map_pure]

/-- Geometric exponential-moment bound for a source search over fresh one-block
inputs. The trial cost is the concrete compression count after realization. -/
theorem V_publicSearch {β γ : Type} (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β) (result : Nat → β → γ)
    (bound : Nat)
    (hinput : ∀ counter,counter < bound → (inputs counter).length=64)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right)
    (hstep : z*(failMass decoder*b+(1-failMass decoder)) ≤ b) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      (∀ c,counter ≤ c → c < bound → cache (inputs c)=none) →
      V secret z (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _
      simpa [searchLoop,publicProgram] using hb
  | succ fuel ih =>
      intro counter hlimit cache hfresh
      rw [publicSearch_succ,V_publicQuery,hinput counter (by omega)]
      simp only [show (64 : Nat)/64=1 by decide,pow_one]
      rw [expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      refine (mul_le_mul' le_rfl (ev_ite_le (fun answer => decoder answer=none) b 1 _ (fun answer => ?_))).trans ?_
      · cases hd : decoder answer with
        | some value => simp
        | none =>
            simp only [if_true]
            apply ih (counter+1) (by omega) _
            intro c hstart hc
            rw [QueryCache.cacheQuery_of_ne]
            · exact hfresh c (by omega) hc
            · intro he
              have he' := hinj c counter hc (by omega) he
              omega
      · rw [probEvent_not,mul_one]
        have hrho : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
          rw [failMass_eq_probEvent]
          rfl
        rw [← hrho]
        exact hstep

theorem encodingTrial_length (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) :
    (encodingTrial lay tree leaf message counter).length=64 := by
  simp [encodingTrial,encodingInput,Cost.pad64_length,SphincsSecurity.bytesLE_length]

theorem digestTrial_length (rho : Digest) (message : Message) (counter : Nat) :
    (digestTrial rho message counter).length=64 := by
  simp [digestTrial,digestInput,Cost.pad64_length,SphincsSecurity.bytesLE_length]

theorem V_counterSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (lay : Layer) (tree leaf : Nat) (message : Digest)
    (hstep : z*(failMass (encodingDecode lay)*b+(1-failMass (encodingDecode lay))) ≤ b)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (encodingTrial lay tree leaf message c)=none) :
    V secret z (counterSearch lay tree leaf message counter fuel) cache ≤ b := by
  rw [counterSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2^32)
    (fun c _ => encodingTrial_length lay tree leaf message c)
    (fun _ _ hl hr he => encodingTrial_injective lay tree leaf message hl hr he)
    hstep fuel counter hlimit cache hfresh

theorem V_digestSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (rho : Digest) (message : Message)
    (hstep : z*(failMass digestDecode*b+(1-failMass digestDecode)) ≤ b)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none) :
    V secret z (digestSearch rho message counter fuel) cache ≤ b := by
  rw [digestSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2^32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh

end SigGolfCandidate.T3.Sampling


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def CacheTagCorrect (answers : Answers) (result : Digest × Cache) : Prop :=
  result.2.tag=evalWithAnswerFn answers (privateMac result.2.region)

theorem cache_payload_tag (answers : Answers) (payload : M (Digest × Region)) :
    CacheTagCorrect answers (evalWithAnswerFn answers (do
      let (publicKey,region) ← payload
      let tag ← privateMac region
      pure (publicKey,Cache.mk tag region))) := by
  unfold CacheTagCorrect
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]

/-- The cached MAC is exactly the result of the same query checked by signing. -/
theorem keygen_cache_tag (answers : Answers) :
    CacheTagCorrect answers (evalWithAnswerFn answers keygen) := by
  exact cache_payload_tag answers keygenPayload

theorem sign_valid_cache (answers : Answers) (result : Digest × Cache) (message : Message)
    (hvalid : CacheTagCorrect answers result) :
    evalWithAnswerFn answers (sign result.2 message)=
      evalWithAnswerFn answers (signPayload result.2 message) := by
  simp only [CacheTagCorrect] at hvalid
  simp only [sign,evalWithAnswerFn_bind,← hvalid,ne_eq,not_true_eq_false,ite_false]

theorem sign_honest_cache (answers : Answers) (message : Message) :
    evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message)=
      evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  exact sign_valid_cache answers _ message (keygen_cache_tag answers)

theorem privateMac_count (region : Region) :
    countBlocks (privateMac region)=(fun tag => (tag,513)) <$> privateMac region := by
  exact countWith_query weight (.inr (.inr (.inr region)))

/-- A rejected cache spends exactly the MAC's 513 compressions. -/
theorem sign_bad_cache_count (answers : Answers) (cache : Cache) (message : Message)
    (hbad : evalWithAnswerFn answers (privateMac cache.region) ≠ cache.tag) :
    evalWithAnswerFn answers (countBlocks (sign cache message))=(none,513) := by
  unfold sign countBlocks
  rw [countWith_bind]
  change evalWithAnswerFn answers (countBlocks (privateMac cache.region) >>= _) = _
  rw [privateMac_count,evalWithAnswerFn_bind,evalWithAnswerFn_map]
  simp only [hbad,ite_true,countWith_pure,evalWithAnswerFn_map,evalWithAnswerFn_pure,Nat.add_zero]
  rw [if_pos hbad,countWith_pure,evalWithAnswerFn_pure]
  rfl

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem chain_add (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    chain lay tree leaf i start (a+b) value=
      (chain lay tree leaf i start a value >>= chain lay tree leaf i (start+a) b) := by
  unfold chain
  rw [← List.range'_append_1,List.foldlM_append]

theorem eval_chain_add (answers : Answers) (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    evalWithAnswerFn answers (chain lay tree leaf i start (a+b) value)=
      evalWithAnswerFn answers (chain lay tree leaf i (start+a) b
        (evalWithAnswerFn answers (chain lay tree leaf i start a value))) := by
  rw [chain_add,evalWithAnswerFn_bind]

def leafSeed (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  let seeds := evalWithAnswerFn answers (privatePair 0 lay.val tree (i/2) leaf)
  if i%2=0 then seeds.1 else seeds.2

def leafValue (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) : Digest :=
  evalWithAnswerFn answers (chain lay tree leaf i 0 (digits.getD i 0) (leafSeed answers lay tree leaf i))

def leafEnd (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  evalWithAnswerFn answers (chain lay tree leaf i 0 (2^width lay i-1) (leafSeed answers lay tree leaf i))

theorem leafSeed_pair (answers : Answers) (lay : Layer) (tree leaf pair half : Nat) (hh : half < 2) :
    leafSeed answers lay tree leaf (2*pair+half)=
      if half=0 then (evalWithAnswerFn answers (privatePair 0 lay.val tree pair leaf)).1
      else (evalWithAnswerFn answers (privatePair 0 lay.val tree pair leaf)).2 := by
  unfold leafSeed
  have hd : (2*pair+half)/2=pair := by omega
  have hm : (2*pair+half)%2=half := by omega
  rw [hd,hm]

theorem leafValue_completes (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) (i : Nat) (hi : i < chainCount lay) :
    evalWithAnswerFn answers (chain lay tree leaf i (digits.getD i 0)
      (2^width lay i-1-digits.getD i 0) (leafValue answers lay tree leaf digits i))=
      leafEnd answers lay tree leaf i := by
  unfold leafValue leafEnd
  have hd := hvalid i hi
  have hc := eval_chain_add answers lay tree leaf i 0 (digits.getD i 0)
    (2^width lay i-1-digits.getD i 0) (leafSeed answers lay tree leaf i)
  rw [Nat.zero_add,Nat.add_sub_of_le hd] at hc
  exact hc.symm

def LeafRows (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length=(if signatureOnly then 0 else min done (chainCount lay)) ∧
  rows.2.length=min done (chainCount lay) ∧
  (∀ i,i < rows.1.length → rows.1.getD i 0=leafEnd answers lay tree leaf i) ∧
  (∀ i,i < rows.2.length → rows.2.getD i 0=leafValue answers lay tree leaf digits i)

theorem getD_append_singleton (xs : List Digest) (value : Digest) (i : Nat) :
    (xs++[value]).getD i 0=if i < xs.length then xs.getD i 0 else if i=xs.length then value else 0 := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi,if_pos hi]
  · rw [List.getD_append_right _ _ _ _ (by omega),if_neg hi]
    by_cases he : i=xs.length
    · subst i;simp
    · rw [if_neg he]
      exact List.getD_eq_default [value] 0 (by simp;omega)

theorem LeafRows.append (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) (i : Nat) (rows : List Digest × List Digest)
    (hrows : LeafRows answers lay tree leaf digits signatureOnly i rows) (hi : i < chainCount lay) :
    LeafRows answers lay tree leaf digits signatureOnly (i+1)
      ((if signatureOnly then rows.1 else rows.1++[leafEnd answers lay tree leaf i]),
       rows.2++[leafValue answers lay tree leaf digits i]) := by
  have hmin : min i (chainCount lay)=i := min_eq_left (by omega)
  have hnext : min (i+1) (chainCount lay)=i+1 := min_eq_left (by omega)
  unfold LeafRows at hrows ⊢
  rcases hrows with ⟨hends,hvals,he,hv⟩
  rw [hmin] at hends hvals
  cases signatureOnly <;> simp only [Bool.false_eq_true,↓reduceIte] at hends ⊢
  · refine ⟨by simp [hends,hnext],by simp [hvals,hnext],?_,?_⟩
    · intro j hj
      rw [getD_append_singleton,hends]
      split
      · exact he j (by omega)
      · have hj' : j=i := by simp only [List.length_append,List.length_singleton,hends] at hj;omega
        subst j;simp
    · intro j hj
      rw [getD_append_singleton,hvals]
      split
      · exact hv j (by omega)
      · have hj' : j=i := by simp only [List.length_append,List.length_singleton,hvals] at hj;omega
        subst j;simp
  · refine ⟨hends,by simp [hvals,hnext],he,?_⟩
    intro j hj
    rw [getD_append_singleton,hvals]
    split
    · exact hv j (by omega)
    · have hj' : j=i := by simp only [List.length_append,List.length_singleton,hvals] at hj;omega
      subst j;simp

def leafHalf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool)
    (pair : Nat) (seeds : Digest × Digest) (rows : List Digest × List Digest) (half : Nat) :
    M (List Digest × List Digest) := do
  let i := 2*pair+half
  if chainCount lay ≤ i then return rows
  let seed := if half=0 then seeds.1 else seeds.2
  let digit := digits.getD i 0
  let value ← chain lay tree leaf i 0 digit seed
  if signatureOnly then return (rows.1,rows.2++[value])
  let last ← chain lay tree leaf i digit (2^width lay i-1-digit) value
  pure (rows.1++[last],rows.2++[value])

theorem LeafRows.half (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : ValidDigits lay digits) (signatureOnly : Bool) (pair half : Nat) (hh : half < 2)
    (rows : List Digest × List Digest)
    (hrows : LeafRows answers lay tree leaf digits signatureOnly (2*pair+half) rows) :
    LeafRows answers lay tree leaf digits signatureOnly (2*pair+(half+1))
      (evalWithAnswerFn answers (leafHalf lay tree leaf digits signatureOnly pair
        (evalWithAnswerFn answers (privatePair 0 lay.val tree pair leaf)) rows half)) := by
  unfold leafHalf
  by_cases hi : chainCount lay ≤ 2*pair+half
  · simp only [hi,ite_true,evalWithAnswerFn_pure]
    simpa only [LeafRows,min_eq_right hi,min_eq_right (show chainCount lay ≤ 2*pair+(half+1) by omega)] using hrows
  · simp only [hi,ite_false,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    rw [← leafSeed_pair answers lay tree leaf pair half hh]
    change LeafRows answers lay tree leaf digits signatureOnly (2*pair+(half+1))
      (evalWithAnswerFn answers (if signatureOnly then pure (rows.1,rows.2++[leafValue answers lay tree leaf digits (2*pair+half)])
      else do
        let last ← chain lay tree leaf (2*pair+half) (digits.getD (2*pair+half) 0)
          (2^width lay (2*pair+half)-1-digits.getD (2*pair+half) 0)
          (leafValue answers lay tree leaf digits (2*pair+half))
        pure (rows.1++[last],rows.2++[leafValue answers lay tree leaf digits (2*pair+half)])))
    have ha := LeafRows.append answers lay tree leaf digits signatureOnly (2*pair+half) rows hrows (by omega)
    cases signatureOnly <;> simpa only [Bool.false_eq_true,↓reduceIte,evalWithAnswerFn_bind,
      evalWithAnswerFn_pure,leafValue_completes answers lay tree leaf digits hvalid (2*pair+half) (by omega),Nat.add_assoc] using ha

def leafRows (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    M (List Digest × List Digest) :=
  (List.range ((chainCount lay+1)/2)).foldlM (fun rows pair => do
    let seeds ← privatePair 0 lay.val tree pair leaf
    (List.range 2).foldlM (leafHalf lay tree leaf digits signatureOnly pair seeds) rows) ([],[])

theorem buildLeaf_eq (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    buildLeaf lay tree leaf digits signatureOnly=(do
      let rows ← leafRows lay tree leaf digits signatureOnly
      if signatureOnly then return (0,rows.2)
      let root ← leafHash lay tree leaf rows.1
      pure (root,rows.2)) := rfl

theorem eval_leafRows_correct (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : ValidDigits lay digits) (signatureOnly : Bool) :
    LeafRows answers lay tree leaf digits signatureOnly (2*((chainCount lay+1)/2))
      (evalWithAnswerFn answers (leafRows lay tree leaf digits signatureOnly)) := by
  unfold leafRows
  refine eval_foldlM_range_inv answers _ _
    (fun pair => LeafRows answers lay tree leaf digits signatureOnly (2*pair)) ([],[]) ?_ ?_
  · simp [LeafRows]
  · intro pair hp rows hrows
    rw [evalWithAnswerFn_bind]
    have hh := eval_foldlM_range_inv answers 2
      (leafHalf lay tree leaf digits signatureOnly pair (evalWithAnswerFn answers (privatePair 0 lay.val tree pair leaf)))
      (fun half => LeafRows answers lay tree leaf digits signatureOnly (2*pair+half)) rows
      (by simpa using hrows) (fun half hhalf rows hrows =>
        LeafRows.half answers lay tree leaf digits hvalid signatureOnly pair half hhalf rows hrows)
    simpa only [Nat.mul_add,Nat.mul_one] using hh

theorem list_eq_range_map (values : List Digest) (f : Nat → Digest) (n : Nat)
    (hlen : values.length=n) (hval : ∀ i,i < n → values.getD i 0=f i) :
    values=(List.range n).map f := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hj
  simpa only [List.getElem_map,List.getElem_range] using
    (List.getD_eq_getElem values 0 hi).symm.trans (hval i (by omega))

def leafRoot (answers : Answers) (lay : Layer) (tree leaf : Nat) : Digest :=
  evalWithAnswerFn answers (leafHash lay tree leaf ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf)))

theorem eval_buildLeaf_root (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) :
    (evalWithAnswerFn answers (buildLeaf lay tree leaf digits)).1=leafRoot answers lay tree leaf := by
  have hr := eval_leafRows_correct answers lay tree leaf digits hvalid false
  have hn : chainCount lay ≤ 2*((chainCount lay+1)/2) := by omega
  simp only [LeafRows,Bool.false_eq_true,ite_false,min_eq_right hn] at hr
  have he := list_eq_range_map _ (leafEnd answers lay tree leaf) _ hr.1
    (fun i hi => hr.2.2.1 i (by rw [hr.1];exact hi))
  rw [buildLeaf_eq]
  simp only [evalWithAnswerFn_bind,Bool.false_eq_true,ite_false,evalWithAnswerFn_pure,he]
  rfl

theorem eval_buildLeaf_values (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) (signatureOnly : Bool) :
    (evalWithAnswerFn answers (buildLeaf lay tree leaf digits signatureOnly)).2=
      (List.range (chainCount lay)).map (leafValue answers lay tree leaf digits) := by
  have hr := eval_leafRows_correct answers lay tree leaf digits hvalid signatureOnly
  have hn : chainCount lay ≤ 2*((chainCount lay+1)/2) := by omega
  simp only [LeafRows,min_eq_right hn] at hr
  have he := list_eq_range_map _ (leafValue answers lay tree leaf digits) _ hr.2.1
    (fun i hi => hr.2.2.2 i (by rw [hr.2.1];exact hi))
  rw [buildLeaf_eq]
  cases signatureOnly <;> simp only [evalWithAnswerFn_bind,Bool.false_eq_true,↓reduceIte,evalWithAnswerFn_pure,he]

/-- Completing each emitted chain value gives exactly the endpoints committed
by the leaf builder, for all four radix/checksum layouts. -/
theorem recover_buildLeaf_values (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) (signatureOnly : Bool) :
    evalWithAnswerFn answers ((List.finRange (chainCount lay)).mapM fun i =>
      chain lay tree leaf i.val (digits.getD i.val 0) (2^width lay i.val-1-digits.getD i.val 0)
        ((evalWithAnswerFn answers (buildLeaf lay tree leaf digits signatureOnly)).2.getD i.val 0))=
      (List.range (chainCount lay)).map (leafEnd answers lay tree leaf) := by
  rw [eval_mapM,eval_buildLeaf_values answers lay tree leaf digits hvalid signatureOnly]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map,List.length_finRange] at hi
  simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,Fin.val_cast,Fin.val_mk]
  have hv : ((List.range (chainCount lay)).map (leafValue answers lay tree leaf digits)).getD i 0=
      leafValue answers lay tree leaf digits i := by simp [List.getD_eq_getElem,hi]
  rw [hv]
  exact leafValue_completes answers lay tree leaf digits hvalid i hi

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem sibling_pair (f : Nat → Digest) (node : Nat) :
    (if node%2=0 then (f node,f (node ^^^ 1)) else (f (node ^^^ 1),f node))=
      (f (2*(node/2)),f (2*(node/2)+1)) := by
  by_cases he : node%2=0
  · rw [if_pos he,Nat.xor_one_of_even (Nat.even_iff.mpr he)]
    have hn : node=2*(node/2) := by omega
    conv_lhs => rw [hn]
  · rw [if_neg he,Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    have hn : node=2*(node/2)+1 := by omega
    have hs : node-1=2*(node/2) := by omega
    rw [hs]
    exact Prod.ext rfl (congrArg f hn)

theorem div_pow_succ (node level : Nat) : node/2^level/2=node/2^(level+1) := by
  rw [Nat.div_div_eq_div_mul,pow_succ]

theorem div_pow_bound {node height start level : Nat} (hl : start+level ≤ height)
    (hn : node < 2^(height-start)) : node/2^level < 2^(height-(start+level)) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  have he : height-start=height-(start+level)+level := by omega
  calc node < 2^(height-start) := hn
       _ = 2^(height-(start+level))*2^level := by rw [he,pow_add]

/-- Any source Merkle authentication path assembled from a built tree climbs
to the exact stored ancestor, including paths that begin at a bucket root. -/
theorem eval_merklePath (answers : Answers) (tag lay tree h start n node : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree h leaves h levels)
    (hsteps : start+n ≤ h) (hnode : node < 2^(h-start)) (path : Fin n → Digest)
    (hpath : ∀ j,path j=treeValue levels (start+j.val) (node/2^j.val ^^^ 1)) :
    evalWithAnswerFn answers ((List.finRange n).foldlM (fun value j => do
      let other := path j
      let pair := if node/2^j.val%2=0 then (value,other) else (other,value)
      nodeHash tag lay tree (2^(h-(start+j.val+1))+node/2^(j.val+1)) pair.1 pair.2)
      (treeValue levels start node))=treeValue levels (start+n) (node/2^n) := by
  have hi := eval_foldlM_list_inv answers (List.finRange n)
    (fun value j => do
      let other := path j
      let pair := if node/2^j.val%2=0 then (value,other) else (other,value)
      nodeHash tag lay tree (2^(h-(start+j.val+1))+node/2^(j.val+1)) pair.1 pair.2)
    (fun i value => value=treeValue levels (start+i) (node/2^i))
    (treeValue levels start node) (by simp) (fun i hi value hv => ?_)
  · simpa only [List.length_finRange] using hi
  · simp only [List.length_finRange] at hi
    simp only [List.getElem_finRange,Fin.val_cast,Fin.val_mk,hpath,hv]
    rw [sibling_pair,div_pow_succ]
    have hp := htree.2.2 (start+i) (by omega) (node/2^(i+1))
      (div_pow_bound (start := start) (level := i+1) (by omega) hnode)
    simpa only [treeValue,Nat.add_assoc] using hp.symm

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def treeRows (lay : Layer) (tree selected : Nat) (digits : List Nat) : M (List Digest × List Digest) :=
  (List.range (2^height lay)).foldlM (fun rows leaf => do
    let (root,values) ← buildLeaf lay tree leaf (if leaf=selected then digits else [])
    pure (rows.1++[root],if leaf=selected then values else rows.2)) ([],[])

theorem buildTree_eq (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    buildTree lay tree selected digits=(do
      let rows ← treeRows lay tree selected digits
      let levels ← buildLevels 3 lay.val tree (height lay) rows.1
      pure (levels,rows.2)) := rfl

theorem eval_treeRows (answers : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : ValidDigits lay digits) :
    evalWithAnswerFn answers (treeRows lay tree selected digits)=
      ((List.range (2^height lay)).map (leafRoot answers lay tree),
       if selected < 2^height lay then (List.range (chainCount lay)).map (leafValue answers lay tree selected digits) else []) := by
  unfold treeRows
  apply Prod.ext
  all_goals
    have hr := eval_foldlM_range_inv answers (2^height lay)
      (fun rows leaf => do
        let (root,values) ← buildLeaf lay tree leaf (if leaf=selected then digits else [])
        pure (rows.1++[root],if leaf=selected then values else rows.2))
      (fun done rows => rows.1=(List.range done).map (leafRoot answers lay tree) ∧
        rows.2=if selected < done then (List.range (chainCount lay)).map (leafValue answers lay tree selected digits) else [])
      ([],[]) (by simp) (fun leaf hleaf rows hrows => ?_)
    try exact hr.1
    try exact hr.2
    simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    have hd : ValidDigits lay (if leaf=selected then digits else []) := by
      split <;> first | exact hvalid | exact validDigits_nil lay
    constructor
    · rw [eval_buildLeaf_root answers lay tree leaf _ hd,hrows.1,List.range_succ,List.map_append,List.map_singleton]
    · by_cases he : leaf=selected
      · subst leaf
        simp only [ite_true,eval_buildLeaf_values answers lay tree selected digits hvalid false,
          Nat.lt_succ_self,if_true]
      · rw [if_neg he,hrows.2]
        have hc : (selected < leaf+1) ↔ selected < leaf := by omega
        simp only [hc]

def builtTree (answers : Answers) (lay : Layer) (tree : Nat) : List (List Digest) :=
  evalWithAnswerFn answers (buildLevels 3 lay.val tree (height lay)
    ((List.range (2^height lay)).map (leafRoot answers lay tree)))

/-- A source tree has the same root and internal nodes for every selected
leaf and every valid encoding of that leaf's message. -/
theorem eval_buildTree_levels (answers : Answers) (lay : Layer) (tree selected : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) :
    (evalWithAnswerFn answers (buildTree lay tree selected digits)).1=builtTree answers lay tree := by
  rw [buildTree_eq]
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_treeRows answers lay tree selected digits hvalid]
  rfl

theorem eval_buildTree_values (answers : Answers) (lay : Layer) (tree selected : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) (hsel : selected < 2^height lay) :
    (evalWithAnswerFn answers (buildTree lay tree selected digits)).2=
      (List.range (chainCount lay)).map (leafValue answers lay tree selected digits) := by
  rw [buildTree_eq]
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_treeRows answers lay tree selected digits hvalid,hsel,ite_true]

theorem builtTree_correct (answers : Answers) (lay : Layer) (tree : Nat) :
    TreeLevels answers 3 lay.val tree (height lay)
      ((List.range (2^height lay)).map (leafRoot answers lay tree)) (height lay) (builtTree answers lay tree) := by
  exact eval_buildLevels_correct answers 3 lay.val tree (height lay) _ (by simp)

theorem builtTree_leaf (answers : Answers) (lay : Layer) (tree leaf : Nat) (hleaf : leaf < 2^height lay) :
    treeValue (builtTree answers lay tree) 0 leaf=leafRoot answers lay tree leaf := by
  unfold treeValue
  rw [(builtTree_correct answers lay tree).2.1]
  simp [List.getD_eq_getElem,hleaf]

theorem eval_chains_honest (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : ValidDigits lay digits) (values : Fin (chainCount lay) → Digest)
    (hvalues : ∀ i,values i=leafValue answers lay tree leaf digits i.val) :
    evalWithAnswerFn answers ((List.finRange (chainCount lay)).mapM fun i =>
      chain lay tree leaf i.val (digits.getD i.val 0) (2^width lay i.val-1-digits.getD i.val 0) (values i))=
      (List.range (chainCount lay)).map (leafEnd answers lay tree leaf) := by
  rw [eval_mapM]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map,List.length_finRange] at hi
  simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,hvalues,Fin.val_cast,Fin.val_mk]
  exact leafValue_completes answers lay tree leaf digits hvalid i hi

/-- The actual verifier's chain and path loops recover the source builder's
root when their values and siblings are the ones emitted by that builder. -/
theorem eval_recoverLayer_honest (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (digits : List Nat) (hvalid : ValidDigits lay digits)
    (hvalues : ∀ i,(sig.layers lay).values i=
      leafValue answers lay (route index lay).2 (route index lay).1 digits i.val)
    (hpath : ∀ j,(sig.layers lay).path j=treeValue (builtTree answers lay (route index lay).2)
      j.val ((route index lay).1/2^j.val ^^^ 1)) :
    evalWithAnswerFn answers (recoverLayer sig index lay digits)=
      treeValue (builtTree answers lay (route index lay).2) (height lay) 0 := by
  unfold recoverLayer
  simp only [evalWithAnswerFn_bind]
  rw [eval_chains_honest answers lay _ _ digits hvalid _ hvalues]
  have hp := eval_merklePath answers 3 lay.val (route index lay).2 (height lay) 0 (height lay)
    (route index lay).1 (builtTree answers lay (route index lay).2)
    ((List.range (2^height lay)).map (leafRoot answers lay (route index lay).2))
    (builtTree_correct answers lay (route index lay).2) (by omega)
    (by simpa using route_leaf_bound index lay) (sig.layers lay).path (by simpa using hpath)
  rw [builtTree_leaf answers lay _ _ (route_leaf_bound index lay)] at hp
  simpa only [Nat.zero_add,Nat.sub_sub,Nat.div_eq_of_lt (route_leaf_bound index lay),leafRoot] using hp

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem readLE_nat_bytes (value start n : Nat) :
    readLE ((List.range' start n).map (fun i => UInt8.ofNat (value/256^i%256)))=
      value/256^start%256^n := by
  induction n generalizing start with
  | zero => simp [readLE,Nat.mod_one]
  | succ n ih =>
      simp only [List.range'_succ,List.map_cons,readLE,List.foldr_cons]
      change (UInt8.ofNat (value/256^start%256)).toNat+256*readLE
        ((List.range' (start+1) n).map (fun i => UInt8.ofNat (value/256^i%256)))=_
      rw [ih]
      simp only [UInt8.toNat_ofNat',show 2^8=256 by decide,Nat.mod_mod]
      rw [pow_succ 256 n,Nat.mul_comm (256^n) 256,Nat.mod_mul,pow_succ 256 start,
        Nat.div_div_eq_div_mul]

theorem readLE_bytesLE (n : Nat) (value : BitVec (8*n)) :
    readLE (bytesLE n value)=value.toNat := by
  have hb : bytesLE n value=(List.range' 0 n).map (fun i => UInt8.ofNat (value.toNat/256^i%256)) := by
    apply List.ext_getElem (by simp [bytesLE_length])
    intro i hi hj
    simp only [bytesLE,List.getElem_ofFn,List.getElem_map,List.getElem_range',Nat.one_mul,Nat.zero_add]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
      UInt8.toNat_ofNat',show 2^8=256 by decide,Nat.mod_mod]
    rw [Nat.pow_mul]
  rw [hb,readLE_nat_bytes,pow_zero,Nat.div_one]
  apply Nat.mod_eq_of_lt
  have hv := value.isLt
  simpa only [Nat.pow_mul] using hv

theorem readDigest_bytesLE (value : Digest) : readDigest (bytesLE 16 value)=value := by
  unfold readDigest
  rw [readLE_bytesLE]
  exact BitVec.ofNat_toNat 128 value

theorem bytesLE_flatMap_getD (values : List Digest) (index byte : Nat)
    (hi : index < values.length) (hb : byte < 16) :
    (values.flatMap (bytesLE 16)).getD (16*index+byte) 0=(bytesLE 16 (values.getD index 0)).getD byte 0 := by
  induction values generalizing index with
  | nil => simp at hi
  | cons value values ih =>
      cases index with
      | zero =>
          simp only [List.flatMap_cons,List.getD_cons_zero,Nat.mul_zero,Nat.zero_add]
          exact List.getD_append _ _ _ _ (by simpa only [bytesLE_length] using hb)
      | succ index =>
          rw [List.flatMap_cons,List.getD_append_right _ _ _ _ (by rw [bytesLE_length];omega)]
          have hs : 16*(index+1)+byte-16=16*index+byte := by omega
          rw [bytesLE_length,hs,List.getD_cons_succ]
          exact ih index (by simpa using hi)

/-- Every 16-byte word in the retained region decodes to the exact masked
digest that key generation serialized there. -/
theorem readDigest_flatMap (values : List Digest) (index : Nat) (hi : index < values.length) :
    readDigest (List.ofFn fun i : Fin 16 => (values.flatMap (bytesLE 16)).getD (16*index+i.val) 0)=
      values.getD index 0 := by
  have he : (List.ofFn fun i : Fin 16 => (values.flatMap (bytesLE 16)).getD (16*index+i.val) 0)=
      bytesLE 16 (values.getD index 0) := by
    apply List.ext_getElem (by simp [bytesLE_length])
    intro i hi' hj
    simp only [List.length_ofFn] at hi'
    simp only [List.getElem_ofFn,bytesLE_flatMap_getD values index i hi hi']
    exact List.getD_eq_getElem _ 0 hj
  rw [he,readDigest_bytesLE]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def cacheWordList (f : Nat → Nat → Digest) : List Digest :=
  (List.range' 2 10).flatMap fun level => (List.range (2^(12-level))).map (f level)

theorem cacheWordList_prefix_length (f : Nat → Nat → Digest) (level : Nat)
    (hlo : 2 ≤ level) (hhi : level ≤ 12) :
    ((List.range' 2 (level-2)).flatMap fun j => (List.range (2^(12-j))).map (f j)).length=
      2048-2^(13-level) := by
  simp only [List.length_flatMap,List.length_map,List.length_range]
  interval_cases level <;> decide +kernel

theorem cacheWordList_length (f : Nat → Nat → Digest) : (cacheWordList f).length=2046 := by
  exact cacheWordList_prefix_length f 12 (by decide) (by decide)

theorem cacheWordList_getD (f : Nat → Nat → Digest) (level node : Nat)
    (hlo : 2 ≤ level) (hhi : level < 12) (hnode : node < 2^(12-level)) :
    (cacheWordList f).getD (2048-2^(13-level)+node) 0=f level node := by
  unfold cacheWordList
  have hrange : List.range' 2 10=List.range' 2 (level-2)++List.range' level (12-level) := by
    have he := List.range'_append_1 (s := 2) (m := level-2) (n := 12-level)
    rw [show 2+(level-2)=level by omega,show (level-2)+(12-level)=10 by omega] at he
    exact he.symm
  rw [hrange,List.flatMap_append]
  rw [List.getD_append_right _ _ _ _ (by rw [cacheWordList_prefix_length f level hlo (by omega)];omega)]
  rw [cacheWordList_prefix_length f level hlo (by omega),Nat.add_sub_cancel_left]
  rw [show 12-level=(11-level)+1 by omega,List.range'_succ,List.flatMap_cons]
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_map,List.length_range] using hnode)]
  simp [List.getD_eq_getElem,hnode]

theorem cacheWordList_serialized_length (f : Nat → Nat → Digest) :
    ((cacheWordList f).flatMap (bytesLE 16)).length=32736 := by
  rw [digest_list_bytes_length,cacheWordList_length]

def cacheRegion (f : Nat → Nat → Digest) : Region :=
  let raw := ((cacheWordList f).flatMap (bytesLE 16)).toArray
  fun i => raw.getD i.val 0

theorem cacheRegion_get (f : Nat → Nat → Digest) (i : Fin 32736) :
    cacheRegion f i=((cacheWordList f).flatMap (bytesLE 16)).getD i.val 0 := by
  simp only [cacheRegion,Array.getD_eq_getD_getElem?,List.getElem?_toArray,List.getD_eq_getElem?_getD]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem cacheWord_offset_bound (level node : Nat) (hlo : 2 ≤ level) (hhi : level < 12)
    (hnode : node < 2^(12-level)) : 2048-2^(13-level)+node < 2046 := by
  interval_cases level <;> norm_num at hnode ⊢ <;> omega

theorem cacheRegion_read (f : Nat → Nat → Digest) (level node : Nat)
    (hlo : 2 ≤ level) (hhi : level < 12) (hnode : node < 2^(12-level)) :
    readDigest (List.ofFn fun i : Fin 16 =>
      cacheRegion f ⟨(16*(2048-2^(13-level)+node)+i.val)%32736,Nat.mod_lt _ (by decide)⟩)=f level node := by
  have hword := cacheWord_offset_bound level node hlo hhi hnode
  have he : (List.ofFn fun i : Fin 16 =>
      cacheRegion f ⟨(16*(2048-2^(13-level)+node)+i.val)%32736,Nat.mod_lt _ (by decide)⟩)=
      (List.ofFn fun i : Fin 16 => ((cacheWordList f).flatMap (bytesLE 16)).getD
        (16*(2048-2^(13-level)+node)+i.val) 0) := by
    congr 1
    funext i
    rw [cacheRegion_get]
    simp only [Fin.val_mk,Nat.mod_eq_of_lt (show 16*(2048-2^(13-level)+node)+i.val < 32736 by omega)]
  rw [he,readDigest_flatMap _ _ (by rw [cacheWordList_length];exact hword),
    cacheWordList_getD f level node hlo hhi hnode]

def maskedTop (answers : Answers) (level node : Nat) : Digest :=
  treeValue (builtTree answers 0 0) level node ^^^ evalWithAnswerFn answers (mask level node)

def cachePayloadProgram (builder : M (List (List Digest) × List Digest)) : M (Digest × Region) := do
  let (levels,_) ← builder
  let masked ← (List.range' 2 10).mapM fun level =>
    (List.range (2^(12-level))).mapM fun i => do
      let value ← mask level i
      pure ((levels.getD level []).getD i 0 ^^^ value)
  let raw := (masked.flatten.flatMap (bytesLE 16)).toArray
  pure ((levels.getD 12 []).getD 0 0,fun i => raw.getD i.val 0)

theorem keygenPayload_eq : keygenPayload=cachePayloadProgram (buildTree 0 0 0 []) := rfl

theorem eval_cachePayloadProgram (answers : Answers) (builder : M (List (List Digest) × List Digest)) :
    evalWithAnswerFn answers (cachePayloadProgram builder)=
      (treeValue (evalWithAnswerFn answers builder).1 12 0,
       cacheRegion fun level node => treeValue (evalWithAnswerFn answers builder).1 level node ^^^
         evalWithAnswerFn answers (mask level node)) := by
  simp only [cachePayloadProgram,evalWithAnswerFn_bind,eval_mapM,evalWithAnswerFn_pure]
  rfl

def PayloadCorrect (answers : Answers) (result : Digest × Region) : Prop :=
  result.1=treeValue (builtTree answers 0 0) 12 0 ∧ result.2=cacheRegion (maskedTop answers)

theorem cachePayloadProgram_correct (answers : Answers) (builder : M (List (List Digest) × List Digest))
    (hlevels : (evalWithAnswerFn answers builder).1=builtTree answers 0 0) :
    PayloadCorrect answers (evalWithAnswerFn answers (cachePayloadProgram builder)) := by
  rw [eval_cachePayloadProgram,hlevels]
  exact ⟨rfl,rfl⟩

theorem keygenPayload_correct (answers : Answers) : PayloadCorrect answers (evalWithAnswerFn answers keygenPayload) := by
  rw [keygenPayload_eq]
  exact cachePayloadProgram_correct answers _ (eval_buildTree_levels answers 0 0 0 [] (validDigits_nil 0))

def KeygenCorrect (answers : Answers) (result : Digest × Cache) : Prop :=
  result.1=treeValue (builtTree answers 0 0) 12 0 ∧
  result.2.region=cacheRegion (maskedTop answers) ∧ CacheTagCorrect answers result

theorem cache_payload_correct (answers : Answers) (payload : M (Digest × Region))
    (hp : PayloadCorrect answers (evalWithAnswerFn answers payload)) :
    KeygenCorrect answers (evalWithAnswerFn answers (do
      let (publicKey,region) ← payload
      let tag ← privateMac region
      pure (publicKey,Cache.mk tag region))) := by
  simp only [KeygenCorrect,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  exact ⟨hp.1,hp.2,rfl⟩

/-- Key generation stores exactly the masked upper tree and its MAC. -/
theorem keygen_correct (answers : Answers) : KeygenCorrect answers (evalWithAnswerFn answers keygen) := by
  exact cache_payload_correct answers keygenPayload (keygenPayload_correct answers)

theorem honest_cache_read (answers : Answers) (cache : Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (leaf level : Nat)
    (hleaf : leaf < 4096) (hlo : 2 ≤ level) (hhi : level < 12) :
    let sibling := leaf/2^level ^^^ 1
    let offset := 16*(2048-2^(13-level)+sibling)
    readDigest (List.ofFn fun i : Fin 16 => cache.region ⟨(offset+i.val)%32736,Nat.mod_lt _ (by decide)⟩) ^^^
      evalWithAnswerFn answers (mask level sibling)=treeValue (builtTree answers 0 0) level sibling := by
  dsimp only
  rw [hcache,cacheRegion_read]
  · simp only [maskedTop,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]
  · exact hlo
  · exact hhi
  · have hd : leaf/2^level < 2^(12-level) := by
      simpa only [Nat.zero_add] using
        div_pow_bound (node := leaf) (height := 12) (start := 0) (level := level) (by omega) hleaf
    exact Nat.xor_lt_two_pow hd (Nat.one_lt_two_pow (by omega))

theorem top_parent (answers : Answers) (node : Nat) (hn : node < 2048) :
    evalWithAnswerFn answers (nodeHash 3 0 0 (2048+node)
      (leafRoot answers 0 0 (2*node)) (leafRoot answers 0 0 (2*node+1)))=
      treeValue (builtTree answers 0 0) 1 node := by
  have ht := (builtTree_correct answers 0 0).2.2 0 (by decide) node hn
  change treeValue (builtTree answers 0 0) 1 node=evalWithAnswerFn answers
    (nodeHash 3 0 0 (2048+node) (treeValue (builtTree answers 0 0) 0 (2*node))
      (treeValue (builtTree answers 0 0) 0 (2*node+1))) at ht
  rw [builtTree_leaf answers 0 0 (2*node) (by change 2*node < 4096;omega),
    builtTree_leaf answers 0 0 (2*node+1) (by change 2*node+1 < 4096;omega)] at ht
  exact ht.symm

/-- The two recomputed siblings and ten retained siblings form the exact
authentication path in key generation's top tree. -/
theorem eval_topPath_honest (answers : Answers) (cache : Cache) (leaf : Nat)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (hleaf : leaf < 4096) :
    evalWithAnswerFn answers (topPath cache leaf)=
      (List.range 12).map (fun j => treeValue (builtTree answers 0 0) j (leaf/2^j ^^^ 1)) := by
  have hs : leaf ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hleaf (by decide)
  have hp : leaf/2 ^^^ 1 < 2048 := Nat.xor_lt_two_pow (n := 11) (by omega) (by decide)
  simp only [topPath,evalWithAnswerFn_bind,eval_mapM,evalWithAnswerFn_pure]
  simp only [eval_buildLeaf_root answers 0 0 _ [] (validDigits_nil 0)]
  have hdiv : ((leaf/2 ^^^ 1)*2)/2=leaf/2 ^^^ 1 := by omega
  rw [hdiv,show (leaf/2 ^^^ 1)*2=2*(leaf/2 ^^^ 1) by omega,top_parent answers _ hp]
  rw [← builtTree_leaf answers 0 0 (leaf ^^^ 1) hs]
  have hr : List.range 12=[0,1]++List.range' 2 10 := by decide
  rw [hr,List.map_append,List.map_cons,List.map_cons,List.map_nil]
  simp only [pow_zero,Nat.div_one,pow_one]
  congr 1
  apply List.map_congr_left
  intro level hlevel
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hlevel
  exact honest_cache_read answers cache hcache leaf level hleaf (by omega) (by omega)

def honestPieces (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map (leafValue answers lay tree leaf digits),
   (List.range (height lay)).map fun j => treeValue (builtTree answers lay tree) j (leaf/2^j ^^^ 1))

theorem eval_signTop_honest (answers : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (hleaf : leaf < 4096)
    (hvalid : ValidDigits 0 digits) :
    evalWithAnswerFn answers (signTop cache leaf digits)=honestPieces answers 0 0 leaf digits := by
  simp only [signTop,evalWithAnswerFn_bind,evalWithAnswerFn_pure,
    eval_buildLeaf_values answers 0 0 leaf digits hvalid true,eval_topPath_honest answers cache leaf hcache hleaf]
  rfl

theorem recoverLayer_honestPieces (answers : Answers) (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) (hvalid : ValidDigits lay digits)
    (hlayer : sig.layers lay=piecesSignature lay
      (honestPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayer sig index lay digits)=
      treeValue (builtTree answers lay (route index lay).2) (height lay) 0 := by
  apply eval_recoverLayer_honest answers sig index lay digits hvalid
  · intro i
    rw [hlayer]
    simp [piecesSignature,honestPieces,List.getD_eq_getElem,i.isLt]
  · intro j
    rw [hlayer]
    simp [piecesSignature,honestPieces,List.getD_eq_getElem,j.isLt]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem eval_buildTree_result (answers : Answers) (lay : Layer) (tree selected : Nat)
    (digits : List Nat) (hvalid : ValidDigits lay digits) (hsel : selected < 2^height lay) :
    evalWithAnswerFn answers (buildTree lay tree selected digits)=
      (builtTree answers lay tree,(List.range (chainCount lay)).map (leafValue answers lay tree selected digits)) := by
  exact Prod.ext (eval_buildTree_levels answers lay tree selected digits hvalid)
    (eval_buildTree_values answers lay tree selected digits hvalid hsel)

def PiecesAgree (sig : Signature) (pieces : List Pieces) (n : Nat) : Prop :=
  ∀ lay : Layer,lay.val < n → sig.layers lay=piecesSignature lay (pieces.getD lay.val ([],[]))

theorem PiecesAgree.prefix {sig : Signature} {previous : List Pieces} {part : Pieces} {n : Nat}
    (hlen : previous.length=n) (h : PiecesAgree sig (previous++[part]) (n+1)) : PiecesAgree sig previous n := by
  intro lay hlay
  rw [h lay (by omega),List.getD_append previous [part] ([],[]) lay.val (by omega)]

theorem PiecesAgree.last {sig : Signature} {previous : List Pieces} {part : Pieces} {n : Nat}
    (hlen : previous.length=n) (hn : n < 4) (h : PiecesAgree sig (previous++[part]) (n+1)) :
    sig.layers (Fin.ofNat 4 n)=piecesSignature (Fin.ofNat 4 n) part := by
  have hv : (Fin.ofNat 4 n : Layer).val=n := Nat.mod_eq_of_lt hn
  rw [h _ (by rw [hv];omega),hv,List.getD_append_right previous [part] ([],[]) n (by omega),hlen]
  simp

def layerResultRoot (answers : Answers) (n : Nat) (value : Digest) : Digest :=
  if n=0 then value else treeValue (builtTree answers 0 0) 12 0

/-- Every successful source layer-signing run can be replayed by the actual
counter-recovering expander using the emitted layer pieces. -/
theorem signLayers_expandLayers (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (hindex : index < 2^31) :
    ∀ n,n ≤ 4 → ∀ value pieces,
      evalWithAnswerFn answers (signLayers cache index n value)=some pieces →
      pieces.length=n ∧ ∀ sig : Signature,PiecesAgree sig pieces n →
        ∃ counters : List (BitVec 32),counters.length=n ∧
          evalWithAnswerFn answers (expandLayers sig index n value)=some (layerResultRoot answers n value,counters) := by
  intro n
  induction n with
  | zero =>
      intro hn value pieces he
      simp only [signLayers,evalWithAnswerFn_pure,Option.some.injEq] at he
      subst pieces
      exact ⟨rfl,fun sig _ => ⟨[],rfl,rfl⟩⟩
  | succ n ih =>
      intro hn value pieces he
      simp only [signLayers,evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some found =>
          obtain ⟨counter,digits⟩ := found
          have hd := (counterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value
            counterLimit 0 counter digits (by decide) hs).2.2
          have hvalid := validDigits_decode hd
          simp only [hs,evalWithAnswerFn_bind] at he
          by_cases hn0 : n=0
          · subst n
            simp only [ite_true,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Option.some.injEq] at he
            subst pieces
            refine ⟨rfl,?_⟩
            intro sig hagree
            have hp := hagree 0 (by decide)
            change sig.layers 0=piecesSignature 0
              (evalWithAnswerFn answers (signTop cache (route index 0).1 digits)) at hp
            rw [eval_signTop_honest answers cache _ digits hcache (route_leaf_bound index 0) hvalid] at hp
            have ht : (route index 0).2=0 := route_top_tree index hindex
            have hr := recoverLayer_honestPieces answers sig index 0 digits hvalid (by simpa only [ht] using hp)
            refine ⟨[counter],rfl,?_⟩
            simp only [expandLayers,evalWithAnswerFn_bind,hs,hr,evalWithAnswerFn_pure,ht,layerResultRoot,
              Nat.one_ne_zero,if_false,List.nil_append]
            change some (evalWithAnswerFn answers (recoverLayer sig index 0 digits),[counter])=
              some (treeValue (builtTree answers 0 0) 12 0,[counter])
            rw [hr,ht]
            rfl
          · simp only [hn0,ite_false,evalWithAnswerFn_bind,
              eval_buildTree_result answers (Fin.ofNat 4 n) _ _ digits hvalid (route_leaf_bound index _)] at he
            cases hp : evalWithAnswerFn answers (signLayers cache index n
              (((builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                (height (Fin.ofNat 4 n)) []).getD 0 0)) with
            | none => simp only [hp,evalWithAnswerFn_pure,reduceCtorEq] at he
            | some previous =>
                simp only [hp,evalWithAnswerFn_pure,Option.some.injEq] at he
                subst pieces
                obtain ⟨hlen,hprevious⟩ := ih (by omega) _ previous hp
                refine ⟨by simp [hlen],?_⟩
                intro sig hagree
                change PiecesAgree sig (previous++[honestPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n+1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover := recoverLayer_honestPieces answers sig index (Fin.ofNat 4 n) digits hvalid hlayer
                obtain ⟨counters,hc,hreplay⟩ := hprevious sig (PiecesAgree.prefix hlen hagree)
                simp only [treeValue] at hrecover
                refine ⟨counters++[counter],by simp [hc],?_⟩
                simp only [expandLayers,evalWithAnswerFn_bind,hs,hrecover,hreplay,evalWithAnswerFn_pure,
                  layerResultRoot,hn0,ite_false,Nat.add_eq_zero_iff,one_ne_zero,and_false]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem recoverOuter_correct (answers : Answers) (sig : Signature) (index coord bucket used : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers 10 coord index 11 leaves 11 levels)
    (hb : bucket < 16) (hfit : used+4 ≤ 118)
    (hproof : Matches sig.proof ((List.range 4).map fun j => treeValue levels (7+j) (bucket/2^j ^^^ 1)) used) :
    evalWithAnswerFn answers (recoverOuter sig index coord bucket (some (treeValue levels 7 bucket,used)))=
      some (treeValue levels 11 0,used+4) := by
  unfold recoverOuter
  refine (eval_foldlM_range_inv answers 4 _
    (fun j state => state=some (treeValue levels (7+j) (bucket/2^j),used+j))
    (some (treeValue levels 7 bucket,used)) (by simp) ?_).trans ?_
  · intro j hj state hs
    rw [hs]
    have hu : used+j < 118 := by omega
    simp only [hu,dif_pos,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    have hp := hproof j (by simp;exact hj) hu
    have hg : ((List.range 4).map fun k => treeValue levels (7+k) (bucket/2^k ^^^ 1)).getD j 0=
        treeValue levels (7+j) (bucket/2^j ^^^ 1) := by simp [List.getD_eq_getElem,hj]
    rw [hg] at hp
    rw [hp,sibling_pair,div_pow_succ]
    have hnode : bucket/2^(j+1) < 2^(11-(7+j+1)) := by
      simpa only [Nat.add_assoc] using
        div_pow_bound (node := bucket) (height := 11) (start := 7) (level := j+1) (by omega) hb
    have ht := htree.2.2 (7+j) (by omega) (bucket/2^(j+1)) hnode
    have he : 4-j-1=11-(7+j+1) := by omega
    rw [he]
    change some (evalWithAnswerFn answers (nodeHash 10 coord index
      (2^(11-(7+j+1))+bucket/2^(j+1))
      (treeValue levels (7+j) (2*(bucket/2^(j+1))))
      (treeValue levels (7+j) (2*(bucket/2^(j+1))+1))),used+j+1)=_
    simp only [treeValue]
    rw [← ht]
    simp only [Nat.add_assoc]
  · simp only [show (7 : Nat)+4=11 by decide,show (2 : Nat)^4=16 by decide,
      Nat.div_eq_of_lt hb]

theorem builtFts_treeLevels (answers : Answers) (index coord : Nat) :
    let built := evalWithAnswerFn answers (buildFts index coord)
    TreeLevels answers 10 coord index 11 (built.1.getD 0 []) 11 built.1 := by
  have ht := eval_buildFts_correct answers index coord
  exact ⟨ht.1,rfl,ht.2.2.2⟩

def forestInner (answers : Answers) (index coord : Nat) (sel : Selection) : List Digest :=
  (frontier (sel.leaves.map fun leaf => sel.bucket*128+leaf) 7 sel.bucket).map
    fun p => treeValue (evalWithAnswerFn answers (buildFts index coord)).1 p.1 p.2

def forestOuter (answers : Answers) (index coord : Nat) (sel : Selection) : List Digest :=
  (List.range 4).map fun j => treeValue (evalWithAnswerFn answers (buildFts index coord)).1
    (7+j) (sel.bucket/2^j ^^^ 1)

/-- One complete source BPORS coordinate reconstructs the builder's root,
consuming its minimal bucket frontier followed by its three outer siblings. -/
theorem forestStep_correct (answers : Answers) (sig : Signature) (index coord used : Nat)
    (chosen : List Selection) (sel : Selection) (roots : List Digest)
    (hsel : chosen.getD coord ⟨0,[]⟩=sel)
    (hbucket : sel.bucket < 16) (hlen : sel.leaves.length=3) (hn : sel.leaves.Nodup)
    (hs : sel.leaves.SortedLE) (hb : ∀ leaf,leaf ∈ sel.leaves → leaf < 128)
    (hfit : used+authCount sel.leaves+4 ≤ 118)
    (hvalues : (List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)=
      (sel.leaves.map fun leaf => sel.bucket*128+leaf).map
        fun leaf => (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0)
    (hproof : Matches sig.proof (forestInner answers index coord sel++forestOuter answers index coord sel) used) :
    evalWithAnswerFn answers (forestStep sig index chosen coord (some (roots,used)))=
      some (roots++[treeValue (evalWithAnswerFn answers (buildFts index coord)).1 11 0],
        used+authCount sel.leaves+4) := by
  have hinner := built_bucket_recovery answers index coord sel.bucket used sel.leaves sig.proof
    hbucket hlen hn hs hb (by omega) hproof.left
  have hcount : (forestInner answers index coord sel).length=authCount sel.leaves := by
    simp only [forestInner,List.length_map]
    exact bucket_frontier_length sel.leaves sel.bucket hlen hn hs hb
  have houterproof := hproof.right
  rw [hcount] at houterproof
  have houter := recoverOuter_correct answers sig index coord sel.bucket (used+authCount sel.leaves)
    (evalWithAnswerFn answers (buildFts index coord)).1
    ((evalWithAnswerFn answers (buildFts index coord)).1.getD 0 [])
    (builtFts_treeLevels answers index coord) hbucket hfit houterproof
  simp only [forestStep,evalWithAnswerFn_bind,hsel,hvalues,hinner,houter,evalWithAnswerFn_pure]

def forestUsed (chosen : List Selection) (n : Nat) : Nat :=
  ((List.range n).map fun coord => authCount (chosen.getD coord ⟨0,[]⟩).leaves+4).sum

def forestRoots (answers : Answers) (index n : Nat) : List Digest :=
  (List.range n).map fun coord => treeValue (evalWithAnswerFn answers (buildFts index coord)).1 11 0

theorem forestUsed_succ (chosen : List Selection) (n : Nat) :
    forestUsed chosen (n+1)=forestUsed chosen n+authCount (chosen.getD n ⟨0,[]⟩).leaves+4 := by
  simp [forestUsed,List.range_succ,Nat.add_assoc]

theorem forestRoots_succ (answers : Answers) (index n : Nat) :
    forestRoots answers index (n+1)=forestRoots answers index n++
      [treeValue (evalWithAnswerFn answers (buildFts index n)).1 11 0] := by
  simp [forestRoots,List.range_succ]

/-- All seven reconstructed coordinates produce exactly the source builder's
forest public key; the tail of the fixed-size proof is checked explicitly. -/
theorem recoverFts_honest (answers : Answers) (sig : Signature) (index : Nat) (chosen : List Selection)
    (hcoords : ∀ coord,coord < 7 →
      let sel := chosen.getD coord ⟨0,[]⟩
      sel.bucket < 16 ∧ sel.leaves.length=3 ∧ sel.leaves.Nodup ∧ sel.leaves.SortedLE ∧
      (∀ leaf,leaf ∈ sel.leaves → leaf < 128) ∧
      forestUsed chosen coord+authCount sel.leaves+4 ≤ 118 ∧
      ((List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)=
        (sel.leaves.map fun leaf => sel.bucket*128+leaf).map
          fun leaf => (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0) ∧
      Matches sig.proof (forestInner answers index coord sel++forestOuter answers index coord sel)
        (forestUsed chosen coord))
    (hpad : ∀ j,j < 118-forestUsed chosen 7 →
      sig.proof ⟨(forestUsed chosen 7+j)%118,Nat.mod_lt _ (by decide)⟩=0) :
    evalWithAnswerFn answers (recoverFts sig index chosen)=
      some (evalWithAnswerFn answers (forestPk index (forestRoots answers index 7))) := by
  have hfold : evalWithAnswerFn answers ((List.range 7).foldlM
      (fun state coord => forestStep sig index chosen coord state) (some ([],0)))=
      some (forestRoots answers index 7,forestUsed chosen 7) := by
    apply eval_foldlM_range_inv answers 7 _
      (fun n state => state=some (forestRoots answers index n,forestUsed chosen n)) _ (by rfl)
    intro coord hc state hs
    rw [hs]
    obtain ⟨hb,hlen,hn,hord,hleaf,hfit,hvalues,hproof⟩ := hcoords coord hc
    rw [forestStep_correct answers sig index coord (forestUsed chosen coord) chosen _ _ rfl
      hb hlen hn hord hleaf hfit hvalues hproof,forestRoots_succ,forestUsed_succ]
  have hzero : (List.range (118-forestUsed chosen 7)).all (fun j =>
      decide (sig.proof ⟨(forestUsed chosen 7+j)%118,Nat.mod_lt _ (by decide)⟩=0))=true := by
    simp only [List.all_eq_true,decide_eq_true_eq,List.mem_range]
    exact hpad
  unfold recoverFts
  change evalWithAnswerFn answers (do
    let state ← (List.range 7).foldlM (fun state coord => forestStep sig index chosen coord state) (some ([],0))
    let some (roots,used) := state | pure none
    if !(List.range (118-used)).all (fun j =>
      decide (sig.proof ⟨(used+j)%118,Nat.mod_lt _ (by decide)⟩=0)) then return none
    pure (some (← forestPk index roots)))=_
  simp only [evalWithAnswerFn_bind,hfold,hzero,Bool.not_true,Bool.false_eq_true,ite_false,evalWithAnswerFn_pure]

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def forestOpened (answers : Answers) (index coord : Nat) (sel : Selection) : List Digest :=
  (sel.leaves.map fun leaf => sel.bucket*128+leaf).map
    fun leaf => (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0

def forestRows (index : Nat) (chosen : List Selection) : M (List Digest × List Digest × List Digest) :=
  (List.range 7).foldlM (fun (state : List Digest × List Digest × List Digest) coord => do
    let sel := chosen.getD coord ⟨0,[]⟩
    let (levels,secrets) ← buildFts index coord
    let selected := sel.leaves.map fun s => sel.bucket*128+s
    let opened := selected.map fun s => secrets.getD s 0
    let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
    let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
    pure (state.1++opened,state.2.1++inner++outer,state.2.2++[(levels.getD 11 []).getD 0 0])) ([],[],[])

def forestOpenPrefix (answers : Answers) (index : Nat) (chosen : List Selection) (n : Nat) : List Digest :=
  (List.range n).flatMap fun coord => forestOpened answers index coord (chosen.getD coord ⟨0,[]⟩)

def forestProofPrefix (answers : Answers) (index : Nat) (chosen : List Selection) (n : Nat) : List Digest :=
  (List.range n).flatMap fun coord =>
    forestInner answers index coord (chosen.getD coord ⟨0,[]⟩)++forestOuter answers index coord (chosen.getD coord ⟨0,[]⟩)

theorem eval_forestRows (answers : Answers) (index : Nat) (chosen : List Selection) :
    evalWithAnswerFn answers (forestRows index chosen)=
      (forestOpenPrefix answers index chosen 7,forestProofPrefix answers index chosen 7,forestRoots answers index 7) := by
  unfold forestRows
  refine eval_foldlM_range_inv answers 7 _
    (fun n state => state=(forestOpenPrefix answers index chosen n,
      forestProofPrefix answers index chosen n,forestRoots answers index n)) ([],[],[]) rfl ?_
  intro coord hc state hs
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  change (state.1++forestOpened answers index coord (chosen.getD coord ⟨0,[]⟩),
    state.2.1++forestInner answers index coord (chosen.getD coord ⟨0,[]⟩)++
      forestOuter answers index coord (chosen.getD coord ⟨0,[]⟩),
    state.2.2++[treeValue (evalWithAnswerFn answers (buildFts index coord)).1 11 0])=_
  rw [hs,forestRoots_succ]
  simp only [forestOpenPrefix,forestProofPrefix,List.range_succ,List.flatMap_append,
    List.flatMap_singleton,List.append_assoc]

theorem signPayload_forestRows (cache : Cache) (message : Message) : signPayload cache message=(do
    let rho ← privateNonce message
    let some (_,output) ← digestSearch rho message 0 attemptLimit | pure none
    let index := output.toNat%2^31
    let state ← forestRows index (selections output)
    let root ← forestPk index state.2.2
    let some layers ← signLayers cache index 4 root | pure none
    pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
      fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)) := rfl

theorem flatMap_range_split {α : Type} (blocks : Nat → List α) (n coord : Nat) (hc : coord < n) :
    (List.range n).flatMap blocks=(List.range coord).flatMap blocks++blocks coord++
      (List.range' (coord+1) (n-coord-1)).flatMap blocks := by
  have hr : List.range n=List.range coord++[coord]++List.range' (coord+1) (n-coord-1) := by
    rw [List.range_eq_range',List.range_eq_range']
    have he := List.range'_append_1 (s := 0) (m := coord) (n := n-coord)
    simp only [Nat.zero_add] at he
    rw [Nat.add_sub_of_le (by omega)] at he
    rw [← he,show n-coord=(n-coord-1)+1 by omega,List.range'_succ]
    simp only [List.append_assoc,List.singleton_append,Nat.add_sub_cancel]
  rw [hr,List.flatMap_append,List.flatMap_append,List.flatMap_singleton]

theorem flatMap_range_getD (blocks : Nat → List Digest) (n coord j : Nat)
    (hc : coord < n) (hj : j < (blocks coord).length) :
    ((List.range n).flatMap blocks).getD (((List.range coord).flatMap blocks).length+j) 0=
      (blocks coord).getD j 0 := by
  rw [flatMap_range_split blocks n coord hc,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hj]

theorem flatMap_range_prefix_bound {α : Type} (blocks : Nat → List α) (n coord : Nat) (hc : coord < n) :
    ((List.range coord).flatMap blocks).length+(blocks coord).length ≤ ((List.range n).flatMap blocks).length := by
  rw [flatMap_range_split blocks n coord hc,List.length_append,List.length_append]
  omega

theorem selection_getD_mem (output : HashOutput) (coord : Nat) (hc : coord < 7) :
    (selections output).getD coord ⟨0,[]⟩ ∈ selections output := by
  have hi : coord < (selections output).length := by rw [selections_length];exact hc
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem map_getD_range {α β : Type} (items : List α) (fallback : α) (f : α → β) :
    (List.range items.length).map (fun i => f (items.getD i fallback))=items.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map,List.length_range] at hi
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem items fallback hi]

theorem forestOpenPrefix_length (answers : Answers) (index : Nat) (output : HashOutput) :
    ∀ n,n ≤ 7 → (forestOpenPrefix answers index (selections output) n).length=3*n := by
  intro n
  induction n with
  | zero => intro _;rfl
  | succ n ih =>
      intro hn
      have hl := selection_leaves_length output _ (selection_getD_mem output n (by omega))
      have hh := ih (by omega)
      simpa only [forestOpenPrefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,
        List.length_append,forestOpened,List.length_map,hl,Nat.mul_add,Nat.mul_one] using congrArg (fun k => k+3) hh

theorem forestProofPrefix_length (answers : Answers) (index : Nat) (output : HashOutput)
    (hadm : admissible (selections output)=true) (n : Nat) (hn : n ≤ 7) :
    (forestProofPrefix answers index (selections output) n).length=forestUsed (selections output) n := by
  have hnodup : ∀ sel ∈ selections output,sel.leaves.Nodup := by
    have hh : (∀ sel ∈ selections output,sel.leaves.Nodup) ∧
        28+((selections output).map fun sel => authCount sel.leaves).sum ≤ 118 := by
      simpa only [admissible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using hadm
    exact hh.1
  unfold forestProofPrefix forestUsed
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro coord hc
  have hc : coord < 7 := by have hh := List.mem_range.mp hc;omega
  have hm := selection_getD_mem output coord hc
  simp only [List.length_append,forestInner,forestOuter,List.length_map,List.length_range]
  rw [bucket_frontier_length _ _ (selection_leaves_length output _ hm) (hnodup _ hm)
    (selection_leaves_sorted output _ hm) (fun leaf hh => selection_leaf_bound output _ leaf hm hh)]

theorem forestUsed_capacity (output : HashOutput) (hadm : admissible (selections output)=true) :
    forestUsed (selections output) 7 ≤ 118 := by
  have hcap : 28+((selections output).map fun sel => authCount sel.leaves).sum ≤ 118 := by
    have hh : (∀ sel ∈ selections output,sel.leaves.Nodup) ∧
        28+((selections output).map fun sel => authCount sel.leaves).sum ≤ 118 := by
      simpa only [admissible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using hadm
    exact hh.2
  have he : forestUsed (selections output) 7=
      ((List.range 7).map fun coord => authCount ((selections output).getD coord ⟨0,[]⟩).leaves).sum+28 := by
    unfold forestUsed
    rw [List.sum_map_add]
    simp
  rw [he,← selections_length output,map_getD_range (selections output) ⟨0,[]⟩ (fun sel => authCount sel.leaves)]
  omega

/-- The signer's exact concatenated opening and proof lists satisfy every
coordinate window and the verifier's zero-padding check. -/
theorem recoverFts_from_signer_lists (answers : Answers) (sig : Signature) (index : Nat) (output : HashOutput)
    (hadm : admissible (selections output)=true)
    (hsecrets : ∀ i,sig.secrets i=(forestOpenPrefix answers index (selections output) 7).getD i.val 0)
    (hproof : ∀ i,sig.proof i=(forestProofPrefix answers index (selections output) 7).getD i.val 0) :
    evalWithAnswerFn answers (recoverFts sig index (selections output))=
      some (evalWithAnswerFn answers (forestPk index (forestRoots answers index 7))) := by
  have hcap := forestUsed_capacity output hadm
  apply recoverFts_honest answers sig index (selections output)
  · intro coord hc
    have hm := selection_getD_mem output coord hc
    have hlen := selection_leaves_length output _ hm
    have hb := selection_bucket_bound output _ hm
    have hsorted := selection_leaves_sorted output _ hm
    have hleaves := fun leaf hleaf => selection_leaf_bound output _ leaf hm hleaf
    have hn : ((selections output).getD coord ⟨0,[]⟩).leaves.Nodup := by
      have hh : (∀ sel ∈ selections output,sel.leaves.Nodup) ∧
          28+((selections output).map fun sel => authCount sel.leaves).sum ≤ 118 := by
        simpa only [admissible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using hadm
      exact hh.1 _ hm
    have hblock : (forestInner answers index coord ((selections output).getD coord ⟨0,[]⟩)++
        forestOuter answers index coord ((selections output).getD coord ⟨0,[]⟩)).length=
        authCount ((selections output).getD coord ⟨0,[]⟩).leaves+4 := by
      simp only [List.length_append,forestInner,forestOuter,List.length_map,List.length_range]
      rw [bucket_frontier_length _ _ hlen hn hsorted hleaves]
    refine ⟨hb,hlen,hn,hsorted,hleaves,?_,?_,?_⟩
    · have hp := flatMap_range_prefix_bound (fun coord =>
          forestInner answers index coord ((selections output).getD coord ⟨0,[]⟩)++
          forestOuter answers index coord ((selections output).getD coord ⟨0,[]⟩)) 7 coord hc
      change (forestProofPrefix answers index (selections output) coord).length+_
        ≤ (forestProofPrefix answers index (selections output) 7).length at hp
      rw [forestProofPrefix_length answers index output hadm coord (by omega),hblock,
        forestProofPrefix_length answers index output hadm 7 le_rfl] at hp
      omega
    · apply List.ext_getElem (by simp only [List.length_map,List.length_range,hlen])
      intro j hj hk
      have hj3 : j < 3 := by simpa only [List.length_map,List.length_range] using hj
      conv_lhs => rw [List.getElem_map,List.getElem_range]
      change sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩=
        (forestOpened answers index coord ((selections output).getD coord ⟨0,[]⟩))[j]
      rw [hsecrets]
      simp only [Fin.val_mk,Nat.mod_eq_of_lt (show coord*3+j < 21 by omega)]
      have hx := flatMap_range_getD
        (fun k => forestOpened answers index k ((selections output).getD k ⟨0,[]⟩)) 7 coord j hc
        (by simpa only [forestOpened,List.length_map,hlen] using hj3)
      change (forestOpenPrefix answers index (selections output) 7).getD
        ((forestOpenPrefix answers index (selections output) coord).length+j) 0=_ at hx
      rw [forestOpenPrefix_length answers index output coord (by omega)] at hx
      rw [show coord*3+j=3*coord+j by omega,hx]
      exact List.getD_eq_getElem _ 0 _
    · intro j hj hu
      rw [hproof]
      have hx := flatMap_range_getD (fun k =>
        forestInner answers index k ((selections output).getD k ⟨0,[]⟩)++
        forestOuter answers index k ((selections output).getD k ⟨0,[]⟩)) 7 coord j hc hj
      change (forestProofPrefix answers index (selections output) 7).getD
        ((forestProofPrefix answers index (selections output) coord).length+j) 0=_ at hx
      rw [forestProofPrefix_length answers index output hadm coord (by omega)] at hx
      exact hx
  · intro j hj
    rw [hproof]
    simp only [Fin.val_mk,Nat.mod_eq_of_lt (show forestUsed (selections output) 7+j < 118 by omega)]
    apply List.getD_eq_default
    rw [forestProofPrefix_length answers index output hadm 7 le_rfl]
    omega

end SigGolfCandidate.T3.Correctness


namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- A successful source payload-signing run expands to its honest top root.
This is deterministic: the oracle answers need not be random or collision free. -/
theorem signPayload_expands (answers : Answers) (cache : Cache) (message : Message) (sig : Signature)
    (hcache : cache.region=cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message)=some sig) :
    ∃ w : Witness,evalWithAnswerFn answers
      (expand message (treeValue (builtTree answers 0 0) 12 0) sig)=some w := by
  rw [signPayload_forestRows] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at he
  | some found =>
      obtain ⟨counter,output⟩ := found
      have hadm := (digestSearch_some answers (evalWithAnswerFn answers (privateNonce message)) message
        attemptLimit 0 counter output (by decide) hd).2.2.2
      simp only [hd,evalWithAnswerFn_bind,eval_forestRows] at he
      cases hl : evalWithAnswerFn answers (signLayers cache (output.toNat%2^31) 4
        (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
          (forestRoots answers (output.toNat%2^31) 7)))) with
      | none => simp only [hl,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some pieces =>
          simp only [hl,evalWithAnswerFn_pure,Option.some.injEq] at he
          subst sig
          let sig : Signature := ⟨evalWithAnswerFn answers (privateNonce message),
            fun i => (forestOpenPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0,
            fun i => (forestProofPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0,
            fun lay => piecesSignature lay (pieces.getD lay.val ([],[]))⟩
          change ∃ w : Witness,evalWithAnswerFn answers
            (expand message (treeValue (builtTree answers 0 0) 12 0) sig)=some w
          have hf := recoverFts_from_signer_lists answers sig (output.toNat%2^31) output hadm
            (fun _ => rfl) (fun _ => rfl)
          have hparts : PiecesAgree sig pieces 4 := fun _ _ => rfl
          obtain ⟨counters,hc,hreplay⟩ := (signLayers_expandLayers answers cache (output.toNat%2^31)
            hcache (Nat.mod_lt _ (by positivity)) 4 (by decide) _ pieces hl).2 sig hparts
          refine ⟨⟨sig,counter,fun lay => counters.getD lay.val 0⟩,?_⟩
          unfold expand
          rw [show sig.rho=evalWithAnswerFn answers (privateNonce message) by rfl]
          simp only [evalWithAnswerFn_bind,hd,hf,hreplay,layerResultRoot,show ¬(4 : Nat)=0 by decide,
            ite_false,ne_eq,not_true_eq_false,evalWithAnswerFn_pure]

/-- All successful signatures from a correctly generated source cache both
expand and verify. Search exhaustion is the only remaining completeness event. -/
theorem signing_success_valid (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message) (sig : Signature)
    (hsign : evalWithAnswerFn answers (sign keys.2 message)=some sig) :
    ∃ w : Witness,evalWithAnswerFn answers (expand message keys.1 sig)=some w ∧
      evalWithAnswerFn answers (verify message keys.1 w)=true := by
  rw [sign_valid_cache answers keys message hkeys.2.2] at hsign
  obtain ⟨w,hw⟩ := signPayload_expands answers keys.2 message sig hkeys.2.1 hsign
  have he : evalWithAnswerFn answers (expand message keys.1 sig)=some w := by rwa [hkeys.1]
  exact ⟨w,he,expand_implies_verify answers message keys.1 sig w he⟩

def SigningCorrect (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (sign keys.2 message)=some sig →
    ∃ w : Witness,evalWithAnswerFn answers (expand message keys.1 sig)=some w ∧
      evalWithAnswerFn answers (verify message keys.1 w)=true

theorem honest_signing_success_valid (answers : Answers) :
    SigningCorrect answers (evalWithAnswerFn answers keygen) := by
  exact signing_success_valid answers _ (keygen_correct answers)

def RealizedSigningCorrect (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (realize secret (sign keys.2 message))=some sig →
    ∃ w : Witness,evalWithAnswerFn answers (realize secret (expand message keys.1 sig))=some w ∧
      evalWithAnswerFn answers (realize secret (verify message keys.1 w))=true

/-- The complete successful-signature correctness statement also holds after
private coordinates are replaced by the concrete secret-dependent hash calls. -/
theorem realized_honest_signing_success_valid (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) :
    RealizedSigningCorrect answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningCorrect
  simp only [realize_eval]
  exact honest_signing_success_valid (answers.compose (realHandler secret))

end SigGolfCandidate.T3.Correctness
