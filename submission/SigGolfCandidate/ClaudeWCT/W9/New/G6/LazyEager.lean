import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyFree
import SigGolfCandidate.T3.Secc.PairGuessLazyEager

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep patch patch_e
  patch_of patch_uniform digestEmb digestEmb_injective evalSPMF_uniform uniform_update rowStep_some rowStep_out
  rowStep_in nonceStep_some nonceStep_none rowsLaw noncesLaw replayRow_true replayRow_false readRow_true readRow_false
  digestInputs_subset_publicUniverse)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)
noncomputable def patchOmega (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    CanonTable.Omega U :=
  ⟨ω.secrets, patch nonceOther ω.other Nn, ω.low, ω.high, patch (digestEmb hsub) ω.residual D⟩
theorem digestOf_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    digestOf (patchOmega hsub ω D Nn) = D := by
  funext x
  change finiteHashAnswer ∅ U (patch (digestEmb hsub) ω.residual D) x.1 = D x
  rw [finiteHashAnswer_none ∅ U _ _ (hsub x.2) rfl]
  exact patch_e (digestEmb_injective hsub) _ _ x
theorem nonceOf_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    nonceOf (patchOmega hsub ω D Nn) = Nn :=
  funext fun m => patch_e nonceOther_injective ω.other Nn m
theorem sameRest_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SameRest ω (patchOmega hsub ω D Nn) := by
  refine ⟨rfl, rfl, rfl, fun x hx => (patch_of (digestEmb hsub) ω.residual D x ?_).symm,
    fun h hh => (patch_of nonceOther ω.other Nn h ?_).symm⟩
  · intro y hy
    apply hx
    rw [← hy]
    exact y.2
  · intro m hm
    exact hh m hm.symm
end OmegaPatch
section OmegaLaw
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
theorem digest_subset (adversary : AdversaryP) : digestInputs ⊆ Wots.referenceInputs adversary :=
  digestInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
noncomputable def omegaLaw (adversary : AdversaryP) : ProbComp (CanonTable.Omega (Wots.referenceInputs adversary)) :=
  ($ᵗ Secrets : ProbComp _) >>= fun secrets =>
    ($ᵗ OtherHalves : ProbComp _) >>= fun other =>
    ($ᵗ LowLabels : ProbComp _) >>= fun low =>
    ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun residual =>
      pure ⟨secrets, other, low, high, residual⟩
noncomputable def ftsPart (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ (WctPoint → Digest) : ProbComp _) >>= fun g =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (wA (canon_subset adversary) ω g, run.2.1, run.2.2)) <$>
      pairRun (wA (canon_subset adversary) ω g) adversary
theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw adversary >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw adversary] *
      Pr[fun x => E (wA (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary _ E]
  rfl
theorem omegaLaw_patch (adversary : AdversaryP) {γ : Type}
    (k : CanonTable.Omega (Wots.referenceInputs adversary) → SPMF γ) :
    (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
      𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => k (patchOmega (digest_subset adversary) ω D Nn)) =
      𝒮[omegaLaw adversary] >>= k := by
  unfold omegaLaw
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  refine bind_congr fun secrets => ?_
  have step1 : ∀ (other : OtherHalves) (low high : LowLabels),
      (𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
        𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k (patchOmega (digest_subset adversary) ⟨secrets, other, low, high, residual⟩ D Nn)) =
      (𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) := by
    intro other low high
    exact patch_uniform (digestEmb_injective (digest_subset adversary)) _ _
      (fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩)
  simp only [step1]
  have step2 : ∀ other : OtherHalves,
      (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) =
      (𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) := by
    intro other
    calc _ = (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
          fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) :=
          bind_congr fun low => bind_congr fun high => RetainedObservation.bind_comm _ _ _
      _ = (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
          𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
          fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) :=
          bind_congr fun low => RetainedObservation.bind_comm _ _ _
      _ = _ := RetainedObservation.bind_comm _ _ _
  simp only [step2]
  exact patch_uniform nonceOther_injective _ _ (fun other =>
    𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
      𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
      fun residual => k ⟨secrets, other, low, high, residual⟩)
end OmegaLaw
section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat) (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)
theorem step_aux (s : WStateL) (input : AuxL) :
    (forcedImpl (envWith rs ns) slot (.inl input)).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (auxWith rs ns s input) : SPMF (AuxSpecL.Range input × LazyMem)) := rfl
theorem step_coin (s : WStateL) (n : Nat) :
    (forcedImpl (envWith rs ns) slot (.inl (.coin n))).run s =
      (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) = _
  rw [liftM_map, Functor.map_map]
theorem step_expose (s : WStateL) (o : Option HashOutput) :
    (forcedImpl (envWith rs ns) slot (.inl (.expose o))).run s = pure ((), { s with memory := s.memory.expose o }) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM (pure ((), s.memory.expose o) : PMF _) : SPMF _) = _
  rw [liftM_pure, map_pure]
theorem step_birth (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.birth x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x true (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_trial (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.trial x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x false (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_nonce (s : WStateL) (m : Message) :
    (forcedImpl (envWith rs ns) slot (.inl (.nonce m))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (nonceStep s.memory m (ns m)) : SPMF (Digest × LazyMem)) := rfl
theorem step_guess (s : WStateL) (f : Guess.GCoord) (c : Digest) :
    (forcedImpl (envWith rs ns) slot (.inr (.inl (f, c)))).run s =
      (fun hit => (hit, { afterTrial (envWith rs ns) s f c hit with memory := s.memory })) <$>
        forcedTrial slot s f c := rfl
theorem step_disclose (s : WStateL) (f : Guess.GCoord) :
    (forcedImpl (envWith rs ns) slot (.inr (.inr f))).run s =
      (fun v => (v, { afterDisclosure (envWith rs ns) s f v with memory := s.memory })) <$>
        UniformTableCompletion.cell (s.allowed f) := rfl
theorem afterTrial_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : Guess.GCoord) (c : Digest) (hit : Bool) :
    afterTrial (envWith rs ns) s f c hit = afterTrial (envWith rs' ns') s f c hit := rfl
theorem afterDisclosure_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : Guess.GCoord) (v : Digest) :
    afterDisclosure (envWith rs ns) s f v = afterDisclosure (envWith rs' ns') s f v := rfl
end Steps
section Congr
open SecretGuessObservation (forcedRun forcedImpl runWith)
def Agree (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ y : digestInputs, mem.rows y.1 = none → D y = D' y) ∧ ∀ m, mem.nonces m = none → Nn m = Nn' m
theorem rowVal_agree {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (hx : mem.rows x = none) : rowVal D x = rowVal D' x := by
  unfold rowVal
  by_cases hd : x ∈ digestInputs
  · rw [dif_pos hd, dif_pos hd]
    exact h.1 ⟨x, hd⟩ hx
  · rw [dif_neg hd, dif_neg hd]
theorem agree_replay {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (b : Bool) : Agree D D' Nn Nn' (mem.replayRow x b) := by
  cases b
  · rw [replayRow_false]
    exact h
  · rw [replayRow_true]
    exact h
theorem agree_read {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (a : HashOutput) (b : Bool) :
    Agree D D' Nn Nn' (mem.readRow x a b) := by
  have hrows : ∀ y : digestInputs, (mem.rows.cacheQuery x a) y.1 = none → D y = D' y := by
    intro y hy
    by_cases hyx : y.1 = x
    · rw [hyx, QueryCache.cacheQuery_self] at hy
      cases hy
    · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact h.1 y hy
  cases b
  · rw [readRow_false]
    exact ⟨hrows, h.2⟩
  · rw [readRow_true]
    exact ⟨hrows, h.2⟩
theorem agree_draw {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (m : Message) (v : Digest) : Agree D D' Nn Nn' (mem.drawNonce m v) := by
  refine ⟨h.1, fun m' hm' => ?_⟩
  change Function.update mem.nonces m (some v) m' = none at hm'
  by_cases hmm : m' = m
  · rw [hmm, Function.update_self] at hm'
    cases hm'
  · rw [Function.update_of_ne hmm] at hm'
    exact h.2 m' hm'
theorem forced_congr {α : Type} (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (slot : Nat)
    (W : OracleComp WSpecL α) (s : WStateL) (h : Agree D D' Nn Nn' s.memory) :
    forcedRun (envE D Nn) slot W s = forcedRun (envE D' Nn') slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [envE, envE, step_coin, step_coin, bind_map_left, bind_map_left]
            exact bind_congr fun c => ih c s h
        | birth x =>
            rw [envE, envE, step_birth, step_birth]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x true)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) true }
                    (agree_read h x _ true)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x true)
        | trial x =>
            rw [envE, envE, step_trial, step_trial]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x false)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) false }
                    (agree_read h x _ false)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x false)
        | nonce m =>
            rw [envE, envE, step_nonce, step_nonce]
            cases hc : s.memory.nonces m with
            | some v =>
                rw [nonceStep_some _ _ _ v hc, nonceStep_some _ _ _ v hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih v _ h
            | none =>
                rw [nonceStep_none _ _ _ hc, nonceStep_none _ _ _ hc, liftM_map, liftM_map, liftM_pure, liftM_pure,
                  map_pure, map_pure, map_pure, map_pure, pure_bind, pure_bind, h.2 m hc]
                exact ih _ _ (agree_draw h m _)
        | expose o =>
            rw [envE, envE, step_expose, step_expose, pure_bind, pure_bind]
            exact ih () _ h
      · rw [envE, envE, step_guess, step_guess, bind_map_left, bind_map_left]
        refine bind_congr fun hit => ?_
        rw [afterTrial_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih hit _ h
      · rw [envE, envE, step_disclose, step_disclose, bind_map_left, bind_map_left]
        refine bind_congr fun v => ?_
        rw [afterDisclosure_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih v _ h
end Congr
section EagerLazy
open SecretGuessObservation (forcedRun forcedImpl runWith)
theorem avg_indep {α : Type} (slot : Nat) (input : WSpecL.Domain) (next : WSpecL.Range input → OracleComp WSpecL α)
    (s : WStateL)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s')
    (X : SPMF (WSpecL.Range input × WStateL)) (hE : ∀ D Nn, (forcedImpl (envE D Nn) slot input).run s = X)
    (hL : (forcedImpl envL slot input).run s = X) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => (forcedImpl (envE D Nn) slot input).run s >>= fun mid =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) =
      ((forcedImpl envL slot input).run s >>= fun mid => runWith (forcedImpl envL slot) (next mid.1) mid.2) := by
  simp only [hE, hL]
  calc _ = (rowsLaw >>= fun D => X >>= fun mid => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) :=
        bind_congr fun D => RetainedObservation.bind_comm _ _ _
    _ = (X >>= fun mid => rowsLaw >>= fun D => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) := RetainedObservation.bind_comm _ _ _
    _ = _ := bind_congr fun mid => ih mid.1 mid.2
theorem avg_fresh_row {α : Type} (slot : Nat) (x : HashInput) (hx : x ∈ digestInputs) (s : WStateL) (b : Bool)
    (next : HashOutput → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (rowVal D x))
        { s with memory := s.memory.readRow x (rowVal D x) b }) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) >>= fun a =>
        forcedRun envL slot (next a) { s with memory := s.memory.readRow x a b }) := by
  have hrv : ∀ D : digestInputs → HashOutput, rowVal D x = D ⟨x, hx⟩ := fun D => by rw [rowVal, dif_pos hx]
  simp only [hrv]
  rw [rowsLaw, uniform_update (⟨x, hx⟩ : digestInputs) (fun a D => noncesLaw >>= fun Nn =>
    forcedRun (envE D Nn) slot (next a) { s with memory := s.memory.readRow x a b })]
  · refine bind_congr fun a => ?_
    rw [← rowsLaw]
    exact ih a _
  · intro a T c
    refine bind_congr fun Nn => forced_congr _ _ _ _ slot _ _ ⟨fun y hy => ?_, fun _ _ => rfl⟩
    have hyx : y ≠ ⟨x, hx⟩ := by
      rintro rfl
      have hcached : (s.memory.readRow x a b).rows x = some a := by
        cases b
        · rw [readRow_false]
          exact QueryCache.cacheQuery_self _ _ _
        · rw [readRow_true]
          exact QueryCache.cacheQuery_self _ _ _
      change (s.memory.readRow x a b).rows x = none at hy
      rw [hcached] at hy
      cases hy
    exact Function.update_of_ne hyx _ _
theorem avg_fresh_nonce {α : Type} (slot : Nat) (m : Message) (s : WStateL)
    (next : Digest → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v =>
        forcedRun envL slot (next v) { s with memory := s.memory.drawNonce m v }) := by
  have step : ∀ D : digestInputs → HashOutput,
      (noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v => noncesLaw >>= fun Nn =>
        forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v }) := by
    intro D
    rw [noncesLaw]
    refine uniform_update m (fun v Nn => forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v })
      fun v T c => forced_congr _ _ _ _ slot _ _ ⟨fun _ _ => rfl, fun m' hm' => ?_⟩
    have hmm : m' ≠ m := by
      rintro rfl
      change Function.update s.memory.nonces m' (some v) m' = none at hm'
      rw [Function.update_self] at hm'
      cases hm'
    exact Function.update_of_ne hmm _ _
  simp only [step]
  rw [RetainedObservation.bind_comm]
  exact bind_congr fun v => ih v _
theorem eager_lazy_core {α : Type} (slot : Nat) (W : OracleComp WSpecL α) (s : WStateL) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [forcedRun, SecretGuessObservation.runWith_pure, rowsLaw, noncesLaw,
        RetainedObservation.lift_bind_const]
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_coin]) (by rw [envL, step_coin])
        | expose o =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_expose]) (by rw [envL, step_expose])
        | birth x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x true }))
                  (fun D Nn => by rw [envE, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.birth x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) true }) := fun D Nn => by
                    rw [envE, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.birth x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a true })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s true next ih
                · exact avg_indep slot _ next s ih
                    (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x true }))
                    (fun D Nn => by rw [envE, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | trial x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x false }))
                  (fun D Nn => by rw [envE, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.trial x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) false }) := fun D Nn => by
                    rw [envE, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.trial x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s false next ih
                · exact avg_indep slot _ next s ih
                    (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x false }))
                    (fun D Nn => by rw [envE, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | nonce m =>
            cases hc : s.memory.nonces m with
            | some v =>
                exact avg_indep slot _ next s ih (pure (v, { s with memory := s.memory }))
                  (fun D Nn => by rw [envE, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
                  (by rw [envL, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
            | none =>
                have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.nonce m))).run s =
                    pure (Nn m, { s with memory := s.memory.drawNonce m (Nn m) }) := fun D Nn => by
                  rw [envE, step_nonce, nonceStep_none _ _ _ hc, liftM_map, liftM_pure, map_pure, map_pure]
                have hL : (forcedImpl envL slot (.inl (.nonce m))).run s =
                    (fun v => (v, { s with memory := s.memory.drawNonce m v })) <$>
                      (liftM (PMF.uniformOfFintype Digest) : SPMF Digest) := by
                  rw [envL, step_nonce, nonceStep_none _ _ _ hc, liftM_map, Functor.map_map]
                simp only [hE, hL, pure_bind, bind_map_left]
                exact avg_fresh_nonce slot m s next ih
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_guess, step_guess]
        have hfun : (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f c hit with memory := s.memory })) =
            (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f c hit with
                memory := s.memory })) := by
          funext hit
          rw [afterTrial_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_disclose, step_disclose]
        have hfun : (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f v with memory := s.memory })) =
            (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f v with
                memory := s.memory })) := by
          funext v
          rw [afterDisclosure_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
theorem eager_lazy {α : Type} (W : OracleComp WSpecL α) (slot : Nat) (s : WStateL) :
    (𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
      forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  rw [evalSPMF_uniform, evalSPMF_uniform]
  exact eager_lazy_core slot W s
end EagerLazy
section Avg
open SecretGuessObservation (forcedRun)
theorem forced_avg_law (adversary : AdversaryP) (slot : Nat) :
    (𝒮[omegaLaw adversary] >>= fun ω => forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL) =
      (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL) := by
  symm
  calc (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL)
      = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          forcedRun (envE D Nn) slot (worldGameL (canon_subset adversary) ω adversary) initL) :=
        bind_congr fun ω => (eager_lazy _ slot initL).symm
    _ = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          (fun ω' : CanonTable.Omega (Wots.referenceInputs adversary) =>
            forcedRun (envE (digestOf ω') (nonceOf ω')) slot
              (worldGameL (canon_subset adversary) ω' adversary) initL)
            (patchOmega (digest_subset adversary) ω D Nn)) := by
        refine bind_congr fun ω => bind_congr fun D => bind_congr fun Nn => ?_
        dsimp only
        rw [digestOf_patch, nonceOf_patch]
        exact congrArg (fun W => forcedRun (envE D Nn) slot W initL)
          (worldGameL_congr (canon_subset adversary) (sameRest_patch (digest_subset adversary) ω D Nn) adversary)
    _ = _ := omegaLaw_patch adversary (fun ω' => forcedRun (envE (digestOf ω') (nonceOf ω')) slot
          (worldGameL (canon_subset adversary) ω' adversary) initL)
theorem forced_avg_eq_lazy (adversary : AdversaryP) (slot : Nat)
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal) :
    ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r =
      ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun envL slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
  have h := congrArg (fun X => expectedValue X payoff) (forced_avg_law adversary slot)
  rw [expectedValue_bind, expectedValue_bind] at h
  simp only [expectedValue_def, probOutput_evalSPMF] at h
  exact h
end Avg
end ClaudeWCT.W9.T3.Security.WPair
