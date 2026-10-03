import SigGolfCandidate.SphincsSecurity.Proof.RandomizedStatement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

section


open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
def finHeadTailEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp
theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] [SampleableType (α × β)] :
    evalSPMF (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =
    evalSPMF ($ᵗ (α × β)) := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]
variable {D R : Type} [DecidableEq D]
def cacheFin : {n : Nat} → QueryCache (D →ₒ R) → (Fin n → D) → (Fin n → R) →
    QueryCache (D →ₒ R)
  | 0, cache, _, _ => cache
  | _ + 1, cache, inputs, outputs =>
      cacheFin (cache.cacheQuery (inputs 0) (outputs 0))
        (fun i => inputs i.succ) (fun i => outputs i.succ)
theorem cacheFin_apply_of_not_mem {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (outputs : Fin n → R) (input : D)
    (hinput : ∀ i, input ≠ inputs i) : cacheFin cache inputs outputs input = cache input := by
  induction n generalizing cache with
  | zero => rfl
  | succ n ih =>
      rw [cacheFin, ih _ _ _ (fun i => hinput i.succ)]
      exact QueryCache.cacheQuery_of_ne cache (outputs 0) (hinput 0)
theorem cacheFin_apply {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (hinj : Function.Injective inputs) (outputs : Fin n → R) (i : Fin n) :
    cacheFin cache inputs outputs (inputs i) = some (outputs i) := by
  induction n generalizing cache with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [cacheFin, cacheFin_apply_of_not_mem]
          · exact QueryCache.cacheQuery_self _ _ _
          · intro j h
            have := hinj h
            exact Fin.succ_ne_zero j this.symm
      | succ i =>
          exact ih _ _ (fun _ _ h => Fin.succ_injective _ (hinj h)) _ i
variable [SampleableType R]
theorem run_sequenceFin_fresh {n : Nat} (inputs : Fin n → D)
    (hinj : Function.Injective inputs) (cache : QueryCache (D →ₒ R))
    (hfresh : ∀ i, cache (inputs i) = none) :
    (simulateQ randomOracle (Concrete.sequenceFin fun i =>
      (liftM ((D →ₒ R).query (inputs i)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)
        pure (outputs, cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero => simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, pure_bind, cacheFin]
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh 0)]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp, map_bind]
      change (($ᵗ R) >>= _) = (($ᵗ R) >>= _)
      apply bind_congr
      intro head
      have htail : ∀ i : Fin n, (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro h
          exact Fin.succ_ne_zero i (hinj h)
      rw [ih (fun i => inputs i.succ) (fun _ _ h => Fin.succ_injective _ (hinj h)) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheFin]
      rfl
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type} {n : Nat}
    (f : A → B) (computation : Fin n → m A) :
    Concrete.sequenceFin (fun i => f <$> computation i) =
      (fun values i => f (values i)) <$> Concrete.sequenceFin computation := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, bind_map_left, ih, map_bind, bind_pure_comp, Functor.map_map]
      apply bind_congr
      intro head
      congr 1
      funext tail i
      cases i using Fin.cases <;> rfl
theorem evalDist_sequenceFin_congr {A : Type} {n : Nat}
    (left right : Fin n → ProbComp A) (h : ∀ i, 𝒮[left i] = 𝒮[right i]) :
    𝒮[Concrete.sequenceFin left] = 𝒮[Concrete.sequenceFin right] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Concrete.sequenceFin, bind_pure_comp, evalSPMF_bind]
      rw [h 0]
      congr 1
      funext head
      rw [evalSPMF_map, evalSPMF_map, ih _ _ (fun i => h i.succ)]
theorem evalDist_sequenceFin_uniform [Fintype R] (n : Nat) :
    𝒮[Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)] =
      𝒮[$ᵗ (Fin n → R)] := by
  classical
  induction n with
  | zero =>
      apply SPMF.ext
      intro values
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [Concrete.sequenceFin, heq]
  | succ n ih =>
      calc
        _ = 𝒮[finHeadTailEquiv R n <$> (do
            let head ← $ᵗ R
            let tail ← $ᵗ (Fin n → R)
            pure (head, tail))] := by
          simp only [Concrete.sequenceFin, map_bind, finHeadTailEquiv,
            Equiv.coe_fn_mk, bind_pure_comp]
          rw [evalSPMF_bind, evalSPMF_bind]
          congr 1
          funext head
          rw [evalSPMF_map, ih, evalSPMF_map, evalSPMF_map, Functor.map_map]
        _ = 𝒮[finHeadTailEquiv R n <$> ($ᵗ (R × (Fin n → R)))] := by
          rw [evalSPMF_map, evalSPMF_map, evalDist_independent_uniform_pair]
        _ = _ := evalSPMF_map_bijective_uniform_cross
          (α := R × (Fin n → R)) (β := Fin (n + 1) → R)
          (finHeadTailEquiv R n) (finHeadTailEquiv R n).bijective
end SphincsSecurity.Seeded
end

section

open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
variable (J R : Type) [Fintype J]
noncomputable def finTableEquiv : (Fin (Fintype.card J) → R) ≃ (J → R) where
  toFun values j := values (Fintype.equivFin J j)
  invFun values i := values ((Fintype.equivFin J).symm i)
  left_inv values := by funext i; simp
  right_inv values := by funext j; simp
variable {J R} {D : Type} [DecidableEq D]
noncomputable def cacheTable (cache : QueryCache (D →ₒ R)) (inputs : J → D) (outputs : J → R) :
    QueryCache (D →ₒ R) :=
  cacheFin cache (fun i => inputs ((Fintype.equivFin J).symm i))
    ((finTableEquiv J R).symm outputs)
theorem cacheTable_apply (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (hinj : Function.Injective inputs) (outputs : J → R) (j : J) :
    cacheTable cache inputs outputs (inputs j) = some (outputs j) := by
  have h := cacheFin_apply cache (fun i => inputs ((Fintype.equivFin J).symm i))
    (hinj.comp (Fintype.equivFin J).symm.injective) ((finTableEquiv J R).symm outputs)
    (Fintype.equivFin J j)
  rw [(Fintype.equivFin J).symm_apply_apply] at h
  simpa only [cacheTable, finTableEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using h
theorem cacheTable_apply_of_not_mem (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (outputs : J → R) (input : D) (hinput : ∀ j, input ≠ inputs j) :
    cacheTable cache inputs outputs input = cache input :=
  cacheFin_apply_of_not_mem _ _ _ _ (fun _ => hinput _)
noncomputable def queryTable (inputs : J → D) : OracleComp (D →ₒ R) (J → R) :=
  finTableEquiv J R <$> Concrete.sequenceFin fun i =>
    (liftM ((D →ₒ R).query (inputs ((Fintype.equivFin J).symm i))) : OracleComp (D →ₒ R) R)
variable [SampleableType R] [Fintype R] [SampleableType (J → R)]
theorem evalDist_queryTable_fresh (inputs : J → D) (hinj : Function.Injective inputs)
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ j, cache (inputs j) = none) :
    𝒮[(simulateQ randomOracle (queryTable inputs)).run cache] =
      𝒮[(fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R))] := by
  classical
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  simp only [bind_pure_comp, Functor.map_map]
  rw [evalSPMF_map, evalDist_sequenceFin_uniform]
  have htable := evalSPMF_map_bijective_uniform_cross
    (α := Fin (Fintype.card J) → R) (β := J → R) (finTableEquiv J R) (finTableEquiv J R).bijective
  rw [evalSPMF_map, ← htable]
  simp only [evalSPMF_map, Functor.map_map]
  congr 1
  funext outputs
  simp only [cacheTable, Equiv.symm_apply_apply]
end SphincsSecurity.Seeded
end
