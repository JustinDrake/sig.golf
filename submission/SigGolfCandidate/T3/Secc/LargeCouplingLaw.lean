import SigGolfCandidate.T3.Secc.LargeCouplingSamplers

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Generic
theorem evalSPMF_bind_comm {α β γ : Type} (mx : ProbComp α) (my : ProbComp β) (k : α → β → ProbComp γ) :
    𝒮[mx >>= fun x => my >>= fun y => k x y] = 𝒮[my >>= fun y => mx >>= fun x => k x y] := by
  simp only [evalSPMF_bind]
  exact SphincsSecurity.Concrete.RetainedObservation.bind_comm _ _ _
theorem evalSPMF_unused (α : Type) [SampleableType α] [Fintype α] [Nonempty α] {β : Type} (k : ProbComp β) :
    𝒮[($ᵗ α : ProbComp α) >>= fun _ => k] = 𝒮[k] := by
  rw [evalSPMF_bind, evalSPMF_uniformSample]
  exact SphincsSecurity.Concrete.RetainedObservation.lift_bind_const _ _
theorem uniform_equiv_bind {α β γ : Type} [SampleableType α] [SampleableType β] [Finite α] (e : α ≃ β)
    (next : β → ProbComp γ) :
    𝒮[($ᵗ β : ProbComp β) >>= next] = 𝒮[($ᵗ α : ProbComp α) >>= fun x => next (e x)] := by
  have hb := evalSPMF_map_bijective_uniform_cross (α := α) (β := β) e e.bijective
  have h := congrArg (fun law : SPMF β => law >>= fun y => 𝒮[next y]) hb
  simp only [evalSPMF_map, bind_map_left] at h
  rw [evalSPMF_bind, evalSPMF_bind, ← h]
theorem uniform_prod_bind {α β γ : Type} [Finite α] [Finite β] [SampleableType α] [SampleableType β]
    [SampleableType (α × β)] (next : α × β → ProbComp γ) :
    𝒮[($ᵗ (α × β) : ProbComp _) >>= next] =
      𝒮[($ᵗ α : ProbComp α) >>= fun x => ($ᵗ β : ProbComp β) >>= fun y => next (x, y)] := by
  have hprod := FullGame.uniform_product (A := α) (B := β)
  have h := congrArg (fun law : SPMF (α × β) => law >>= fun p => 𝒮[next p]) hprod
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] at h
  rw [evalSPMF_bind, ← h, evalSPMF_bind]
  simp only [evalSPMF_bind]
end Generic
section Tables
open SphincsSecurity.Concrete.UniformTableSplit in
theorem uniform_join_bind {ι C A R : Type} [Fintype ι] [Fintype C] [Fintype A] [Nonempty A] [DecidableEq ι]
    [DecidableEq C] (embed : ι → C) (hinj : Function.Injective embed) [SampleableType (C → A)]
    [SampleableType (ι → A)] [SampleableType (Outside embed → A)] (next : (C → A) → ProbComp R) :
    𝒮[($ᵗ (C → A) : ProbComp _) >>= next] =
      𝒮[($ᵗ (ι → A) : ProbComp _) >>= fun r => ($ᵗ (Outside embed → A) : ProbComp _) >>= fun o =>
        next (join embed hinj r o)] := by
  let _ : SampleableType ((ι → A) × (Outside embed → A)) := SampleableType.ofFintype _
  rw [uniform_equiv_bind (split embed hinj).symm next, uniform_prod_bind]
  rfl
open SphincsSecurity.Concrete.UniformTableSplit in
theorem overwrite_bind {ι C A R : Type} [Fintype ι] [Fintype C] [Fintype A] [Nonempty A] [DecidableEq ι]
    [DecidableEq C] (embed : ι → C) (hinj : Function.Injective embed) [SampleableType (C → A)]
    [SampleableType (ι → A)] [SampleableType (Outside embed → A)] (next : (C → A) → ProbComp R) :
    𝒮[($ᵗ (C → A) : ProbComp _) >>= fun t => ($ᵗ (ι → A) : ProbComp _) >>= fun r =>
        next (overwrite embed hinj r t)] =
      𝒮[($ᵗ (C → A) : ProbComp _) >>= next] := by
  rw [uniform_join_bind embed hinj, uniform_join_bind embed hinj next]
  simp only [overwrite_join]
  rw [evalSPMF_unused (ι → A)]
  exact evalSPMF_bind_comm _ _ _
end Tables
section Law
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem others_bind {R : Type} (next : OtherHalves → ProbComp R) :
    𝒮[($ᵗ OtherHalves : ProbComp _) >>= next] =
      𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        next (nonceOver (privateEquiv priv).2 nv)] := by
  rw [private_bind (fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
    next (nonceOver (privateEquiv priv).2 nv))]
  simp only [Equiv.apply_symm_apply]
  rw [evalSPMF_unused Secrets]
  unfold nonceOver
  rw [overwrite_bind nonceHalf nonceHalf_injective next]
theorem residual_bind (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi U hE labels rows τ)] := by
  have hj : ∀ (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (g : EncLeaf × Fin (2 ^ 22) → HashOutput)
      (out : SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput),
      residualPsi U hE labels rows
        (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels) g out) =
      SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (mix rowPrefix (Function.uncurry rows) g) out := by
    intro rows g out
    unfold residualPsi
    have hg : (fun x => SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) g out (encCell U hE labels x)) = g :=
      funext fun x => SphincsSecurity.Concrete.UniformTableSplit.join_embed _ _ _ _ x
    rw [hg, SphincsSecurity.Concrete.UniformTableSplit.overwrite_join]
  rw [evalSPMF_bind_congr' _ (fun rows => uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels)
    (fun τ => next (residualPsi U hE labels rows τ)))]
  simp only [hj]
  rw [uniform_equiv_bind (Equiv.curry (EncLeaf) (Fin (2 ^ 22)) HashOutput).symm.symm]
  simp only [Equiv.symm_symm, Equiv.curry_apply, Function.uncurry_curry]
  rw [uniform_mix rowPrefix rowPrefix_determined (fun R =>
    ($ᵗ (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) : ProbComp _) >>=
      fun out => next (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) R out))]
  rw [uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels) next]
theorem law_derived (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        ($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (programmed U hU sec (joinLabels low high) (residualPsi U hE (joinLabels low high) rows τ)))] := by
  simp only [eagerAnswers_eq]
  rw [tables_bind U hU (fun priv pub => next (CanonGraph.eagerAnswers priv U pub))]
  refine (evalSPMF_bind_congr' _ fun sec => others_bind _).trans ?_
  refine evalSPMF_bind_congr' _ fun sec => evalSPMF_bind_congr' _ fun priv' => evalSPMF_bind_congr' _ fun nv => ?_
  rw [labels_bind]
  refine evalSPMF_bind_congr' _ fun low => evalSPMF_bind_congr' _ fun high => ?_
  exact residual_bind U hE (joinLabels low high) _
theorem law_target (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (programmed U hU sec (joinLabels low high) (residualPsi U hE (joinLabels low high) rows τ)))] := by
  rw [law_derived U hU hE next]
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  rfl
end Law
end SigGolfCandidate.T3.Security.LargeCoupling
