import SigGolfCandidate.T3.FullCache.NativeTables
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import SigGolfCandidate.ClaudeWCT.W9.New.CanonTable.ChainTable
import SigGolfCandidate.ClaudeWCT.W9.New.G6.World
import SigGolfCandidate.T3.Secc.PairGuessWorld
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.PairGuessEager
import SigGolfCandidate.T3.Secc.PairGuessFinal

section


namespace ClaudeWCT.Guess
open OracleComp OracleSpec OracleComp.DeferredSampling
section Override
variable {α β V : Type}
noncomputable def extendSwap (ι : β → α) (p : (α → V) × (β → V)) : (α → V) × (β → V) :=
  (Function.extend ι p.2 p.1, p.1 ∘ ι)
theorem extendSwap_involutive {ι : β → α} (hι : Function.Injective ι) :
    Function.Involutive (extendSwap (V := V) ι) := by
  rintro ⟨f, g⟩
  simp only [extendSwap]
  refine Prod.ext ?_ ?_
  · funext x
    simp only
    rcases Classical.em (∃ b, ι b = x) with hx | hx
    · obtain ⟨b, rfl⟩ := hx
      rw [hι.extend_apply]
      rfl
    · rw [Function.extend_apply' _ _ _ hx, Function.extend_apply' _ _ _ hx]
  · funext b
    simp only [Function.comp_apply]
    exact hι.extend_apply g f b
theorem bind_congr_law {A B : Type} {mx my : ProbComp A} (h : 𝒮[mx] = 𝒮[my]) (f : A → ProbComp B) :
    𝒮[mx >>= f] = 𝒮[my >>= f] := by
  rw [evalSPMF_bind, evalSPMF_bind, h]
theorem extend_bind [Finite α] [Finite β] [Finite V] [SampleableType (α → V)] [SampleableType (β → V)]
    [SampleableType ((α → V) × (β → V))] {ι : β → α} (hι : Function.Injective ι) {Result : Type}
    (next : (α → V) → ProbComp Result) :
    𝒮[do
      let f ← ($ᵗ (α → V) : ProbComp _)
      let g ← ($ᵗ (β → V) : ProbComp _)
      next (Function.extend ι g f)] =
      𝒮[do let f ← ($ᵗ (α → V) : ProbComp _); next f] := by
  have hu := SigGolfCandidate.T3.Security.FullGame.uniform_product (A := α → V) (B := β → V)
  have hb := evalSPMF_map_bijective_uniform_cross (α := (α → V) × (β → V)) (β := (α → V) × (β → V))
    (extendSwap ι) (extendSwap_involutive hι).bijective
  calc
    _ = 𝒮[(do let f ← ($ᵗ (α → V) : ProbComp _); let g ← ($ᵗ (β → V) : ProbComp _); pure (f, g)) >>=
          fun p => next (extendSwap ι p).1] := by
        simp only [bind_assoc, pure_bind, extendSwap]
    _ = 𝒮[($ᵗ ((α → V) × (β → V)) : ProbComp _) >>= fun p => next (extendSwap ι p).1] := by
        exact bind_congr_law hu _
    _ = 𝒮[(extendSwap ι <$> ($ᵗ ((α → V) × (β → V)) : ProbComp _)) >>= fun p => next p.1] := by
        rw [bind_map_left]
    _ = 𝒮[($ᵗ ((α → V) × (β → V)) : ProbComp _) >>= fun p => next p.1] := by
        exact bind_congr_law hb _
    _ = 𝒮[(do let f ← ($ᵗ (α → V) : ProbComp _); let g ← ($ᵗ (β → V) : ProbComp _); pure (f, g)) >>=
          fun p => next p.1] := by
        exact (bind_congr_law hu _).symm
    _ = 𝒮[do let f ← ($ᵗ (α → V) : ProbComp _); let _g ← ($ᵗ (β → V) : ProbComp _); next f] := by
        simp only [bind_assoc, pure_bind]
    _ = _ := by
        apply evalSPMF_bind_congr_left
        intro f
        exact evalSPMF_bind_const_neverFails _ (probFailure_uniformSample (β → V)) _
end Override
end ClaudeWCT.Guess
end

section


namespace ClaudeWCT.W9.CanonTable
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.CanonGraph
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def splitHidden (g : WctPoint → Digest) : (WctAddr → Digest) × (WctAddr × Fin 2 → Digest) :=
  (fun a => g (a, 0), fun c => g (shiftCoord c))
def joinHidden (p : (WctAddr → Digest) × (WctAddr × Fin 2 → Digest)) : WctPoint → Digest :=
  fun q => if h : q.2.val = 0 then p.1 q.1 else p.2 (q.1, ⟨q.2.val - 1, by omega⟩)
def hiddenEquiv : (WctPoint → Digest) ≃ (WctAddr → Digest) × (WctAddr × Fin 2 → Digest) where
  toFun := splitHidden
  invFun := joinHidden
  left_inv g := by
    funext ⟨a, ⟨s, hs⟩⟩
    unfold joinHidden splitHidden shiftCoord
    simp only
    split_ifs with h
    · subst h; rfl
    · congr 2
      apply Fin.ext
      simp only
      omega
  right_inv p := by
    obtain ⟨p0, p12⟩ := p
    refine Prod.ext ?_ ?_
    · funext a
      simp [splitHidden, joinHidden]
    · funext ⟨a, ⟨q, hq⟩⟩
      simp [splitHidden, joinHidden, shiftCoord]
theorem hiddenEquiv_symm_apply (p : (WctAddr → Digest) × (WctAddr × Fin 2 → Digest)) :
    hiddenEquiv.symm p = joinHidden p := rfl
theorem joinHidden_hiddenEquiv (g : WctPoint → Digest) : joinHidden (hiddenEquiv g) = g :=
  hiddenEquiv.symm_apply_apply g
variable {U : Finset HashInput} (hU : canonInputs ⊆ U)
theorem worldAnswers_join (ω : Omega U) (g0 : WctAddr → Digest) (g12 : WctAddr × Fin 2 → Digest) :
    worldAnswers hU ω (joinHidden (g0, g12)) =
      eagerAnswers (privateEquiv.symm (Function.extend Sum.inr g0 ω.secrets, ω.other)) U
        (programmed U hU (Function.extend Sum.inr g0 ω.secrets)
          (joinLabels (Function.extend stepNode g12 ω.low) ω.high) ω.residual) := by
  have h0 : (fun a => joinHidden (g0, g12) (a, 0)) = g0 := by
    funext a; simp [joinHidden]
  have h12 : (fun c => joinHidden (g0, g12) (shiftCoord c)) = g12 := by
    funext ⟨a, ⟨q, hq⟩⟩; simp [joinHidden, shiftCoord]
  unfold worldAnswers worldLabels worldSecrets worldLow
  rw [h0, h12]
section Law
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels
noncomputable local instance instSampleableTypeHidden : SampleableType (WctPoint → Digest) :=
  SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSeedHidden : SampleableType (WctAddr → Digest) :=
  SampleableType.ofFintype _
noncomputable local instance instSampleableTypeStepHidden : SampleableType (WctAddr × Fin 2 → Digest) :=
  SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdHidden :
    SampleableType ((WctAddr → Digest) × (WctAddr × Fin 2 → Digest)) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdSecretsSeed :
    SampleableType (Secrets × (WctAddr → Digest)) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowStep :
    SampleableType (LowLabels × (WctAddr × Fin 2 → Digest)) := SampleableType.ofFintype _
theorem hidden_bind {Result : Type} (next : (WctPoint → Digest) → ProbComp Result) :
    𝒮[do let g ← ($ᵗ (WctPoint → Digest) : ProbComp _); next g] =
      𝒮[do
        let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
        let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
        next (joinHidden (g0, g12))] := by
  have hsplit : 𝒮[hiddenEquiv <$> ($ᵗ (WctPoint → Digest) : ProbComp _)] =
      𝒮[do
        let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
        let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
        pure (g0, g12)] :=
    (evalSPMF_map_bijective_uniform_cross (α := WctPoint → Digest)
      (β := (WctAddr → Digest) × (WctAddr × Fin 2 → Digest)) hiddenEquiv hiddenEquiv.bijective).trans
      (FullGame.uniform_product (A := WctAddr → Digest) (B := WctAddr × Fin 2 → Digest)).symm
  have h := congrArg (fun law : SPMF ((WctAddr → Digest) × (WctAddr × Fin 2 → Digest)) =>
    law >>= fun result => 𝒮[next (hiddenEquiv.symm result)]) hsplit
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply, hiddenEquiv_symm_apply, joinHidden_hiddenEquiv] using h
theorem world_tables_bind {Result : Type} (next : Answers → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (eagerAnswers privateTable U publicTable)] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        let g ← ($ᵗ (WctPoint → Digest) : ProbComp _)
        next (worldAnswers hU ⟨secrets, other, low, high, residual⟩ g)] := by
  let K : Secrets → OtherHalves → LowLabels → LowLabels → (U → HashOutput) → Answers :=
    fun s o l h r => eagerAnswers (privateEquiv.symm (s, o)) U (programmed U hU s (joinLabels l h) r)
  have hL : 𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (eagerAnswers privateTable U publicTable)] =
      𝒮[do
        let s ← ($ᵗ Secrets : ProbComp _)
        let o ← ($ᵗ OtherHalves : ProbComp _)
        let l ← ($ᵗ LowLabels : ProbComp _)
        let h ← ($ᵗ LowLabels : ProbComp _)
        let r ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (K s o l h r)] := by
    rw [tables_bind U hU (fun privateTable publicTable => next (eagerAnswers privateTable U publicTable))]
    apply evalSPMF_bind_congr_left; intro s
    apply evalSPMF_bind_congr_left; intro o
    exact labels_bind (fun labels => do
      let r ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (eagerAnswers (privateEquiv.symm (s, o)) U (programmed U hU s labels r)))
  rw [hL]
  symm
  have hR1 : 𝒮[do
        let s ← ($ᵗ Secrets : ProbComp _)
        let o ← ($ᵗ OtherHalves : ProbComp _)
        let l ← ($ᵗ LowLabels : ProbComp _)
        let h ← ($ᵗ LowLabels : ProbComp _)
        let r ← ($ᵗ (U → HashOutput) : ProbComp _)
        let g ← ($ᵗ (WctPoint → Digest) : ProbComp _)
        next (worldAnswers hU ⟨s, o, l, h, r⟩ g)] =
      𝒮[do
        let s ← ($ᵗ Secrets : ProbComp _)
        let o ← ($ᵗ OtherHalves : ProbComp _)
        let l ← ($ᵗ LowLabels : ProbComp _)
        let h ← ($ᵗ LowLabels : ProbComp _)
        let r ← ($ᵗ (U → HashOutput) : ProbComp _)
        let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
        let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
        next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
    apply evalSPMF_bind_congr_left; intro s
    apply evalSPMF_bind_congr_left; intro o
    apply evalSPMF_bind_congr_left; intro l
    apply evalSPMF_bind_congr_left; intro h
    apply evalSPMF_bind_congr_left; intro r
    rw [hidden_bind (fun g => next (worldAnswers hU ⟨s, o, l, h, r⟩ g))]
    apply evalSPMF_bind_congr_left; intro g0
    apply evalSPMF_bind_congr_left; intro g12
    rw [worldAnswers_join]
  rw [hR1]
  have hR2 : 𝒮[do
        let s ← ($ᵗ Secrets : ProbComp _)
        let o ← ($ᵗ OtherHalves : ProbComp _)
        let l ← ($ᵗ LowLabels : ProbComp _)
        let h ← ($ᵗ LowLabels : ProbComp _)
        let r ← ($ᵗ (U → HashOutput) : ProbComp _)
        let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
        let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
        next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
      𝒮[do
        let s ← ($ᵗ Secrets : ProbComp _)
        let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
        let o ← ($ᵗ OtherHalves : ProbComp _)
        let l ← ($ᵗ LowLabels : ProbComp _)
        let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
        let h ← ($ᵗ LowLabels : ProbComp _)
        let r ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
    apply evalSPMF_bind_congr_left; intro s
    have e1 : ∀ o l h, 𝒮[do
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      fun o l h => evalSPMF_bind_bind_swap _ _ _
    have e2 : ∀ o l, 𝒮[do
          let h ← ($ᵗ LowLabels : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      fun o l => evalSPMF_bind_bind_swap _ _ _
    have e3 : ∀ o, 𝒮[do
          let l ← ($ᵗ LowLabels : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      fun o => evalSPMF_bind_bind_swap _ _ _
    have e4 : 𝒮[do
          let o ← ($ᵗ OtherHalves : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let o ← ($ᵗ OtherHalves : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      evalSPMF_bind_bind_swap _ _ _
    have f1 : ∀ g0 o l h, 𝒮[do
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      fun g0 o l h => evalSPMF_bind_bind_swap _ _ _
    have f2 : ∀ g0 o l, 𝒮[do
          let h ← ($ᵗ LowLabels : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] =
        𝒮[do
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] :=
      fun g0 o l => evalSPMF_bind_bind_swap _ _ _
    calc _ = 𝒮[do
          let o ← ($ᵗ OtherHalves : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
          apply evalSPMF_bind_congr_left; intro o
          apply evalSPMF_bind_congr_left; intro l
          apply evalSPMF_bind_congr_left; intro h
          exact e1 o l h
      _ = 𝒮[do
          let o ← ($ᵗ OtherHalves : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
          apply evalSPMF_bind_congr_left; intro o
          apply evalSPMF_bind_congr_left; intro l
          exact e2 o l
      _ = 𝒮[do
          let o ← ($ᵗ OtherHalves : ProbComp _)
          let g0 ← ($ᵗ (WctAddr → Digest) : ProbComp _)
          let l ← ($ᵗ LowLabels : ProbComp _)
          let h ← ($ᵗ LowLabels : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
          apply evalSPMF_bind_congr_left; intro o
          exact e3 o
      _ = _ := e4.trans ?_
    apply evalSPMF_bind_congr_left; intro g0
    apply evalSPMF_bind_congr_left; intro o
    apply evalSPMF_bind_congr_left; intro l
    calc _ = 𝒮[do
          let h ← ($ᵗ LowLabels : ProbComp _)
          let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
          let r ← ($ᵗ (U → HashOutput) : ProbComp _)
          next (K (Function.extend Sum.inr g0 s) o (Function.extend stepNode g12 l) h r)] := by
          apply evalSPMF_bind_congr_left; intro h
          exact f1 g0 o l h
      _ = _ := f2 g0 o l
  rw [hR2]
  have hX1 := @Guess.extend_bind SecretIndex WctAddr Digest _ _ _ instSampleableTypeSecrets
    instSampleableTypeSeedHidden instSampleableTypeProdSecretsSeed Sum.inr Sum.inr_injective Result
    (fun s' => do
      let o ← ($ᵗ OtherHalves : ProbComp _)
      let l ← ($ᵗ LowLabels : ProbComp _)
      let g12 ← ($ᵗ (WctAddr × Fin 2 → Digest) : ProbComp _)
      let h ← ($ᵗ LowLabels : ProbComp _)
      let r ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (K s' o (Function.extend stepNode g12 l) h r))
  refine hX1.trans ?_
  apply evalSPMF_bind_congr_left; intro s
  apply evalSPMF_bind_congr_left; intro o
  exact @Guess.extend_bind Node (WctAddr × Fin 2) Digest _ _ _ instSampleableTypeLowLabels
    instSampleableTypeStepHidden instSampleableTypeProdLowStep stepNode stepNode_injective Result
    (fun l' => do
      let h ← ($ᵗ LowLabels : ProbComp _)
      let r ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (K s o l' h r))
end Law
end ClaudeWCT.W9.CanonTable
end

section


namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev pairTerm (q : Nat) : ENNReal := SigGolfCandidate.T3.Security.BPair.pairTerm q
noncomputable abbrev guessTerm (q : Nat) : ENNReal := SigGolfCandidate.T3.Security.BPair.guessTerm q
def OneGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ c, GuessedIn answers log entries c
section WorldBound
open SecretGuessObservation (fixedRun lazyRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def secretsLaw : SPMF (Guess.GCoord → Digest) := UniformTableCompletion.complete init.allowed
noncomputable def ftsRun (adversary : AdversaryP) :
    SPMF ((Guess.GCoord → Digest) × (Bool × QueryLog Requests × List Wots.Entry)) :=
  secretsLaw >>= fun g => (fun run => (g, run)) <$> 𝒮[pairRun (wA hU ω g) adversary]
theorem fts_event_le_world (adversary : AdversaryP)
    (event : (Guess.GCoord → Digest) → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WState → Prop)
    (himp : ∀ g result, fixedRun env g (worldGame hU ω adversary) init result ≠ 0 → event g result.1 →
      wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤ Pr[wevent | lazyRun env (worldGame hU ω adversary) init] := by
  rw [← SecretGuessObservation.run_erasure env (worldGame hU ω adversary) init (fun _ => Finset.univ_nonempty)]
  unfold ftsRun secretsLaw
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGame hU ω g adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
theorem fts_pair_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun x => x.2.2.2.length ≤ q ∧ PairGuessIn (wA hU ω x.1) x.2.2.1 x.2.2.2 | ftsRun hU ω adversary] ≤
      pairTerm q := by
  refine (fts_event_le_world hU ω adversary
    (fun g run => run.2.2.length ≤ q ∧ PairGuessIn (wA hU ω g) run.2.1 run.2.2)
    (fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ q)
    ?_).trans ?_
  · rintro g result hr ⟨hlen, c, c', hcc, hc, hc'⟩
    obtain ⟨hp, hgs⟩ := worldGame_tracking hU ω g adversary result hr
    exact ⟨Guess.two_le_card_of_prefixIn hcc (hgs c hc) (hgs c' hc'), hp.trans hlen⟩
  · have h := SigGolfCandidate.T3.Security.BPair.lazyRun_pair_le env (worldGame hU ω adversary) PUnit.unit q
    rw [card_digest] at h
    exact h
theorem fts_one_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun x => x.2.2.2.length ≤ q ∧ OneGuessIn (wA hU ω x.1) x.2.2.1 x.2.2.2 | ftsRun hU ω adversary] ≤
      guessTerm q := by
  refine (fts_event_le_world hU ω adversary
    (fun g run => run.2.2.length ≤ q ∧ OneGuessIn (wA hU ω g) run.2.1 run.2.2)
    (fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ q)
    ?_).trans ?_
  · rintro g result hr ⟨hlen, c, hc⟩
    obtain ⟨hp, hgs⟩ := worldGame_tracking hU ω g adversary result hr
    exact ⟨Guess.nonempty_of_prefixIn (hgs c hc), hp.trans hlen⟩
  · have h := SigGolfCandidate.T3.Security.BPair.lazyRun_guess_le env (worldGame hU ω adversary) PUnit.unit q
    rw [card_digest] at h
    exact h
end WorldBound
end ClaudeWCT.W9.T3.Security.WPair
end

section



namespace ClaudeWCT.W9.T3.Security.WPair
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload
  ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinate GameWith.idealGame
theorem counted_le_interactionT (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (B : α × QueryLog Requests → Nat → Prop)
    (hB : ∀ v c c', c' ≤ c → B v c → B v c') :
    Pr[fun x => B x.1 x.2 | simulateQ (SigGolfCandidate.T3.Security.Wots.Ref.fixedWorld T)
        (SphincsSecurity.QueryCap.counted Derivation.charged
        (FullGame.loggedWith (FullGame.authenticatedSign published) program))] ≤
      Pr[fun r => B (r.1, r.2.1) r.2.2.length | interactionT T published program] := by
  induction program using OracleComp.inductionOn generalizing B with
  | pure value =>
      rw [FullGame.loggedWith_pure, SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, interactionT_pure,
        probEvent_pure, probEvent_pure]
      exact le_rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world]
        change Pr[fun x => B x.1 x.2 | simulateQ (SigGolfCandidate.T3.Security.Wots.Ref.fixedWorld T)
          (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)))] ≤ _
        rw [SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        rcases input with n | x
        · rw [interactionT_coin]
          change Pr[_ | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= _] ≤ _
          apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
          intro coin
          simp only [Derivation.charged, if_false, Nat.zero_add, Prod.mk.eta, bind_pure]
          exact ih coin B hB
        · rw [interactionT_public]
          change Pr[_ | pure (T (.inl (.inr x))) >>= _] ≤ _
          rw [pure_bind]
          simp only [Derivation.charged, if_true]
          rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
          calc _ = Pr[fun r => B r.1 (1 + r.2) | simulateQ (SigGolfCandidate.T3.Security.Wots.Ref.fixedWorld T)
                (SphincsSecurity.QueryCap.counted Derivation.charged
                  (FullGame.loggedWith (FullGame.authenticatedSign published) (next (T (.inl (.inr x))))))] := rfl
            _ ≤ Pr[fun r => B (r.1, r.2.1) (1 + r.2.2.length) |
                interactionT T published (next (T (.inl (.inr x))))] :=
              ih (T (.inl (.inr x))) (fun v c => B v (1 + c)) (fun v c c' h hb => hB v _ _ (by omega) hb)
            _ ≤ _ := by
              apply probEvent_mono
              intro r _ hr
              simp only [Function.comp_apply, List.length_cons]
              rw [Nat.add_comm]
              exact hr
      · rw [FullGame.loggedWith_request, SphincsSecurity.QueryCap.counted_bind]
        rw [simulateQ_bind, SigGolfCandidate.T3.Security.Wots.Ref.fixedWorld_counted_hashOnly T _
          (Wots.Ref.authenticatedSign_hashOnly published request), pure_bind]
        rw [SphincsSecurity.QueryCap.counted_map, simulateQ_bind, simulateQ_map, interactionT_request]
        simp only [simulateQ_pure, bind_map_left]
        rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
        refine le_trans (ih _ (fun v c => B (v.1, ⟨request, evalWithAnswerFn T
          (FullGame.authenticatedSign published request)⟩ :: v.2)
          ((SourceReplay.queried T (FullGame.authenticatedSign published request)).length + c))
          (fun v c c' h hb => hB _ _ _ (by omega) hb)) ?_
        apply probEvent_mono
        intro r _ hr
        simp only [Function.comp_apply] at hr ⊢
        exact hB _ _ _ (by omega) hr
section PerTable
variable (adversary : AdversaryP) (q : Nat) (T : Answers)
  (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
noncomputable abbrev verdictOn (value : Option ForgeryP × QueryLog Requests) : M Bool :=
  GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 value
include hshort in
theorem fixed_step (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (Wots.Ref.fixedInteraction adversary T))
    (hev : Wots.Ref.chargeSum (Wots.Ref.combine T interaction).events ≤ q ∧
      ∀ g i c, CaseC.GameSplit adversary (Wots.Ref.combine T interaction) g i c →
        P (Wots.Ref.cut (Wots.Ref.combine T interaction).state T) i.value.2
          (SigGolfCandidate.T3.Security.BPair.publicEntries c.events)) :
    Wots.Ref.chargeSum interaction.events + (SourceReplay.queried T (verdictOn T interaction.value)).length ≤ q ∧
      P T interaction.value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value))) := by
  have hg0val : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  have hg0 : Wots.Ref.pureRecord T keygen (∅, ∅) ∈ support (Wots.Ref.fixedRecord T keygen (∅, ∅)) := by
    rw [Wots.Ref.fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := Wots.Ref.fixedRecord_mem_record T keygen (∅, ∅) (Wots.Ref.agrees_empty T) _ hg0
  have hi' := hi
  unfold Wots.Ref.fixedInteraction at hi'
  rw [← hg0val] at hi'
  obtain ⟨hirec, hagi⟩ := Wots.Ref.fixedRecord_mem_record T _ _ hag0 interaction hi'
  have hci : Wots.Ref.verdictRecord T interaction ∈ support (Wots.Ref.fixedRecord T
      (GameWith.verdict PaddedGame.checker (Wots.Ref.pureRecord T keygen (∅, ∅)).value.1 interaction.value)
      interaction.state) := by
    rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := Wots.Ref.fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : CaseC.GameSplit adversary (Wots.Ref.combine T interaction) (Wots.Ref.pureRecord T keygen (∅, ∅))
      interaction (Wots.Ref.verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hcharge, hP⟩ := hev
  have hPv := hP _ interaction _ hsplit
  have hentries : SigGolfCandidate.T3.Security.BPair.publicEntries (Wots.Ref.verdictRecord T interaction).events =
      Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value)) :=
    SigGolfCandidate.T3.Security.BPair.publicEntries_pureRecord T _ interaction.state
  rw [hentries] at hPv
  refine ⟨?_, hshort _ _ _ _ (Wots.Ref.cut_shortAgree _ _) hPv⟩
  have hv : Wots.Ref.chargeSum (Wots.Ref.verdictRecord T interaction).events =
      (SourceReplay.queried T (verdictOn T interaction.value)).length :=
    Wots.Ref.pureRecord_charge T _ (Wots.Ref.verdict_hashOnly _ _) interaction.state
  have hc : Wots.Ref.chargeSum (Wots.Ref.combine T interaction).events =
      Wots.Ref.chargeSum (Wots.Ref.pureRecord T keygen (∅, ∅)).events +
        (Wots.Ref.chargeSum interaction.events + Wots.Ref.chargeSum (Wots.Ref.verdictRecord T interaction).events) := by
    simp only [Wots.Ref.combine, Wots.Ref.chargeSum_append]
  omega
include hshort hmono in
theorem fixed_le_pairRun :
    Pr[fun result => Wots.Ref.chargeSum result.events ≤ q ∧
        ∀ g i c, CaseC.GameSplit adversary result g i c →
          P (Wots.Ref.cut result.state T) i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events) |
      Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => run.2.2.length ≤ q ∧ P T run.2.1 run.2.2 | pairRun T adversary] := by
  rw [Wots.Ref.fixed_game_eq, probEvent_map]
  let B : Option ForgeryP × QueryLog Requests → Nat → Prop := fun value charge =>
    charge + (SourceReplay.queried T (verdictOn T value)).length ≤ q ∧
      P T value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T value)))
  have hB : ∀ v c c', c' ≤ c → B v c → B v c' := fun v c c' h hb => ⟨by have := hb.1; omega, hb.2⟩
  refine le_trans (probEvent_mono fun interaction hi hev =>
    (show B interaction.value (Wots.Ref.chargeSum interaction.events) from
      fixed_step adversary q T P hshort interaction hi hev)) ?_
  have hcount := Wots.Ref.fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (Wots.Ref.pureRecord T keygen (∅, ∅)).state
  calc _ = Pr[fun x => B x.1 x.2 | (fun result : FirstHit.Recorded (Option ForgeryP × QueryLog Requests) =>
          (result.value, Wots.Ref.chargeSum result.events)) <$> Wots.Ref.fixedInteraction adversary T] := by
        rw [probEvent_map]; rfl
    _ = Pr[fun x => B x.1 x.2 | simulateQ (SigGolfCandidate.T3.Security.Wots.Ref.fixedWorld T)
          (SphincsSecurity.QueryCap.counted
          Derivation.charged (FullGame.loggedWith (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
            (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] := by
        unfold Wots.Ref.fixedInteraction
        rw [hcount]
    _ ≤ Pr[fun r => B (r.1, r.2.1) r.2.2.length | interactionT T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)] :=
        counted_le_interactionT T _ _ B hB
    _ ≤ _ := by
        unfold pairRun
        rw [bind_pure_comp, probEvent_map]
        apply probEvent_mono
        intro r _ hr
        obtain ⟨hlen, hP⟩ := hr
        refine ⟨?_, hmono _ _ _ _ (fun e he => List.mem_append_right _ he) hP⟩
        simp only [List.length_append]
        have := SigGolfCandidate.T3.Security.BPair.entriesOf_length_le T
          (SourceReplay.queried T (verdictOn T (r.1, r.2.1)))
        simp only [verdictOn] at this hlen ⊢
        omega
end PerTable
section Law
noncomputable local instance instFintypeCoordinate_g6PairEager : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_g6PairEager : SampleableType FullGame.FullTable :=
  Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
theorem shared_le_recorded (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (E : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ E (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => Wots.Ref.chargeSum pair.1.events ≤ q ∧ E pair.1 pair.2 | Wots.Ref.recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => Wots.Ref.chargeSum (QueryRecorded.recordedTrace z.1).events ≤ q ∧
        E (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] := by
        apply SigGolfCandidate.T3.Security.BPair.pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, he⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨?_, he⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => Wots.Ref.chargeSum pair.1.events ≤ q ∧ E pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [Wots.Ref.completed_map, MonitoredPrivate.event_lift]
noncomputable def pairExperiment (adversary : AdversaryP) : ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
          (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable, run.2.1, run.2.2)) <$>
        pairRun (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable) adversary
theorem shared_le_pair (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries') :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun s => s.2.2.length ≤ q ∧ P s.1 s.2.1 s.2.2 | pairExperiment adversary] := by
  refine (shared_le_recorded adversary q hq (fun rec A => ∀ g i c, CaseC.GameSplit adversary rec g i c →
    P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))).trans ?_
  rw [Wots.Ref.recorded_eq_eager adversary (fun rec A => Wots.Ref.chargeSum rec.events ≤ q ∧
    ∀ g i c, CaseC.GameSplit adversary rec g i c →
      P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))]
  unfold Wots.Ref.eagerSide pairExperiment
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro privateTable
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro publicTable
  rw [probEvent_map, probEvent_map, Wots.Ref.fillAnswers_empty]
  exact fixed_le_pairRun adversary q (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable)
    P hshort hmono
end Law
end ClaudeWCT.W9.T3.Security.WPair
end

section



namespace ClaudeWCT.W9.T3.Security.WPair
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem uniform_secretsLaw (I : SampleableType (Guess.GCoord → Digest)) (g : Guess.GCoord → Digest) :
    Pr[= g | (@uniformSample (Guess.GCoord → Digest) I : ProbComp _)] = Pr[= g | secretsLaw] := by
  rw [@probOutput_uniformSample _ I _ g, secretsLaw, SPMF.probOutput_eq_apply,
    SphincsSecurity.Concrete.UniformTableCompletion.complete_apply]
  have hmem : ∀ coordinate, g coordinate ∈ init.allowed coordinate := fun _ => Finset.mem_univ _
  rw [if_pos hmem]
  have hcard : (∏ coordinate, (init.allowed coordinate).card) = Fintype.card (Guess.GCoord → Digest) := by
    change (∏ _coordinate : Guess.GCoord, (Finset.univ : Finset Digest).card) = _
    rw [Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fun]
  rw [hcard]
theorem canon_subset (adversary : AdversaryP) : canonInputs ⊆ Wots.referenceInputs adversary :=
  canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
theorem eagerAnswers_eq (U : Finset HashInput) (privateTable : FullGame.FullTable) (publicTable : U → HashOutput) :
    Wots.eagerAnswers U privateTable publicTable = CanonGraph.eagerAnswers privateTable U publicTable := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem inner_fts_eq {U : Finset HashInput} (hU : canonInputs ⊆ U) (ω : CanonTable.Omega U) (adversary : AdversaryP)
    (I : SampleableType (Guess.GCoord → Digest))
    (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | (@uniformSample (Guess.GCoord → Digest) I : ProbComp _) >>= fun g =>
        (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (wA hU ω g, run.2.1, run.2.2)) <$>
          pairRun (wA hU ω g) adversary] =
      Pr[fun x => E (wA hU ω x.1, x.2.2.1, x.2.2.2) | ftsRun hU ω adversary] := by
  unfold ftsRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro g
  rw [uniform_secretsLaw, probEvent_map, probEvent_map]
  rfl
section Chain
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
theorem pairExperiment_eq (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)
        let g ← ($ᵗ (WctPoint → Digest) : ProbComp _)
        (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
            (wA (canon_subset adversary) ⟨secrets, other, low, high, residual⟩ g, run.2.1, run.2.2)) <$>
          pairRun (wA (canon_subset adversary) ⟨secrets, other, low, high, residual⟩ g) adversary] := by
  let K : Answers → ProbComp (Answers × QueryLog Requests × List Wots.Entry) := fun T =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (T, run.2.1, run.2.2)) <$> pairRun T adversary
  have h1 : 𝒮[pairExperiment adversary] =
      𝒮[do
        let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
        let publicTable ← ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)
        K (CanonGraph.eagerAnswers privateTable (Wots.referenceInputs adversary) publicTable)] := by
    unfold pairExperiment
    rw [SigGolfCandidate.T3.Security.BPair.bind_uniform_congr _ instSampleableTypeFullTable_canonGraph]
    apply evalSPMF_bind_congr_left
    intro privateTable
    rw [SigGolfCandidate.T3.Security.BPair.bind_uniform_congr _
      (instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _)]
    apply evalSPMF_bind_congr_left
    intro publicTable
    simp only [K, eagerAnswers_eq]
  rw [h1, CanonTable.world_tables_bind (canon_subset adversary) K]
theorem pairExperiment_event_le (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop)
    (bound : ENNReal)
    (h : ∀ ω : CanonTable.Omega (Wots.referenceInputs adversary),
      Pr[fun x => E (wA (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] ≤ bound) :
    Pr[E | pairExperiment adversary] ≤ bound := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_eq adversary)]
  apply probEvent_bind_le_of_forall_le
  intro secrets _
  apply probEvent_bind_le_of_forall_le
  intro other _
  apply probEvent_bind_le_of_forall_le
  intro low _
  apply probEvent_bind_le_of_forall_le
  intro high _
  apply probEvent_bind_le_of_forall_le
  intro residual _
  rw [inner_fts_eq]
  exact h ⟨secrets, other, low, high, residual⟩
theorem pairExperiment_pair (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => s.2.2.length ≤ q ∧ PairGuessIn s.1 s.2.1 s.2.2 | pairExperiment adversary] ≤ pairTerm q :=
  pairExperiment_event_le adversary _ _ fun ω => fts_pair_le (canon_subset adversary) ω adversary q
theorem pairExperiment_one (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => s.2.2.length ≤ q ∧ OneGuessIn s.1 s.2.1 s.2.2 | pairExperiment adversary] ≤ guessTerm q :=
  pairExperiment_event_le adversary _ _ fun ω => fts_one_le (canon_subset adversary) ω adversary q
end Chain
section Short
open SourceQueries
theorem digest_short (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) Wots.Ref.ShortQuery := by
  unfold digest publicHash
  refine (allQueriesSatisfy_query_iff _ _).mpr ?_
  apply Wots.Ref.short_of_le
  simp [digestInput, SphincsSecurity.bytesLE_length]
theorem wctDigestSearch_short (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) Wots.Ref.ShortQuery := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold WCT9.digestSearch
      apply bind_allowed Wots.Ref.ShortQuery (digest_short _ _ _)
      intro output
      split
      · exact pure_allowed _ _
      · exact ih _
theorem signedOutput_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (message : Message)
    (signature : Signature) : CaseC.signedOutput A message signature = CaseC.signedOutput T message signature := by
  unfold CaseC.signedOutput
  rw [eval_congr_allowed (wctDigestSearch_short _ _ _ _) h]
theorem loggedOutputs_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (log : QueryLog Requests) :
    loggedOutputs A log = loggedOutputs T log := by
  unfold loggedOutputs
  congr 1
  funext entry
  congr 1
  funext signature
  exact signedOutput_short h _ _
theorem disclosed_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (log : QueryLog Requests) (a : Guess.ChainAddr)
    (p : Nat) (hd : Disclosed A log a p) : Disclosed T log a p := by
  unfold Disclosed at hd ⊢
  rw [← loggedOutputs_short h]
  exact hd
theorem chainStep_short (index coord selected i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (WCT9.chainInput index coord selected i step value)) Wots.Ref.ShortQuery := by
  unfold shortHash publicHash
  refine bind_allowed _ ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun _ => pure_allowed _ _
  apply Wots.Ref.short_of_le
  simp [WCT9.chainInput, zero16, SphincsSecurity.bytesLE_length]
theorem chainValue_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (a : Guess.ChainAddr) (p : Nat) :
    Guess.chainValue A a p = Guess.chainValue T a p := by
  have hseed : Guess.seedOf A a = Guess.seedOf T a := by
    unfold Guess.seedOf
    have hp : evalWithAnswerFn A (privatePair 8 a.2.1.val a.1.val 0 (4 * a.2.2.1.val + a.2.2.2.val / 2)) =
        evalWithAnswerFn T (privatePair 8 a.2.1.val a.1.val 0 (4 * a.2.2.1.val + a.2.2.2.val / 2)) := by
      apply eval_congr_allowed _ h
      unfold privatePair privateHash
      exact bind_allowed _ ((allQueriesSatisfy_query_iff _ _).mpr trivial) fun _ => pure_allowed _ _
    simp only [hp]
  unfold Guess.chainValue
  rw [hseed]
  apply eval_congr_allowed _ h
  unfold WCT9.chain
  exact foldlM_allowed _ _ _ (fun v step => chainStep_short _ _ _ _ _ v) _
theorem guessedIn_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (log : QueryLog Requests)
    (entries : List Wots.Entry) (c : Guess.GCoord) (hg : GuessedIn A log entries c) : GuessedIn T log entries c := by
  obtain ⟨hnd, answer, he⟩ := hg
  refine ⟨fun hd => hnd (disclosed_short h.symm log _ _ hd), answer, ?_⟩
  unfold Guess.honestProbe at he ⊢
  rw [← chainValue_short h]
  exact he
theorem guessedIn_mono (A : Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (c : Guess.GCoord) (hg : GuessedIn A log entries c) :
    GuessedIn A log entries' c :=
  ⟨hg.1, hg.2.elim fun answer he => ⟨answer, hsub _ he⟩⟩
end Short
theorem pair_guess_bound : PairGuessBound pairTerm := by
  intro adversary q hq
  refine (shared_le_pair adversary q hq PairGuessIn ?_ ?_).trans (pairExperiment_pair adversary q)
  · rintro A T log entries h ⟨c, c', hcc, hc, hc'⟩
    exact ⟨c, c', hcc, guessedIn_short h log entries c hc, guessedIn_short h log entries c' hc'⟩
  · rintro A log entries entries' hsub ⟨c, c', hcc, hc, hc'⟩
    exact ⟨c, c', hcc, guessedIn_mono A log entries entries' hsub c hc,
      guessedIn_mono A log entries entries' hsub c' hc'⟩
end ClaudeWCT.W9.T3.Security.WPair
end
