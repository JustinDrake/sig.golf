import SigGolfCandidate.T3.Secc.LargeCouplingTable

/-!
# LR-34 (law, 1/3): mixing two uniform tables along a self-determined prefix is uniform

`mix P f g` takes `f` on its prefix `P f` and `g` elsewhere. If the prefix of a table is determined by the table's
values on it (`PrefixDetermined P`: tables agreeing with `f` on `P f` have the same prefix), the swap
`(f, g) ↦ (mix P f g, mix P g f ∘ …)` is an involution, hence

* `uniform_mix`: `𝒮[f ← $ᵗ; g ← $ᵗ; next (mix P f g)] = 𝒮[h ← $ᵗ; next h]`.

Used for the honest-message encoding rows: their first-success prefix is presampled (`AuxData.rows`), the rest is
the residual table.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Swap
variable {ι A : Type} [Fintype ι] [Fintype A] [Nonempty A]

/-- `f` on its prefix, `g` elsewhere. -/
noncomputable def mix (P : (ι → A) → ι → Prop) (f g : ι → A) : ι → A := fun i => if P f i then f i else g i

/-- The prefix of a table is determined by its values on the prefix. -/
def PrefixDetermined (P : (ι → A) → ι → Prop) : Prop :=
  ∀ f g : ι → A, (∀ i, P f i → f i = g i) → ∀ i, P g i ↔ P f i

/-- The swap of two tables along the first one's prefix. -/
noncomputable def swapPair (P : (ι → A) → ι → Prop) (p : (ι → A) × (ι → A)) : (ι → A) × (ι → A) :=
  (mix P p.1 p.2, fun i => if P p.1 i then p.2 i else p.1 i)

theorem prefix_mix (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P) (f g : ι → A) (i : ι) :
    P (mix P f g) i ↔ P f i :=
  hP f (mix P f g) (fun j hj => by unfold mix; rw [if_pos hj]) i

theorem swapPair_involutive (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P) :
    Function.Involutive (swapPair P) := by
  intro p
  rcases p with ⟨f, g⟩
  have hpre : ∀ i, P (mix P f g) i ↔ P f i := prefix_mix P hP f g
  simp only [swapPair]
  ext i
  · simp only [mix]
    by_cases h : P f i
    · rw [if_pos ((hpre i).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hpre i).mp h')), if_neg h]
  · simp only [mix]
    by_cases h : P f i
    · rw [if_pos ((hpre i).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hpre i).mp h')), if_neg h]

/-- **Mixing along a self-determined prefix is uniform.** -/
theorem uniform_mix [SampleableType (ι → A)] {Result : Type} (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P)
    (next : (ι → A) → ProbComp Result) :
    𝒮[do let f ← ($ᵗ (ι → A) : ProbComp _); let g ← ($ᵗ (ι → A) : ProbComp _); next (mix P f g)] =
      𝒮[do let h ← ($ᵗ (ι → A) : ProbComp _); next h] := by
  let _ : SampleableType ((ι → A) × (ι → A)) := SampleableType.ofFintype _
  have hprod := FullGame.uniform_product (A := ι → A) (B := ι → A)
  have h1 : 𝒮[do let f ← ($ᵗ (ι → A) : ProbComp _); let g ← ($ᵗ (ι → A) : ProbComp _); next (mix P f g)] =
      𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next (swapPair P p).1] := by
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next (swapPair P p).1]) hprod
    simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind, swapPair] using h
  have h2 : 𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next (swapPair P p).1] =
      𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next p.1] := by
    have hb := evalSPMF_map_bijective_uniform_cross (α := (ι → A) × (ι → A)) (β := (ι → A) × (ι → A))
      (swapPair P) (swapPair_involutive P hP).bijective
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next p.1]) hb
    simpa only [evalSPMF_bind, evalSPMF_map, bind_map_left] using h
  have h3 : 𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next p.1] =
      𝒮[do let h ← ($ᵗ (ι → A) : ProbComp _); next h] := by
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next p.1]) hprod.symm
    simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] at h
    rw [evalSPMF_bind, h, evalSPMF_bind]
    congr 1
    funext f
    rw [evalSPMF_uniformSample]
    exact SphincsSecurity.Concrete.RetainedObservation.lift_bind_const _ _
  rw [h1, h2, h3]

end Swap

end SigGolfCandidate.T3.Security.LargeCoupling
