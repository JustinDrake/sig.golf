import SigGolfCandidate.T3.Secc.LargeCouplingChain

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Contact
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem probEvent_bind_le_of {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β) (g : α → SPMF γ)
    (E : β → Prop) (F : γ → Prop) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my]) (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x]) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by rw [hw x]; gcongr; exact h x
theorem uniform_weight {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) (x : α) :
    Pr[= x | (@uniformSample α s1 : ProbComp α)] = Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] := by
  rw [show Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] = Pr[= x | (@uniformSample α s2 : ProbComp α)] from rfl,
    probOutput_uniformSample, probOutput_uniformSample]
theorem evalSPMF_uniform_inst {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) :
    𝒮[(@uniformSample α s1 : ProbComp α)] = 𝒮[(@uniformSample α s2 : ProbComp α)] := by
  apply evalSPMF_ext
  intro x
  rw [probOutput_uniformSample, probOutput_uniformSample]
def RealContact (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  ContactR adversary q x.1 x.2
noncomputable def fixedNext (adversary : AdversaryP) (T : Answers) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  (fun r => (r, T)) <$> Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)
theorem contact_real_side (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[Contact adversary q | SeccLaw.completedExperiment adversary q hq] =
      Pr[RealContact adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.completed_eager_cut adversary q hq (ContactR adversary q)
  rw [show (Contact adversary q) = fun z => ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 from rfl, h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => ContactR adversary q x.1 (Wots.Ref.cut x.1.state x.2)) =
      RealContact adversary q := by
    funext x
    exact propext (contactR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
  rw [h2]
  unfold Wots.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
def worldEquiv : Secrets × ((Message → Digest) × LowLabels) ≃ (WCoord → LargeResidual.Digest) where
  toFun p := Sum.elim (Sum.elim p.2.2 p.1) p.2.1
  invFun lab := (fun s => lab (.inl (.inr s)), fun m => lab (.inr m), fun N => lab (.inl (.inl N)))
  left_inv p := rfl
  right_inv lab := by
    funext c
    rcases c with (N | s) | m <;> rfl
theorem world_split {R : Type} (K : Secrets → (Message → Digest) → LowLabels → ProbComp R) :
    𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => K sec nv low] =
      𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _) >>= fun lab =>
        K (fun s => lab (.inl (.inr s))) (fun m => lab (.inr m)) (fun N => lab (.inl (.inl N)))] := by
  let _ : SampleableType ((Message → Digest) × LowLabels) := SampleableType.ofFintype _
  let _ : SampleableType (Secrets × ((Message → Digest) × LowLabels)) := SampleableType.ofFintype _
  rw [uniform_equiv_bind worldEquiv, uniform_prod_bind]
  refine evalSPMF_bind_congr' _ fun sec => ?_
  rw [uniform_prod_bind]
  rfl
theorem weight_self {α : Type} (mx : ProbComp α) (x : α) : Pr[= x | mx] = Pr[= x | 𝒮[mx]] := rfl
theorem contact_le_lazy (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[Contact adversary q | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hU : canonInputs ⊆ Wots.referenceInputs adversary :=
    canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  rw [contact_real_side, router_side,
    probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun high => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun lab => ?_
  have hτ : ∀ (k : (Wots.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm ((fun s => lab (.inl (.inr s))),
          nonceOver (privateEquiv priv).2 (fun m => lab (.inr m)))) (Wots.referenceInputs adversary)
          (programmed (Wots.referenceInputs adversary) hU (fun s => lab (.inl (.inr s)))
            (joinLabels (fun N => lab (.inl (.inl N))) high)
            (residualPsi (Wots.referenceInputs adversary) hE (joinLabels (fun N => lab (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.referenceInputs adversary) hU hE (fun c => lab (.inl c)) (fun m => lab (.inr m)) τ
          ⟨high, rows, priv⟩ := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealContact
    rw [probEvent_map]
    have h := table_contact_le adversary q hq initLaw
      (coherent_psi (Wots.referenceInputs adversary) hU hE (fun c => lab (.inl c)) (fun m => lab (.inr m)) τ
        ⟨high, rows, priv⟩)
    have hlab : Sum.elim (fun c => lab (.inl c)) (fun m => lab (.inr m)) = lab := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end Contact
end SigGolfCandidate.T3.Security.LargeCoupling
