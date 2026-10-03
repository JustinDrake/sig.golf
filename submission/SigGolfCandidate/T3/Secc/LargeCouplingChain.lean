import SigGolfCandidate.T3.Secc.LargeCouplingLaw

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Chain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure ⟨high, rows, priv⟩
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem complete_univ_apply (labels : WCoord → LargeResidual.Digest) :
    SphincsSecurity.Concrete.UniformTableCompletion.complete (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest)) labels =
      Pr[= labels | ($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] := by
  rw [SphincsSecurity.Concrete.UniformTableCompletion.complete_apply, if_pos (fun _ => Finset.mem_univ _),
    probOutput_uniformSample, Fintype.card_fun, Finset.prod_const, Finset.card_univ, Finset.card_univ]
theorem complete_univ :
    SphincsSecurity.Concrete.UniformTableCompletion.complete (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest)) =
      𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] := by
  apply SPMF.ext
  intro labels
  rw [complete_univ_apply]
  rfl
theorem completeRows_none_apply (U : Finset HashInput) (table : Cell U → LargeResidual.HashOutput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) table =
      Pr[= table | ($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  unfold SphincsSecurity.Concrete.ResidualTableCompletion.completeRows
  rw [SphincsSecurity.Concrete.UniformTableCompletion.complete_apply, if_pos (fun _ => by
      simp [SphincsSecurity.Concrete.ResidualTableCompletion.allowed]),
    probOutput_uniformSample, Fintype.card_fun]
  simp only [SphincsSecurity.Concrete.ResidualTableCompletion.allowed, Finset.prod_const, Finset.card_univ]
theorem completeRows_none (U : Finset HashInput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) =
      𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  apply SPMF.ext
  intro table
  rw [completeRows_none_apply]
  rfl
section Lazy
variable {U : Finset HashInput}
theorem lazy_aux {β : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (i : AuxQuery) (k : AuxSpec.Range i → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (liftM ((RWorld U).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem finish_stop {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U)))
    (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | X >>= finish] = Pr[fun r => r.1 = none ∧ P r.2 | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      simp only [finish, probEvent_pure, true_and]
      split_ifs <;> simp
  | some v =>
      simp only [reduceCtorEq, false_and, if_false, mul_eq_zero]
      right
      unfold finish
      simp only [probEvent_bind_eq_tsum, probEvent_pure, reduceCtorEq, false_and, if_false, mul_zero, tsum_zero]
theorem probEvent_bind_congr_eq {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] = Pr[E' | g x]) : Pr[E | m >>= f] = Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]
theorem observed_avg {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | 𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun labels =>
        𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q labels τ program LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ P r.2 | lazyRun aux q program LargeResidual.initial] := by
  rw [← complete_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (fun _ => Finset.univ_nonempty)
  rw [← finish_stop (lazyRun aux q program LargeResidual.initial) P, ← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  simp only [Function.comp_apply, retain, Option.map_eq_none_iff]
theorem initLaw_spmf : (liftM initLaw : SPMF AuxData) = 𝒮[initComp] := by
  apply SPMF.ext
  intro a
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput, initLaw,
    MonitoredPrivate.event_lift, probEvent_eq_eq_probOutput]
  rfl
theorem router_side (adversary : AdversaryP) (q : Nat) :
    Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun lab =>
        𝒮[($ᵗ (Cell (Wots.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q lab τ (routerWith (Wots.referenceInputs adversary) adversary q ⟨high, rows, priv⟩)
          LargeResidual.initial] := by
  unfold router initReq
  rw [lazy_aux]
  change Pr[_ | (liftM initLaw : SPMF AuxData) >>= _] = _
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_congr_eq
  intro high
  apply probEvent_bind_congr_eq
  intro rows
  apply probEvent_bind_congr_eq
  intro priv
  exact (observed_avg (auxLaw initLaw) q _ (fun st => st.counters.calls ≤ q)).symm
end Lazy
end Chain
end SigGolfCandidate.T3.Security.LargeCoupling
