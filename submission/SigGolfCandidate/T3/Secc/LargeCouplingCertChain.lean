import SigGolfCandidate.T3.Secc.LargeCouplingCertTable
import SigGolfCandidate.T3.Secc.LargeCouplingCertShort
import SigGolfCandidate.T3.Secc.LargeContactCertClean
import SigGolfCandidate.T3.Secc.LargeCouplingContact

/-!
# LR-34 (certificate coupling, chain): contact-free clean wins are lazy-router certificates

**`cert_le_lazy`**: `Pr[CleanWin q ∧ ¬Contact | completedExperiment] ≤ Pr[CertOut | lazy router]`.

Route: `cert_of_clean` (deterministic link to the real certificate event `CertR`), F2's `completed_eager_cut` with
`certR_short` (the shared law in the eager fixed world), the law of the eager tables in the router's coordinates
(`law_target`, `world_split`), the per-table coupling `table_cert_le` (with `coherent_psi`), and the average of the
eager observed router (`run_posterior`): a finished eager run is a finished lazy run (`observed_avg_le`).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

section CertChain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers

theorem pmf_probEvent_mono_support' {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]

/-- The real certificate event of the eager fixed-world record paired with its table. -/
def RealCert (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  CertR adversary q x.1 x.2

/-- **The certificate side, real part.** -/
theorem cert_real_side (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] =
      Pr[RealCert adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.completed_eager_cut adversary q hq (CertR adversary q)
  rw [h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => CertR adversary q x.1 (Wots.Ref.cut x.1.state x.2)) =
      RealCert adversary q := by
    funext x
    exact propext (certR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
  rw [h2]
  unfold Wots.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1

section Lazy
variable {U : Finset HashInput}

theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x

/-- Finishing a lazy run keeps its finished-value events, with mass at most one. -/
theorem finish_some_le {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U))) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | X >>= finish] ≤ Pr[fun r => ∃ v, r.1 = some v ∧ P v | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish ((none : Option R), st)] = 0 := by
        simp only [finish, probEvent_pure]
        rw [if_neg]
        rintro ⟨v, hv, -⟩
        cases hv
      rw [h0, mul_zero]
      exact zero_le
  | some v =>
      by_cases hP : P v
      · rw [if_pos ⟨v, rfl, hP⟩]
        exact mul_le_of_le_one_right zero_le probEvent_le_one
      · have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish (some v, st)] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro x hx hE
          unfold finish at hx
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hx
          obtain ⟨labels, -, table, -, rfl⟩ := hx
          obtain ⟨v', hv', hP'⟩ := hE
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact hP hP'
        rw [h0, mul_zero]
        exact zero_le

/-- **Averaging the eager observed world from the initial state is dominated by the lazy world** (finished-value
events). -/
theorem observed_avg_le {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v | 𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun labels =>
        𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q labels τ program LargeResidual.initial] ≤
      Pr[fun r => ∃ v, r.1 = some v ∧ P v | lazyRun aux q program LargeResidual.initial] := by
  rw [← complete_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (fun _ => Finset.univ_nonempty)
  refine le_trans (le_of_eq ?_) (finish_some_le (lazyRun aux q program LargeResidual.initial) P)
  rw [← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  apply propext
  rcases r with ⟨_ | v, st⟩
  · simp [retain]
  · simp [retain]

theorem certOut_iff (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    CertOut r ↔ ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st := by
  constructor
  · rintro ⟨st, h1, h2⟩
    exact ⟨_, h1, st, rfl, h2⟩
  · rintro ⟨v, h1, st, rfl, h2⟩
    exact ⟨st, h1, h2⟩

/-- **The lazy router dominates the average of eager observed routers** (certificate events). -/
theorem router_side_cert (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun lab =>
        𝒮[($ᵗ (Cell (Wots.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q lab τ (routerWith (Wots.referenceInputs adversary) adversary q ⟨high, rows, priv⟩)
          LargeResidual.initial] ≤
      Pr[CertOut |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hce : (@CertOut (Wots.referenceInputs adversary)) =
      fun r => ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st :=
    funext fun r => propext (certOut_iff r)
  rw [hce]
  unfold router initReq
  rw [lazy_aux]
  change _ ≤ Pr[_ | (liftM initLaw : SPMF AuxData) >>= _]
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_mono_le
  intro high
  apply probEvent_bind_mono_le
  intro rows
  apply probEvent_bind_mono_le
  intro priv
  exact observed_avg_le (auxLaw initLaw) q _ _

end Lazy

/-- **The certificate side**: contact-free clean wins of the shared law are lazy-router certificates. -/
theorem cert_le_lazy (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[CertOut | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
        LargeResidual.initial] := by
  have hU : canonInputs ⊆ Wots.referenceInputs adversary :=
    canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  refine le_trans (pmf_probEvent_mono_support' _ fun z hz h => cert_of_clean adversary q hq z hz h.1 h.2) ?_
  rw [cert_real_side]
  refine le_trans ?_ (router_side_cert adversary q)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.referenceInputs adversary) hU hE (fixedNext adversary))]
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
    unfold fixedNext RealCert
    rw [probEvent_map]
    have h := table_cert_le adversary q hq initLaw
      (coherent_psi (Wots.referenceInputs adversary) hU hE (fun c => lab (.inl c)) (fun m => lab (.inr m)) τ
        ⟨high, rows, priv⟩)
    have hlab : Sum.elim (fun c => lab (.inl c)) (fun m => lab (.inr m)) = lab := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h

end CertChain

end SigGolfCandidate.T3.Security.LargeCoupling
