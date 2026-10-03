import SigGolfCandidate.T3.Secc.WotsTransportTable

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
noncomputable def completionComp : ProbComp SeccLaw.CompletionTables :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun publicTable => pure (privateTable, publicTable)
theorem completionComp_eq :
    (liftM completionComp : PMF SeccLaw.CompletionTables) = PMF.uniformOfFintype SeccLaw.CompletionTables := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.uniformOfFintype_apply, ← PMF.probOutput_eq_apply]
  have hl : Pr[= (a, b) | (liftM completionComp : PMF SeccLaw.CompletionTables)] = Pr[= (a, b) | completionComp] := by
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, MonitoredPrivate.event_lift]
  rw [hl]
  unfold completionComp
  change Pr[=(a, b) | (($ᵗ FullGame.FullTable : ProbComp _) >>= fun x =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun y => pure (id x, id y))] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map, probOutput_uniformSample]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)), ← Nat.cast_mul]
  congr 2
  rw [← Fintype.card_prod]
theorem pmf_probEvent_mono {α : Type} (p : PMF α) {E F : α → Prop} (h : ∀ x ∈ p.support, E x → F x) :
    Pr[E | p] ≤ Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hE : E x
    · rw [if_pos hE, if_pos (h x hx hE)]
    · rw [if_neg hE]
      exact zero_le
  · have hz' : p x = 0 := (PMF.apply_eq_zero_iff p x).mpr hx
    have hz : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact hz'
    split_ifs <;> simp [hz, hz']
noncomputable def recordedCompleted (adversary : AdversaryP) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
    completionComp >>= fun tables => pure (result, SeccLaw.completeWith result.state tables)
theorem completed_map (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq =
      (liftM (recordedCompleted adversary) : PMF _) := by
  unfold SeccLaw.completedExperiment recordedCompleted
  rw [PMF.monad_map_eq_map, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have he := PaddedGame.traced_record_erasure adversary q hq
  rw [PMF.monad_map_eq_map] at he
  rw [show (PaddedGame.tracedExperiment adversary q hq).bind (fun result =>
      (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
        (QueryRecorded.recordedTrace result, SeccLaw.completeWith result.2.2.base.source.2 tables)) =
      ((PaddedGame.tracedExperiment adversary q hq).map QueryRecorded.recordedTrace).bind (fun result =>
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
          (result, SeccLaw.completeWith result.state tables)) from by rw [PMF.bind_map]; rfl]
  rw [he, ← completionComp_eq, liftM_bind]
  congr 1
  funext result
  rw [← PMF.monad_map_eq_map, ← liftM_map, map_eq_bind_pure_comp]
  rfl
theorem caseAB_le_recorded (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseAB adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => Good adversary q pair.1 pair.2 | recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => Good adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] := by
        apply pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => Good adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [completed_map, MonitoredPrivate.event_lift]
theorem restrict_uniform {β : Type} (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V)
    (k : SeccLaw.PublicTable → ProbComp β) :
    𝒮[($ᵗ (V → HashOutput) : ProbComp _) >>= fun table =>
        k (table ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub)] =
      𝒮[($ᵗ SeccLaw.PublicTable : ProbComp _) >>= k] := by
  rw [FiniteRowSplit.public_table_bind SeccLaw.publicUniverse V hsub]
  apply evalSPMF_bind_congr'
  intro chainTable
  have hc : ∀ extra, (FiniteRowSplit.publicTableEquiv SeccLaw.publicUniverse V hsub).symm (chainTable, extra) ∘
      FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub = chainTable := by
    intro extra
    funext query
    rw [Function.comp_apply]
    exact FiniteRowSplit.publicTableEquiv_reconstruct SeccLaw.publicUniverse V hsub chainTable extra query
  simp only [hc]
  exact evalSPMF_bind_const_neverFails _ (by simp) _
theorem completeWith_eq_cut (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : V → HashOutput) :
    SeccLaw.completeWith state (privateTable, publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) =
      cut state (fillAnswers V state privateTable publicTable) := by
  funext query
  rcases query with (n | x) | c
  · rfl
  · change (state.2 x).getD (SeccLaw.publicFill (publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) x) =
      (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then
        (state.2 x).getD (SphincsSecurity.Concrete.finiteHashAnswer ∅ V publicTable x) else (0 : HashOutput))
    cases hx : state.2 x with
    | some v =>
        rw [if_pos (show x ∈ SeccLaw.publicUniverse ∨ (some v).isSome = true from Or.inr rfl),
          Option.getD_some, Option.getD_some]
    | none =>
        rw [Option.getD_none, Option.getD_none]
        unfold SeccLaw.publicFill
        by_cases hu : x ∈ SeccLaw.publicUniverse
        · rw [dif_pos hu, if_pos (Or.inl hu), SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x (hsub hu) rfl,
            Function.comp_apply]
          rfl
        · rw [dif_neg hu, if_neg (fun h => h.elim hu (fun h' => by simp at h'))]
  · rfl
theorem referenceInputs_universe (adversary : AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem referenceInputs_inputsIn (adversary : AdversaryP) :
    InputsIn (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) :=
  fun privateTable _ => (ChainGraph.program_subset_recordedInputs _ privateTable).trans Finset.subset_union_right
theorem recorded_eq_eager (adversary : AdversaryP) (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun pair => event pair.1 pair.2 | recordedCompleted adversary] =
      Pr[fun pair => event pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] := by
  have hlaw : 𝒮[recordedCompleted adversary] =
      𝒮[(fun pair : FirstHit.Recorded Bool × Answers => (pair.1, cut pair.1.state pair.2)) <$>
        (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
          ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
            ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
              pure (result, fillAnswers (referenceInputs adversary) result.state privateTable publicTable))] := by
    unfold recordedCompleted completionComp
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    apply evalSPMF_bind_congr'
    intro result
    apply evalSPMF_bind_congr'
    intro privateTable
    rw [← restrict_uniform (referenceInputs adversary) (referenceInputs_universe adversary)]
    apply evalSPMF_bind_congr'
    intro publicTable
    rw [completeWith_eq_cut]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
  have hc := record_completion (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)
    (referenceInputs_inputsIn adversary)
  exact probEvent_congr' (fun _ _ => Iff.rfl) hc
theorem eager_le_reference (adversary : AdversaryP) (q : Nat) :
    Pr[fun pair => Good adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => WotsPrimitive sample.answers sample.trace | referenceComp adversary q] := by
  unfold eagerSide referenceComp
  apply probEvent_bind_mono
  intro privateTable
  apply probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_game_le adversary q _
end Ref
theorem caseAB_le_reference (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseAB adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => WotsPrimitive sample.answers sample.trace | referenceExperiment adversary q] := by
  refine (Ref.caseAB_le_recorded adversary q hq).trans ?_
  rw [Ref.recorded_eq_eager adversary (Ref.Good adversary q)]
  refine (Ref.eager_le_reference adversary q).trans (le_of_eq ?_)
  unfold referenceExperiment
  rw [MonitoredPrivate.event_lift]
noncomputable def eagerRecorded (adversary : AdversaryP) : PMF (FirstHit.Recorded Bool × Answers) :=
  liftM (($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun result => (result, eagerAnswers (referenceInputs adversary) privateTable publicTable)) <$>
        Ref.fixedRecord (eagerAnswers (referenceInputs adversary) privateTable publicTable)
          (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅))
theorem completed_eager_cut (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun z => event (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] =
      Pr[fun x => event x.1 (Ref.cut x.1.state x.2) | eagerRecorded adversary] := by
  calc _ = Pr[fun pair => event pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun pair => event pair.1 pair.2 | Ref.recordedCompleted adversary] := by
        rw [Ref.completed_map, MonitoredPrivate.event_lift]
    _ = _ := by
        rw [Ref.recorded_eq_eager adversary event]
        unfold eagerRecorded Ref.eagerSide
        rw [MonitoredPrivate.event_lift]
        simp only [Ref.fillAnswers_empty]
theorem completed_eager_event (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : FirstHit.Recorded Bool → Answers → Prop)
    (hshort : ∀ rec A T, Ref.ShortAgree A T → event rec A → event rec T) :
    Pr[fun z => event (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun x => event x.1 x.2 | eagerRecorded adversary] := by
  rw [completed_eager_cut]
  exact Ref.pmf_probEvent_mono _ fun x _ h => hshort x.1 _ x.2 (Ref.cut_shortAgree _ _) h
theorem completed_eager_event_cut (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : FirstHit.Recorded Bool → Answers → Prop)
    (hcut : ∀ rec T, event rec (Ref.cut rec.state T) → event rec T) :
    Pr[fun z => event (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun x => event x.1 x.2 | eagerRecorded adversary] := by
  rw [completed_eager_cut]
  exact Ref.pmf_probEvent_mono _ fun x _ h => hcut x.1 x.2 h
end SigGolfCandidate.T3.Security.Wots
