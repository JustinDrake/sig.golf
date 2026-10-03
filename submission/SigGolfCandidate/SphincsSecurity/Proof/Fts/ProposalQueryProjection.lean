import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ProposalWordDistribution
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestSelectionIndex
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ProposalBridgeKernel
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.BoundaryTrace

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
theorem evalDist_sampleUniformProposalWord {α : Type} [SampleableType α] [Fintype α] [Nonempty α] (steps : Nat) :
    𝒮[sampleUniformProposalWord α steps] =
      (liftM (independentProposalWord (PMF.uniformOfFintype α) steps) : SPMF (List α)) := by
  induction steps with
  | zero => simp only [sampleUniformProposalWord, independentProposalWord, evalSPMF_pure]
  | succ steps ih =>
      simp only [sampleUniformProposalWord, evalSPMF_bind, evalSPMF_pure, evalSPMF_uniformSample, ih,
        independentProposalWord, PMF.map, Function.comp_def, ← PMF.monad_bind_eq_bind, PMF.evalSPMF_eq]
      simp only [← PMF.monad_pure_eq_pure, liftM_pure]
noncomputable def targetProposalAcceptance : ENNReal := targetProposalOverhead⁻¹
theorem targetProposalAcceptance_ne_zero : targetProposalAcceptance ≠ 0 := by
  rw [targetProposalAcceptance, ENNReal.inv_ne_zero]
  unfold targetProposalOverhead
  finiteness
theorem targetProposalAcceptance_lt_one : targetProposalAcceptance < 1 := by
  rw [targetProposalAcceptance, ENNReal.inv_lt_one]
  unfold targetProposalOverhead
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem targetProposalAcceptance_cap {Ω : Type*} (record : PMF Ω) (label : Ω → Index)
    (hbound : ∀ index, (record.map label) index ≤ targetProposalIndexRate) (index : Index) :
    targetProposalAcceptance * (record.map label) index ≤ PMF.uniformOfFintype Index index := by
  rw [PMF.uniformOfFintype_apply, targetProposalAcceptance]
  calc
    _ ≤ targetProposalOverhead⁻¹ * targetProposalIndexRate := mul_le_mul' le_rfl (hbound index)
    _ = _ := by
      have hpositive : 0 < targetProposalOverhead :=
        zero_lt_one.trans (ENNReal.inv_lt_one.mp targetProposalAcceptance_lt_one)
      rw [targetProposalIndexRate, ← mul_assoc,
        ENNReal.inv_mul_cancel hpositive.ne'
          (by unfold targetProposalOverhead; finiteness), one_mul]
end SphincsSecurity.Concrete
end

section





namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
private theorem probCompLift_apply {α : Type} (comp : ProbComp α) (value : α) :
    (liftM comp : PMF α) value = Pr[= value | comp] := by
  rw [← PMF.probOutput_eq_apply]
  rfl
theorem probOutput_completeSigningIndex_eq_loop (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signWithView key message)).run cache >>=
      fun result => completeSelectedIndex result.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, bind_assoc]
  apply probOutput_bind_congr
  rintro ⟨selected, loopCache⟩ _
  cases selected with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind, selectedLoopView?, Option.map_none]
  | some selected =>
      obtain ⟨randomness, selectedIndex, leaves⟩ := selected
      simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure, StateT.run_pure,
        pure_bind, selectedLoopView?, Option.map_some]
      simp
abbrev TracedSigningRecord (ω : Type) :=
  ((Option Signature × Option FewTimeView) × ω) × QueryCache HashSpec
noncomputable def tracedSigningRun {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ProbComp (TracedSigningRecord ω) :=
  ((simulateQ (romImpl.withTrace trace) (signWithView key message)).run).run cache
theorem tracedSigningRun_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result : TracedSigningRecord ω => (result.1.1, result.2)) <$>
      tracedSigningRun trace key message cache = (simulateQ romImpl (signWithView key message)).run cache := by
  have h := congrArg (fun comp : StateT (QueryCache HashSpec) ProbComp (Option Signature × Option FewTimeView) => comp.run cache)
    (QueryImpl.fst_map_run_withTrace romImpl trace (signWithView key message))
  simpa only [StateT.run_map, tracedSigningRun] using h
def signingRecordResponse {ω : Type} (result : TracedSigningRecord ω) :
    (Option Signature × ω) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2)
theorem tracedSigningRun_signature {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    signingRecordResponse <$> tracedSigningRun trace key message cache =
      ((simulateQ (romImpl.withTrace trace) (sign key message)).run).run cache := by
  change (fun result : TracedSigningRecord ω => ((result.1.1.1, result.1.2), result.2)) <$>
    tracedSigningRun trace key message cache = _
  have h := congrArg (fun comp : OracleComp OracleWorld (Option Signature) =>
    ((simulateQ (romImpl.withTrace trace) comp).run).run cache) (signWithView_fst key message)
  simpa only [simulateQ_map, WriterT.run_map, StateT.run_map, tracedSigningRun] using h
theorem probOutput_tracedSigningIndex_eq_loop {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [← probOutput_completeSigningIndex_eq_loop, ← tracedSigningRun_forget trace key message cache]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
noncomputable def completedSigningRecord {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : PMF (TracedSigningRecord ω × Index) :=
  (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)).bind fun result =>
    (liftM (completeSelectedIndex result.1.1.2) : PMF Index).map (fun index => (result, index))
theorem completedSigningRecord_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.fst =
      (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.fst = PMF.pure result := by
    rw [PMF.map_comp]
    exact PMF.map_const _ result
  simp_rw [hbranch]
  exact PMF.bind_pure _
theorem completedSigningRecord_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.snd =
      (liftM (tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2) : PMF Index) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.snd = liftM (completeSelectedIndex result.1.1.2) := by
    rw [PMF.map_comp]
    exact PMF.map_id _
  simp_rw [hbranch]
  exact (liftM_bind (m := ProbComp) (n := PMF) _ _).symm
theorem completedSigningRecord_index_le {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (spent : Nat) (hspent : spent ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ MessageDeficitExceptional key cache)
    (hindex : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) (index : Index) :
    ((completedSigningRecord trace key message cache).map Prod.snd) index ≤ targetProposalIndexRate := by
  rw [completedSigningRecord_index, probCompLift_apply, probOutput_tracedSigningIndex_eq_loop]
  exact probOutput_completeSelectedLoopIndex_le_proposalRate key message cache spent hspent hcache hclean hindex index
theorem completedSigningRecord_selected_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (record : TracedSigningRecord ω) (index : Index) (view : FewTimeView)
    (hr : (record, index) ∈ (completedSigningRecord trace key message cache).support)
    (hview : record.1.1.2 = some view) : index = view.1 := by
  rw [completedSigningRecord, PMF.mem_support_bind_iff] at hr
  obtain ⟨source, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨selected, hselected, heq⟩ := hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  simpa only [hview, completeSelectedIndex, Option.elim_some, liftM_pure,
    PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff] using hselected
structure ProposalCacheBound (key : SecretKey) (cache : QueryCache HashSpec) (spent : Nat) : Prop where
  spent_le : spent ≤ 2 ^ 127
  cache_le : QueryCache.enncard cache ≤ spent
  no_deficit : ¬ MessageDeficitExceptional key cache
  index_le : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
    (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)
theorem completedSigningRecord_acceptance_cap {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) (index : Index) :
    targetProposalAcceptance * ((completedSigningRecord trace key message cache).map Prod.snd) index ≤
      PMF.uniformOfFintype Index index :=
  targetProposalAcceptance_cap (completedSigningRecord trace key message cache) Prod.snd
    (completedSigningRecord_index_le trace key message cache spent hbound.spent_le hbound.cache_le
      hbound.no_deficit hbound.index_le) index
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
theorem independentProposalWord_length {α : Type*} (law : PMF α) (steps : Nat) :
    (independentProposalWord law steps).map List.length = PMF.pure steps := by
  induction steps with
  | zero => exact PMF.pure_map _ _
  | succ steps ih =>
      rw [independentProposalWord, PMF.map_bind]
      have hbranch (head : α) :
          ((independentProposalWord law steps).map (head :: ·)).map List.length =
            PMF.pure (steps + 1) := by
        calc
          _ = ((independentProposalWord law steps).map List.length).map Nat.succ := by
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = _ := by rw [ih, PMF.pure_map]
      simp_rw [hbranch]
      exact PMF.bind_const _ _
theorem rejectedProposalWord_length {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map List.length =
      proposalFailureCount accept hpos hle := by
  rw [rejectedProposalWord, PMF.map_bind]
  simp_rw [independentProposalWord_length]
  exact PMF.bind_pure _
noncomputable def proposalBlockLength (accept : ENNReal) (hpos : accept ≠ 0)
    (hle : accept ≤ 1) : PMF Nat :=
  (proposalFailureCount accept hpos hle).map Nat.succ
theorem proposalBlockLength_zero (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    proposalBlockLength accept hpos hle 0 = 0 :=
  pmf_map_apply_zero_of_not_image _ _ _ (fun _ => Nat.zero_ne_add_one _)
theorem proposalBlockLength_succ (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (failures : Nat) :
    proposalBlockLength accept hpos hle (failures + 1) = accept * (1 - accept) ^ failures :=
  (pmf_map_injective_apply _ _ Nat.succ_injective failures).trans rfl
theorem rejectedProposalWord_blockLength {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map (fun word => word.length + 1) =
      proposalBlockLength accept hpos hle := by
  change _ = ((proposalFailureCount accept hpos hle).map Nat.succ)
  rw [← rejectedProposalWord_length law accept hpos hle, PMF.map_comp]
  rfl
noncomputable def recordLengthBridge {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (Nat × Ω) :=
  record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (fun length => (length, outcome))
theorem recordProposalBridge_length_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map
      (fun result => (result.1.length + 1, result.2)) = recordLengthBridge record accept hpos hle := by
  rw [recordProposalBridge, PMF.map_bind]
  have hbranch (outcome : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))).map
        (fun result => (result.1.length + 1, result.2)) =
      (proposalBlockLength accept hpos hle).map (fun length => (length, outcome)) := by
    rw [← rejectedProposalWord_blockLength rejected accept hpos hle, PMF.map_comp, PMF.map_comp]
    rfl
  simp_rw [hbranch]
  rfl
theorem recordLengthBridge_record {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.snd = record := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (Function.const Nat outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]
theorem recordLengthBridge_length {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.fst = proposalBlockLength accept hpos hle := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun _ => (proposalBlockLength accept hpos hle).map id) = _
  rw [PMF.map_id, PMF.bind_const]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def pmfSumImpl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    QueryImpl (leftSpec + rightSpec) (StateT σ PMF)
  | .inl input => StateT.mk fun state => liftM ((left input).run state)
  | .inr input => StateT.mk fun state => liftM ((right input).run state)
theorem pmfSumImpl_inl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : leftSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inl input)).run state = (liftM ((left input).run state) : PMF _) := rfl
theorem pmfSumImpl_inr {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : rightSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inr input)).run state = (liftM ((right input).run state) : PMF _) := rfl
theorem pmfSumImpl_eq_lift_add {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    pmfSumImpl left right = fun input => StateT.mk fun state =>
      (liftM (((left + right) input).run state) : PMF _) := by
  funext input
  cases input <;> rfl
theorem simulateQ_liftProbCompImpl_run {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (computation : OracleComp spec α) (state : σ) :
    (simulateQ (fun input => StateT.mk fun current => (liftM ((impl input).run current) : PMF _))
      computation).run state = (liftM ((simulateQ impl computation).run state) : PMF _) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (liftM_pure (m := ProbComp) (n := PMF) _).symm
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, StateT.run_mk]
      rw [liftM_bind (m := ProbComp) (n := PMF)]
      exact congrArg (fun continuation => (liftM ((impl input).run state) : PMF _).bind continuation)
        (funext fun result => ih result.1 result.2)
noncomputable def proposalRecordImpl {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT (List α × σ) PMF) :=
  fun input => StateT.mk fun state =>
    if active input state.2 then
      (recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
        (fun result => (response input result.2,
          (state.1 ++ result.1 ++ [label input result.2],
            advance input state.2 (result.1.length + 1) result.2)))
    else
      (record input state.2).map fun outcome =>
        (response input outcome, (state.1, advance input state.2 0 outcome))
noncomputable def lengthRecordImpl {ι σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT σ PMF) :=
  fun input => StateT.mk fun state =>
    if active input state then
      (recordLengthBridge (record input state) accept hpos hle).map
        (fun result => (response input result.2, advance input state result.1 result.2))
    else
      (record input state).map fun outcome => (response input outcome, advance input state 0 outcome)
theorem proposalRecordImpl_project {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (input : spec.Domain) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      ((proposalRecordImpl record response advance label rejected active accept hpos hle) input).run state =
    ((lengthRecordImpl record response advance active accept hpos hle) input).run state.2 := by
  change PMF.map (Prod.map id Prod.snd) _ = _
  simp only [proposalRecordImpl, lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state.2 = true
  · simp only [hactive, if_true]
    calc
      _ = ((recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
          (fun result => (result.1.length + 1, result.2))).map
            (fun result => (response input result.2, advance input state.2 result.1 result.2)) := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by rw [recordProposalBridge_length_record]
  · simp only [hactive, Bool.false_eq_true, if_false, PMF.map_comp]
    rfl
theorem simulateQ_proposalRecordImpl_project {ι α σ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (computation : OracleComp spec β) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalRecordImpl record response advance label rejected active accept hpos hle)
        computation).run state =
    (simulateQ (lengthRecordImpl record response advance active accept hpos hle)
      computation).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (proposalRecordImpl_project record response advance label rejected active accept hpos hle)
    computation state
theorem lengthRecordImpl_project {ι σ τ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (input : spec.Domain) (state : σ) :
    Prod.map id project <$> ((lengthRecordImpl record response advance active accept hpos hle) input).run state =
      (base input).run (project state) := by
  change PMF.map (Prod.map id project) _ = _
  simp only [lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state = true
  · simp only [hactive, if_true, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
    calc
      _ = ((recordLengthBridge (record input state) accept hpos hle).map Prod.snd).map
          (fun outcome => (response input outcome, next input state outcome)) := by
        rw [PMF.map_comp]
        rfl
      _ = _ := by rw [recordLengthBridge_record, hrecord]
  · simpa only [hactive, Bool.false_eq_true, if_false, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
      using hrecord input state
theorem simulateQ_lengthRecordImpl_project {ι σ τ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (computation : OracleComp spec β) (state : σ) :
    Prod.map id project <$>
      (simulateQ (lengthRecordImpl record response advance active accept hpos hle) computation).run state =
      (simulateQ base computation).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ project
    (lengthRecordImpl_project record response advance active accept hpos hle base project next hnext hrecord)
    computation state
end SphincsSecurity.Concrete
end
