import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryHashEvaluation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.BankedProposalStep
import SigGolfCandidate.SphincsSecurity.Proof.Reference.DirectQueryBudget
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateMonitor

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundaryHashAtLeast signDigestLoop
theorem boundaryHashAtLeast_lift_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, BoundaryHashAtLeast parameter (liftM (computation i)) (cost i)) :
    BoundaryHashAtLeast parameter (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact boundaryHashAtLeast_zero _ _
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind, ← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_ftsNode (traceParameter parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    BoundaryHashAtLeast traceParameter
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest))
      (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact boundaryHashAtLeast_tweakableHash traceParameter parameter
        (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) (digestBytes (secret (ftsLeafOfNat nodeIdx)))
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro right
      exact boundaryHashAtLeast_tweakableHash _ _ _ _
theorem boundaryHashAtLeast_buildLevels (traceParameter : PublicParameter)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      BoundaryHashAtLeast traceParameter (liftM (hashNode level nodeIdx left right)) 1)
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    BoundaryHashAtLeast traceParameter (liftM (buildLevels hashNode height leaves levels))
      (levelsHashCost height levels) := by
  induction levels with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ levels ih =>
      rw [buildLevels, liftM_bind, levelsHashCost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ ih
      intro table
      rw [buildLevel, liftM_bind, liftM_bind]
      rw [bind_assoc]
      refine BoundaryHashAtLeast.mono (a := 2 ^ (height - (levels + 1)) + 0) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ _ 0
      · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
          (fun nodeIdx : Fin (2 ^ (height - (levels + 1))) =>
            hashNode (levels + 1) nodeIdx.val (table levels (2 * nodeIdx.val)) (table levels (2 * nodeIdx.val + 1)))
          (fun _ => 1) (fun _ => hhash _ _ _ _)
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
      · intro _
        exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_buildFtsTree_levels (traceParameter parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildFtsTree parameter index (fun leaf => pure (secret leaf)) :
        OracleComp HashSpec _)) (2 ^ (ftsTreeHeight + 1) - 1) := by
  have hcost : 2 ^ (ftsTreeHeight + 1) - 1 = 2 ^ ftsTreeHeight + (levelsHashCost ftsTreeHeight ftsTreeHeight + 0) := by
    rw [levelsHashCost_self, pow_succ]
    have := Nat.two_pow_pos ftsTreeHeight
    omega
  rw [hcost, buildFtsTree, liftM_bind]
  apply boundaryHashAtLeast_bind _ _ _ _ _
  · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
      (fun leafIdx : FtsLeaf => (do
        let value ← (pure (secret leafIdx) : OracleComp HashSpec Digest)
        let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
        return (value, hashed)))
      (fun _ => 1) (fun leafIdx => by
        rw [pure_bind, liftM_bind, ← Nat.add_zero 1]
        apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_tweakableHash _ _ _ _)
        intro _
        exact boundaryHashAtLeast_zero _ _)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
  · intro leaves
    rw [liftM_bind]
    apply boundaryHashAtLeast_bind _ _ _ _ _
      (boundaryHashAtLeast_buildLevels _ _ (fun _ _ _ _ => boundaryHashAtLeast_tweakableHash _ _ _ _) _ _ _)
    intro _
    exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_buildFtsTree (traceParameter parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildFtsTree parameter index (fun leaf => pure (secret leaf)) :
        OracleComp HashSpec _)) ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  exact boundaryHashAtLeast_buildFtsTree_levels traceParameter parameter index secret
theorem boundaryHashAtLeast_signAttempt (parameter : PublicParameter) (key : SecretKey)
    (message : Message) (randomness : Randomness) :
    BoundaryHashAtLeast parameter (liftM (signAttempt key message randomness : OracleComp HashSpec _)) 1 := by
  unfold signAttempt messageDigest
  rw [liftM_bind, liftM_bind, bind_assoc]
  apply boundaryHashAtLeast_bind _ _ _ 1 0 (boundaryHashAtLeast_hash _ _)
  intro output
  exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_signDigestLoop_bind {α : Type} (parameter : PublicParameter)
    (key : SecretKey) (message : Message) (cost attempts : Nat)
    (next : Option (Randomness × Index × (IndexGroup → FtsLeaf)) → OracleComp OracleWorld α)
    (hnext : ∀ selected, BoundaryHashAtLeast parameter (next (some selected)) cost) :
    BoundaryHashAtLeast parameter (signDigestLoop attempts key message >>= next) (min attempts cost) := by
  induction attempts with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ attempts ih =>
      rw [signDigestLoop, bind_assoc, ← Nat.zero_add (min (attempts + 1) cost)]
      apply boundaryHashAtLeast_bind _ _ _ 0 _ (boundaryHashAtLeast_zero _ _)
      intro randomness
      rw [bind_assoc]
      apply BoundaryHashAtLeast.mono (a := 1 + min attempts cost) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ 1 _ (boundaryHashAtLeast_signAttempt _ _ _ _)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected =>
          simp only [pure_bind]
          exact BoundaryHashAtLeast.mono (hnext _) (min_le_right _ _)
theorem boundaryHashAtLeast_sign (parameter : PublicParameter) (key : SecretKey) (message : Message) :
    BoundaryHashAtLeast parameter (sign key message) ftsOpenHashCost := by
  rw [sign_eq]
  apply BoundaryHashAtLeast.mono (a := min digestAttemptLimit ftsOpenHashCost) ?_
    (le_min ftsOpenHashCost_le_digestAttemptLimit le_rfl)
  apply boundaryHashAtLeast_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  show BoundaryHashAtLeast parameter (liftM (signAfterDigest key randomness index leaves :
      OracleComp HashSpec (Option Signature))) ftsOpenHashCost
  rw [signAfterDigest, signFrom, liftM_bind, ← Nat.add_zero ftsOpenHashCost]
  apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_buildFtsTree _ _ _ _)
  intro _
  exact boundaryHashAtLeast_zero _ _
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem probCompLift_support {α : Type} (computation : ProbComp α) :
    (liftM computation : PMF α).support = support computation := by
  ext value
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply, mem_support_iff]
  rfl
theorem originalProposalRecord_boundary (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (originalProposalRecord key input cache).map (fun record => ((record.output, record.trace), record.cache)) =
      (liftM (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) : PMF _) := by
  cases input with
  | inl world =>
      simp only [originalProposalRecord, PMF.map_comp, expandedAdversaryImpl]
      rw [boundaryRun_query]
      exact (liftM_map (m := ProbComp) (n := PMF) _ _).symm
  | inr message =>
      rw [originalProposalRecord, PMF.map_comp]
      calc
        _ = ((completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map Prod.fst).map
            signingRecordResponse := (PMF.map_comp _ _ _).symm
        _ = _ := by
          rw [completedSigningRecord_forget, ← PMF.monad_map_eq_map,
            ← liftM_map (m := ProbComp) (n := PMF), tracedSigningRun_signature]
          rfl
theorem originalProposalRecord_boundary_support (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    ((record.output, record.trace), record.cache) ∈
      support (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) := by
  have hm := (PMF.mem_support_map_iff
    (fun record : ProposalExecutionRecord input => ((record.output, record.trace), record.cache))
    (originalProposalRecord key input cache) _).mpr ⟨record, hr, rfl⟩
  rwa [originalProposalRecord_boundary, probCompLift_support] at hm
theorem originalProposalRecord_query_bound {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (cache : QueryCache HashSpec)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)) cache q) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input cache).support) :
    record.trace.hashCalls ≤ q ∧
      HashQueryBound (simulateQ (expandedAdversaryImpl key) (next record.output)) record.cache
        (q - record.trace.hashCalls) := by
  rw [simulateQ_bind, simulateQ_spec_query] at hbound
  exact boundaryRun_bind_query_bound key.parameter (expandedAdversaryImpl key input)
    (fun output => simulateQ (expandedAdversaryImpl key) (next output)) q cache hbound _
    (originalProposalRecord_boundary_support key input cache record hr)
theorem originalProposalRecord_sign_hashCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inr message))
    (hr : record ∈ (originalProposalRecord key (.inr message) cache).support) :
    ftsOpenHashCost ≤ record.trace.hashCalls :=
  boundaryHashAtLeast_sign key.parameter key message cache _
    (originalProposalRecord_boundary_support key (.inr message) cache record hr)
theorem targetCreationMultiplier_le_record_hashCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    targetCreationMultiplier key cache input ≤ record.trace.hashCalls := by
  cases input with
  | inl world =>
      rw [originalProposalRecord_world_hashCalls key world cache record hr, targetCreationMultiplier]
      cases world with
      | inl sample => exact le_refl _
      | inr input =>
          simp only [freshWorldTargetHashCost, signingExecutionHashCost]
          split_ifs <;> norm_num
  | inr message =>
      have hmass := mul_le_mul' admissibleProbability_inv_le
        (freshDigestSelectionProbability_le_one key message cache)
      calc
        _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
          refine (by simpa only [targetCreationMultiplier, mul_one] using hmass : _ ≤ (2142 : ENNReal)).trans ?_
          exact_mod_cast (show 2142 ≤ 2 ^ ftsTreeHeight by decide)
        _ ≤ (ftsOpenHashCost : ENNReal) := Nat.cast_le.mpr two_pow_ftsTreeHeight_le_ftsOpenHashCost
        _ ≤ record.trace.hashCalls := Nat.cast_le.mpr (originalProposalRecord_sign_hashCalls key message cache record hr)
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem certificateLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateMonitorState)
    (hr : result ∈ ((certificateLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateMonitorUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩
theorem certificateMonitorUpdate_le_hashCalls (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent ≤
        state.2.spent + record.trace.hashCalls ∧
      (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass ≤
        state.2.creationMass + record.trace.hashCalls := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive]
    exact ⟨le_rfl, add_le_add le_rfl (targetCreationMultiplier_le_record_hashCalls key input state.1 record hr)⟩
  · simp only [certificateMonitorUpdate, if_neg hactive]
    exact ⟨Nat.le_add_right _ _, le_self_add⟩
theorem certificateLength_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.1 q) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.spent ≤ state.2.spent + q ∧ result.2.2.creationMass ≤ state.2.creationMass + q := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨Nat.le_add_right _ _, le_self_add⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      have hquery := originalProposalRecord_query_bound key input next q state.1 hbound record hrecord
      have hstep := certificateMonitorUpdate_le_hashCalls key budget required stopAfter input state length record hrecord
      have htail := ih record.output _ _ hquery.2 result hr
      simp only [originalProposalAdvance] at htail
      constructor
      · omega
      · calc
          _ ≤ (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass +
              (q - record.trace.hashCalls : Nat) := htail.2
          _ ≤ (state.2.creationMass + record.trace.hashCalls) + (q - record.trace.hashCalls : Nat) :=
            add_le_add hstep.2 le_rfl
          _ = state.2.creationMass + q := by
            rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hquery.1]
theorem certificateProposal_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : List Index × CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.2.1 q) (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2.spent ≤ state.2.2.spent + q ∧
      result.2.2.2.creationMass ≤ state.2.2.creationMass + q := by
  have hprojection := simulateQ_certificateProposalImpl_length key budget required stopAfter computation state
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, hprojection] at hm
  exact certificateLength_run_cost_le key budget required stopAfter computation q state.2 hbound _ hm
end SphincsSecurity.Concrete
end
