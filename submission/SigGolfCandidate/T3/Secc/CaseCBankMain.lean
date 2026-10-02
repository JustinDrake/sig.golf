import SigGolfCandidate.T3.Secc.CaseCBankStep

/-!
# Stream CC: the bank inequality on the actual padded experiment

`bank_potential_le`: the final potential of the bank experiment is at most
`(theta + 1/16)/2^128 · E[digest births] + budget · 18400/10^8 / 2^128`, where the births are SEC's
`CreationGame.expectedBirths IsDigestInput` (fresh adversary/verifier digest queries within budget), bounded by the
shared-law digest-class charge (`expectedBirths_le_shared`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankMain : DecidableEq T3.Cache := Classical.decEq _

/-- **One step of the bank**, for every interaction query. -/
theorem potential_step (published : T3.Cache) (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (st : BankState) :
    expectedValue ((bankImpl published budget input).run st) (fun r => potential budget r.2) ≤
      potential budget st + birthCharge budget input st := by
  cases input with
  | inl input => exact world_step published budget input st
  | inr request => exact (sign_step published budget request st).trans le_self_add

/-- Supermartingale accumulation: the final potential is at most the initial one plus the expected charges. -/
theorem potential_run {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState) :
    expectedValue ((simulateQ (bankImpl published budget) program).run st) (fun r => potential budget r.2) ≤
      potential budget st + BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget)
        (birthCharge budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((bankImpl published budget input).run st) (fun result =>
            potential budget result.2 + BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget)
              (birthCharge budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((bankImpl published budget input).run st) (fun result => potential budget result.2) +
            expectedValue ((bankImpl published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget)
                (birthCharge budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ (potential budget st + birthCharge budget input st) + _ :=
          add_le_add (potential_step published budget input st) le_rfl
        _ = _ := by ring

/-! ## Births: the bank's charges are SEC's class births -/

/-- The 0/1 birth indicator of a query (SEC's `classWeight IsDigestInput`). -/
noncomputable def birthWeight (budget : Nat) : LazyPrivate.Interaction.Domain → QueryRecorded.State → ENNReal :=
  fun input s => (CreationGame.classWeight IsDigestInput budget input ([], s) : ENNReal)

theorem birthCharge_eq (budget : Nat) (input : LazyPrivate.Interaction.Domain) (st : BankState) :
    birthCharge budget input st = (theta + 1 / 16) / 2 ^ 128 * birthWeight budget input st.2 := by
  rcases input with (n | x) | request
  · simp [birthCharge, birthWeight, CreationGame.classWeight]
  · simp only [birthCharge, birthWeight, CreationGame.classWeight]
    by_cases h : Birth budget x st.2
    · have h' : st.2.base.source.1 < budget ∧ IsDigestInput x ∧ st.2.base.source.2.2 x = none :=
        ⟨h.2.2, h.1, h.2.1⟩
      rw [if_pos h, if_pos h', Nat.cast_one, mul_one]
    · have h' : ¬(st.2.base.source.1 < budget ∧ IsDigestInput x ∧ st.2.base.source.2.2 x = none) :=
        fun h' => h ⟨h'.2.1, h'.2.2, h'.1⟩
      rw [if_neg h, if_neg h', Nat.cast_zero, mul_zero]
  · simp [birthCharge, birthWeight, CreationGame.classWeight]

theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (program : OracleComp LazyPrivate.Interaction α) (s : QueryRecorded.State) (g : Ghost) :
    BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget) (birthCharge budget) program (g, s) =
      (theta + 1 / 16) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges
        (QueryRecorded.proposalModel published budget hbudget).traced
        (fun input state => (CreationGame.classWeight IsDigestInput budget input state : ENNReal)) program ([], s) := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget) (birthCharge budget) program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (bankImpl published budget)
        (fun input st => (theta + 1 / 16) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact birthCharge_eq budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  have hb := BPORS.Adaptive.Creation.expectedCharges_project (bankImpl published budget)
    (QueryRecorded.proposalModel published budget hbudget).original Prod.snd
    (fun input st => by
      rw [bank_query_project, QueryRecorded.proposal_query_erasure])
    (birthWeight budget) program (g, s)
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel published budget hbudget).traced
    (QueryRecorded.proposalModel published budget hbudget).original Prod.snd
    (QueryRecorded.proposalModel published budget hbudget).traced_query_erasure
    (birthWeight budget) program ([], s)
  rw [hb, ← ht]
  congr 1
  funext input state
  unfold birthWeight
  rcases input with (n | x) | request <;> rfl

/-- Support monotonicity of expectations for `PMF`. -/
theorem pmf_expectedValue_mono {α : Type} (p : PMF α) {f g : α → ENNReal} (h : ∀ x ∈ p.support, f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · exact mul_le_mul' le_rfl (h x hx)
  · have hp : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hx
    rw [hp, zero_mul, zero_mul]

/-! ## The initial potential -/

theorem keygen_notDigest : AllQueriesSatisfy keygen BPB.NotDigestQ := by
  unfold keygen keygenPayload
  apply SourceQueries.bind_allowed
  · apply SourceQueries.bind_allowed _ (BPB.buildTree_ok 0 0 0 [])
    intro built
    rcases built with ⟨levels, other⟩
    apply SourceQueries.bind_allowed
    · apply SourceQueries.mapM_allowed
      intro level
      apply SourceQueries.mapM_allowed
      intro i
      apply SourceQueries.bind_allowed _ (BPB.mask_ok level i)
      intro _
      exact SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
  · intro generated
    rcases generated with ⟨publicKey, region⟩
    apply SourceQueries.bind_allowed
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro _
      exact SourceQueries.pure_allowed _ _

theorem reuseMass_of_noDigest (cache : Sampling.RCache) (h : ∀ x, IsDigestInput x → cache x = none) (m : Message) :
    reuseMass cache m = 0 := by
  unfold reuseMass
  rw [ENNReal.div_eq_zero_iff]
  left
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [admissibleEntry, h _ (digestRowOf_isDigest ⟨p, rfl⟩)]

theorem keygen_noDigest (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    ∀ x, IsDigestInput x → (lazyOf generated.2).2 x = none := by
  intro x hx
  by_contra hne
  have hl := recorded_lazy_support keygen QueryRecorded.initial generated hg
  have := run_new_public keygen (fun x => ¬IsDigestInput x)
    (allQueriesSatisfy_mono _ _ _ (fun q hq x hqx hd => by
      subst hqx
      obtain ⟨rho, m, c, rfl⟩ := hd
      exact hq (BPB.hdrTag_digestInput rho m c)) keygen_notDigest)
    (lazyOf QueryRecorded.initial) (generated.1, lazyOf generated.2) hl x rfl hne
  exact this hx

theorem potential_initial_le (budget : Nat) (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    potential budget (Ghost.empty, generated.2) ≤ (budget : ENNReal) * (18400 / 100000000) / 2 ^ 128 := by
  have hreuse : reusePotential (lazyOf generated.2) = 0 := by
    unfold reusePotential
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    split_ifs
    · exact reuseMass_of_noDigest _ (keygen_noDigest generated hg) m
    · rfl
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : bankValue Ghost.empty = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he := excess_three_quarters
      simpa [excessForecast, Ghost.empty, labels, horizon] using he

/-- **The bank inequality.** -/
theorem bank_potential_le (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bankExperiment adversary budget) (fun r => potential budget r.2) ≤
      (theta + 1 / 16) / 2 ^ 128 * CreationGame.expectedBirths IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * (18400 / 100000000) / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * (18400 / 100000000) / 2 ^ 128 +
          (theta + 1 / 16) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges
            (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
            (fun input state => (CreationGame.classWeight IsDigestInput budget input state : ENNReal))
            (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)) := by
      apply pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (potential_run generated.1.2 budget _ _).trans ?_
      rw [bank_charges_eq_births generated.1.2 budget hbudget]
      exact add_le_add (potential_initial_le budget generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), pmf_expectedValue_left_mul]
      unfold CreationGame.expectedBirths
      ring

end SigGolfCandidate.T3.Security.CaseC
