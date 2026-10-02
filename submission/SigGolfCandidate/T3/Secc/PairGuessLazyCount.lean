import SigGolfCandidate.T3.Secc.PairGuessLazy

/-!
# B-PAIR (CC-4 G2/G3/G5): counting ghosts of the eager run of the lazy world

On `fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL ω adversary) initL` results `r`:

* G2: `r.2.memory.births.length ≤ r.1.2.2.length` (one birth at most per recorded entry);
* G3: every signer trial row is a digest query of the honest signer of a logged signing;
* G5: `r.2.memory.exposures.length ≤ r.1.2.1.length` (one exposure at most per signing).

`worldGameL_bank` packages §8.3's ghosts and tracking with G2/G3/G5 in the shape of CC's `BPairGhosts`.
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Steps
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)

/-- Births, exposures and trial rows kept. -/
def Keeps (m m' : LazyMem) : Prop := m'.births = m.births ∧ m'.exposures = m.exposures ∧ m'.trials = m.trials

theorem Keeps.refl (m : LazyMem) : Keeps m m := ⟨rfl, rfl, rfl⟩

theorem Keeps.trans {m1 m2 m3 : LazyMem} (h1 : Keeps m1 m2) (h2 : Keeps m2 m3) : Keeps m1 m3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem fixed_coin_state (n : Nat) (s : WStateL) (r : Fin (n + 1) × WStateL)
    (hr : fixedRun (envE D Nn) fts (coinReqL n) s r ≠ 0) : r.2 = s := by
  unfold coinReqL fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) r ≠ 0 at hr
  rw [liftM_map, Functor.map_map] at hr
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
    SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨c, _, rfl⟩ := hr
  rfl

theorem fixed_guess_state (p : FtsCoord × Digest) (s : WStateL) (r : Bool × WStateL)
    (hr : fixedRun (envE D Nn) fts (guessReq p) s r ≠ 0) : r.2.memory = s.memory := by
  unfold guessReq fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  change (pure (decide (fts p.1 = p.2), SecretGuessObservation.afterTrial (envE D Nn) s p.1 p.2
    (decide (fts p.1 = p.2))) : SPMF (Bool × WStateL)) r ≠ 0 at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  rw [hr]
  rfl

theorem fixed_disclosures_state (positions : List FtsCoord) (s : WStateL) (r : List Digest × WStateL)
    (hr : fixedRun (envE D Nn) fts (positions.mapM discloseReq) s r ≠ 0) : r.2.memory = s.memory := by
  induction positions generalizing s r with
  | nil =>
      rw [List.mapM_nil] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
  | cons first rest ih =>
      rw [List.mapM_cons] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
      rw [runL_pure_nonzero _ fts _ _ r hr]
      have hm1 : m1.2.memory = s.memory := by
        unfold discloseReq fixedRun runWith at h1
        rw [simulateQ_spec_query] at h1
        change (pure (fts first, SecretGuessObservation.afterDisclosure (envE D Nn) s first (fts first)) :
          SPMF (Digest × WStateL)) m1 ≠ 0 at h1
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h1
        rw [h1]
        rfl
      exact (ih m1.2 m2 h2).trans hm1

theorem fixed_nonce_keeps (m : Message) (s : WStateL) (r : Digest × WStateL)
    (hr : fixedRun (envE D Nn) fts (nonceReq m) s r ≠ 0) : Keeps s.memory r.2.memory := by
  cases hc : s.memory.nonces m with
  | some v =>
      rw [nonceReq, fixed_aux_single D Nn fts s (.nonce m) v s.memory (nonceStep_some _ _ _ v hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact Keeps.refl _
  | none =>
      rw [nonceReq, fixed_aux_single D Nn fts s (.nonce m) (Nn m) (s.memory.drawNonce m (Nn m))
        ((nonceStep_none _ _ _ hc).trans (map_pure _ _))] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact ⟨rfl, rfl, rfl⟩

theorem fixed_expose_mem (o : Option HashOutput) (s : WStateL) (r : Unit × WStateL)
    (hr : fixedRun (envE D Nn) fts (exposeReq o) s r ≠ 0) : r.2.memory = s.memory.expose o := by
  rw [exposeReq, fixed_aux_single D Nn fts s (.expose o) () (s.memory.expose o) rfl] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  rw [hr]

theorem fixed_birth_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) fts (birthReq x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [birthReq, fixed_aux_single D Nn fts s (.birth x) a (s.memory.replayRow x true)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [birthReq, fixed_aux_single D Nn fts s (.birth x) (rowVal D x) (s.memory.readRow x (rowVal D x) true)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_true]
      · rw [birthReq, fixed_aux_single D Nn fts s (.birth x) 0 (s.memory.replayRow x true)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]

theorem fixed_trial_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) fts (trialReq x) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials ++ [x] := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [trialReq, fixed_aux_single D Nn fts s (.trial x) a (s.memory.replayRow x false)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [trialReq, fixed_aux_single D Nn fts s (.trial x) (rowVal D x) (s.memory.readRow x (rowVal D x) false)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_false]
      · rw [trialReq, fixed_aux_single D Nn fts s (.trial x) 0 (s.memory.replayRow x false)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]

end Steps

section Programs
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCount : DecidableEq T3.Cache := Classical.decEq _

/-- The honest signer's digest queries under the eager table. -/
theorem queried_sign_search (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request)
    (hc : request.cache = published) (x : HashInput)
    (hx : (.inl (.inr x) : T3.Spec.Domain) ∈ SecurityExtraction.queried (Omega.answers hU ω fts)
      (digestSearch (nonceOf ω request.message) request.message 0 attemptLimit)) :
    (.inl (.inr x) : T3.Spec.Domain) ∈ SecurityExtraction.queried (Omega.answers hU ω fts)
      (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  rw [SecurityExtraction.queried_bind, if_pos hc, Correctness.signPayload_eq, SecurityExtraction.queried_bind,
    SecurityExtraction.queried_bind, eval_nonce hU ω fts request.message]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hx))

theorem queried_digestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    SecurityExtraction.queried A (digestSearch rho m counter (fuel + 1)) =
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) : T3.Spec.Domain) ::
        SecurityExtraction.queried A
          (if digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
            then pure (some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))))
            else digestSearch rho m (counter + 1) fuel) := by
  rw [digestSearch]
  exact SecurityExtraction.queried_query_bind A _ _

/-- The lazy search: births and exposures kept; every new trial row is a digest query of the honest search. -/
theorem searchL_counts (fts : FtsCoord → Digest) (rho : Digest) (m : Message) (counter fuel : Nat) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option (BitVec 32 × HashOutput) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (searchL rho m counter fuel) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (digestSearch rho m counter fuel) := by
  induction fuel generalizing counter s r with
  | zero =>
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨rfl, rfl, fun x hx => Or.inl hx⟩
  | succ fuel ih =>
      rw [searchL] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      obtain ⟨hb1, he1, ht1⟩ := fixed_trial_counts _ _ fts _ s m1 h1
      have g1 := run_good _ _ fts _ s hs m1 h1
      have hv1 : m1.1 = Omega.answers hU ω fts (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) := by
        have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ s hs.1 m1 h1
        rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (trialReq (pad64 (digestInput rho m
            (BitVec.ofNat 32 counter)))) = pure (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))
          from by simp only [trialReq, simulateQ_spec_query, inlineWith]] at h
        rw [congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h), answers_digest hU ω fts _ (digestInput_mem _ _ _)]
      rw [queried_digestSearch_succ, ← hv1]
      by_cases hadm : digestAdmissible m1.1 = true
      · simp only [hadm, ↓reduceIte] at hr ⊢
        rw [runL_pure_nonzero _ fts _ _ r hr]
        refine ⟨hb1, he1, fun x hx => ?_⟩
        rw [ht1, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_self)
      · simp only [hadm, ↓reduceIte, Bool.false_eq_true] at hr ⊢
        obtain ⟨hb2, he2, ht2⟩ := ih (counter + 1) m1.2 g1.1 r hr
        refine ⟨hb2.trans hb1, he2.trans he1, fun x hx => ?_⟩
        rcases ht2 x hx with hx | hx
        · rw [ht1, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Or.inl hx
          · exact Or.inr (List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hx)

theorem finishL_state (fts : FtsCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (finishL hU ω request rho found) s r ≠ 0) :
    r.2.memory = s.memory := by
  cases found with
  | none => rw [runL_pure_nonzero _ fts _ s r hr]
  | some found =>
      obtain ⟨c, out⟩ := found
      change fixedRun (envE (digestOf ω) (nonceOf ω)) fts (match signerLayers hU ω request out with
        | none => pure none
        | some pieces => do
            let values ← (openedPositions out).mapM discloseReq
            pure (some (Correctness.assembledSignature rho
              (openedValues (overwrite (openedPositions out) values) out,
                (signerForest hU ω out).2.1, (signerForest hU ω out).2.2) pieces))) s r ≠ 0 at hr
      cases hl : signerLayers hU ω request out with
      | none =>
          rw [hl] at hr
          rw [runL_pure_nonzero _ fts _ s r hr]
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, hm, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
          rw [runL_pure_nonzero _ fts _ _ r hr]
          exact fixed_disclosures_state _ _ fts _ s mid hm

/-- A lazy signing: births kept; at most one exposure; new trial rows are the honest signer's digest queries. -/
theorem signL_counts (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (signL hU ω published request) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures.length ≤ s.memory.exposures.length + 1 ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) := by
  unfold signL at hr
  by_cases hc : request.cache = published
  · rw [if_pos hc] at hr
    obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
    obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
    obtain ⟨m3, h3, hr⟩ := runL_bind_nonzero _ fts _ _ m2.2 r hr
    have k1 := fixed_nonce_keeps _ _ fts request.message s m1 h1
    have g1 := run_good _ _ fts _ s hs m1 h1
    have hv1 : m1.1 = nonceOf ω request.message := by
      have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ s hs.1 m1 h1
      rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (nonceReq request.message) =
        pure (nonceOf ω request.message) from by simp only [nonceReq, simulateQ_spec_query, inlineWith]] at h
      exact congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h)
    obtain ⟨hb2, he2, ht2⟩ := searchL_counts hU ω fts m1.1 request.message 0 attemptLimit m1.2 g1.1 m2 h2
    have hm3 := fixed_expose_mem _ _ fts _ m2.2 m3 h3
    have hr4 := finishL_state hU ω fts request m1.1 m2.1 m3.2 r hr
    rw [hr4, hm3]
    refine ⟨hb2.trans k1.1, ?_, fun x hx => ?_⟩
    · change (m2.2.memory.exposures ++ (m2.1.map Prod.snd).toList).length ≤ s.memory.exposures.length + 1
      rw [List.length_append, he2, k1.2.1]
      cases m2.1 <;> simp
    · change x ∈ m2.2.memory.trials at hx
      rcases ht2 x hx with hx | hx
      · rw [k1.2.2] at hx
        exact Or.inl hx
      · rw [hv1] at hx
        exact Or.inr (queried_sign_search hU ω fts published request hc x hx)
  · rw [if_neg hc] at hr
    rw [runL_pure_nonzero _ fts _ s r hr]
    exact ⟨rfl, Nat.le_succ _, fun x hx => Or.inl hx⟩

/-- A public query: at most one birth; exposures and trial rows kept. -/
theorem hashL_counts (fts : FtsCoord → Digest) (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (hashL hU ω x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  unfold hashL at hr
  cases hd : decodeProbe x with
  | some p =>
      rw [hd] at hr
      dsimp only at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
      rw [runL_pure_nonzero _ fts _ _ r hr, fixed_guess_state _ _ fts p s m1 h1]
      exact ⟨Nat.le_succ _, rfl, rfl⟩
  | none =>
      rw [hd] at hr
      dsimp only at hr
      by_cases hx : x ∈ digestInputs
      · rw [if_pos hx] at hr
        exact fixed_birth_counts _ _ fts x s r hr
      · rw [if_neg hx] at hr
        rw [runL_pure_nonzero _ fts _ s r hr]
        exact ⟨Nat.le_succ _, rfl, rfl⟩

/-- The counting ghosts of an adversary interaction. -/
theorem interactionL_counts (fts : FtsCoord → Digest) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory)
    (r : (α × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (interactionL hU ω published program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.2.length ∧
      r.2.memory.exposures.length ≤ s.memory.exposures.length + r.1.2.1.length ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts) (FullGame.authenticatedSign published entry.1) := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [interactionL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨by simp, by simp, fun x hx => Or.inl hx⟩
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        have hm := fixed_coin_state _ _ fts n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [interactionL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω fts x s m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, ?_, fun y hy => ?_⟩
        · change m2.2.memory.births.length ≤ s.memory.births.length + (m2.1.2.2.length + 1)
          omega
        · rw [he1] at i2
          exact i2
        · rcases i3 y hy with hy | hy
          · rw [ht1] at hy
            exact Or.inl hy
          · exact Or.inr hy
      · rw [interactionL_request] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := signL_counts hU ω fts published request s hs m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, ?_, fun y hy => ?_⟩
        · rw [hb1] at i1
          exact i1
        · change m2.2.memory.exposures.length ≤ s.memory.exposures.length + (m2.1.2.1.length + 1)
          omega
        · rcases i3 y hy with hy | ⟨entry, he, hq⟩
          · rcases ht1 y hy with hy | hq
            · exact Or.inl hy
            · exact Or.inr ⟨⟨request, m1.1⟩, List.mem_cons_self, hq⟩
          · exact Or.inr ⟨entry, List.mem_cons_of_mem _ he, hq⟩

/-- The counting ghosts of a T3 program (the verdict). -/
theorem programL_counts (fts : FtsCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (programL hU ω program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.length ∧
      r.2.memory.exposures = s.memory.exposures ∧ r.2.memory.trials = s.memory.trials := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨by simp, rfl, rfl⟩
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        have hm := fixed_coin_state _ _ fts n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω fts x s m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, i2.trans he1, i3.trans ht1⟩
        change m2.2.memory.births.length ≤ s.memory.births.length + (m2.1.2.length + 1)
        omega
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr

/-- **G2/G3/G5** on the eager run of the lazy world. -/
theorem worldGameL_counts (fts : FtsCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.memory.births.length ≤ r.1.2.2.length ∧
      (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
        SecurityExtraction.queried (Omega.answers hU ω fts)
          (FullGame.authenticatedSign (evalWithAnswerFn (Omega.answers hU ω fts) keygen).2 entry.1)) ∧
      r.2.memory.exposures.length ≤ r.1.2.1.length := by
  unfold worldGameL worldGameCore at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ initL r hr
  obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
  rw [runL_pure_nonzero _ fts _ _ r hr]
  have g1 := run_good _ _ fts _ initL (good_empty _ _) m1 h1
  obtain ⟨i1, i2, i3⟩ := interactionL_counts hU ω fts _ _ initL (good_empty _ _) m1 h1
  obtain ⟨p1, p2, p3⟩ := programL_counts hU ω fts _ m1.2 g1.1 m2 h2
  have h0 : initL.memory = LazyMem.empty := rfl
  rw [h0] at i1 i2 i3
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · change m2.2.memory.births.length ≤ (m1.1.2.2 ++ m2.1.2).length
    rw [List.length_append]
    change m1.2.memory.births.length ≤ 0 + m1.1.2.2.length at i1
    omega
  · change x ∈ m2.2.memory.trials at hx
    rw [p3] at hx
    rcases i3 x hx with hx | hx
    · exact absurd hx (List.not_mem_nil)
    · rw [keygen_answers hU ω fts]
      exact hx
  · change m2.2.memory.exposures.length ≤ m1.1.2.1.length
    rw [p2]
    change m1.2.memory.exposures.length ≤ 0 + m1.1.2.1.length at i2
    omega

end Programs

section Bank

/-- **The bank's ghost facts** (§8.3 `worldGameL_ghosts`, `worldGameL_tracking`, CC-4's G2/G3/G5), in the shape of
CC's `BPairGhosts`. -/
theorem worldGameL_bank (adversary : AdversaryP) (ω : Omega (Wots.referenceInputs adversary))
    (fts : FtsCoord → Digest) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) fts
      (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        signedOutput (Omega.answers (canon_subset adversary) ω fts) entry.1.message σ = some output →
          output ∈ r.2.memory.exposures) ∧
    (∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)) ∧
    (∀ f, GuessedIn (Omega.answers (canon_subset adversary) ω fts) r.1.2.1 r.1.2.2 f → f ∈ r.2.guesses) ∧
    r.2.memory.births.length ≤ r.1.2.2.length ∧
    (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
      SecurityExtraction.queried (Omega.answers (canon_subset adversary) ω fts)
        (FullGame.authenticatedSign (evalWithAnswerFn (Omega.answers (canon_subset adversary) ω fts) keygen).2
          entry.1)) ∧
    r.2.memory.exposures.length ≤ r.1.2.1.length := by
  obtain ⟨g1, g2⟩ := worldGameL_ghosts (canon_subset adversary) ω fts adversary r hr
  obtain ⟨c1, c2, c3⟩ := worldGameL_counts (canon_subset adversary) ω fts adversary r hr
  exact ⟨g1, g2, (worldGameL_tracking (canon_subset adversary) ω fts adversary r hr).2, c1, c2, c3⟩

end Bank

end SigGolfCandidate.T3.Security.BPair
