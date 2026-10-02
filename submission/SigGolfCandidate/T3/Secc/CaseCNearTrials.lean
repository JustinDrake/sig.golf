import SigGolfCandidate.T3.Secc.CaseCNearBPair

/-!
# Stream CC: CC-4's G3 — every signer trial row of the eager lazy world is an honest signer digest query

* `digestSearch_reaches`: the honest digest search queries every trial row it reaches;
* `digestSearch_sub_signer`: the honest digest search of a published request (honest nonce) is part of the honest
  authenticated signer's queries;
* `searchL_trials`: a world search adds only reached trial rows (consistent rows = the table's values);
* `signL_trials`, `interactionL_trials`, `programL_trials`, **`bpairTrials`**.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The honest side -/

theorem digestSearch_reaches (A : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start c, start ≤ c → c < start + fuel →
      (∀ c', start ≤ c' → c' < c →
        admissible (selections (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c')))) = false) →
      (.inl (.inr (Sampling.digestTrial rho m c)) : T3.Spec.Domain) ∈ queried A (digestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start c h1 h2; omega
  | succ fuel ih =>
      intro start c h1 h2 hrej
      rw [BPB.digestSearch_succ, queried_bind, BPB.queried_digest]
      by_cases hc : c = start
      · subst hc
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        have hadm := hrej start le_rfl (by omega)
        rw [if_neg (by rw [hadm]; decide)]
        exact ih (start + 1) c (by omega) (by omega) fun c' h1' h2' => hrej c' (by omega) h2'

theorem digestSearch_sub_signer (A : Correctness.Answers) (published : T3.Cache) (request : Request)
    (hc : request.cache = published) (x : T3.Spec.Domain)
    (hx : x ∈ queried A (digestSearch (evalWithAnswerFn A (privateNonce request.message)) request.message 0
      attemptLimit)) :
    x ∈ queried A (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  rw [queried_bind, BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc, signPayload_factor, queried_bind, BPB.queried_privateNonce]
  apply List.mem_append_right
  rw [queried_bind]
  exact List.mem_append_left _ hx

/-! ## The world search -/

section World
variable (D : BPair.digestInputs → HashOutput) (Nn : Message → Digest) (fts : BPair.FtsCoord → Digest)

theorem searchL_trials (rho : Digest) (m : Message) :
    ∀ fuel c s r, SecretGuessObservation.runWith (implE D Nn fts) (BPair.searchL rho m c fuel) s r ≠ 0 →
      BPair.Consistent D Nn s.memory →
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ ∃ c', c ≤ c' ∧ c' < c + fuel ∧
        x = Sampling.digestTrial rho m c' ∧
        ∀ c'', c ≤ c'' → c'' < c' → admissible (selections (BPair.rowVal D (Sampling.digestTrial rho m c''))) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr _ x hx
      change SecretGuessObservation.runWith (implE D Nn fts) (pure none) s r ≠ 0 at hr
      rw [runE_pure_nonzero D Nn fts _ s r hr] at hx
      exact Or.inl hx
  | succ fuel ih =>
      intro c s r hr hcons x hx
      rw [searchL_succ] at hr
      obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := auxE_nonzero D Nn fts (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hres' : res ∈ ((BPair.envE D Nn).auxiliary s (.trial (Sampling.digestTrial rho m c))).support :=
        (PMF.mem_support_iff _ _).mpr hres
      change res ∈ (BPair.rowStep s.memory (Sampling.digestTrial rho m c) false _).support at hres'
      -- the trial step: the answer is the table's, the row is recorded as a trial
      have hstep : res.1 = BPair.rowVal D (Sampling.digestTrial rho m c) ∧
          res.2.trials = s.memory.trials ++ [Sampling.digestTrial rho m c] ∧ BPair.Consistent D Nn res.2 := by
        unfold BPair.rowStep at hres'
        cases hx0 : s.memory.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx0] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨hcons.1 _ a hx0, rfl, hcons⟩
        | none =>
            simp only [hx0] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            change res ∈ ((fun a => (a, s.memory.readRow (Sampling.digestTrial rho m c) a false)) <$>
              (pure (BPair.rowVal D (Sampling.digestTrial rho m c)) : PMF HashOutput)).support at hres'
            rw [map_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            refine ⟨rfl, rfl, ?_, hcons.2⟩
            intro y b hy
            simp only [BPair.LazyMem.readRow] at hy
            by_cases he : y = Sampling.digestTrial rho m c
            · subst he
              rw [QueryCache.cacheQuery_self] at hy
              exact (Option.some.inj hy).symm
            · rw [QueryCache.cacheQuery_of_ne _ _ he] at hy
              exact hcons.1 y b hy
      obtain ⟨hans, htr, hcons1⟩ := hstep
      dsimp only at hr
      by_cases had : admissible (selections res.1) = true
      · rw [if_pos had] at hr
        rw [runE_pure_nonzero D Nn fts _ _ r hr] at hx
        change x ∈ res.2.trials at hx
        rw [htr, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr ⟨c, le_rfl, by omega, hx, fun c'' h1 h2 => by omega⟩
      · rw [if_neg had] at hr
        rcases ih (c + 1) _ r hr hcons1 x hx with hx' | ⟨c', h1, h2, h3, h4⟩
        · change x ∈ res.2.trials at hx'
          rw [htr, List.mem_append, List.mem_singleton] at hx'
          rcases hx' with hx' | hx'
          · exact Or.inl hx'
          · exact Or.inr ⟨c, le_rfl, by omega, hx', fun c'' h1 h2 => by omega⟩
        · refine Or.inr ⟨c', by omega, by omega, h3, fun c'' h1' h2' => ?_⟩
          by_cases hc'' : c'' = c
          · subst hc''
            rw [← hans]
            simpa using had
          · exact h4 c'' (by omega) h2'

end World

/-! ## Trials of the world handlers -/

section Handlers
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U) (fts : BPair.FtsCoord → Digest)

theorem coinE_memory (n : Nat) (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts) (BPair.coinReqL n) s r ≠ 0) :
    r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero _ _ fts (.coin n) s r hr
  have hres' : res ∈ ((BPair.envE (BPair.digestOf ω) (BPair.nonceOf ω)).auxiliary s (.coin n)).support :=
    (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl

/-- A public query records no trial. -/
theorem hashL_trials (x : HashInput) (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts) (BPair.hashL hU ω x) s r ≠ 0) :
    r.2.memory.trials = s.memory.trials := by
  unfold BPair.hashL at hr
  cases hd : BPair.decodeProbe x with
  | some p =>
      rw [hd] at hr
      obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
      rw [runE_pure_nonzero _ _ fts _ _ r hr]
      rw [secretE_memory _ _ fts (.inl p) s mid hmid]
  | none =>
      rw [hd] at hr
      simp only at hr
      split_ifs at hr with hdi
      · obtain ⟨res, hres, rfl⟩ := auxE_nonzero _ _ fts (.birth x) s r hr
        have hres' : res ∈ ((BPair.envE (BPair.digestOf ω) (BPair.nonceOf ω)).auxiliary s (.birth x)).support :=
          (PMF.mem_support_iff _ _).mpr hres
        change res ∈ (BPair.rowStep s.memory x true _).support at hres'
        unfold BPair.rowStep at hres'
        cases hx0 : s.memory.rows x with
        | some a =>
            simp only [hx0] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            rfl
        | none =>
            simp only [hx0] at hres'
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            rfl
      · rw [runE_pure_nonzero _ _ fts _ _ r hr]

theorem nonce_step (m : Message) (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts) (BPair.nonceReq m) s r ≠ 0) :
    r.2.memory.nonces m = some r.1 ∧ r.2.memory.trials = s.memory.trials := by
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero _ _ fts (.nonce m) s r hr
  have hres' : res ∈ ((BPair.envE (BPair.digestOf ω) (BPair.nonceOf ω)).auxiliary s (.nonce m)).support :=
    (PMF.mem_support_iff _ _).mpr hres
  change res ∈ (BPair.nonceStep s.memory m _).support at hres'
  unfold BPair.nonceStep at hres'
  cases hn : s.memory.nonces m with
  | some v =>
      simp only [hn] at hres'
      rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
      subst hres'
      exact ⟨hn, rfl⟩
  | none =>
      simp only [hn] at hres'
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
      obtain ⟨v, -, rfl⟩ := hres'
      exact ⟨by simp [BPair.LazyMem.drawNonce], rfl⟩

theorem expose_trials (o : Option HashOutput) (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts) (BPair.exposeReq o) s r ≠ 0) :
    r.2.memory.trials = s.memory.trials := by
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero _ _ fts (.expose o) s r hr
  have hres' : res ∈ ((BPair.envE (BPair.digestOf ω) (BPair.nonceOf ω)).auxiliary s (.expose o)).support :=
    (PMF.mem_support_iff _ _).mpr hres
  change res ∈ (pure ((), s.memory.expose o) : PMF _).support at hres'
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
  subst hres'
  rfl

theorem mapM_disclose_memory (l : List BPair.FtsCoord) (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts)
      (l.mapM BPair.discloseReq) s r ≠ 0) : r.2.memory = s.memory := by
  induction l generalizing s r with
  | nil =>
      change SecretGuessObservation.runWith _ (pure []) s r ≠ 0 at hr
      rw [runE_pure_nonzero _ _ fts _ _ r hr]
  | cons a l ih =>
      rw [List.mapM_cons] at hr
      obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
      obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid.2 r hr
      rw [runE_pure_nonzero _ _ fts _ _ r hr]
      exact (ih mid.2 mid2 hmid2).trans (secretE_memory _ _ fts (.inr a) s mid hmid)

theorem finishL_memory (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput))
    (s : BPair.WStateL) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts)
      (BPair.finishL hU ω request rho found) s r ≠ 0) : r.2.memory = s.memory := by
  rcases found with _ | ⟨c, output⟩
  · change SecretGuessObservation.runWith _ (pure none) s r ≠ 0 at hr
    rw [runE_pure_nonzero _ _ fts _ _ r hr]
  · simp only [BPair.finishL] at hr
    revert hr
    generalize BPair.signerForest hU ω output = sf
    generalize BPair.signerLayers hU ω request output = g
    intro hr
    cases g with
    | none => rw [runE_pure_nonzero _ _ fts _ _ r hr]
    | some pieces =>
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        rw [runE_pure_nonzero _ _ fts _ _ r hr]
        exact mapM_disclose_memory ω fts _ s mid hmid

end Handlers

/-! ## G3 -/

section G3
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U) (fts : BPair.FtsCoord → Digest)

theorem good_step {β : Type} (W : OracleComp BPair.WSpecL β) (s : BPair.WStateL)
    (hs : BPair.Good (BPair.digestOf ω) (BPair.nonceOf ω) s.memory) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts) W s r ≠ 0) :
    BPair.Good (BPair.digestOf ω) (BPair.nonceOf ω) r.2.memory :=
  (BPair.run_good (BPair.digestOf ω) (BPair.nonceOf ω) fts W s hs r hr).1

/-- **A signing records only honest signer digest queries of its own request as trials.** -/
theorem signL_trials (published : T3.Cache) (request : Request) (s : BPair.WStateL)
    (hs : BPair.Good (BPair.digestOf ω) (BPair.nonceOf ω) s.memory) (r)
    (hr : SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts)
      (BPair.signL hU ω published request) s r ≠ 0) :
    ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : T3.Spec.Domain) ∈
      queried (BPair.Omega.answers hU ω fts) (FullGame.authenticatedSign published request) := by
  intro x hx
  unfold BPair.signL at hr
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte] at hr
    rw [runE_pure_nonzero _ _ fts _ _ r hr] at hx
    exact Or.inl hx
  simp only [hc, ↓reduceIte] at hr
  obtain ⟨mid1, hmid1, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
  obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid1.2 r hr
  obtain ⟨mid3, hmid3, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid2.2 r hr
  have hfin := finishL_memory hU ω fts request mid1.1 mid2.1 mid3.2 r hr
  have hexp := expose_trials ω fts _ mid2.2 mid3 hmid3
  obtain ⟨hnon, htr1⟩ := nonce_step ω fts request.message s mid1 hmid1
  have hgood1 := good_step ω fts _ s hs mid1 hmid1
  have hrho : mid1.1 = BPair.nonceOf ω request.message := hgood1.1.2 _ _ hnon
  rw [hfin, hexp] at hx
  rcases searchL_trials _ _ fts mid1.1 request.message attemptLimit 0 mid1.2 mid2 hmid2 hgood1.1 x hx with
    hx' | ⟨c', -, hc', rfl, hrej⟩
  · rw [htr1] at hx'
    exact Or.inl hx'
  · right
    apply digestSearch_sub_signer _ published request hc
    rw [BPair.eval_nonce hU ω fts, ← hrho]
    apply digestSearch_reaches _ _ _ attemptLimit 0 c' (Nat.zero_le _) (by omega)
    intro c'' h1 h2
    have h := hrej c'' h1 h2
    have hval : evalWithAnswerFn (BPair.Omega.answers hU ω fts) (digest mid1.1 request.message (BitVec.ofNat 32 c'')) =
        BPair.rowVal (BPair.digestOf ω) (Sampling.digestTrial mid1.1 request.message c'') :=
      BPair.answers_digest hU ω fts _ (BPair.digestInput_mem _ _ _)
    rw [hval]
    exact h

/-- **The interaction records only honest signer digest queries of logged requests as trials.** -/
theorem interactionL_trials (published : T3.Cache) {α : Type} (oa : OracleComp LazyPrivate.Interaction α) :
    ∀ s r, SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts)
      (BPair.interactionL hU ω published oa) s r ≠ 0 →
      BPair.Good (BPair.digestOf ω) (BPair.nonceOf ω) s.memory →
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
        queried (BPair.Omega.answers hU ω fts) (FullGame.authenticatedSign published entry.1) := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      intro s r hr _ x hx
      rw [interactionL_pure] at hr
      rw [runE_pure_nonzero _ _ fts _ s r hr] at hx
      exact Or.inl hx
  | query_bind input next ih =>
      intro s r hr hs x hx
      rcases input with (n | y) | request
      · rw [interactionL_coin] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        have hm := coinE_memory ω fts n s mid hmid
        rcases ih mid.1 mid.2 r hr (by rw [hm]; exact hs) x hx with h | h
        · rw [hm] at h; exact Or.inl h
        · exact Or.inr h
      · rw [interactionL_public] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid.2 r hr
        rw [runE_pure_nonzero _ _ fts _ _ r hr] at hx ⊢
        have ht := hashL_trials hU ω fts y s mid hmid
        rcases ih mid.1 mid.2 mid2 hmid2 (good_step ω fts _ s hs mid hmid) x hx with h | h
        · rw [ht] at h; exact Or.inl h
        · exact Or.inr h
      · rw [interactionL_request] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid.2 r hr
        rw [runE_pure_nonzero _ _ fts _ _ r hr] at hx ⊢
        rcases ih mid.1 mid.2 mid2 hmid2 (good_step ω fts _ s hs mid hmid) x hx with h | ⟨entry, he, hq⟩
        · rcases signL_trials hU ω fts published request s hs mid hmid x h with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨⟨request, mid.1⟩, List.mem_cons_self, h'⟩
        · exact Or.inr ⟨entry, List.mem_cons_of_mem _ he, hq⟩

theorem programL_trials {β : Type} (program : M β) :
    ∀ s r, SecretGuessObservation.runWith (implE (BPair.digestOf ω) (BPair.nonceOf ω) fts)
      (BPair.programL hU ω program) s r ≠ 0 → r.2.memory.trials = s.memory.trials := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro s r hr
      rw [programL_pure] at hr
      rw [runE_pure_nonzero _ _ fts _ s r hr]
  | query_bind input next ih =>
      intro s r hr
      rcases input with (n | y) | c
      · rw [programL_coin] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        rw [ih mid.1 mid.2 r hr, coinE_memory ω fts n s mid hmid]
      · rw [programL_public] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid.2 r hr
        rw [runE_pure_nonzero _ _ fts _ _ r hr]
        exact (ih mid.1 mid.2 mid2 hmid2).trans (hashL_trials hU ω fts y s mid hmid)
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s r hr

end G3

/-- **CC-4's G3, proved.** -/
theorem bpairTrials : BPairTrials := by
  intro adversary ω fts r hr _ x hx
  unfold fixedL BPair.worldGameL BPair.worldGameCore at hr
  obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero _ _ fts _ _ _ r hr
  obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero _ _ fts _ _ mid.2 r hr
  rw [runE_pure_nonzero _ _ fts _ _ r hr] at hx ⊢
  have ht := programL_trials (BPair.canon_subset adversary) ω fts _ mid.2 mid2 hmid2
  change x ∈ mid2.2.memory.trials at hx
  rw [ht] at hx
  rcases interactionL_trials (BPair.canon_subset adversary) ω fts _ _ BPair.initL mid hmid
    (BPair.good_empty _ _) x hx with h | ⟨entry, he, hq⟩
  · simp [BPair.initL, SecretGuessObservation.initialState, BPair.LazyMem.empty] at h
  · refine ⟨entry, he, ?_⟩
    rw [BPair.keygen_answers (BPair.canon_subset adversary) ω fts]
    exact hq

/-- **The small route, from B-PAIR's compiled §8 and CC's proofs only.** -/
theorem small_route_near_world :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_of_trials bpairTrials

end SigGolfCandidate.T3.Security.CaseC
