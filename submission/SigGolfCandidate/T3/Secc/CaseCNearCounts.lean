import SigGolfCandidate.T3.Secc.CaseCNearLink

/-!
# Stream CC: births and exposures are counted by the entries and the log (CC-4's G2 and G5)

On every eager fixed run of the lazy world (`fixedRun (envE D Nn) fts`), a world game's births are at most its
entries (each birth is an adversary/verifier public read, recorded as an entry) and its exposures at most its log
(each published signing exposes at most one output and is one log entry):

* `interactionL_counts` / `programL_counts` / `worldGameCore_counts`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Counts
variable (D : BPair.digestInputs → HashOutput) (Nn : Message → Digest) (fts : BPair.FtsCoord → Digest)

/-- The eager fixed implementation. -/
noncomputable abbrev implE := SecretGuessObservation.fixedImpl (BPair.envE D Nn) fts

theorem runE_bind_nonzero {β γ : Type} (W : OracleComp BPair.WSpecL β) (K : β → OracleComp BPair.WSpecL γ)
    (s : BPair.WStateL) (r : γ × BPair.WStateL)
    (hr : SecretGuessObservation.runWith (implE D Nn fts) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith (implE D Nn fts) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith (implE D Nn fts) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr

theorem runE_pure_nonzero {β : Type} (b : β) (s : BPair.WStateL) (r : β × BPair.WStateL)
    (hr : SecretGuessObservation.runWith (implE D Nn fts) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr

theorem auxE_nonzero (i : BPair.AuxL) (s : BPair.WStateL) (r : BPair.AuxSpecL.Range i × BPair.WStateL)
    (hr : SecretGuessObservation.runWith (implE D Nn fts) (liftM (BPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, (BPair.envE D Nn).auxiliary s i res ≠ 0 ∧ r = (res.1, { s with memory := res.2 }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.fixedImpl, StateT.run_mk] at hr
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  exact ⟨res, by simpa [SPMF.liftM_apply] using hres, hr⟩

theorem secretE_memory (p : (BPair.FtsCoord × Digest) ⊕ BPair.FtsCoord) (s : BPair.WStateL)
    (r : (BPair.WSpecL.Range (.inr p)) × BPair.WStateL)
    (hr : SecretGuessObservation.runWith (implE D Nn fts) (liftM (BPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · simp only [SecretGuessObservation.fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff,
      not_not] at hr
    rw [hr]
    rfl
  · simp only [SecretGuessObservation.fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff,
      not_not] at hr
    rw [hr]
    rfl

/-- `μ` does not grow along `W`, and `ν` grows by at most `c` of the result. -/
def Counted {β : Type} (W : OracleComp BPair.WSpecL β) (cB cE : β → Nat) : Prop :=
  ∀ s r, SecretGuessObservation.runWith (implE D Nn fts) W s r ≠ 0 →
    r.2.memory.births.length ≤ s.memory.births.length + cB r.1 ∧
      r.2.memory.exposures.length ≤ s.memory.exposures.length + cE r.1

theorem counted_memory {β : Type} (W : OracleComp BPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implE D Nn fts) W s r ≠ 0 → r.2.memory = s.memory) :
    Counted D Nn fts W (fun _ => 0) (fun _ => 0) := by
  intro s r hr
  rw [h s r hr]
  simp

theorem counted_pure {β : Type} (b : β) : Counted D Nn fts (pure b : OracleComp BPair.WSpecL β) (fun _ => 0) (fun _ => 0) :=
  counted_memory D Nn fts _ fun s r hr => by rw [runE_pure_nonzero D Nn fts b s r hr]

theorem counted_coin (n : Nat) : Counted D Nn fts (BPair.coinReqL n) (fun _ => 0) (fun _ => 0) := by
  apply counted_memory
  intro s r hr
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero D Nn fts (.coin n) s r hr
  have hres' : res ∈ ((BPair.envE D Nn).auxiliary s (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl

/-- A row step: births grow by at most one (and not at all for signer trials); exposures unchanged. -/
theorem rowStep_counts (mem : BPair.LazyMem) (x : HashInput) (isBirth : Bool) (src : PMF HashOutput)
    (res : HashOutput × BPair.LazyMem) (h : res ∈ (BPair.rowStep mem x isBirth src).support) :
    res.2.births.length ≤ mem.births.length + (if isBirth then 1 else 0) ∧
      res.2.exposures.length = mem.exposures.length := by
  unfold BPair.rowStep at h
  cases hx : mem.rows x with
  | some a =>
      simp only [hx] at h
      rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at h
      subst h
      cases isBirth <;> simp [BPair.LazyMem.replayRow]
  | none =>
      simp only [hx] at h
      split_ifs at h
      · rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at h
        obtain ⟨a, -, rfl⟩ := h
        cases isBirth <;> simp [BPair.LazyMem.readRow]
      · rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at h
        subst h
        cases isBirth <;> simp [BPair.LazyMem.replayRow]

theorem counted_bind_const {β γ : Type} {W : OracleComp BPair.WSpecL β} {K : β → OracleComp BPair.WSpecL γ}
    {a b a' b' : Nat} (hW : Counted D Nn fts W (fun _ => a) (fun _ => b))
    (hK : ∀ x, Counted D Nn fts (K x) (fun _ => a') (fun _ => b')) :
    Counted D Nn fts (W >>= K) (fun _ => a + a') (fun _ => b + b') := by
  intro s r hr
  obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts W K s r hr
  obtain ⟨h1, h2⟩ := hW s mid hmid
  obtain ⟨h3, h4⟩ := hK mid.1 mid.2 r hr
  exact ⟨by simp only at h1 h3 ⊢; omega, by simp only at h2 h4 ⊢; omega⟩

theorem counted_mono {β : Type} {W : OracleComp BPair.WSpecL β} {cB cE cB' cE' : β → Nat}
    (h : Counted D Nn fts W cB cE) (hB : ∀ x, cB x ≤ cB' x) (hE : ∀ x, cE x ≤ cE' x) :
    Counted D Nn fts W cB' cE' := by
  intro s r hr
  obtain ⟨h1, h2⟩ := h s r hr
  exact ⟨h1.trans (Nat.add_le_add_left (hB _) _), h2.trans (Nat.add_le_add_left (hE _) _)⟩

theorem counted_aux_row (x : HashInput) (isBirth : Bool) (i : BPair.AuxL)
    (hi : i = .birth x ∧ isBirth = true ∨ i = .trial x ∧ isBirth = false) :
    Counted D Nn fts (liftM (BPair.WSpecL.query (.inl i))) (fun _ => if isBirth then 1 else 0) (fun _ => 0) := by
  intro s r hr
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero D Nn fts i s r hr
  have hres' : res ∈ ((BPair.envE D Nn).auxiliary s i).support := (PMF.mem_support_iff _ _).mpr hres
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change res ∈ (BPair.rowStep s.memory x true _).support at hres'
    obtain ⟨h1, h2⟩ := rowStep_counts s.memory x true _ res hres'
    exact ⟨h1, by simp only; omega⟩
  · change res ∈ (BPair.rowStep s.memory x false _).support at hres'
    obtain ⟨h1, h2⟩ := rowStep_counts s.memory x false _ res hres'
    exact ⟨h1, by simp only; omega⟩

theorem counted_birth (x : HashInput) : Counted D Nn fts (BPair.birthReq x) (fun _ => 1) (fun _ => 0) :=
  counted_aux_row D Nn fts x true _ (Or.inl ⟨rfl, rfl⟩)

theorem counted_trial (x : HashInput) :
    Counted D Nn fts (liftM (BPair.WSpecL.query (.inl (.trial x)))) (fun _ => 0) (fun _ => 0) :=
  counted_aux_row D Nn fts x false _ (Or.inr ⟨rfl, rfl⟩)

theorem counted_secret (p : (BPair.FtsCoord × Digest) ⊕ BPair.FtsCoord) :
    Counted D Nn fts (liftM (BPair.WSpecL.query (.inr p))) (fun _ => 0) (fun _ => 0) :=
  counted_memory D Nn fts _ fun s r hr => secretE_memory D Nn fts p s r hr

theorem counted_hashL {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U) (x : HashInput) :
    Counted D Nn fts (BPair.hashL hU ω x) (fun _ => 1) (fun _ => 0) := by
  unfold BPair.hashL
  cases BPair.decodeProbe x with
  | some p =>
      exact counted_mono D Nn fts (counted_bind_const D Nn fts (counted_secret D Nn fts (.inl p))
        fun _ => counted_pure D Nn fts _) (fun _ => by omega) (fun _ => le_rfl)
  | none =>
      simp only
      split_ifs
      · exact counted_birth D Nn fts x
      · exact counted_mono D Nn fts (counted_pure D Nn fts _) (fun _ => by omega) (fun _ => le_rfl)

theorem counted_searchL (rho : Digest) (m : Message) :
    ∀ fuel c, Counted D Nn fts (BPair.searchL rho m c fuel) (fun _ => 0) (fun _ => 0) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact counted_pure D Nn fts _
  | succ fuel ih =>
      intro c
      rw [searchL_succ]
      exact counted_mono D Nn fts (counted_bind_const D Nn fts (counted_trial D Nn fts (Sampling.digestTrial rho m c))
        (K := fun output => if admissible (selections output) = true then pure (some (BitVec.ofNat 32 c, output))
          else BPair.searchL rho m (c + 1) fuel) (a' := 0) (b' := 0) (fun output => by
          by_cases had : admissible (selections output) = true
          · simp only [had, if_true]; exact counted_pure D Nn fts _
          · simp only [had, Bool.false_eq_true, if_false]; exact ih (c + 1)))
        (fun _ => le_of_eq (by simp)) (fun _ => le_of_eq (by simp))

theorem counted_nonce (m : Message) : Counted D Nn fts (BPair.nonceReq m) (fun _ => 0) (fun _ => 0) := by
  intro s r hr
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero D Nn fts (.nonce m) s r hr
  have hres' : res ∈ ((BPair.envE D Nn).auxiliary s (.nonce m)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ (BPair.nonceStep s.memory m _).support at hres'
  unfold BPair.nonceStep at hres'
  cases hn : s.memory.nonces m with
  | some v =>
      simp only [hn] at hres'
      rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
      subst hres'
      simp
  | none =>
      simp only [hn] at hres'
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
      obtain ⟨v, -, rfl⟩ := hres'
      simp [BPair.LazyMem.drawNonce]

theorem counted_expose (o : Option HashOutput) : Counted D Nn fts (BPair.exposeReq o) (fun _ => 0) (fun _ => 1) := by
  intro s r hr
  obtain ⟨res, hres, rfl⟩ := auxE_nonzero D Nn fts (.expose o) s r hr
  have hres' : res ∈ ((BPair.envE D Nn).auxiliary s (.expose o)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ (pure ((), s.memory.expose o) : PMF _).support at hres'
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
  subst hres'
  refine ⟨by simp [BPair.LazyMem.expose], ?_⟩
  simp only [BPair.LazyMem.expose, List.length_append]
  cases o <;> simp

theorem counted_mapM_disclose (l : List BPair.FtsCoord) :
    Counted D Nn fts (l.mapM BPair.discloseReq) (fun _ => 0) (fun _ => 0) := by
  induction l with
  | nil => exact counted_pure D Nn fts _
  | cons a l ih =>
      rw [List.mapM_cons]
      exact counted_mono D Nn fts (counted_bind_const D Nn fts (counted_secret D Nn fts (.inr a))
        fun _ => counted_bind_const D Nn fts ih fun _ => counted_pure D Nn fts _)
        (fun _ => le_of_eq (by simp)) (fun _ => le_of_eq (by simp))

theorem counted_finishL {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    Counted D Nn fts (BPair.finishL hU ω request rho found) (fun _ => 0) (fun _ => 0) := by
  rcases found with _ | ⟨c, output⟩
  · exact counted_pure D Nn fts _
  · simp only [BPair.finishL]
    generalize BPair.signerForest hU ω output = sf
    generalize BPair.signerLayers hU ω request output = g
    cases g with
    | none => exact counted_pure D Nn fts _
    | some pieces =>
        exact counted_mono D Nn fts (counted_bind_const D Nn fts (counted_mapM_disclose D Nn fts _)
          fun _ => counted_pure D Nn fts _) (fun _ => le_of_eq (by simp)) (fun _ => le_of_eq (by simp))

theorem counted_signL {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (published : T3.Cache) (request : Request) :
    Counted D Nn fts (BPair.signL hU ω published request) (fun _ => 0) (fun _ => 1) := by
  unfold BPair.signL
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte]
    exact counted_mono D Nn fts (counted_pure D Nn fts _) (fun _ => le_rfl) (fun _ => by omega)
  simp only [hc, ↓reduceIte]
  exact counted_mono D Nn fts (counted_bind_const D Nn fts (counted_nonce D Nn fts request.message) fun rho =>
    counted_bind_const D Nn fts (counted_searchL D Nn fts rho request.message attemptLimit 0)
      fun found => counted_bind_const D Nn fts (counted_expose D Nn fts (found.map Prod.snd))
        fun _ => counted_finishL D Nn fts hU ω request rho found) (fun _ => le_of_eq (by simp))
    (fun _ => le_of_eq (by simp))

theorem interactionL_counts {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (published : T3.Cache) {α : Type} (oa : OracleComp LazyPrivate.Interaction α) :
    ∀ s r, SecretGuessObservation.runWith (implE D Nn fts) (BPair.interactionL hU ω published oa) s r ≠ 0 →
      r.2.memory.births.length ≤ s.memory.births.length + r.1.2.2.length ∧
        r.2.memory.exposures.length ≤ s.memory.exposures.length + r.1.2.1.length := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      intro s r hr
      rw [interactionL_pure] at hr
      rw [runE_pure_nonzero D Nn fts _ s r hr]
      simp
  | query_bind input next ih =>
      intro s r hr
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
        obtain ⟨h1, h2⟩ := counted_coin D Nn fts n s mid hmid
        obtain ⟨h3, h4⟩ := ih mid.1 mid.2 r hr
        simp only at h1 h2
        exact ⟨by omega, by omega⟩
      · rw [interactionL_public] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero D Nn fts _ _ mid.2 r hr
        rw [runE_pure_nonzero D Nn fts _ _ r hr]
        obtain ⟨h1, h2⟩ := counted_hashL D Nn fts hU ω x s mid hmid
        obtain ⟨h3, h4⟩ := ih mid.1 mid.2 mid2 hmid2
        simp only [List.length_cons] at h1 h2 ⊢
        exact ⟨by omega, by omega⟩
      · rw [interactionL_request] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero D Nn fts _ _ mid.2 r hr
        rw [runE_pure_nonzero D Nn fts _ _ r hr]
        obtain ⟨h1, h2⟩ := counted_signL D Nn fts hU ω published request s mid hmid
        obtain ⟨h3, h4⟩ := ih mid.1 mid.2 mid2 hmid2
        simp only [List.length_cons] at h1 h2 ⊢
        exact ⟨by omega, by omega⟩

theorem programL_counts {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    {β : Type} (program : M β) :
    ∀ s r, SecretGuessObservation.runWith (implE D Nn fts) (BPair.programL hU ω program) s r ≠ 0 →
      r.2.memory.births.length ≤ s.memory.births.length + r.1.2.length ∧
        r.2.memory.exposures.length ≤ s.memory.exposures.length := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro s r hr
      rw [programL_pure] at hr
      rw [runE_pure_nonzero D Nn fts _ s r hr]
      simp
  | query_bind input next ih =>
      intro s r hr
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
        obtain ⟨h1, h2⟩ := counted_coin D Nn fts n s mid hmid
        obtain ⟨h3, h4⟩ := ih mid.1 mid.2 r hr
        simp only at h1 h2
        exact ⟨by omega, by omega⟩
      · rw [programL_public] at hr
        obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ s r hr
        obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero D Nn fts _ _ mid.2 r hr
        rw [runE_pure_nonzero D Nn fts _ _ r hr]
        obtain ⟨h1, h2⟩ := counted_hashL D Nn fts hU ω x s mid hmid
        obtain ⟨h3, h4⟩ := ih mid.1 mid.2 mid2 hmid2
        simp only [List.length_cons] at h1 h2 ⊢
        exact ⟨by omega, by omega⟩
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s r hr

/-- **G2 and G5**: births are at most the entries, exposures at most the log. -/
theorem worldGameCore_counts {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (adversary : AdversaryP) (r)
    (hr : SecretGuessObservation.runWith (implE D Nn fts) (BPair.worldGameCore hU ω adversary) BPair.initL r ≠ 0) :
    r.2.memory.births.length ≤ r.1.2.2.length ∧ r.2.memory.exposures.length ≤ r.1.2.1.length := by
  unfold BPair.worldGameCore at hr
  obtain ⟨mid, hmid, hr⟩ := runE_bind_nonzero D Nn fts _ _ _ r hr
  obtain ⟨mid2, hmid2, hr⟩ := runE_bind_nonzero D Nn fts _ _ mid.2 r hr
  rw [runE_pure_nonzero D Nn fts _ _ r hr]
  obtain ⟨h1, h2⟩ := interactionL_counts D Nn fts hU ω _ _ _ mid hmid
  obtain ⟨h3, h4⟩ := programL_counts D Nn fts hU ω _ mid.2 mid2 hmid2
  have h0 : BPair.initL.memory.births.length = 0 := rfl
  have h0' : BPair.initL.memory.exposures.length = 0 := rfl
  simp only [List.length_append]
  exact ⟨by omega, by omega⟩

end Counts

/-- **B-PAIR's remaining ghost facts** (§8.3 `worldGameL_ghosts` and `worldGameL_tracking`, and CC-4's G3). -/
def BPairGhostsCore : Prop :=
  ∀ (adversary : AdversaryP) ω fts r, fixedL adversary ω fts r ≠ 0 →
    let A := BPair.Omega.answers (BPair.canon_subset adversary) ω fts
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        BPair.signedOutput A entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
    (∀ x a, (x, a) ∈ r.1.2.2 → x ∈ BPair.digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)) ∧
    (∀ f, BPair.GuessedIn A r.1.2.1 r.1.2.2 f → f ∈ r.2.guesses) ∧
    (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
      SecurityExtraction.queried A (FullGame.authenticatedSign (evalWithAnswerFn A keygen).2 entry.1))

theorem bpairGhosts_of_core (h : BPairGhostsCore) : BPairGhosts := by
  intro adversary ω fts r hr
  obtain ⟨h1, h2, h3, h4⟩ := h adversary ω fts r hr
  obtain ⟨g2, g5⟩ := worldGameCore_counts (BPair.digestOf ω) (BPair.nonceOf ω) fts (BPair.canon_subset adversary) ω
    adversary r hr
  exact ⟨h1, h2, h3, g2, h4, g5⟩

/-- **The small route from B-PAIR's remaining §8 deliverables.** -/
theorem small_route_of_bpair_core (hchain : BPairNearChain) (hcore : BPairGhostsCore) (hlaw : BPairLaw) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_of_bpair hchain (bpairGhosts_of_core hcore) hlaw

end SigGolfCandidate.T3.Security.CaseC
