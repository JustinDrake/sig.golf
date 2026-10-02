import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.T3.Secc.LargeContactCase
import SigGolfCandidate.T3.Secc.LargeContactCertLeaf

/-!
# LR-34 (certificate coupling): invariants of the router fold of the real run

Deterministic facts about `routerFold` (the router-state fold of a tagged split, honest nonces):

* `coverOk_fold`: every memoized published search result's digest output is exposed or the reuse flag is set
  (CC semantics of `RouterState.signed`), and `memoOk_fold`: memoized results are the honest search results;
* `sign_memo_fold`: after a published signing step its message is memoized (and stays so);
* `exposures_fold_le`: at most one exposure per signing step;
* `trials_fold`: the trial rows of the fold are trial rows of published signing steps;
* `birth_fold`: an adversary/verifier digest row of `U`, never a trial row, always answered `N`, and occurring as a
  public event, is a birth `(X, N)` of the final state;
* `disclosed_steps_mem`: the monitor's disclosures come from signing steps.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactCertFold : DecidableEq T3.Cache := Classical.decEq _

/-- Every memoized search with an output has that output exposed, or the reuse flag is set. -/
def CoverOk (st : RouterState) : Prop :=
  ∀ m c N, st.memo.lookup m = some (some (c, N)) → N ∈ st.exposures ∨ st.reused = true

/-- The number of signing steps of a tagged run. -/
def signCount : List TaggedStep → Nat
  | [] => 0
  | .world _ :: rest => signCount rest
  | .sign _ _ _ :: rest => signCount rest + 1

/-- The signing log of a tagged run. -/
def stepLog : List TaggedStep → QueryLog Requests
  | [] => []
  | .world _ :: rest => stepLog rest
  | .sign request output _ :: rest => ⟨request, output⟩ :: stepLog rest

theorem signCount_eq_length (steps : List TaggedStep) : signCount steps = (stepLog steps).length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [signCount, stepLog, ih]

/-- **The log of a supported tagged record is the log of its signing steps.** -/
theorem taggedRecord_log {α : Type} (program : OracleComp LazyPrivate.Interaction α) (published : T3.Cache)
    (state : LazyPrivate.State) (t : Tagged α) (ht : t ∈ support (taggedRecord published program state)) :
    t.value.2 = stepLog t.steps := by
  induction program using OracleComp.inductionOn generalizing state t with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at ht
      subst ht
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at ht
          obtain ⟨middle, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          exact ih middle.1 middle.2 last hl
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at ht
          obtain ⟨block, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          change ⟨request, block.value⟩ :: last.value.2 = ⟨request, block.value⟩ :: stepLog last.steps
          rw [ih block.value block.state last hl]

theorem sign_mem_stepLog {steps : List TaggedStep} {request : Security.Request} {output : Option Signature}
    {events : List FirstHit.QueryEvent} (h : TaggedStep.sign request output events ∈ steps) :
    (⟨request, output⟩ : (r : Requests.Domain) × Requests.Range r) ∈ stepLog steps := by
  induction steps with
  | nil => cases h
  | cons s rest ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · cases s with
        | world e => exact ih h'
        | sign r o ev => exact List.mem_cons_of_mem _ (ih h')

section Fold
variable (U : Finset HashInput) (A : Answers) (published : T3.Cache)

/-! ## Field lemmas -/

theorem routerEvent_fields (st : RouterState) (e : FirstHit.QueryEvent) :
    (routerEvent U st e).exposures = st.exposures ∧ (routerEvent U st e).reused = st.reused ∧
      (routerEvent U st e).memo = st.memo ∧ (routerEvent U st e).trials = st.trials := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · change (st.next U X y).exposures = _ ∧ (st.next U X y).reused = _ ∧ (st.next U X y).memo = _ ∧
      (st.next U X y).trials = _
    unfold RouterState.next
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem routerEvents_fields (events : List FirstHit.QueryEvent) (st : RouterState) :
    (events.foldl (routerEvent U) st).exposures = st.exposures ∧ (events.foldl (routerEvent U) st).reused = st.reused ∧
      (events.foldl (routerEvent U) st).memo = st.memo ∧ (events.foldl (routerEvent U) st).trials = st.trials := by
  induction events generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := ih (routerEvent U st e)
      obtain ⟨g1, g2, g3, g4⟩ := routerEvent_fields U st e
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

theorem finishState_bank (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState A st1 found).exposures = st1.exposures ∧ (finishState A st1 found).reused = st1.reused ∧
      (finishState A st1 found).memo = st1.memo ∧ (finishState A st1 found).trials = st1.trials := by
  unfold finishState
  cases found with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem signedState_bank (nv : Message → Digest) (st : RouterState) (request : Security.Request) :
    (request.cache = published →
      (signedState A nv published st request).exposures = (startState A nv st request.message).exposures ∧
      (signedState A nv published st request).reused = (startState A nv st request.message).reused ∧
      (signedState A nv published st request).memo = (startState A nv st request.message).memo ∧
      (signedState A nv published st request).trials = (startState A nv st request.message).trials) ∧
    (request.cache ≠ published → signedState A nv published st request = st) := by
  rw [signedState_eq]
  constructor
  · intro hc
    rw [if_pos hc]
    exact finishState_bank A _ _
  · intro hc
    rw [if_neg hc]

/-! ## Memo and coverage -/

theorem signed_memo_lookup (st : RouterState) (rho : Digest) (m m' : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).memo.lookup m' = if m' = m then some found else st.memo.lookup m' := by
  rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons]
  by_cases h : m' = m
  · subst h; simp
  · have hne : (m' == m) = false := by simpa using h
    rw [hne, if_neg h]

theorem signed_exposures_reused (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (∀ N, N ∈ st.exposures → N ∈ (st.signed rho m found).exposures) ∧
      (st.reused = true → (st.signed rho m found).reused = true) ∧
      (∀ c N, found = some (c, N) → N ∈ (st.signed rho m found).exposures ∨ (st.signed rho m found).reused = true) := by
  unfold RouterState.signed
  split_ifs
  · exact ⟨fun N h => h, fun _ => rfl, fun _ _ _ => Or.inr rfl⟩
  · refine ⟨fun N h => List.mem_append_left _ h, fun h => h, fun c N hf => Or.inl ?_⟩
    subst hf
    simp

theorem coverOk_startState (nv : Message → Digest) (st : RouterState) (m : Message) (h : CoverOk st)
    (hmemo : MemoOk A st) : CoverOk (startState A nv st m) ∧ MemoOk A (startState A nv st m) := by
  unfold startState
  split_ifs with hs
  · exact ⟨h, hmemo⟩
  · obtain ⟨hx, hr, hnew⟩ := signed_exposures_reused st (nv m) m (LargeResidual.signDigest A m)
    constructor
    · intro m' c N hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · exact hnew c N (Option.some.inj hl)
      · rcases h m' c N hl with h1 | h1
        · exact Or.inl (hx N h1)
        · exact Or.inr (hr h1)
    · intro m' f hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · subst hm; exact (Option.some.inj hl).symm
      · exact hmemo m' f hl

theorem coverOk_signedState (st : RouterState) (request : Security.Request) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (signedState A (honestNonce A) published st request) := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · obtain ⟨h1, h2, h3, -⟩ := hpub hc
    intro m c N hl
    rw [h1, h2]
    rw [h3] at hl
    exact (coverOk_startState A (honestNonce A) st request.message h hmemo).1 m c N hl
  · rw [hnpub hc]; exact h

theorem coverOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : CoverOk st) : CoverOk (routerEvent U st e) := by
  obtain ⟨h1, h2, h3, -⟩ := routerEvent_fields U st e
  intro m c N hl
  rw [h1, h2]
  rw [h3] at hl
  exact h m c N hl

theorem memoOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : MemoOk A st) : MemoOk A (routerEvent U st e) := by
  intro m f hl
  rw [(routerEvent_fields U st e).2.2.1] at hl
  exact h m f hl

theorem invariants_steps (steps : List TaggedStep) (st : RouterState) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (steps.foldl (routerStep U A (honestNonce A) published) st) ∧
      MemoOk A (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact coverOk_event U st e h
        | sign request out evs => exact coverOk_signedState A published st request h hmemo
      · cases s with
        | world e => exact memoOk_event U A st e hmemo
        | sign request out evs => exact signedState_memo A (honestNonce A) published st request hmemo

theorem invariants_events (events : List FirstHit.QueryEvent) (st : RouterState) (h : CoverOk st)
    (hmemo : MemoOk A st) :
    CoverOk (events.foldl (routerEvent U) st) ∧ MemoOk A (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      exact ih _ (coverOk_event U st e h) (memoOk_event U A st e hmemo)

theorem memo_isSome_event (st : RouterState) (e : FirstHit.QueryEvent) (m : Message)
    (h : (st.memo.lookup m).isSome) : ((routerEvent U st e).memo.lookup m).isSome := by
  rw [(routerEvent_fields U st e).2.2.1]; exact h

theorem memo_isSome_sign (st : RouterState) (request : Security.Request) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((signedState A (honestNonce A) published st request).memo.lookup m).isSome := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.1]
    unfold startState
    split_ifs with hs
    · exact h
    · rw [signed_memo_lookup]
      split_ifs <;> simp_all
  · rw [hnpub hc]; exact h

theorem memo_isSome_signed_self (st : RouterState) (request : Security.Request) (hc : request.cache = published) :
    ((signedState A (honestNonce A) published st request).memo.lookup request.message).isSome := by
  rw [((signedState_bank A published (honestNonce A) st request).1 hc).2.2.1]
  unfold startState
  split_ifs with hs
  · exact hs
  · rw [signed_memo_lookup, if_pos rfl]; rfl

theorem memo_isSome_steps (steps : List TaggedStep) (st : RouterState) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup m).isSome := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact memo_isSome_event U st e m h
      | sign request out evs => exact memo_isSome_sign A published st request m h

/-- After a published signing step its message is memoized. -/
theorem sign_memo_steps (steps : List TaggedStep) (st : RouterState) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup request.message).isSome := by
  induction steps generalizing st with
  | nil => cases hmem
  | cons s rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact memo_isSome_steps U A published rest _ _ (memo_isSome_signed_self A published st request hc)
      · exact ih _ hmem

/-- **Coverage**: a published signing step's honest digest output is exposed in the final fold, or the reuse
flag is set. -/
theorem covered_fold (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) (c : BitVec 32) (N : HashOutput)
    (hN : LargeResidual.signDigest A request.message = some (c, N)) :
    N ∈ (routerFold U A published steps verdict).exposures ∨ (routerFold U A published steps verdict).reused = true := by
  unfold routerFold
  have hinv0 : CoverOk RouterState.initial ∧ MemoOk A RouterState.initial :=
    ⟨fun m c N h => by simp [RouterState.initial] at h, fun m f h => by simp [RouterState.initial] at h⟩
  obtain ⟨h1, h2⟩ := invariants_steps U A published steps _ hinv0.1 hinv0.2
  obtain ⟨h3, h4⟩ := invariants_events U A verdict _ h1 h2
  have hs := sign_memo_steps U A published steps RouterState.initial request out evs hmem hc
  have hs' : ((verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published)
      RouterState.initial)).memo.lookup request.message).isSome := by
    rw [(routerEvents_fields U verdict _).2.2.1]; exact hs
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs'
  have hfe := h4 _ _ hf
  rw [hN] at hfe
  subst hfe
  exact h3 _ c N hf

/-! ## Exposures and trials -/

theorem exposures_signedState_le (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).exposures.length ≤ st.exposures.length + 1 := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).1]
    unfold startState
    split_ifs
    · omega
    · unfold RouterState.signed
      split_ifs
      · dsimp only; omega
      · dsimp only
        rw [List.length_append]
        have : ((LargeResidual.signDigest A request.message).map Prod.snd).toList.length ≤ 1 := by
          cases LargeResidual.signDigest A request.message <;> simp
        omega
  · rw [hnpub hc]; omega

theorem exposures_steps_le (steps : List TaggedStep) (st : RouterState) :
    (steps.foldl (routerStep U A (honestNonce A) published) st).exposures.length ≤
      st.exposures.length + signCount steps := by
  induction steps generalizing st with
  | nil => simp [signCount]
  | cons s rest ih =>
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      cases s with
      | world e =>
          change (routerEvent U st e).exposures.length + signCount rest ≤ st.exposures.length + signCount rest
          rw [(routerEvent_fields U st e).1]
      | sign request out evs =>
          have := exposures_signedState_le A published st request
          change (signedState A (honestNonce A) published st request).exposures.length + signCount rest ≤
            st.exposures.length + (signCount rest + 1)
          omega

/-- The bank is alive at the end of the fold. -/
theorem exposures_fold_le (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) :
    (routerFold U A published steps verdict).exposures.length ≤ signCount steps := by
  unfold routerFold
  rw [(routerEvents_fields U verdict _).1]
  have := exposures_steps_le U A published steps RouterState.initial
  simpa [RouterState.initial] using this

/-- New trial rows come from published fresh signing steps. -/
theorem trials_steps (steps : List TaggedStep) (st : RouterState) (X : HashInput)
    (hX : X ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials) :
    X ∈ st.trials ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧ request.cache = published ∧
      X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message) := by
  induction steps generalizing st with
  | nil => exact Or.inl hX
  | cons s rest ih =>
      rw [List.foldl_cons] at hX
      rcases ih _ hX with h | ⟨r, o, e, hm, hc, hr⟩
      · cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials at h
            rw [(routerEvent_fields U st e).2.2.2] at h
            exact Or.inl h
        | sign request out evs =>
            change X ∈ (signedState A (honestNonce A) published st request).trials at h
            obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
            by_cases hc : request.cache = published
            · rw [(hpub hc).2.2.2] at h
              unfold startState at h
              split_ifs at h
              · exact Or.inl h
              · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1, List.mem_append] at h
                rcases h with h | h
                · exact Or.inl h
                · exact Or.inr ⟨request, out, evs, List.mem_cons_self, hc, h⟩
            · rw [hnpub hc] at h; exact Or.inl h
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hc, hr⟩

/-! ## Births -/

theorem seen_event_mono' (st : RouterState) (e : FirstHit.QueryEvent) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (routerEvent U st e).seen := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact h
  · change Y ∈ (st.next U X y).seen
    unfold RouterState.next
    split_ifs <;> exact List.mem_cons_of_mem _ h
  · exact h

theorem seen_event_self (st : RouterState) (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) :
    X ∈ (routerEvent U st ⟨b, .inl (.inr X), y⟩).seen := by
  change X ∈ (st.next U X y).seen
  unfold RouterState.next
  split_ifs <;> exact List.mem_cons_self

theorem seen_events_mono' (events : List FirstHit.QueryEvent) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih => exact ih _ (seen_event_mono' U st e Y h)

theorem seen_signed (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).seen = st.seen ∧
      (signedState A (honestNonce A) published st request).births = st.births := by
  refine ⟨(signedState_seen A (honestNonce A) published st request).1, ?_⟩
  rw [signedState_eq]
  split_ifs
  · rw [(finishState_fields _ _ _).2.2.2.1, (startState_fields _ _ _ _).2.2.2]
  · rfl

theorem seen_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).seen := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact seen_event_mono' U st e Y h
      | sign request out evs =>
          change Y ∈ (signedState A (honestNonce A) published st request).seen
          rw [(seen_signed A published st request).1]; exact h

/-- The birth invariant of a fixed digest row `X` answered `N`. -/
def BirthInv (X : HashInput) (N : HashOutput) (st : RouterState) : Prop := X ∈ st.seen → (X, N) ∈ st.births

theorem birthInv_event (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (st : RouterState) (e : FirstHit.QueryEvent) (hans : ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (htr : X ∉ st.trials) (h : BirthInv X N st) : BirthInv X N (routerEvent U st e) := by
  rcases e with ⟨b, (n | Y) | c, y⟩
  · exact h
  · change X ∈ (st.next U Y y).seen → (X, N) ∈ (st.next U Y y).births
    intro hs
    unfold RouterState.next at hs ⊢
    by_cases hY : Y = X
    · subst hY
      have hy : y = N := hans b y rfl
      subst hy
      by_cases hf : st.Fresh Y
      · rw [if_pos ⟨hXU, hXd, hf⟩]
        exact List.mem_cons_self
      · have hfr : ¬(Y ∈ U ∧ IsDigestRow Y ∧ st.Fresh Y) := fun h' => hf h'.2.2
        rw [if_neg hfr]
        have hseen : Y ∈ st.seen := by
          by_contra hn
          exact hf ⟨hn, htr⟩
        exact h hseen
    · have hs' : X ∈ st.seen := by
        split_ifs at hs <;>
        · rcases List.mem_cons.mp hs with h1 | h1
          · exact absurd h1.symm hY
          · exact h1
      split_ifs
      · exact List.mem_cons_of_mem _ (h hs')
      · exact h hs'
  · exact h

theorem birthInv_events (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (events : List FirstHit.QueryEvent) (hans : ∀ e ∈ events, ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ st.trials) (h : BirthInv X N st) :
    BirthInv X N (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih =>
      rw [List.foldl_cons]
      apply ih (fun e' he' => hans e' (List.mem_cons_of_mem _ he'))
      · rw [(routerEvent_fields U st e).2.2.2]; exact htr
      · exact birthInv_event U X N hXU hXd st e (hans e List.mem_cons_self) htr h

theorem trials_sign_mono (st : RouterState) (request : Security.Request) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (signedState A (honestNonce A) published st request).trials := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.2]
    unfold startState
    split_ifs
    · exact h
    · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1]; exact List.mem_append_left _ h
  · rw [hnpub hc]; exact h

theorem trials_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e =>
          change Y ∈ (routerEvent U st e).trials
          rw [(routerEvent_fields U st e).2.2.2]; exact h
      | sign request out evs => exact trials_sign_mono A published st request Y h

theorem birthInv_steps (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (steps : List TaggedStep)
    (hans : ∀ s ∈ steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ (steps.foldl (routerStep U A (honestNonce A) published) st).trials)
    (h : BirthInv X N st) :
    BirthInv X N (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons] at htr ⊢
      have hrest := fun s' hs' => hans s' (List.mem_cons_of_mem _ hs')
      apply ih hrest _ htr
      have hst : X ∉ st.trials := fun hm => htr (trials_steps_mono U A published rest _ X (by
        cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials
            rw [(routerEvent_fields U st e).2.2.2]; exact hm
        | sign request out evs => exact trials_sign_mono A published st request X hm))
      cases s with
      | world e => exact birthInv_event U X N hXU hXd st e (hans _ List.mem_cons_self e rfl) hst h
      | sign request out evs =>
          change X ∈ (signedState A (honestNonce A) published st request).seen →
            (X, N) ∈ (signedState A (honestNonce A) published st request).births
          rw [(seen_signed A published st request).1, (seen_signed A published st request).2]
          exact h

end Fold

end SigGolfCandidate.T3.Security.LargeCoupling
