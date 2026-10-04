import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactCase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute
import SigGolfCandidate.T3.Secc.LargeContactCert
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCLeaf
import SigGolfCandidate.T3.Secc.LargeContactCertClean

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CoverOk (st : RouterState) : Prop :=
  ∀ m c N, st.memo.lookup m = some (some (c, N)) → N ∈ st.exposures ∨ st.reused = true
def signCount : List TaggedStep → Nat
  | [] => 0
  | .world _ :: rest => signCount rest
  | .sign _ _ _ :: rest => signCount rest + 1
def stepLog : List TaggedStep → QueryLog Requests
  | [] => []
  | .world _ :: rest => stepLog rest
  | .sign request output _ :: rest => ⟨request, output⟩ :: stepLog rest
theorem signCount_eq_length (steps : List TaggedStep) : signCount steps = (stepLog steps).length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [signCount, stepLog, ih]
theorem taggedRecord_log {α : Type} (program : OracleComp LazyPrivate.Interaction α) (published : SigGolfCandidate.T3.Cache)
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
variable (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
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
theorem exposures_fold_le (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) :
    (routerFold U A published steps verdict).exposures.length ≤ signCount steps := by
  unfold routerFold
  rw [(routerEvents_fields U verdict _).1]
  have := exposures_steps_le U A published steps RouterState.initial
  simpa [RouterState.initial] using this
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
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCert : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem treeChild_inl {lay : Layer} {tree : Fin (2 ^ 31)} {level c : Nat} {x : Coord}
    (h : treeChild lay tree level c = some x) : ∃ n, x = .inl n := by
  unfold treeChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem ftsChild_inl {index : Fin (2 ^ 31)} {coord : Fin 9} {level c : Nat} {x : Coord}
    (h : ftsChild index coord level c = some x) : ∃ n, x = .inl n := by
  unfold ftsChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem not_inr_keygenDisclosed (s : CanonGraph.SecretIndex) : (.inr s : Coord) ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨_, _, _, _, hc⟩ := h
  obtain ⟨n, hn⟩ := treeChild_inl hc
  cases hn
theorem disclosed_steps_mem (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (mon : Monitor) (d : Coord)
    (hd : d ∈ (steps.foldl (Monitor.step U A q published) mon).disclosed) :
    d ∈ mon.disclosed ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧
      d ∈ signDisclosed A published request := by
  induction steps generalizing mon with
  | nil => exact Or.inl hd
  | cons s rest ih =>
      rw [List.foldl_cons] at hd
      rcases ih _ hd with h | ⟨r, o, e, hm, hr⟩
      · cases s with
        | world e =>
            change d ∈ (mon.event U A q e).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request out evs =>
            change d ∈ (mon.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, out, evs, List.mem_cons_self, h⟩
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hr⟩
theorem search_queried (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start k, start ≤ k → k < start + fuel →
      (∀ c', start ≤ c' → c' < k →
        WCT9.admissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) →
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (WCT9.digestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start k h1 h2; omega
  | succ fuel ih =>
      intro start k h1 h2 hrej
      rw [BPB.digestSearch_succ, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest]
      by_cases hk : k = start
      · subst hk
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) k (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2')
theorem search_result (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start,
      (∀ c N, evalWithAnswerFn A (WCT9.digestSearch rho m start fuel) = some (c, N) →
        ∃ k, start ≤ k ∧ k < start + fuel ∧ c = BitVec.ofNat 32 k ∧ ∀ c', start ≤ c' → c' < k →
          WCT9.admissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) ∧
      (evalWithAnswerFn A (WCT9.digestSearch rho m start fuel) = none → ∀ c', start ≤ c' → c' < start + fuel →
          WCT9.admissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      refine ⟨fun c N h => ?_, fun _ c' h1 h2 => by omega⟩
      simp [WCT9.digestSearch] at h
  | succ fuel ih =>
      intro start
      rw [BPB.digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hadm : WCT9.admissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure]
        refine ⟨fun c N h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨start, le_rfl, by omega, h.1.symm, fun c' h1 h2 => by omega⟩
      · rw [if_neg hadm]
        have hrej : WCT9.admissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = false := by
          simpa using hadm
        obtain ⟨ih1, ih2⟩ := ih (start + 1)
        refine ⟨fun c N h => ?_, fun h c' h1 h2 => ?_⟩
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih1 c N h
          refine ⟨k, by omega, by omega, hk3, fun c' h1 h2 => ?_⟩
          by_cases hc : c' = start
          · subst hc; exact hrej
          · exact hk4 c' (by omega) h2
        · by_cases hc : c' = start
          · subst hc; exact hrej
          · exact ih2 h c' (by omega) (by omega)
theorem trialRows_queried (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (hc : request.cache = published) (X : HashInput)
    (hX : X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message)) :
    (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published request) := by
  set rho := honestNonce A request.message with hrho
  have hsd : LargeResidual.signDigest A request.message =
      evalWithAnswerFn A (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) := rfl
  have hq : (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈
      queried A (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) := by
    obtain ⟨r1, r2⟩ := search_result A rho request.message WCT9.digestAttemptLimit 0
    cases hfound : LargeResidual.signDigest A request.message with
    | none =>
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => r2 (hsd ▸ hfound) c' (Nat.zero_le _) (by omega))
    | some found =>
        obtain ⟨c, N⟩ := found
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        obtain ⟨k0, -, hk0, hck, hrej⟩ := r1 c N (hsd ▸ hfound)
        have hlim : WCT9.digestAttemptLimit = 2 ^ 21 := rfl
        have hct : c.toNat = k0 := by
          rw [hck, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => hrej c' (Nat.zero_le _) (by omega))
  unfold FullGame.authenticatedSign
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc]
  change (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (WCT9.Rev3.signPayload request.cache request.message)
  rw [BPB.signPayload_nonce, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateNonce]
  apply List.mem_append_right
  unfold BPB.payloadForNonce
  rw [queried_bind]
  exact List.mem_append_left _ hq
theorem seen_events_self (U : Finset HashInput) (events : List FirstHit.QueryEvent) (st : RouterState)
    (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) (he : (⟨b, .inl (.inr X), y⟩ : FirstHit.QueryEvent) ∈ events) :
    X ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => cases he
  | cons e rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact seen_events_mono' U rest _ X (seen_event_self U st b X y)
      · exact ih _ he
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (digestIndex IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertClean : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem exists_pos_digit (r : WCT9.Rank) : ∃ t : Fin 7, 1 ≤ WCT9.digit r t := by
  by_contra h
  push Not at h
  have hz : ∀ t ∈ (Finset.univ : Finset (Fin 7)), WCT9.digit r t = 0 := fun t _ => by have := h t; omega
  have := WCT9.step_count r
  rw [Finset.sum_eq_zero hz] at this
  omega
theorem cert_of_clean (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) :
    CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  set U := Wots.referenceInputs adversary with hUdef
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun U z.2 q g.value.2 t.steps c.events).contact = false := by simpa using hmon
  intro g' t' c' hsplit'
  obtain ⟨rfl, rfl, rfl⟩ := taggedSplit_unique hsplit hsplit'
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have hpk : g.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  obtain ⟨hlen, forgery, hf, hfresh, m, w, hof, hv, hsub⟩ :=
    WotsExtract.verdict_accepting g.value.1 t.value t.state c hc z.2 hac hcval
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_route z.2 m g.value.1 w hpk hv
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun U z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le U z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hXU : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events → X ∈ U := by
    intro X prior hev
    have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
    have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    rw [← hev'] at hmem
    exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
  have hclearV : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events →
      Clear z.2 (monitorRun U z.2 q g.value.2 t.steps c.events).known X (z.2 (.inl (.inr X))) := by
    intro X prior hev
    have hseen := events_seen U z.2 q c.events _ hmon' _ hev X rfl
    exact monitorRun_clear U z.2 q g.value.2 t.steps c.events hsteps hverdict hmon' hcalls X hseen
      (hXU X prior hev)
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    exact (hclearV X prior hev).mono fun d hd =>
      monitorRun_known U z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, hqF⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgood, hfts⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  have hsd : ¬BPB.SignedDigest t.value.2 m w := fun hsd =>
    BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩
  refine ⟨hcval, hmon', hcalls, ?_⟩
  set st := routerFold U z.2 g.value.2 t.steps c.events with hst
  have hlog : t.value.2 = stepLog t.steps := taggedRecord_log _ _ _ t ht
  have halive : st.exposures.length ≤ CaseC.horizon := by
    have h1 : st.exposures.length ≤ signCount t.steps := exposures_fold_le U z.2 g.value.2 t.steps c.events
    rw [signCount_eq_length, ← hlog] at h1
    have : CaseC.horizon = 2 ^ 32 := rfl
    omega
  refine ⟨halive, ?_⟩
  by_cases hr : st.reused = true
  · exact Or.inl hr
  right
  set Xs := pad64 (digestInput (wrho w) m (wdc w)) with hXs
  have hXsU : Xs ∈ U := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    exact hXU Xs prior hev
  have hXsd : IsDigestRow Xs := ⟨wrho w, m, wdc w, rfl⟩
  have hres' := BPB.logged_resolves g.value.2 (adversary g.value.1 g.value.2) g.state (t.untag.value, t.untag.state)
    (FirstHit.recorded_support _ _ _ hu)
  have hagree' : ∀ input answer, SourceReplay.known t.state input = some answer → z.2 input = answer :=
    fun input answer h => hac input answer (SourceReplay.known_mono _ _ htc h)
  have hnot := BPB.caseC_fresh_not_signer z.2 g.value.2 t.value.2 t.state hres' hagree' m w N hN hS hgood hsd
  have hnotrial : Xs ∉ (t.steps.foldl (routerStep U z.2 (honestNonce z.2) g.value.2) RouterState.initial).trials := by
    intro hm
    rcases trials_steps U z.2 g.value.2 t.steps RouterState.initial Xs hm with h0 | ⟨r, o, e, hmem, hcr, hrow⟩
    · cases h0
    · have hq' := trialRows_queried z.2 g.value.2 r hcr Xs hrow
      have hlogm : (⟨r, o⟩ : (r : Requests.Domain) × Requests.Range r) ∈ t.value.2 := by
        rw [hlog]; exact sign_mem_stepLog hmem
      exact hnot _ hlogm hq'
  have hansSteps : ∀ s ∈ t.steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro s hs e hse b y he
    have h1 := hsteps s hs e hse (by rw [he]; trivial)
    rw [he] at h1
    exact h1.symm.trans hNz
  have hansV : ∀ e ∈ c.events, ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro e he b y hee
    have h1 := hverdict e he (by rw [hee]; trivial)
    rw [hee] at h1
    exact h1.symm.trans hNz
  have hbirth : (Xs, N) ∈ st.births := by
    have hI := birthInv_steps U z.2 g.value.2 Xs N hXsU hXsd t.steps hansSteps RouterState.initial hnotrial
      (fun h => by cases h)
    have hI2 := birthInv_events U Xs N hXsU hXsd c.events hansV _ hnotrial hI
    obtain ⟨prior, hev⟩ := hsub _ hdq
    apply hI2
    exact seen_events_self U c.events _ prior Xs _ hev
  refine ⟨(Xs, N), hbirth, hS, ?_⟩
  have hposCov : ∀ (k : WCT9.Coord) (t : Fin 7), 1 ≤ WCT9.digit (WCT9.rank N k) t →
      ∃ x ∈ st.exposures, ClaudeWCT.Bank.WCT.outIdx x = ClaudeWCT.Bank.WCT.outIdx N ∧
        WCT9.child x k = WCT9.child N k ∧ WCT9.digit (WCT9.rank N k) t ≤ WCT9.digit (WCT9.rank x k) t := by
    intro k tt hu1
    have hu3 : WCT9.digit (WCT9.rank N k) tt ≤ 3 := WCT9.digit_le_three _ _
    set a : CanonGraph.WctAddr := (digestIndex N, k, WCT9.child N k, tt) with ha
    set s : Fin 3 := ⟨3 - WCT9.digit (WCT9.rank N k) tt, by omega⟩ with hs
    have hq0 := CaseC.recoverFtsP_chain_queried z.2 N w k tt hu1
    obtain ⟨hval, hpad⟩ := (hfts.2 k).1 tt
    rw [hval, (hpad hu1).1, (hpad hu1).2] at hq0
    have hX : (.inl (.inr (pad64 (wctChainInputP (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val tt.val
        (3 - WCT9.digit (WCT9.rank N k) tt) ((0, 0) : Digest × Digest).1 0 ((0, 0) : Digest × Digest).2
        (Extract.wctValue z.2 (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val tt.val
          (3 - WCT9.digit (WCT9.rank N k) tt))))) : Spec.Domain) =
        .inl (.inr (Extract.honestInput z.2 (CanonGraph.Node.wctChain (a, s)).toPos)) := by
      rw [wctChainInputP_zero]
      rfl
    rw [hX] at hq0
    obtain ⟨prior, hev⟩ := hsub _ (hqF _ hq0)
    have hcl := hclearV _ prior hev
    have hk := hcl.2.1 (CanonGraph.Node.wctChain (a, s)) (posOf_honest_wctChain z.2 a s) (wctItem a s.val) 3 rfl
      (slotValue_honest_wctChain z.2 a s)
    obtain ⟨p', hp', hd⟩ := known_wctItem (by omega) hk
    rcases hd with hkg | hkd
    · exact (keygen_not_wct a p' hkg).elim
    have hkd' : wctItem a p' ∈ (t.steps.foldl (Monitor.step U z.2 q g.value.2) Monitor.initial).disclosed := by
      unfold monitorRun at hkd
      rwa [disclosed_events] at hkd
    rcases disclosed_steps_mem U z.2 q g.value.2 t.steps Monitor.initial _ hkd' with h0 | ⟨r, o, e, hmem, hdis⟩
    · cases h0
    unfold signDisclosed at hdis
    split_ifs at hdis with hcr
    · rcases hsr : LargeResidual.signDigest z.2 r.message with _ | ⟨c', N'⟩
      · rw [hsr] at hdis; cases hdis
      · rw [hsr] at hdis
        dsimp only at hdis
        split_ifs at hdis with hok
        · have hp3 : p' ≤ 3 := by omega
          obtain ⟨hidx, hchild, hpos⟩ := wctItem_mem_signItemsWith _ N' a p' hp3 hdis
          have hd3 : WCT9.digit (WCT9.rank N' k) tt ≤ 3 := WCT9.digit_le_three _ _
          rcases covered_fold U z.2 g.value.2 t.steps c.events r o e hmem hcr c' N' hsr with hx | hx
          · refine ⟨N', hx, ?_, hchild.symm, ?_⟩
            · exact Fin.ext (congrArg Fin.val hidx).symm
            · simp only [ha] at hpos
              simp only [hs, Fin.val_mk] at hp'
              omega
          · exact (hr hx).elim
        · cases hdis
    · cases hdis
  show ClaudeWCT.Bank.WCT.Covered st.exposures N
  intro k tt
  by_cases hu : 1 ≤ WCT9.digit (WCT9.rank N k) tt
  · exact hposCov k tt hu
  · obtain ⟨t', ht'⟩ := exists_pos_digit (WCT9.rank N k)
    obtain ⟨x, hx, hidx, hch, -⟩ := hposCov k t' ht'
    exact ⟨x, hx, hidx, hch, by omega⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
