import SigGolfCandidate.T3.Secc.LargeCouplingQuery
import SigGolfCandidate.T3.Secc.LargeContactMonitor

/-!
# LR-34 (coupling, signing): the router signs exactly as the honest signer

In the eager observed world of a coherent table, the router's honest steps are deterministic:

* `observed_search`: the router's digest search (uncharged residual reads) returns the honest search result under
  `T`, only caching digest rows (`ReadsOnly`);
* `Coherent.signDigest`, `Coherent.routeOk_iff`, `Coherent.routerDigits_route`, `Coherent.signItems_eq`: the honest
  search, the route-search success and the reference digits are the router's (presampled) ones;
* `assembleSig_congr`: a signature built from disclosed values only reads the signature's items.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingSigning : DecidableEq T3.Cache := Classical.decEq _

/-! ## Read-only steps -/

/-- A world step that only caches digest rows answered by `τ`. -/
structure ReadsOnly {U : Finset HashInput} (τ : Cell U → HashOutput) (ws ws' : LargeResidual.State WCoord (Cell U)) :
    Prop where
  candidates : ws'.candidates = ws.candidates
  counters : ws'.counters = ws.counters
  rows : ∀ row v, ws'.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)

theorem ReadsOnly.refl {U : Finset HashInput} (τ : Cell U → HashOutput) (ws : LargeResidual.State WCoord (Cell U)) :
    ReadsOnly τ ws ws :=
  ⟨rfl, rfl, fun _ _ h => Or.inl h⟩

theorem ReadsOnly.trans {U : Finset HashInput} {τ : Cell U → HashOutput} {ws ws' ws'' : LargeResidual.State WCoord (Cell U)}
    (h1 : ReadsOnly τ ws ws') (h2 : ReadsOnly τ ws' ws'') : ReadsOnly τ ws ws'' := by
  refine ⟨h2.candidates.trans h1.candidates, h2.counters.trans h1.counters, fun row v hv => ?_⟩
  rcases h2.rows row v hv with h | h
  · exact h1.rows row v h
  · exact Or.inr h

/-! ## The digest search -/

section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)

theorem digestRow_isDigest (rho : Digest) (m : Message) (c : BitVec 32) : IsDigestRow (pad64 (digestInput rho m c)) :=
  ⟨rho, m, c, rfl⟩

/-- **The router's digest search** is the honest search under any table answering the trial rows as `τ`. -/
theorem observed_search (T : Answers) (rho : Digest) (m : Message)
    (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U)
    (hT : ∀ c : BitVec 32, T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, hU c⟩) :
    ∀ (fuel c : Nat) (ws : LargeResidual.State WCoord (Cell U)), ∃ ws',
      observedRun aux q labels τ (simulateQ (readImpl U a) (digestSearch rho m c fuel)) ws =
        pure (some (evalWithAnswerFn T (digestSearch rho m c fuel)), ws') ∧ ReadsOnly τ ws ws' := by
  intro fuel
  induction fuel with
  | zero =>
      intro c ws
      refine ⟨ws, ?_, ReadsOnly.refl τ ws⟩
      simp only [digestSearch, simulateQ_pure, evalWithAnswerFn_pure]
      exact observed_pure aux q labels τ _ ws
  | succ fuel ih =>
      intro c ws
      simp only [digestSearch, digest, publicHash, simulateQ_bind, evalWithAnswerFn_bind]
      have hq : simulateQ (readImpl U a) (Spec.query (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
          M HashOutput) = readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
        change simulateQ (readImpl U a) (liftM (Spec.query _)) = _
        rw [simulateQ_spec_query]
        simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]
      rw [hq, observed_readReq]
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩
      have hTX : (evalWithAnswerFn T (Spec.query (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
          M HashOutput) : HashOutput) = τ X := hT _
      have hrd : ReadsOnly τ ws (readState q ws X (τ X) .none) := by
        refine ⟨rfl, rfl, fun row v hv => ?_⟩
        by_cases hr : row = X
        · subst hr
          simp only [readState, Function.update_self] at hv
          exact Or.inr ⟨digestRow_isDigest _ _ _, (Option.some.inj hv).symm⟩
        · simp only [readState, Function.update_of_ne hr] at hv
          exact Or.inl hv
      rw [hTX]
      by_cases hadm : digestAdmissible (τ X) = true
      · simp only [hadm, if_true, simulateQ_pure, evalWithAnswerFn_pure]
        exact ⟨_, observed_pure aux q labels τ _ _, hrd⟩
      · simp only [hadm, Bool.false_eq_true, if_false]
        obtain ⟨ws', h1, h2⟩ := ih (c + 1) (readState q ws X (τ X) .none)
        exact ⟨ws', h1, hrd.trans h2⟩

end Search

/-! ## Coherent signing data -/

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}

theorem digestRow_mem (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) ∈ U := by
  apply hUpub
  apply SeccLaw.mem_publicUniverse
  have h := Wots.Ref.pad64_length_le (digestInput rho m c)
  have hl : (digestInput rho m c).length = 64 := by
    simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]
  unfold SeccLaw.maxInputLength
  omega

theorem Coherent.digestRow (hcoh : Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest)
    (m : Message) (c : BitVec 32) :
    T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, digestRow_mem hUpub rho m c⟩ := by
  have hd := digestRow_isDigest rho m c
  have hnp := not_parsed_of_digest hd
  apply hcoh.residual _ _ (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N')
  rintro ⟨L, ctr, hX, -⟩
  exact encRow_not_digest L _ ctr (hX ▸ hd)

theorem Coherent.privateNonce (hcoh : Coherent U T vals nv τ a) (m : Message) :
    evalWithAnswerFn T (T3.privateNonce m) = nv m := by
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact hcoh.nonce m

theorem Coherent.signDigest (hcoh : Coherent U T vals nv τ a) (m : Message) :
    LargeResidual.signDigest T m = evalWithAnswerFn T (digestSearch (nv m) m 0 attemptLimit) := by
  unfold LargeResidual.signDigest
  rw [hcoh.privateNonce]

theorem Coherent.routerDigits_eq (hcoh : Coherent U T vals nv τ a) (L : Wots.LeafAddr)
    (hL : ∃ L' : EncLeaf, L'.toWots = L) : LargeResidual.routerDigits a L = Wots.referenceDigits T L := by
  unfold LargeResidual.routerDigits
  rw [dif_pos hL]
  have hs := Classical.choose_spec hL
  have hlay : (Classical.choose hL).1.lay = L.lay := congrArg Wots.LeafAddr.lay hs
  conv_rhs => rw [← hs]
  rw [hcoh.referenceDigits, hlay]

theorem routeAddr_enc (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    ∃ L : EncLeaf, L.toWots = routeAddr index lay := route_source index hindex lay

theorem Coherent.routeOk_iff (hcoh : Coherent U T vals nv τ a) (index : Nat) (hindex : index < 2 ^ 31) :
    RouteOkR a index ↔ RouteOk T index := by
  constructor
  · intro h lay
    obtain ⟨L, r, hL, hs, hd⟩ := h lay
    rw [← hL, hcoh.search L, hs]
    have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL
    simp only [Option.bind_some]
    rw [hlay]
    cases hdec : decode lay r.2 with
    | none => rw [hdec] at hd; cases hd
    | some w => rfl
  · intro h lay
    obtain ⟨L, hL⟩ := routeAddr_enc index hindex lay
    have h1 := h lay
    rw [← hL, hcoh.search L] at h1
    have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL
    cases hs : a.sel L with
    | none => rw [hs] at h1; cases h1
    | some r =>
        rw [hs] at h1
        refine ⟨L, r, hL, hs, ?_⟩
        rw [← hlay]
        simp only [Option.bind_some] at h1
        cases hdec : decode L.1.lay r.2 with
        | none => rw [hdec] at h1; cases h1
        | some w => rfl

theorem layerChains_congr (d d' : Wots.LeafAddr → List Nat) (index : Fin (2 ^ 31)) (lay : Layer)
    (h : d (routeAddr index.val lay) = d' (routeAddr index.val lay)) : layerChains d index lay = layerChains d' index lay := by
  unfold layerChains
  split_ifs
  · rw [h]
  · rfl

theorem Coherent.layerChains_eq (hcoh : Coherent U T vals nv τ a) (index : Fin (2 ^ 31)) (lay : Layer) :
    layerChains (routerDigits a) index lay = layerChains (Wots.referenceDigits T) index lay :=
  layerChains_congr _ _ index lay (hcoh.routerDigits_eq _ (routeAddr_enc index.val index.isLt lay))

theorem Coherent.layerItems_eq (hcoh : Coherent U T vals nv τ a) (index : Fin (2 ^ 31)) :
    layerItems (routerDigits a) index = layerItems (Wots.referenceDigits T) index := by
  unfold layerItems
  apply List.flatMap_congr
  intro lay _
  rw [hcoh.layerChains_eq]

theorem Coherent.signItems_eq (hcoh : Coherent U T vals nv τ a) (N : HashOutput) :
    signItemsWith (routerDigits a) N = LargeResidual.signItems T N := by
  unfold LargeResidual.signItems signItemsWith
  rw [hcoh.layerItems_eq]

theorem assembleSig_def (rho : Digest) (N : HashOutput) (v : Coord → Digest) (d : Wots.LeafAddr → List Nat) :
    assembleSig rho N v d = ⟨rho,
      fun i => (((List.range 7).flatMap fun c => ftsOpened (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v).getD i.val 0,
      fun i => (((List.range 7).flatMap fun c => ftsProof (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v).getD i.val 0,
      fun lay => piecesSignature lay ((layerChains d (digestIndex N) lay).map v, (layerPath (digestIndex N) lay).map v)⟩ :=
  rfl

/-- A signature built from disclosed values reads the values only on the signature's items. -/
theorem assembleSig_congr (rho : Digest) (N : HashOutput) (v v' : Coord → Digest) (d : Wots.LeafAddr → List Nat)
    (h : ∀ c ∈ signItemsWith d N, v c = v' c) : assembleSig rho N v d = assembleSig rho N v' d := by
  rw [assembleSig_def, assembleSig_def]
  have hfts : ∀ c ∈ ftsItems (digestIndex N) (selections N), v c = v' c := fun c hc =>
    h c (List.mem_append_left _ hc)
  have hlay : ∀ c ∈ layerItems d (digestIndex N), v c = v' c := fun c hc => h c (List.mem_append_right _ hc)
  have hopen : ((List.range 7).flatMap fun c => ftsOpened (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v =
      ((List.range 7).flatMap fun c => ftsOpened (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v' := by
    apply List.map_congr_left
    intro c hc
    apply hfts
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append_left _ hci⟩
  have hproof : ((List.range 7).flatMap fun c => ftsProof (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v =
      ((List.range 7).flatMap fun c => ftsProof (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map v' := by
    apply List.map_congr_left
    intro c hc
    apply hfts
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append_right _ hci⟩
  rw [hopen, hproof]
  congr 1
  funext lay
  congr 2
  · apply List.map_congr_left
    intro c hc
    exact hlay c (List.mem_flatMap.mpr ⟨lay, List.mem_finRange lay, List.mem_append_left _ hc⟩)
  · apply List.map_congr_left
    intro c hc
    exact hlay c (List.mem_flatMap.mpr ⟨lay, List.mem_finRange lay, List.mem_append_right _ hc⟩)

theorem assembleSig_digits (rho : Digest) (N : HashOutput) (v : Coord → Digest) (d d' : Wots.LeafAddr → List Nat)
    (h : ∀ lay, d (routeAddr (digestIndex N).val lay) = d' (routeAddr (digestIndex N).val lay)) :
    assembleSig rho N v d = assembleSig rho N v d' := by
  rw [assembleSig_def, assembleSig_def]
  congr 1
  funext lay
  rw [layerChains_congr d d' _ lay (h lay)]

end Coherent

/-! ## The router's signing -/

/-- Every memoized search result is the honest search result. -/
def MemoOk (T : Answers) (st : RouterState) : Prop :=
  ∀ m f, st.memo.lookup m = some f → f = LargeResidual.signDigest T m

/-- The router state after a signing request, in closed form. -/
noncomputable def signedState (T : Answers) (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) : RouterState :=
  if request.cache = published then
    let st1 := if (st.memo.lookup request.message).isSome then st
      else st.signed (nv request.message) request.message (LargeResidual.signDigest T request.message)
    match LargeResidual.signDigest T request.message with
    | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
        { st1 with disclosed := st1.disclosed ++ LargeResidual.signItems T N } else st1
    | none => st1
  else st

/-- The end of a closed-form signing. -/
noncomputable def finishState (T : Answers) (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  match found with
  | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
      { st1 with disclosed := st1.disclosed ++ LargeResidual.signItems T N } else st1
  | none => st1

/-- The first part of a closed-form signing (the bank ghost of a fresh signing). -/
noncomputable def startState (T : Answers) (nv : Message → Digest) (st : RouterState) (m : Message) : RouterState :=
  if (st.memo.lookup m).isSome then st else st.signed (nv m) m (LargeResidual.signDigest T m)

theorem signedState_eq (T : Answers) (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState T nv published st request = if request.cache = published then
      finishState T (startState T nv st request.message) (LargeResidual.signDigest T request.message) else st := rfl

theorem startState_fields (T : Answers) (nv : Message → Digest) (st : RouterState) (m : Message) :
    (startState T nv st m).disclosed = st.disclosed ∧ (startState T nv st m).seen = st.seen ∧
      (startState T nv st m).calls = st.calls ∧ (startState T nv st m).births = st.births := by
  unfold startState
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := RouterState.signed_fields st (nv m) m (LargeResidual.signDigest T m)
    exact ⟨h1, h2, h3, h4⟩

theorem finishState_fields (T : Answers) (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState T st1 found).disclosed = st1.disclosed ++ (match found with
      | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then LargeResidual.signItems T N else []
      | none => []) ∧
    (finishState T st1 found).seen = st1.seen ∧ (finishState T st1 found).calls = st1.calls ∧
    (finishState T st1 found).births = st1.births ∧ (finishState T st1 found).memo = st1.memo := by
  unfold finishState
  cases found with
  | none => exact ⟨by simp, rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨by simp, rfl, rfl, rfl, rfl⟩

theorem signedState_disclosed (T : Answers) (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).disclosed = st.disclosed ++ signDisclosed T published request := by
  rw [signedState_eq]
  unfold signDisclosed
  split_ifs with hc
  · rw [(finishState_fields _ _ _).1, (startState_fields _ _ _ _).1]
    congr 1
  · simp

theorem signedState_seen (T : Answers) (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).seen = st.seen ∧ (signedState T nv published st request).calls = st.calls := by
  rw [signedState_eq]
  split_ifs with hc
  · rw [(finishState_fields _ _ _).2.1, (finishState_fields _ _ _).2.2.1, (startState_fields _ _ _ _).2.1,
      (startState_fields _ _ _ _).2.2.1]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem signedState_memo (T : Answers) (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) (hmemo : MemoOk T st) : MemoOk T (signedState T nv published st request) := by
  rw [signedState_eq]
  split_ifs with hc
  · intro m' f hf
    rw [(finishState_fields _ _ _).2.2.2.2] at hf
    unfold startState at hf
    split_ifs at hf with hm
    · exact hmemo m' f hf
    · simp only [(RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons] at hf
      by_cases hmm : m' = request.message
      · subst hmm
        simp only [beq_self_eq_true] at hf
        exact (Option.some.inj hf).symm
      · have hne : (m' == request.message) = false := by simpa using hmm
        rw [hne] at hf
        exact hmemo m' f hf
  · exact hmemo

theorem eval_authenticatedSign (T : Answers) (published : T3.Cache) (request : Security.Request) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      if request.cache = published then evalWithAnswerFn T (signPayload published request.message) else none := by
  unfold FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  split_ifs with h1
  · rw [h1]
  · rfl

section Sign
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))

/-- The honest answer of a signing whose search result is `found` (closed form, nonce `rho`). -/
noncomputable def finishOut (T : Answers) (vals : Coord → Digest) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    Option Signature :=
  match found with
  | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
      some (assembleSig rho N vals (Wots.referenceDigits T)) else none
  | none => none

/-- The world state after the end of a signing. -/
noncomputable def finishWorld (T : Answers) (U : Finset HashInput) (q : Nat) (labels : WCoord → Digest)
    (ws : LargeResidual.State WCoord (Cell U)) (found : Option (BitVec 32 × HashOutput)) :
    LargeResidual.State WCoord (Cell U) :=
  match found with
  | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then discloseStates U q labels ws (LargeResidual.signItems T N)
      else ws
  | none => ws

theorem observed_signFinish (hcoh : Coherent U T vals nv τ a) (st1 : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (ws1 : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (signFinish U a st1 rho found) ws1 =
      pure (some (finishOut T vals rho found, finishState T st1 found),
        finishWorld T U q (Sum.elim vals nv) ws1 found) := by
  cases found with
  | none => exact observed_pure aux q _ τ _ ws1
  | some f =>
      obtain ⟨c, N⟩ := f
      have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
      unfold signFinish finishOut finishState finishWorld
      dsimp only
      by_cases hok : RouteOk T (N.toNat % 2 ^ 31)
      · rw [if_pos ((hcoh.routeOk_iff _ hidx).mpr hok), if_pos hok, if_pos hok, if_pos hok]
        rw [observed_discloseAll, observed_pure, hcoh.signItems_eq]
        congr 4
        rw [assembleSig_digits rho N _ _ (Wots.referenceDigits T) (fun lay =>
          hcoh.routerDigits_eq _ (routeAddr_enc _ (digestIndex N).isLt lay))]
        congr 1
        apply assembleSig_congr
        intro c' hc'
        exact lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ c' hc'
      · rw [if_neg (fun h => hok ((hcoh.routeOk_iff _ hidx).mp h)), if_neg hok, if_neg hok, if_neg hok]
        exact observed_pure aux q _ τ _ ws1

end Sign

section SignRel
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))

theorem known_signed (published : T3.Cache) (request : Security.Request) (c : Coord) (hc : st.known c) :
    (signedState T nv published st request).known c := by
  unfold RouterState.known at hc ⊢
  refine Known.mono (fun d hd => ?_) hc
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    rw [signedState_disclosed]
    exact List.mem_append_left _ hd

theorem known_signed_new (published : T3.Cache) (request : Security.Request) (c : Coord)
    (hc : c ∈ signDisclosed T published request) : (signedState T nv published st request).known c := by
  apply Known.base
  right
  rw [signedState_disclosed]
  exact List.mem_append_right _ hc

/-- **The relation after a signing**, for any final world state that only disclosed the new items (and nonces) and
cached digest rows. -/
theorem Rel.afterSign (hrel : Rel U T vals nv τ a q mon st ws) (published : T3.Cache) (request : Security.Request)
    (wsF : LargeResidual.State WCoord (Cell U))
    (hcand : ∀ c : Coord, c ∉ signDisclosed T published request → wsF.candidates (.inl c) = ws.candidates (.inl c))
    (hmemF : ∀ c, Sum.elim vals nv c ∈ wsF.candidates c) (hcnt : wsF.counters = ws.counters)
    (hrows : ∀ row v, wsF.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)) :
    Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request) wsF := by
  have hms : mon.sign T published request =
      ⟨mon.disclosed ++ signDisclosed T published request, mon.seen, mon.calls, mon.digests, false⟩ := by
    unfold Monitor.sign
    rw [if_neg (by rw [hrel.contact]; decide)]
  obtain ⟨hseen, hcalls⟩ := signedState_seen T nv published st request
  rw [hms]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, hmemF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [signedState_disclosed, hrel.disclosed]
  · rw [hseen, hrel.seen]
  · rw [hcalls, hrel.calls]
  · rw [hcnt, hcalls, hrel.wcalls]
  · rw [hcnt, hrel.digests]
  · rw [hcnt]; exact hrel.probes
  · rw [hcalls]; exact hrel.budget
  · intro c hck
    have hc1 : c ∉ signDisclosed T published request := fun h => hck (known_signed_new published request c h)
    have hc2 : ¬st.known c := fun h => hck (known_signed published request c h)
    rw [hcand c hc1, hcnt]
    exact hrel.hidden c hc2
  · intro row v hv
    rcases hrows row v hv with h | h
    · exact hrel.rowsEq row v h
    · exact h.2
  · intro row v hv
    rw [hseen]
    rcases hrows row v hv with h | h
    · exact hrel.rowsSeen row v h
    · exact Or.inr h.1
  · intro X hX hXU N hN cs hcs
    rw [hseen] at hX
    exact known_signed published request _ (hrel.seenCells X hX hXU N hN cs hcs)
  · intro X hX hXU L ctr hL
    rw [hseen] at hX
    exact known_signed published request _ (hrel.seenEnc X hX hXU L ctr hL)

theorem disclosedState_props (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) (v : Digest) :
    (disclosedState q s c v .none).candidates = Function.update s.candidates c {v} ∧
      (disclosedState q s c v .none).counters = s.counters ∧ (disclosedState q s c v .none).rows = s.rows :=
  ⟨rfl, rfl, rfl⟩

theorem finishWorld_props (s : LargeResidual.State WCoord (Cell U)) (found : Option (BitVec 32 × HashOutput)) :
    (finishWorld T U q (Sum.elim vals nv) s found).counters = s.counters ∧
    (finishWorld T U q (Sum.elim vals nv) s found).rows = s.rows ∧
    (∀ c, (finishWorld T U q (Sum.elim vals nv) s found).candidates c = s.candidates c ∨
      (finishWorld T U q (Sum.elim vals nv) s found).candidates c = {Sum.elim vals nv c}) ∧
    (∀ c : Coord, c ∉ (match found with
        | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then LargeResidual.signItems T N else []
        | none => []) →
      (finishWorld T U q (Sum.elim vals nv) s found).candidates (.inl c) = s.candidates (.inl c)) := by
  unfold finishWorld
  cases found with
  | none => exact ⟨rfl, rfl, fun c => Or.inl rfl, fun c _ => rfl⟩
  | some f =>
      obtain ⟨c0, N⟩ := f
      dsimp only
      split_ifs with hok
      · refine ⟨discloseStates_counters _ _, discloseStates_rows _ _, fun c => ?_, fun c hc => ?_⟩
        · rw [discloseStates_candidates]
          split_ifs
          · exact Or.inr rfl
          · exact Or.inl rfl
        · rw [discloseStates_candidates, if_neg]
          intro hm
          obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
          rw [Sum.inl.inj hdc] at hd
          exact hc hd
      · exact ⟨rfl, rfl, fun c => Or.inl rfl, fun c _ => rfl⟩

end SignRel

section SignMain
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} {mon : Monitor} {st : RouterState}
  {ws : LargeResidual.State WCoord (Cell U)} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))

theorem finishOut_real (hcoh : Coherent U T vals nv τ a) (published : T3.Cache)
    (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T)) (request : Security.Request)
    (hc : request.cache = published) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      finishOut T vals (nv request.message) (LargeResidual.signDigest T request.message) := by
  rw [eval_authenticatedSign, if_pos hc, signPayload_disclosed hcoh.agrees published hpub, hcoh.honestValue,
    hcoh.privateNonce]
  unfold finishOut
  rcases LargeResidual.signDigest T request.message with _ | ⟨c, N⟩
  · rfl
  · dsimp only

/-- **One routed signing request** (eager observed world): a single outcome — the honest signer's answer, the
closed-form router state, and the relation with the monitor's signing step. -/
theorem routeSign_observed (hcoh : Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    (hrel : Rel U T vals nv τ a q mon st ws) (hmemo : MemoOk T st) (request : Security.Request) :
    ∃ wsF, observedRun aux q (Sum.elim vals nv) τ (routeSign U a published st request) ws =
        pure (some (evalWithAnswerFn T (FullGame.authenticatedSign published request),
          signedState T nv published st request), wsF) ∧
      Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request) wsF := by
  unfold routeSign
  by_cases hc : request.cache = published
  · rw [if_pos hc, observed_discloseReq]
    simp only [Sum.elim_inr]
    have hreal := finishOut_real hcoh published hpub request hc
    have hsd : signDisclosed T published request = match LargeResidual.signDigest T request.message with
        | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then LargeResidual.signItems T N else []
        | none => [] := by
      unfold signDisclosed
      rw [if_pos hc]
      congr 1
    set ws1 := disclosedState q ws (.inr request.message) (nv request.message) .none with hws1
    have hws1c := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).1
    have hws1n := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).2.1
    have hws1r := (disclosedState_props (q := q) ws (.inr request.message) (nv request.message)).2.2
    have hmem1 : ∀ c, Sum.elim vals nv c ∈ ws1.candidates c := by
      intro c
      rw [hws1c]
      by_cases hcm : c = .inr request.message
      · subst hcm
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hcm]
        exact hrel.mem c
    -- the final world state, from any read-only state after the nonce
    have hfinal : ∀ ws2 : LargeResidual.State WCoord (Cell U), ReadsOnly τ ws1 ws2 →
        Rel U T vals nv τ a q (mon.sign T published request) (signedState T nv published st request)
          (finishWorld T U q (Sum.elim vals nv) ws2 (LargeResidual.signDigest T request.message)) := by
      intro ws2 hro
      obtain ⟨hfc, hfr, hfcand, hfold⟩ := finishWorld_props (T := T) (q := q) (vals := vals) (nv := nv) ws2
        (LargeResidual.signDigest T request.message)
      apply hrel.afterSign published request
      · intro c hcn
        rw [hsd] at hcn
        rw [hfold c hcn, hro.candidates, hws1c, Function.update_of_ne (by simp)]
      · intro c
        rcases hfcand c with h | h
        · rw [h, hro.candidates]; exact hmem1 c
        · rw [h]; exact Finset.mem_singleton_self _
      · rw [hfc, hro.counters, hws1n]
      · intro row v hv
        rw [hfr] at hv
        rcases hro.rows row v hv with h | h
        · rw [hws1r] at h; exact Or.inl h
        · exact Or.inr h
    cases hm : st.memo.lookup request.message with
    | some f =>
        have hf := hmemo _ f hm
        simp only
        rw [observed_signFinish aux hcoh st (nv request.message) f ws1, hf]
        refine ⟨_, ?_, hfinal ws1 (ReadsOnly.refl τ ws1)⟩
        rw [hreal, signedState_eq, if_pos hc]
        unfold startState
        rw [hm]
        rfl
    | none =>
        simp only
        obtain ⟨ws2, hs, hro⟩ := observed_search aux q (Sum.elim vals nv) τ a T (nv request.message)
          request.message (digestRow_mem hUpub _ _) (hcoh.digestRow hUpub _ _) attemptLimit 0 ws1
        rw [observedRun, runWith_bind, ← observedRun, hs, pure_bind]
        simp only [Option.elim_some]
        rw [← observedRun, ← hcoh.signDigest, observed_signFinish aux hcoh _ (nv request.message) _ ws2]
        refine ⟨_, ?_, hfinal ws2 hro⟩
        rw [hreal, signedState_eq, if_pos hc]
        unfold startState
        rw [hm]
        rfl
  · rw [if_neg hc]
    have hnone : evalWithAnswerFn T (FullGame.authenticatedSign published request) = none := by
      rw [eval_authenticatedSign, if_neg hc]
    have hst : signedState T nv published st request = st := by rw [signedState_eq, if_neg hc]
    refine ⟨ws, ?_, ?_⟩
    · rw [hnone, hst]
      exact observed_pure aux q _ τ _ ws
    · exact hrel.afterSign published request ws (fun c _ => rfl) hrel.mem rfl (fun row v hv => Or.inl hv)

end SignMain

end SigGolfCandidate.T3.Security.LargeCoupling
