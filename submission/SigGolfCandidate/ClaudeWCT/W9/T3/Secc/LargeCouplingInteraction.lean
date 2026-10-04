import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingQuery
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactMonitor
import SigGolfCandidate.T3.Secc.LargeCouplingSigning
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingSplit
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportTable
import SigGolfCandidate.T3.Secc.LargeCouplingVerdict
import SigGolfCandidate.T3.Secc.LargeCouplingInteraction
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (slotValue digestIndex routeAddr IsDigestRow State Cell observedRun
  readState disclosedState runWith_bind observed_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (digestRow_isDigest digestRow_mem)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingSigning : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
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
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)
theorem observed_search (T : Answers) (rho : Digest) (m : Message)
    (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U)
    (hT : ∀ c : BitVec 32, T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, hU c⟩) :
    ∀ (fuel c : Nat) (ws : LargeResidual.State WCoord (Cell U)), ∃ ws',
      observedRun aux q labels τ (simulateQ (readImpl U a) (WCT9.digestSearch rho m c fuel)) ws =
        pure (some (evalWithAnswerFn T (WCT9.digestSearch rho m c fuel)), ws') ∧ ReadsOnly τ ws ws' := by
  intro fuel
  induction fuel with
  | zero =>
      intro c ws
      refine ⟨ws, ?_, ReadsOnly.refl τ ws⟩
      simp only [WCT9.digestSearch, simulateQ_pure, evalWithAnswerFn_pure]
      exact observed_pure aux q labels τ _ ws
  | succ fuel ih =>
      intro c ws
      rw [show WCT9.digestSearch rho m c (fuel + 1) = (digest rho m (BitVec.ofNat 32 c) >>= fun output =>
          if WCT9.admissible output = true then pure (some (BitVec.ofNat 32 c, output))
          else WCT9.digestSearch rho m (c + 1) fuel) from rfl]
      simp only [digest, publicHash, simulateQ_bind, evalWithAnswerFn_bind]
      have hq : simulateQ (readImpl U a) (SigGolfCandidate.T3.Spec.query
          (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
          M HashOutput) = readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
        change simulateQ (readImpl U a) (liftM (SigGolfCandidate.T3.Spec.query _)) = _
        rw [simulateQ_spec_query]
        simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]
      rw [hq, observed_readReq]
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩
      have hTX : (evalWithAnswerFn T (SigGolfCandidate.T3.Spec.query
          (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) :
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
      by_cases hadm : WCT9.admissible (τ X) = true
      · simp only [hadm, if_true, simulateQ_pure, evalWithAnswerFn_pure]
        exact ⟨_, observed_pure aux q labels τ _ _, hrd⟩
      · simp only [hadm, Bool.false_eq_true, if_false]
        obtain ⟨ws', h1, h2⟩ := ih (c + 1) (readState q ws X (τ X) .none)
        exact ⟨ws', h1, hrd.trans h2⟩
end Search
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.digestRow (hcoh : Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest)
    (m : Message) (c : BitVec 32) :
    T (.inl (.inr (pad64 (digestInput rho m c)))) = τ ⟨_, digestRow_mem hUpub rho m c⟩ := by
  have hd := digestRow_isDigest rho m c
  have hnp := not_parsed_of_digest hd
  apply hcoh.residual _ _ (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N')
  rintro ⟨L, ctr, hX, -⟩
  exact encRow_not_digest L _ ctr (hX ▸ hd)
theorem Coherent.privateNonce (hcoh : Coherent U T vals nv τ a) (m : Message) :
    evalWithAnswerFn T (SigGolfCandidate.T3.privateNonce m) = nv m := by
  simp only [SigGolfCandidate.T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact hcoh.nonce m
theorem Coherent.signDigest (hcoh : Coherent U T vals nv τ a) (m : Message) :
    LargeResidual.signDigest T m =
      evalWithAnswerFn T (WCT9.digestSearch (nv m) m 0 WCT9.digestAttemptLimit) := by
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
      fun k => ⟨fun t => v (wctItem (digestIndex N, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)),
        fun l => ((wctPath (digestIndex N) k N).map v).getD l.val 0⟩,
      fun lay => piecesSignature lay ((layerChains d (digestIndex N) lay).map v, (layerPath (digestIndex N) lay).map v)⟩ :=
  rfl
theorem assembleSig_congr (rho : Digest) (N : HashOutput) (v v' : Coord → Digest) (d : Wots.LeafAddr → List Nat)
    (h : ∀ c ∈ signItemsWith d N, v c = v' c) : assembleSig rho N v d = assembleSig rho N v' d := by
  rw [assembleSig_def, assembleSig_def]
  have hfts : ∀ c ∈ ftsItems (digestIndex N) N, v c = v' c := fun c hc =>
    h c (List.mem_append_left _ hc)
  have hlay : ∀ c ∈ layerItems d (digestIndex N), v c = v' c := fun c hc => h c (List.mem_append_right _ hc)
  have hopen : ∀ (k : Fin 9) (t : Fin 7),
      v (wctItem (digestIndex N, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)) =
        v' (wctItem (digestIndex N, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)) := by
    intro k t
    apply hfts
    have ho : wctItem (digestIndex N, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t) ∈
        wctOpened (digestIndex N) k N := by
      unfold wctOpened
      exact List.mem_ofFn.mpr ⟨t, rfl⟩
    exact List.mem_flatMap.mpr ⟨k, List.mem_finRange k, List.mem_append_left _ ho⟩
  have hpath : ∀ k : Fin 9, (wctPath (digestIndex N) k N).map v = (wctPath (digestIndex N) k N).map v' := by
    intro k
    apply List.map_congr_left
    intro c hc
    exact hfts c (List.mem_flatMap.mpr ⟨k, List.mem_finRange k, List.mem_append_right _ hc⟩)
  congr 1
  · funext k
    congr 1
    · funext t
      exact hopen k t
    · rw [hpath k]
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
def MemoOk (T : Answers) (st : RouterState) : Prop :=
  ∀ m f, st.memo.lookup m = some f → f = LargeResidual.signDigest T m
noncomputable def signedState (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) : RouterState :=
  if request.cache = published then
    let st1 := if (st.memo.lookup request.message).isSome then st
      else st.signed (nv request.message) request.message (LargeResidual.signDigest T request.message)
    match LargeResidual.signDigest T request.message with
    | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
        { st1 with disclosed := st1.disclosed ++ LargeResidual.signItems T N } else st1
    | none => st1
  else st
noncomputable def finishState (T : Answers) (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  match found with
  | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
      { st1 with disclosed := st1.disclosed ++ LargeResidual.signItems T N } else st1
  | none => st1
noncomputable def startState (T : Answers) (nv : Message → Digest) (st : RouterState) (m : Message) : RouterState :=
  if (st.memo.lookup m).isSome then st else st.signed (nv m) m (LargeResidual.signDigest T m)
theorem signedState_eq (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
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
theorem signedState_disclosed (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).disclosed = st.disclosed ++ signDisclosed T published request := by
  rw [signedState_eq]
  unfold signDisclosed
  split_ifs with hc
  · rw [(finishState_fields _ _ _).1, (startState_fields _ _ _ _).1]
    congr 1
  · simp
theorem signedState_seen (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    (signedState T nv published st request).seen = st.seen ∧ (signedState T nv published st request).calls = st.calls := by
  rw [signedState_eq]
  split_ifs with hc
  · rw [(finishState_fields _ _ _).2.1, (finishState_fields _ _ _).2.2.1, (startState_fields _ _ _ _).2.1,
      (startState_fields _ _ _ _).2.2.1]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
theorem signedState_memo (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
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
theorem eval_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request) :
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
noncomputable def finishOut (T : Answers) (vals : Coord → Digest) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    Option Signature :=
  match found with
  | some (_, N) => if RouteOk T (N.toNat % 2 ^ 31) then
      some (assembleSig rho N vals (Wots.referenceDigits T)) else none
  | none => none
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
theorem known_signed (published : SigGolfCandidate.T3.Cache) (request : Security.Request) (c : Coord) (hc : st.known c) :
    (signedState T nv published st request).known c := by
  unfold RouterState.known at hc ⊢
  refine Known.mono (fun d hd => ?_) hc
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    rw [signedState_disclosed]
    exact List.mem_append_left _ hd
theorem known_signed_new (published : SigGolfCandidate.T3.Cache) (request : Security.Request) (c : Coord)
    (hc : c ∈ signDisclosed T published request) : (signedState T nv published st request).known c := by
  apply Known.base
  right
  rw [signedState_disclosed]
  exact List.mem_append_right _ hc
theorem Rel.afterSign (hrel : Rel U T vals nv τ a q mon st ws) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
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
    exact fun c hc => known_signed published request _ (hrel.seenEnc X hX hXU L ctr hL c hc)
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
theorem finishOut_real (hcoh : Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T)) (request : Security.Request)
    (hc : request.cache = published) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      finishOut T vals (nv request.message) (LargeResidual.signDigest T request.message) := by
  rw [authenticatedSign_disclosed hcoh.agrees published hpub, if_pos hc, hcoh.honestValue, hcoh.privateNonce]
  unfold finishOut
  rcases LargeResidual.signDigest T request.message with _ | ⟨c, N⟩
  · rfl
  · dsimp only
theorem routeSign_observed (hcoh : Coherent U T vals nv τ a) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
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
          request.message (digestRow_mem hUpub _ _) (hcoh.digestRow hUpub _ _) WCT9.digestAttemptLimit 0 ws1
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
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def taggedFixed {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) : LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let answer ← Wots.Ref.fixedWorld F (.inl world)
          (fun last => (⟨last.value, .world ⟨state, .inl world, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next answer (FirstHit.advance state (.inl world) answer)
      | .inr request, next => do
          let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
section Fixed
variable {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
theorem taggedFixed_pure (value : α) (state : LazyPrivate.State) :
    taggedFixed F published (pure value : OracleComp LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedFixed_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let answer ← Wots.Ref.fixedWorld F (.inl input)
      (fun last => (⟨last.value, .world ⟨state, .inl input, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next answer) (FirstHit.advance state (.inl input) answer)) := rfl
theorem taggedFixed_request (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next block.value) block.state) := rfl
theorem taggedFixed_support (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State)
    (hF : Wots.Ref.Agrees F state) (tagged : Tagged α) (h : tagged ∈ support (taggedFixed F published program state)) :
    tagged ∈ support (taggedRecord published program state) ∧ Wots.Ref.Agrees F tagged.state := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedFixed_pure, mem_support_pure_iff] at h
      subst h
      exact ⟨by rw [taggedRecord_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, mem_support_bind_iff] at h
          obtain ⟨answer, ha, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hcons : ∀ cached, SourceReplay.known state (.inl input) = some cached → cached = answer := by
            intro cached hc
            rcases input with n | x
            · cases hc
            · have h1 := hF _ _ hc
              rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              rw [ha, ← h1]
          have hadv : Wots.Ref.Agrees F (FirstHit.advance state (.inl input) answer) := by
            rcases input with n | x
            · exact hF
            · rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              subst ha
              exact Wots.Ref.agrees_advance hF _
          obtain ⟨h1, h2⟩ := ih answer _ hadv last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_world, mem_support_bind_iff]
          refine ⟨(answer, FirstHit.advance state (.inl input) answer),
            Wots.Ref.lazy_query_mem state (.inl input) answer hcons, ?_⟩
          rw [support_map]
          exact ⟨last, h1, rfl⟩
      | inr request =>
          rw [taggedFixed_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          obtain ⟨hb1, hb2⟩ := Wots.Ref.fixedRecord_mem_record F _ state hF block hb
          obtain ⟨h1, h2⟩ := ih block.value block.state hb2 last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_request, mem_support_bind_iff]
          exact ⟨block, hb1, by rw [support_map]; exact ⟨last, h1, rfl⟩⟩
theorem taggedFixed_untag (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    Tagged.untag <$> taggedFixed F published program state =
      Wots.Ref.fixedRecord F (FullGame.loggedWith (FullGame.authenticatedSign published) program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [taggedFixed_pure, map_pure, FullGame.loggedWith_pure, Wots.Ref.fixedRecord_pure]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, FullGame.loggedWith_world]
          change _ = Wots.Ref.fixedRecord F (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state
          rw [Wots.Ref.fixedRecord_query_bind, map_bind]
          apply bind_congr
          intro answer
          rw [Functor.map_map, ← ih answer]
          simp only [Functor.map_map]
          rfl
      | inr request =>
          rw [taggedFixed_request, FullGame.loggedWith_request, Wots.Ref.fixedRecord_bind, map_bind]
          apply bind_congr
          intro block
          rw [Wots.Ref.fixedRecord_map, ← ih block.value, Functor.map_map, Functor.map_map,
            map_eq_bind_pure_comp]
          simp only [Function.comp_def, bind_pure_comp, Functor.map_map]
          rfl
end Fixed
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell observedRun runWith_bind observed_pure)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingVerdict : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Monitor
variable (U : Finset HashInput) (A : Answers) (q : Nat)
theorem query_frozen (mon : Monitor) (h : mon.contact = true) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon := by
  unfold Monitor.query; rw [if_pos h]
theorem event_frozen (mon : Monitor) (h : mon.contact = true) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_frozen U A q mon h X answer
  · rfl
theorem events_frozen (mon : Monitor) (h : mon.contact = true) (events : List FirstHit.QueryEvent) :
    events.foldl (Monitor.event U A q) mon = mon := by
  induction events with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, event_frozen U A q mon h e, ih]
theorem query_over (mon : Monitor) (hc : mon.contact = false) (hq : q ≤ mon.calls) (X : HashInput)
    (y : HashOutput) : (mon.query U A q X y).contact = false ∧ q < (mon.query U A q X y).calls := by
  unfold Monitor.query
  rw [if_neg (by rw [hc]; decide), if_neg (fun h => by omega)]
  exact ⟨rfl, show q < mon.calls + 1 by omega⟩
theorem event_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (e : FirstHit.QueryEvent) :
    (mon.event U A q e).contact = false ∧ q < (mon.event U A q e).calls := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · exact ⟨hc, hq⟩
  · exact query_over U A q mon hc (by omega) X answer
  · exact ⟨hc, hq⟩
theorem events_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (events : List FirstHit.QueryEvent) :
    (events.foldl (Monitor.event U A q) mon).contact = false ∧ q < (events.foldl (Monitor.event U A q) mon).calls := by
  induction events generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := event_over U A q mon hc hq e
      exact ih _ h1 h2
end Monitor
noncomputable def routerEvent (U : Finset HashInput) (st : RouterState) (e : FirstHit.QueryEvent) : RouterState :=
  match e with
  | ⟨_, .inl (.inr X), y⟩ => st.next U X y
  | _ => st
def PhaseOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) {β : Type} (monF : Monitor) (value : β) (stF : RouterState)
    (out : Option (Option (β × RouterState))) (ws' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (out = none ∧ monF.contact = true ∧ ws'.counters.calls ≤ q) ∨
    (out = some none ∧ monF.contact = false ∧ q < monF.calls) ∨
    (out = some (some (value, stF)) ∧ Rel U T vals nv τ a q monF stF ws')
section Verdict
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem routeVerdict_pure {β : Type} (v : β) (st : RouterState) :
    routeVerdict U a q (pure v : M β) st = pure (some (v, st)) := rfl
theorem routeVerdict_public {β : Type} (X : HashInput) (next : HashOutput → M β) (st : RouterState) :
    routeVerdict U a q (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else (routeQuery U a st X >>= fun r => routeVerdict U a q (next r.1) r.2) := rfl
theorem routeVerdict_observed (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) {β : Type} (V : M β)
    (hV : PublicVerdict.Only V) :
    ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
      Rel U T vals nv τ a q mon st ws →
      ∃ out ws', observedRun aux q (Sum.elim vals nv) τ (routeVerdict U a q V st) ws = pure (out, ws') ∧
        PhaseOutcome U T vals nv τ a q ((Wots.Ref.pureRecord T V state).events.foldl (Monitor.event U T q) mon)
          (evalWithAnswerFn T V) ((Wots.Ref.pureRecord T V state).events.foldl (routerEvent U) st) out ws' := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro mon st ws state hrel
      refine ⟨some (some (v, st)), ws, ?_, Or.inr (Or.inr ⟨rfl, hrel⟩)⟩
      rw [routeVerdict_pure]
      exact observed_pure aux q _ τ _ ws
  | query_bind input next ih =>
      intro mon st ws state hrel
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hV
      rcases input with (n | X) | c
      · exact False.elim hi
      · rw [Wots.Ref.pureRecord_query_bind]
        simp only [List.foldl_cons]
        rw [routeVerdict_public]
        by_cases hb : q ≤ st.calls
        · rw [if_pos hb]
          refine ⟨some none, ws, observed_pure aux q _ τ _ ws, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
          have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
          exact events_over U T q _ h1.1 h1.2 _
        · rw [if_neg hb]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed aux hcoh hrel hlt hq X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          · refine ⟨none, ws1, ?_, Or.inl ⟨rfl, ?_, hcalls⟩⟩
            · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
              rfl
            · change (List.foldl (Monitor.event U T q) (mon.query U T q X (T (.inl (.inr X)))) _).contact = true
              rw [events_frozen U T q _ hc]
              exact hc
          · obtain ⟨out, ws2, hrun2, hph⟩ := ih (T (.inl (.inr X))) (hn _) _ _ ws1 _ hrel1
            refine ⟨out, ws2, ?_, hph⟩
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            exact hrun2
      · exact False.elim hi
end Verdict
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell observedRun runWith_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def routerStep (U : Finset HashInput) (T : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) : TaggedStep → RouterState
  | .world e => routerEvent U st e
  | .sign request _ _ => signedState T nv published st request
section Steps
variable (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
theorem steps_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (steps : List TaggedStep) :
    (steps.foldl (Monitor.step U A q published) mon).contact = false ∧
      q < (steps.foldl (Monitor.step U A q published) mon).calls := by
  induction steps generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).1
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            rfl
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).2
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            exact hq
theorem steps_frozen (mon : Monitor) (hc : mon.contact = true) (steps : List TaggedStep) :
    steps.foldl (Monitor.step U A q published) mon = mon := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = mon := by
        cases s with
        | world e => exact event_frozen U A q mon hc e
        | sign request out events => simp only [Monitor.step, Monitor.sign, hc, if_true]
      rw [h1, ih]
end Steps
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem routeInteraction_pure {α : Type} (published : SigGolfCandidate.T3.Cache) (v : α) (st : RouterState) :
    routeInteraction U a published q (pure v : OracleComp LazyPrivate.Interaction α) st = pure (some ((v, []), st)) :=
  rfl
theorem routeInteraction_coin {α : Type} (published : SigGolfCandidate.T3.Cache) (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) st =
      (coinReq U n >>= fun c => routeInteraction U a published q (next c) st) := rfl
theorem routeInteraction_hash {α : Type} (published : SigGolfCandidate.T3.Cache) (X : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else
        (routeQuery U a st X >>= fun r => routeInteraction U a published q (next r.1) r.2) := rfl
theorem routeInteraction_request {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) st =
      (routeSign U a published st request >>= fun s =>
        routeInteraction U a published q (next s.1) s.2 >>= fun rest =>
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2))) := rfl
theorem interaction_le (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q → F (none, ws')) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop mon st ws state hrel hmemo
      rcases input with (n | X) | request
      ·
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop mon st ws _ hrel hmemo
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rw [probEvent_pure, if_pos (hstop ws1 hcalls)]
            exact probEvent_le_one
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop _ _ ws1 _ hrel1 hmemo1
      ·
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hpub hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
