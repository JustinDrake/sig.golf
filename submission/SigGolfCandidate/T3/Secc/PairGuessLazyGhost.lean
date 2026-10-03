import SigGolfCandidate.T3.Secc.PairGuessLazyFree

section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem cell_not_digest (s : CanonGraph.Secrets) (node : CanonGraph.Node) (labels : CanonGraph.Labels) :
    CanonGraph.cell s node labels ∉ digestInputs := by
  have h := CanonGraph.hdrBlock_cell s node labels
  cases node <;> simp only [CanonGraph.Node.toPos, Extract.Pos.hdr] at h <;> exact not_digest_of_hdr h (by decide)
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
theorem answers_digest (ω : Omega U) (fts : FtsCoord → Digest) (x : HashInput) (hx : x ∈ digestInputs) :
    Omega.answers hU ω fts (.inl (.inr x)) = rowVal (digestOf ω) x := by
  rw [rowVal, dif_pos hx]
  change finiteHashAnswer ∅ U (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual) x =
    finiteHashAnswer ∅ U ω.residual x
  by_cases hxU : x ∈ U
  · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
    apply CanonGraph.programmed_other
    intro node he
    have hxe : x = CanonGraph.cell (ω.secrets fts) node ω.labels := he
    exact cell_not_digest _ node _ (hxe ▸ hx)
  · simp only [finiteHashAnswer, dif_neg hxU]
theorem eval_nonce (ω : Omega U) (fts : FtsCoord → Digest) (m : Message) :
    evalWithAnswerFn (Omega.answers hU ω fts) (privateNonce m) = nonceOf ω m := by
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other) (.inr (.inl m))).extractLsb' 0 128 = _
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low]
  exact splitEquiv_symm_other _ _ (nonceHalf m) (nonceHalf_not_secret m)
theorem signerRho_eq (ω : Omega U) (request : Request) : signerRho hU ω request = nonceOf ω request.message :=
  eval_nonce hU ω _ request.message
end Table
section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCouple : DecidableEq T3.Cache := Classical.decEq _
noncomputable def inlineWith (D : digestInputs → HashOutput) (Nn : Message → Digest) : QueryImpl WSpecL (OracleComp WSpec)
  | .inl (.coin n) => (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
  | .inl (.birth x) => pure (rowVal D x)
  | .inl (.trial x) => pure (rowVal D x)
  | .inl (.nonce m) => pure (Nn m)
  | .inl (.expose _) => pure ()
  | .inr q => liftM (WSpec.query (.inr q))
noncomputable def inlineAux (ω : Omega U) : QueryImpl WSpecL (OracleComp WSpec) := inlineWith (digestOf ω) (nonceOf ω)
theorem inline_hashL (ω : Omega U) (x : HashInput) : simulateQ (inlineAux ω) (hashL hU ω x) = hashW hU ω x := by
  unfold hashL hashW
  cases hd : decodeProbe x with
  | some p =>
      simp only [guessReq, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, inlineAux, inlineWith]
  | none =>
      by_cases hx : x ∈ digestInputs
      · simp only [if_pos hx, birthReq, simulateQ_spec_query, inlineAux, inlineWith]
        rw [answers_digest hU ω _ x hx]
      · simp only [if_neg hx, simulateQ_pure]
theorem eval_digestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    evalWithAnswerFn A (digestSearch rho m counter (fuel + 1)) =
      if digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true then
        some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))))
      else evalWithAnswerFn A (digestSearch rho m (counter + 1) fuel) := by
  rw [digestSearch, evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 counter)) =
    A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) from eval_query' A _]
  by_cases h : digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
theorem inline_searchL (ω : Omega U) (rho : Digest) (m : Message) (counter fuel : Nat) :
    simulateQ (inlineAux ω) (searchL rho m counter fuel) =
      pure (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (digestSearch rho m counter fuel)) := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
      rw [eval_digestSearch_succ, answers_digest hU ω _ _ (digestInput_mem _ _ _)]
      simp only [searchL, trialReq, simulateQ_bind, simulateQ_spec_query, inlineAux, inlineWith, pure_bind]
      by_cases h : digestAdmissible (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) = true
      · simp only [h, ↓reduceIte, simulateQ_pure]
      · simp only [h, ↓reduceIte, Bool.false_eq_true]
        exact ih _
theorem inline_disclosures (ω : Omega U) (positions : List FtsCoord) :
    simulateQ (inlineAux ω) (positions.mapM discloseReq) =
      positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest) := by
  induction positions with
  | nil => rfl
  | cons first rest ih =>
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind]
      simp only [discloseReq, simulateQ_spec_query, simulateQ_bind, ih, simulateQ_pure]
      simp only [inlineAux, inlineWith]
theorem inline_signL (ω : Omega U) (published : T3.Cache) (request : Request) :
    simulateQ (inlineAux ω) (signL hU ω published request) = signW hU ω published request := by
  unfold signW
  rw [openedFor_eq]
  simp only [sign_answers]
  unfold signL signWith signerOpened
  by_cases hc : request.cache = published
  · simp only [if_pos hc, nonceReq, exposeReq, simulateQ_bind, simulateQ_spec_query, inline_searchL hU ω]
    simp only [inlineAux, inlineWith, pure_bind]
    rw [← signerRho_eq hU ω request]
    change simulateQ (inlineAux ω) (finishL hU ω request (signerRho hU ω request) (signerFound hU ω request)) = _
    cases hf : signerFound hU ω request with
    | none => simp only [finishL, simulateQ_pure, List.mapM_nil, pure_bind]
    | some found =>
        obtain ⟨counter, output⟩ := found
        cases hl : signerLayers hU ω request output with
        | none => simp only [finishL, hl, simulateQ_pure, List.mapM_nil, pure_bind]
        | some pieces =>
            simp only [finishL, hl, simulateQ_bind, inline_disclosures, simulateQ_pure]
  · simp only [if_neg hc, simulateQ_pure, List.mapM_nil, pure_bind]
theorem interactionL_pure (ω : Omega U) (published : T3.Cache) {α : Type} (value : α) :
    interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : Omega U) (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : Omega U) (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : Omega U) (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signL hU ω published request >>= fun signature => interactionL hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : Omega U) {β : Type} (value : β) : programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => programL hU ω (next coin)) := rfl
theorem programL_public (ω : Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inr c)) >>= next) = programL hU ω (next 0) := rfl
theorem inline_interactionL (ω : Omega U) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (inlineAux ω) (interactionL hU ω published program) = interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionL_pure, interactionW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin, interactionW_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionL_public, interactionW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionL_request, interactionW_request, simulateQ_bind, inline_signL]
        refine bind_congr fun signature => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
theorem inline_programL (ω : Omega U) {β : Type} (program : M β) :
    simulateQ (inlineAux ω) (programL hU ω program) = programW hU ω program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programL_pure, programW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [programL_public, programW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [programL_private]
        exact ih (0 : HashOutput)
noncomputable abbrev worldGameL (ω : Omega U) (adversary : AdversaryP) := worldGameCore hU ω adversary
theorem worldGame_inline (ω : Omega U) (adversary : AdversaryP) :
    worldGame hU ω adversary = simulateQ (inlineAux ω) (worldGameL hU ω adversary) := by
  unfold worldGameL worldGameCore worldGame
  rw [simulateQ_bind, inline_interactionL]
  refine bind_congr fun interaction => ?_
  rw [simulateQ_bind, inline_programL]
  exact bind_congr fun verdict => by rw [simulateQ_pure]
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def forget (s : WStateL) : WState := ⟨s.allowed, s.retired, s.guesses, s.probes, PUnit.unit⟩
def Consistent (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ x a, mem.rows x = some a → a = rowVal D x) ∧ ∀ m v, mem.nonces m = some v → v = Nn m
theorem consistent_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Consistent D Nn LazyMem.empty :=
  by
  refine ⟨fun x a h => ?_, fun m v h => ?_⟩
  · simp [LazyMem.empty] at h
  · simp [LazyMem.empty] at h
theorem rowStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', Consistent D Nn mem' ∧ rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') := by
  have hreplay : Consistent D Nn (mem.replayRow x isBirth) := by
    unfold LazyMem.replayRow
    split
    · exact hm
    · exact hm
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
      change pure (a, mem.replayRow x isBirth) = _
      rw [hm.1 x a h]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ⟨?_, hm.2⟩, ?_⟩
        · intro y a hy
          change mem.rows.cacheQuery x (rowVal D x) y = some a at hy
          by_cases hyx : y = x
          · subst hyx
            rw [QueryCache.cacheQuery_self] at hy
            exact (Option.some.inj hy).symm
          · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
            exact hm.1 y a hy
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
      · refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (m : Message) :
    ∃ mem', Consistent D Nn mem' ∧ nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, hm, ?_⟩
      change pure (v, mem) = _
      rw [hm.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), ⟨hm.1, ?_⟩, map_pure _ _⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.2 m' v hv
theorem coin_spmf (n : Nat) : (liftM (liftM (coinImpl n) : PMF (Fin (n + 1))) : SPMF (Fin (n + 1))) =
    (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := evalSPMF_query (spec := unifSpec) n
theorem fixed_aux_pure {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem'))
    (next : AuxSpecL.Range input → OracleComp WSpecL α) :
    runWith (fixedImpl (envE D Nn) fts) (liftM (WSpecL.query (.inl input)) >>= next) s =
      runWith (fixedImpl (envE D Nn) fts) (next v) { s with memory := mem' } := by
  rw [SecretGuessObservation.runWith_query_bind]
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((envE D Nn).auxiliary s input) : SPMF _)) >>= _ = _
  rw [h, liftM_pure, map_pure, pure_bind]
theorem fixed_inline {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Consistent D Nn s.memory) :
    (fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) fts W s =
      fixedRun env fts (simulateQ (inlineWith D Nn) W) (forget s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => simp only [fixedRun, SecretGuessObservation.runWith_pure, simulateQ_pure, map_pure]
  | query_bind input next ih =>
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
            change ((fun result => (result.1, { s with memory := result.2 })) <$>
              (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) >>= _ =
              fixedRun env fts ((liftM (WSpec.query (.inl n)) : OracleComp WSpec _) >>= fun c =>
                simulateQ (inlineWith D Nn) (next c)) (forget s)
            rw [fixedRun, SecretGuessObservation.runWith_query_bind]
            change _ = ((fun result => (result.1, { forget s with memory := result.2 })) <$>
              (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) >>= _
            have hL : ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) =
                (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, Functor.map_map]
            have hR : ((fun result => (result.1, { forget s with memory := result.2 })) <$>
                (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) =
                (fun c => (c, forget s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, coin_spmf, Functor.map_map]
            rw [hL, hR]
            exact (bind_map_left _ _ _).trans ((bind_congr fun c => ih c s hs).trans
              (bind_map_left (fun c => (c, forget s)) _ (fun result =>
                runWith (fixedImpl env fts) (simulateQ (inlineWith D Nn) (next result.1)) result.2)).symm)
        | birth x =>
            obtain ⟨mem', hc, h⟩ := rowStep_eager D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn fts s (.birth x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | trial x =>
            obtain ⟨mem', hc, h⟩ := rowStep_eager D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn fts s (.trial x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | nonce m =>
            obtain ⟨mem', hc, h⟩ := nonceStep_eager D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn fts s (.nonce m) (Nn m) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (Nn m) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn fts s (.expose o) () (s.memory.expose o) rfl, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure () >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ ⟨hs.1, hs.2⟩
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (decide (fts f = c), SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) >>= _) =
          fixedRun env fts ((liftM (WSpec.query (.inr (.inl (f, c)))) : OracleComp WSpec Bool) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (decide (fts f = c), SecretGuessObservation.afterTrial env (forget s) f c (decide (fts f = c))) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (fts f, SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) >>= _) =
          fixedRun env fts ((liftM (WSpec.query (.inr (.inr f)))  : OracleComp WSpec Digest) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (fts f, SecretGuessObservation.afterDisclosure env (forget s) f (fts f)) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
theorem fixed_inline_nonzero {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (fts : FtsCoord → Digest) (W : OracleComp WSpecL α) (s : WStateL) (hs : Consistent D Nn s.memory)
    (r : α × WStateL) (hr : fixedRun (envE D Nn) fts W s r ≠ 0) :
    fixedRun env fts (simulateQ (inlineWith D Nn) W) (forget s) (r.1, forget r.2) ≠ 0 := by
  rw [← fixed_inline D Nn fts W s hs]
  have hm : r ∈ support (fixedRun (envE D Nn) fts W s) := by
    simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr
  have h : (r.1, forget r.2) ∈ support ((fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) fts W s) := by
    rw [support_map]
    exact ⟨r, hm, rfl⟩
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using h
end Run
section LazyCouple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
open SecretGuessObservation (fixedRun)
theorem forget_initL : forget initL = init := rfl
theorem fixed_worldGameL (fts : FtsCoord → Digest) (adversary : AdversaryP) :
    Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL =
      𝒮[pairRun (Omega.answers hU ω fts) adversary] := by
  have h := congrArg (Functor.map Prod.fst)
    (fixed_inline (digestOf ω) (nonceOf ω) fts (worldGameL hU ω adversary) initL (consistent_empty _ _))
  rw [Functor.map_map] at h
  rw [show (Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL) =
    (fun r => (r.1, forget r.2).1) <$> fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL
    from rfl, h, forget_initL, ← fixed_worldGame hU ω fts adversary]
  change _ = Prod.fst <$> fixedRun env fts (worldGame hU ω adversary) init
  rw [worldGame_inline]
  rfl
theorem worldGameL_tracking (fts : FtsCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.probes ≤ r.1.2.2.length ∧
      ∀ f, GuessedIn (Omega.answers hU ω fts) r.1.2.1 r.1.2.2 f → f ∈ r.2.guesses := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ initL (consistent_empty _ _) r hr
  rw [forget_initL] at h
  change fixedRun env fts (simulateQ (inlineAux ω) (worldGameL hU ω adversary)) init (r.1, forget r.2) ≠ 0 at h
  rw [← worldGame_inline] at h
  exact worldGame_tracking hU ω fts adversary (r.1, forget r.2) h
end LazyCouple
end SigGolfCandidate.T3.Security.BPair
end

section

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
section Ghost
open SecretGuessObservation (fixedRun fixedImpl runWith)
theorem runL_bind_nonzero {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL)
    (r : γ × WStateL) (hr : fixedRun E fts (first >>= next) s r ≠ 0) :
    ∃ mid, fixedRun E fts first s mid ≠ 0 ∧ fixedRun E fts (next mid.1) mid.2 r ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runL_pure_nonzero {β : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (v : β) (s : WStateL) (r : β × WStateL) (hr : fixedRun E fts (pure v) s r ≠ 0) :
    r = (v, s) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
structure Grows (m m' : LazyMem) : Prop where
  rows : ∀ x a, m.rows x = some a → m'.rows x = some a
  births : ∀ a ∈ m.births, a ∈ m'.births
  trials : ∀ x ∈ m.trials, x ∈ m'.trials
  exposures : ∀ o ∈ m.exposures, o ∈ m'.exposures
theorem Grows.refl (m : LazyMem) : Grows m m := ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
theorem Grows.trans {m1 m2 m3 : LazyMem} (h1 : Grows m1 m2) (h2 : Grows m2 m3) : Grows m1 m3 :=
  ⟨fun x a h => h2.rows x a (h1.rows x a h), fun a h => h2.births a (h1.births a h),
    fun x h => h2.trials x (h1.trials x h), fun o h => h2.exposures o (h1.exposures o h)⟩
def Good (D : digestInputs → HashOutput) (Nn : Message → Digest) (m : LazyMem) : Prop :=
  Consistent D Nn m ∧ ∀ x a, m.rows x = some a → a ∈ m.births ∨ x ∈ m.trials
theorem good_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Good D Nn LazyMem.empty :=
  ⟨consistent_empty D Nn, fun x a h => by simp [LazyMem.empty] at h⟩
theorem replayRow_true (mem : LazyMem) (x : HashInput) : mem.replayRow x true = mem := by
  simp [LazyMem.replayRow]
theorem replayRow_false (mem : LazyMem) (x : HashInput) :
    mem.replayRow x false = { mem with trials := mem.trials ++ [x] } := by
  simp [LazyMem.replayRow]
theorem readRow_true (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a true = { mem with rows := mem.rows.cacheQuery x a, births := mem.births ++ [a] } := by
  simp [LazyMem.readRow]
theorem readRow_false (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a false = { mem with rows := mem.rows.cacheQuery x a, trials := mem.trials ++ [x] } := by
  simp [LazyMem.readRow]
theorem cacheQuery_good (D : digestInputs → HashOutput) (mem : LazyMem) (x : HashInput) (y : HashInput) (b : HashOutput)
    (hy : mem.rows.cacheQuery x (rowVal D x) y = some b) :
    b = rowVal D x ∧ y = x ∨ mem.rows y = some b := by
  by_cases hyx : y = x
  · subst hyx
    rw [QueryCache.cacheQuery_self] at hy
    exact Or.inl ⟨(Option.some.inj hy).symm, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
    exact Or.inr hy
theorem rowStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') ∧ Good D Nn mem' ∧
      Grows mem mem' ∧ (x ∈ digestInputs → mem'.rows x = some (rowVal D x)) := by
  have hreplay : Good D Nn (mem.replayRow x isBirth) ∧ Grows mem (mem.replayRow x isBirth) := by
    cases isBirth
    · rw [replayRow_false]
      refine ⟨⟨hm.1, fun y a hy => ?_⟩, ⟨fun _ _ h => h, fun _ h => h, fun y h => List.mem_append_left _ h,
        fun _ h => h⟩⟩
      rcases hm.2 y a hy with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · rw [replayRow_true]
      exact ⟨hm, Grows.refl mem⟩
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      have ha := hm.1.1 x a h
      refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun _ => ?_⟩
      · change pure (a, mem.replayRow x isBirth) = _
        rw [ha]
      · rw [hreplay.2.rows x a h, ha]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ?_, ?_, ?_, fun _ => ?_⟩
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
        · cases isBirth
          · rw [readRow_false]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_append_left _ h)
          · rw [readRow_true]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl (List.mem_append_left _ h)
                · exact Or.inr h
        · have hrows : ∀ y b, mem.rows y = some b → mem.rows.cacheQuery x (rowVal D x) y = some b := by
            intro y b hy
            have hyx : y ≠ x := by
              rintro rfl
              rw [h] at hy
              cases hy
            rw [QueryCache.cacheQuery_of_ne _ _ hyx]
            exact hy
          cases isBirth
          · rw [readRow_false]
            exact ⟨hrows, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
          · rw [readRow_true]
            exact ⟨hrows, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
        · cases isBirth
          · rw [readRow_false]
            exact QueryCache.cacheQuery_self _ _ _
          · rw [readRow_true]
            exact QueryCache.cacheQuery_self _ _ _
      · refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun h' => absurd h' hx⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (m : Message) :
    ∃ mem', nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') ∧ Good D Nn mem' ∧ Grows mem mem' := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, ?_, hm, Grows.refl mem⟩
      change pure (v, mem) = _
      rw [hm.1.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), map_pure _ _, ⟨⟨hm.1.1, ?_⟩, hm.2⟩,
        ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.1.2 m' v hv
theorem expose_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (o : Option HashOutput) : Good D Nn (mem.expose o) ∧ Grows mem (mem.expose o) :=
  ⟨hm, ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩⟩
theorem fixed_aux_single (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem')) :
    fixedRun (envE D Nn) fts (liftM (WSpecL.query (.inl input))) s = pure (v, { s with memory := mem' }) := by
  rw [fixedRun, ← bind_pure (liftM (WSpecL.query (.inl input))), fixed_aux_pure D Nn fts s input v mem' h,
    SecretGuessObservation.runWith_pure]
theorem run_good {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Good D Nn s.memory) (r : α × WStateL)
    (hr : fixedRun (envE D Nn) fts W s r ≠ 0) : Good D Nn r.2.memory ∧ Grows s.memory r.2.memory := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      rw [runL_pure_nonzero _ fts a s r hr]
      exact ⟨hs, Grows.refl _⟩
  | query_bind input next ih =>
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            unfold fixedRun at hr
            rw [SecretGuessObservation.runWith_query_bind, RetainedObservation.bind_nonzero] at hr
            obtain ⟨mid, hm, hr⟩ := hr
            have hmid : mid.2 = s := by
              change ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) mid ≠ 0 at hm
              rw [liftM_map, Functor.map_map] at hm
              simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
                SPMF.pure_apply_eq_zero_iff, not_not] at hm
              obtain ⟨c, _, rfl⟩ := hm
              rfl
            obtain ⟨h1, h2⟩ := ih mid.1 mid.2 (by rw [hmid]; exact hs) hr
            rw [hmid] at h2
            exact ⟨h1, h2⟩
        | birth x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn fts s (.birth x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | trial x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn fts s (.trial x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | nonce m =>
            obtain ⟨mem', heq, hg, hgr⟩ := nonceStep_ghost D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn fts s (.nonce m) (Nn m) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn fts s (.expose o) () (s.memory.expose o) rfl] at hr
            have he := expose_ghost D Nn s.memory hs o
            obtain ⟨h1, h2⟩ := ih () { s with memory := s.memory.expose o } he.1 hr
            exact ⟨h1, he.2.trans h2⟩
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (decide (fts f = c), SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) :
          SPMF (Bool × WStateL)) >>= fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) hs hr
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (fts f, SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) : SPMF (Digest × WStateL)) >>=
          fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) hs hr
end Ghost
section WorldGhost
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessLazyGhost : DecidableEq T3.Cache := Classical.decEq _
theorem hashL_ghost (fts : FtsCoord → Digest) (x : HashInput) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (hashL hU ω x) s r ≠ 0) (hx : x ∈ digestInputs) :
    r.2.memory.rows x = some r.1 := by
  have hd : decodeProbe x = none := by
    cases hd : decodeProbe x with
    | none => rfl
    | some p =>
        have hpx := eq_of_decodeProbe hd
        rw [hpx] at hx
        exact absurd hx (probeInput_not_digest p.1 p.2)
  unfold hashL at hr
  rw [hd] at hr
  dsimp only at hr
  rw [if_pos hx] at hr
  obtain ⟨mem', heq, -, -, hrow⟩ := rowStep_ghost (digestOf ω) (nonceOf ω) s.memory hs x true
  rw [birthReq, fixed_aux_single (digestOf ω) (nonceOf ω) fts s (.birth x) _ mem' heq] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst hr
  exact hrow hx
theorem finishL_some (fts : FtsCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (finishL hU ω request rho found) s r ≠ 0)
    (σ : Signature) (hσ : r.1 = some σ) : ∃ c out, found = some (c, out) ∧ σ.rho = rho := by
  cases found with
  | none =>
      rw [runL_pure_nonzero _ fts _ s r hr] at hσ
      cases hσ
  | some found =>
      obtain ⟨c, out⟩ := found
      refine ⟨c, out, rfl, ?_⟩
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
          rw [runL_pure_nonzero _ fts _ s r hr] at hσ
          cases hσ
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, -, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
          rw [runL_pure_nonzero _ fts _ _ r hr] at hσ
          cases hσ
          exact Correctness.assembledSignature_rho _ _ _
theorem signL_ghost (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (signL hU ω published request) s r ≠ 0)
    (σ : Signature) (output : HashOutput) (hσ : r.1 = some σ)
    (ho : signedOutput (Omega.answers hU ω fts) request.message σ = some output) :
    output ∈ r.2.memory.exposures := by
  unfold signL at hr
  by_cases hc : request.cache = published
  · rw [if_pos hc] at hr
    obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
    obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
    obtain ⟨m3, h3, hr⟩ := runL_bind_nonzero _ fts _ _ m2.2 r hr
    have g1 := run_good _ _ fts _ s hs m1 h1
    have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
    have hv1 : m1.1 = nonceOf ω request.message := by
      have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ s hs.1 m1 h1
      rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (nonceReq request.message) =
        pure (nonceOf ω request.message) from by simp only [nonceReq, simulateQ_spec_query, inlineWith]] at h
      exact congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h)
    have hv2 : m2.1 = evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
        (digestSearch m1.1 request.message 0 attemptLimit) := by
      have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) fts _ m1.2 g1.1.1 m2 h2
      change fixedRun env fts (simulateQ (inlineAux ω) (searchL m1.1 request.message 0 attemptLimit)) (forget m1.2)
        (m2.1, forget m2.2) ≠ 0 at h
      rw [inline_searchL hU ω] at h
      exact congrArg Prod.fst (fixedRun_pure_nonzero fts _ _ _ h)
    have hm3 : m3.2.memory = m2.2.memory.expose (m2.1.map Prod.snd) := by
      rw [exposeReq, fixed_aux_single (digestOf ω) (nonceOf ω) fts m2.2 (.expose _) () _ rfl] at h3
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h3
      subst h3
      rfl
    have g3' := run_good _ _ fts _ m2.2 g2.1 m3 h3
    have g3 := run_good _ _ fts _ m3.2 g3'.1 r hr
    obtain ⟨c, out, hfound, hrho⟩ := finishL_some hU ω fts request m1.1 m2.1 m3.2 r hr σ hσ
    have hout : output = out := by
      rw [signedOutput_free hU ω fts] at ho
      unfold signedOutput at ho
      rw [hrho, ← hv2, hfound] at ho
      exact (Option.some.inj ho).symm
    subst hout
    apply g3.2.exposures
    rw [hm3, hfound]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [if_neg hc] at hr
    rw [runL_pure_nonzero _ fts _ s r hr] at hσ
    cases hσ
theorem interactionL_ghost (fts : FtsCoord → Digest) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory)
    (r : (α × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (interactionL hU ω published program) s r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        signedOutput (Omega.answers hU ω fts) entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
      ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [interactionL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact ⟨fun _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        exact ih m1.1 m1.2 (run_good _ _ fts _ s hs m1 h1).1 r hr
      · rw [interactionL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
        obtain ⟨i1, i2⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨i1, fun y a hy hdy => ?_⟩
        rcases List.mem_cons.mp hy with he | hy
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact g2.2.rows _ _ (hashL_ghost hU ω fts y s hs m1 h1 hdy)
        · exact i2 y a hy hdy
      · rw [interactionL_request] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
        obtain ⟨i1, i2⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨fun entry he σ output hσ ho => ?_, i2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he
          exact g2.2.exposures _ (signL_ghost hU ω fts published request s hs m1 h1 σ output hσ ho)
        · exact i1 entry he σ output hσ ho
theorem programL_ghost (fts : FtsCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (programL hU ω program) s r ≠ 0) :
    ∀ x a, (x, a) ∈ r.1.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact fun _ _ h => (by simp at h)
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        exact ih m1.1 m1.2 (run_good _ _ fts _ s hs m1 h1).1 r hr
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
        have i2 := ih m1.1 m1.2 g1.1 m2 h2
        intro y a hy hdy
        rcases List.mem_cons.mp hy with he | hy
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact g2.2.rows _ _ (hashL_ghost hU ω fts y s hs m1 h1 hdy)
        · exact i2 y a hy hdy
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr
theorem worldGameL_ghosts (fts : FtsCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (worldGameL hU ω adversary) initL r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        signedOutput (Omega.answers hU ω fts) entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
      ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials) := by
  have g0 := run_good _ _ fts _ initL (good_empty _ _) r hr
  unfold worldGameL worldGameCore at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ initL r hr
  obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
  have hrr := runL_pure_nonzero _ fts _ _ r hr
  have g1 := run_good _ _ fts _ initL (good_empty _ _) m1 h1
  have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
  obtain ⟨i1, i2⟩ := interactionL_ghost hU ω fts _ _ initL (good_empty _ _) m1 h1
  have p2 := programL_ghost hU ω fts _ m1.2 g1.1 m2 h2
  have hrows : ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
    rw [hrr]
    intro x a hx hdx
    rcases List.mem_append.mp hx with hx | hx
    · exact g2.2.rows _ _ (i2 x a hx hdx)
    · exact p2 x a hx hdx
  refine ⟨?_, fun x a hx hdx => ⟨hrows x a hx hdx, g0.1.2 x a (hrows x a hx hdx)⟩⟩
  rw [hrr]
  intro entry he σ output hσ ho
  exact g2.2.exposures _ (i1 entry he σ output hσ ho)
end WorldGhost
end SigGolfCandidate.T3.Security.BPair
end
