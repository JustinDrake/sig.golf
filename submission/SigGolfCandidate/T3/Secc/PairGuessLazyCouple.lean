import SigGolfCandidate.T3.Secc.PairGuessLazyFree

/-!
# B-PAIR (CC-2, 4/5): the lazy world is the world with its auxiliary oracle inlined

`inlineAux ω` answers the auxiliary oracle of `WSpecL` from `ω` (digest rows by `digestOf ω`, nonces by
`nonceOf ω`, exposures trivially). The original world program is the inlined lazy one
(`worldGame_inline : worldGame ω = simulateQ (inlineAux ω) (worldGameL ω)`), and a fixed run of `worldGameL` in
the eager environment of `ω`'s own tables projects to the fixed run of `worldGame` (`fixed_inline`). Hence the
coupling (`fixed_worldGameL`, `worldGameL_tracking`) carries over.
-/

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

/-! ## Digest rows and nonces of the eager table -/

theorem cell_not_digest (s : CanonGraph.Secrets) (node : CanonGraph.Node) (labels : CanonGraph.Labels) :
    CanonGraph.cell s node labels ∉ digestInputs := by
  have h := CanonGraph.hdrBlock_cell s node labels
  cases node <;> simp only [CanonGraph.Node.toPos, Extract.Pos.hdr] at h <;> exact not_digest_of_hdr h (by decide)

section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)

/-- The eager table at a digest row is `ω`'s digest-row table. -/
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

/-- The eager table's nonce is `ω`'s nonce table. -/
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

/-! ## The inlined auxiliary oracle -/

section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCouple : DecidableEq T3.Cache := Classical.decEq _

/-- The auxiliary oracle answered from tables `D` (digest rows) and `Nn` (nonces). -/
noncomputable def inlineWith (D : digestInputs → HashOutput) (Nn : Message → Digest) : QueryImpl WSpecL (OracleComp WSpec)
  | .inl (.coin n) => (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
  | .inl (.birth x) => pure (rowVal D x)
  | .inl (.trial x) => pure (rowVal D x)
  | .inl (.nonce m) => pure (Nn m)
  | .inl (.expose _) => pure ()
  | .inr q => liftM (WSpec.query (.inr q))

/-- The auxiliary oracle answered from `ω`. -/
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

/-! ### Equation lemmas of the lazy world programs -/

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

/-- The lazy world program (the interface name). -/
noncomputable abbrev worldGameL (ω : Omega U) (adversary : AdversaryP) := worldGameCore hU ω adversary

/-- **The world program is the lazy one with its auxiliary oracle inlined.** -/
theorem worldGame_inline (ω : Omega U) (adversary : AdversaryP) :
    worldGame hU ω adversary = simulateQ (inlineAux ω) (worldGameL hU ω adversary) := by
  unfold worldGameL worldGameCore worldGame
  rw [simulateQ_bind, inline_interactionL]
  refine bind_congr fun interaction => ?_
  rw [simulateQ_bind, inline_programL]
  exact bind_congr fun verdict => by rw [simulateQ_pure]

end Inline

/-! ## The eager run of the lazy world projects to the run of the world -/

section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)

/-- The world state of a lazy-world state (memory forgotten). -/
def forget (s : WStateL) : WState := ⟨s.allowed, s.retired, s.guesses, s.probes, PUnit.unit⟩

/-- The lazy memory agrees with the eager tables `D`, `Nn`. -/
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

/-- An eager auxiliary step answering `v` deterministically. -/
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

/-- **Projection**: with memory consistent with `D`, `Nn`, the eager run of a lazy-world program projects to the
world run of the program with its auxiliary oracle answered from `D`, `Nn`. -/
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

/-! ## The coupling of the lazy world -/

section LazyCouple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
open SecretGuessObservation (fixedRun)

theorem forget_initL : forget initL = init := rfl

/-- **Coupling (law)**: the eager run of the lazy world with `ω`'s own tables is the reference run. -/
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

/-- **Coupling (tracking)**: probes are bounded by the recorded entries, and every guessed secret is a guess. -/
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
