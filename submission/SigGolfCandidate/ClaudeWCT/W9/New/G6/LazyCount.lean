import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyCouple

section

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep NotDN
  Grows Good good_empty rowStep_ghost nonceStep_ghost expose_ghost)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Ghost
open SecretGuessObservation (fixedRun fixedImpl runWith)
theorem runL_bind_nonzero {β γ : Type}
    (E : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem)
    (g : Guess.GCoord → Digest) (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL)
    (r : γ × WStateL) (hr : fixedRun E g (first >>= next) s r ≠ 0) :
    ∃ mid, fixedRun E g first s mid ≠ 0 ∧ fixedRun E g (next mid.1) mid.2 r ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runL_pure_nonzero {β : Type} (E : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem)
    (g : Guess.GCoord → Digest) (v : β) (s : WStateL) (r : β × WStateL) (hr : fixedRun E g (pure v) s r ≠ 0) :
    r = (v, s) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixed_aux_single (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem')) :
    fixedRun (envE D Nn) g (liftM (WSpecL.query (.inl input))) s = pure (v, { s with memory := mem' }) := by
  rw [fixedRun, ← bind_pure (liftM (WSpecL.query (.inl input))), fixed_aux_pure D Nn g s input v mem' h,
    SecretGuessObservation.runWith_pure]
theorem run_good {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Good D Nn s.memory) (r : α × WStateL)
    (hr : fixedRun (envE D Nn) g W s r ≠ 0) : Good D Nn r.2.memory ∧ Grows s.memory r.2.memory := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      rw [runL_pure_nonzero _ g a s r hr]
      exact ⟨hs, Grows.refl _⟩
  | query_bind input next ih =>
      rcases input with input | (⟨c, v⟩ | c)
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
            rw [fixedRun, fixed_aux_pure D Nn g s (.birth x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | trial x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn g s (.trial x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | nonce m =>
            obtain ⟨mem', heq, hg, hgr⟩ := nonceStep_ghost D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn g s (.nonce m) (Nn m) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn g s (.expose o) () (s.memory.expose o) rfl] at hr
            have he := expose_ghost D Nn s.memory hs o
            obtain ⟨h1, h2⟩ := ih () { s with memory := s.memory.expose o } he.1 hr
            exact ⟨h1, he.2.trans h2⟩
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (decide (g c = v), SecretGuessObservation.afterTrial (envE D Nn) s c v (decide (g c = v))) :
          SPMF (Bool × WStateL)) >>= fun mid => runWith (fixedImpl (envE D Nn) g) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterTrial (envE D Nn) s c v (decide (g c = v))) hs hr
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (g c, SecretGuessObservation.afterDisclosure (envE D Nn) s c (g c)) : SPMF (Digest × WStateL)) >>=
          fun mid => runWith (fixedImpl (envE D Nn) g) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterDisclosure (envE D Nn) s c (g c)) hs hr
end Ghost
section WorldGhost
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable local instance instDecidableEqCache_g6LazyGhost : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem decodeProbe_digest {x : HashInput} (hx : x ∈ digestInputs) : Guess.decodeProbe x = none := by
  cases hd : Guess.decodeProbe x with
  | none => rfl
  | some q =>
      have hqx := Guess.eq_of_decodeProbe hd
      rw [hqx] at hx
      exact absurd hx (probeInput_not_digest _ _ _)
theorem hashL_ghost (g : Guess.GCoord → Digest) (x : HashInput) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (hashL hU ω x) s r ≠ 0) (hx : x ∈ digestInputs) :
    r.2.memory.rows x = some r.1 := by
  have hd := decodeProbe_digest hx
  unfold hashL at hr
  rw [hd] at hr
  dsimp only at hr
  rw [if_pos hx] at hr
  obtain ⟨mem', heq, -, -, hrow⟩ := rowStep_ghost (digestOf ω) (nonceOf ω) s.memory hs x true
  rw [birthReq, fixed_aux_single (digestOf ω) (nonceOf ω) g s (.birth x) _ mem' heq] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst hr
  exact hrow hx
theorem finishL_some (g : Guess.GCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (finishL hU ω request rho found) s r ≠ 0)
    (σ : Signature) (hσ : r.1 = some σ) : ∃ c out, found = some (c, out) ∧ σ.rho = rho := by
  cases found with
  | none =>
      rw [runL_pure_nonzero _ g _ s r hr] at hσ
      cases hσ
  | some found =>
      obtain ⟨c, out⟩ := found
      refine ⟨c, out, rfl, ?_⟩
      simp only [finishL] at hr
      cases hl : signerLayersW hU ω request out with
      | none =>
          rw [hl] at hr
          rw [runL_pure_nonzero _ g _ s r hr] at hσ
          cases hσ
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, -, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
          rw [runL_pure_nonzero _ g _ _ r hr] at hσ
          cases hσ
          exact WCT9.assembledSignature_rho _ _ _
theorem fixed_nonce_value (g : Guess.GCoord → Digest) (m : Message) (s : WStateL)
    (hs : SigGolfCandidate.T3.Security.BPair.Consistent (digestOf ω) (nonceOf ω) s.memory) (r : Digest × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (nonceReq m) s r ≠ 0) : r.1 = nonceOf ω m := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) g _ s hs r hr
  rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (nonceReq m) = pure (nonceOf ω m) from by
    simp only [nonceReq, simulateQ_spec_query, inlineWith]] at h
  exact congrArg Prod.fst (fixedRun_pure_nonzero g _ _ _ h)
theorem fixed_searchL_value (g : Guess.GCoord → Digest) (rho : Digest) (m : Message) (counter fuel : Nat)
    (s : WStateL) (hs : SigGolfCandidate.T3.Security.BPair.Consistent (digestOf ω) (nonceOf ω) s.memory)
    (r : Option (BitVec 32 × HashOutput) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (searchL rho m counter fuel) s r ≠ 0) :
    r.1 = evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho m counter fuel) := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) g _ s hs r hr
  change fixedRun env g (simulateQ (inlineAux ω) (searchL rho m counter fuel)) (forget s) (r.1, forget r.2) ≠ 0 at h
  rw [inline_searchL hU ω] at h
  exact congrArg Prod.fst (fixedRun_pure_nonzero g _ _ _ h)
theorem signL_ghost (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (signL hU ω published request) s r ≠ 0)
    (σ : Signature) (output : HashOutput) (hσ : r.1 = some σ)
    (ho : CaseC.signedOutput (wA hU ω g) request.message σ = some output) :
    output ∈ r.2.memory.exposures := by
  unfold signL at hr
  by_cases hc : request.cache = published
  · rw [if_pos hc] at hr
    obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
    obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
    obtain ⟨m3, h3, hr⟩ := runL_bind_nonzero _ g _ _ m2.2 r hr
    have g1 := run_good _ _ g _ s hs m1 h1
    have g2 := run_good _ _ g _ m1.2 g1.1 m2 h2
    have hv2 := fixed_searchL_value hU ω g _ _ _ _ m1.2 g1.1.1 m2 h2
    have hm3 : m3.2.memory = m2.2.memory.expose (m2.1.map Prod.snd) := by
      rw [exposeReq, fixed_aux_single (digestOf ω) (nonceOf ω) g m2.2 (.expose _) () _ rfl] at h3
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h3
      subst h3
      rfl
    have g3' := run_good _ _ g _ m2.2 g2.1 m3 h3
    have g3 := run_good _ _ g _ m3.2 g3'.1 r hr
    obtain ⟨c, out, hfound, hrho⟩ := finishL_some hU ω g request m1.1 m2.1 m3.2 r hr σ hσ
    have hout : output = out := by
      unfold CaseC.signedOutput at ho
      rw [eval_free hU ω g 0 (wctDigestSearch_free _ _ _ _), hrho, ← hv2, hfound] at ho
      exact (Option.some.inj ho).symm
    subst hout
    apply g3.2.exposures
    rw [hm3, hfound]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [if_neg hc] at hr
    rw [runL_pure_nonzero _ g _ s r hr] at hσ
    cases hσ
theorem interactionL_ghost (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory)
    (r : (α × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (interactionL hU ω published program) s r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        CaseC.signedOutput (wA hU ω g) entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
      ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [interactionL_pure] at hr
      rw [runL_pure_nonzero _ g _ s r hr]
      exact ⟨fun _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        exact ih m1.1 m1.2 (run_good _ _ g _ s hs m1 h1).1 r hr
      · rw [interactionL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        have g2 := run_good _ _ g _ m1.2 g1.1 m2 h2
        obtain ⟨i1, i2⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨i1, fun y a hy hdy => ?_⟩
        rcases List.mem_cons.mp hy with he | hy
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact g2.2.rows _ _ (hashL_ghost hU ω g y s hs m1 h1 hdy)
        · exact i2 y a hy hdy
      · rw [interactionL_request] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        have g2 := run_good _ _ g _ m1.2 g1.1 m2 h2
        obtain ⟨i1, i2⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨fun entry he σ output hσ ho => ?_, i2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he
          exact g2.2.exposures _ (signL_ghost hU ω g published request s hs m1 h1 σ output hσ ho)
        · exact i1 entry he σ output hσ ho
theorem programL_ghost (g : Guess.GCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (programL hU ω program) s r ≠ 0) :
    ∀ x a, (x, a) ∈ r.1.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ g _ s r hr]
      exact fun _ _ h => (by simp at h)
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        exact ih m1.1 m1.2 (run_good _ _ g _ s hs m1 h1).1 r hr
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        have g2 := run_good _ _ g _ m1.2 g1.1 m2 h2
        have i2 := ih m1.1 m1.2 g1.1 m2 h2
        intro y a hy hdy
        rcases List.mem_cons.mp hy with he | hy
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact g2.2.rows _ _ (hashL_ghost hU ω g y s hs m1 h1 hdy)
        · exact i2 y a hy hdy
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr
theorem worldGameL_ghosts (g : Guess.GCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        CaseC.signedOutput (wA hU ω g) entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
      ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials) := by
  have g0 := run_good _ _ g _ initL (good_empty _ _) r hr
  unfold worldGameL worldGameCore at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ initL r hr
  obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
  have hrr := runL_pure_nonzero _ g _ _ r hr
  have g1 := run_good _ _ g _ initL (good_empty _ _) m1 h1
  have g2 := run_good _ _ g _ m1.2 g1.1 m2 h2
  obtain ⟨i1, i2⟩ := interactionL_ghost hU ω g _ _ initL (good_empty _ _) m1 h1
  have p2 := programL_ghost hU ω g _ m1.2 g1.1 m2 h2
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
end ClaudeWCT.W9.T3.Security.WPair
end

section

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep NotDN
  Grows Good good_empty Keeps rowStep_some rowStep_in rowStep_out nonceStep_some nonceStep_none replayRow_true
  replayRow_false readRow_true readRow_false)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Steps
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
theorem fixed_coin_state (n : Nat) (s : WStateL) (r : Fin (n + 1) × WStateL)
    (hr : fixedRun (envE D Nn) g (coinReqL n) s r ≠ 0) : r.2 = s := by
  unfold coinReqL fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) r ≠ 0 at hr
  rw [liftM_map, Functor.map_map] at hr
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
    SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨c, _, rfl⟩ := hr
  rfl
theorem fixed_trialQ_state (c : Guess.GCoord) (v : Digest) (s : WStateL) (r : Bool × WStateL)
    (hr : fixedRun (envE D Nn) g (Guess.trialQ (auxSpec := AuxSpecL) c v) s r ≠ 0) : r.2.memory = s.memory := by
  have h := Guess.fixedRun_trialQ (envE D Nn) g c v s r hr
  rw [h]
  rfl
theorem fixed_discloseQ_state (c : Guess.GCoord) (s : WStateL) (r : Digest × WStateL)
    (hr : fixedRun (envE D Nn) g (Guess.discloseQ (auxSpec := AuxSpecL) c) s r ≠ 0) : r.2.memory = s.memory := by
  have h := Guess.fixedRun_discloseQ (envE D Nn) g c s r hr
  rw [h]
  rfl
theorem fixed_probeW_state (step : Guess.ChainAddr → Fin 3 → Digest → HashOutput) (top : Guess.ChainAddr → HashOutput)
    (miss : HashOutput) (a : Guess.ChainAddr) (p : Fin 3) (v : Digest) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) g (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold Guess.probeW at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
  have k1 := fixed_trialQ_state D Nn g _ v s m1 h1
  cases hhit : m1.1 with
  | false =>
      rw [hhit] at hr
      simp only [Bool.false_eq_true, if_false] at hr
      rw [runL_pure_nonzero _ g _ _ r hr]
      exact k1
  | true =>
      rw [hhit] at hr
      simp only [if_true] at hr
      cases hs : Guess.succPos p with
      | none =>
          rw [hs] at hr
          rw [runL_pure_nonzero _ g _ _ r hr]
          exact k1
      | some p' =>
          rw [hs] at hr
          obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
          rw [runL_pure_nonzero _ g _ _ r hr]
          exact (fixed_discloseQ_state D Nn g _ m1.2 m2 h2).trans k1
theorem fixed_discloseAll_state (cs : List Guess.GCoord) (s : WStateL) (r : List Digest × WStateL)
    (hr : fixedRun (envE D Nn) g (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) s r ≠ 0) :
    r.2.memory = s.memory := by
  induction cs generalizing s r with
  | nil =>
      unfold Guess.discloseAll at hr
      rw [List.mapM_nil] at hr
      rw [runL_pure_nonzero _ g _ s r hr]
  | cons first rest ih =>
      unfold Guess.discloseAll at hr ih
      rw [List.mapM_cons] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
      obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
      rw [runL_pure_nonzero _ g _ _ r hr]
      exact (ih m1.2 m2 h2).trans (fixed_discloseQ_state D Nn g first s m1 h1)
theorem fixed_nonce_keeps (m : Message) (s : WStateL) (r : Digest × WStateL)
    (hr : fixedRun (envE D Nn) g (nonceReq m) s r ≠ 0) : Keeps s.memory r.2.memory := by
  cases hc : s.memory.nonces m with
  | some v =>
      rw [nonceReq, fixed_aux_single D Nn g s (.nonce m) v s.memory (nonceStep_some _ _ _ v hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact SigGolfCandidate.T3.Security.BPair.Keeps.refl _
  | none =>
      rw [nonceReq, fixed_aux_single D Nn g s (.nonce m) (Nn m) (s.memory.drawNonce m (Nn m))
        ((nonceStep_none _ _ _ hc).trans (map_pure _ _))] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      exact ⟨rfl, rfl, rfl⟩
theorem fixed_expose_mem (o : Option HashOutput) (s : WStateL) (r : Unit × WStateL)
    (hr : fixedRun (envE D Nn) g (exposeReq o) s r ≠ 0) : r.2.memory = s.memory.expose o := by
  rw [exposeReq, fixed_aux_single D Nn g s (.expose o) () (s.memory.expose o) rfl] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  rw [hr]
theorem fixed_birth_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) g (birthReq x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [birthReq, fixed_aux_single D Nn g s (.birth x) a (s.memory.replayRow x true)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [birthReq, fixed_aux_single D Nn g s (.birth x) (rowVal D x) (s.memory.readRow x (rowVal D x) true)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_true]
      · rw [birthReq, fixed_aux_single D Nn g s (.birth x) 0 (s.memory.replayRow x true)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_true]
theorem fixed_trial_counts (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE D Nn) g (trialReq x) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials ++ [x] := by
  cases hc : s.memory.rows x with
  | some a =>
      rw [trialReq, fixed_aux_single D Nn g s (.trial x) a (s.memory.replayRow x false)
        (rowStep_some _ _ _ _ a hc)] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      rw [hr]
      refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]
  | none =>
      by_cases hx : x ∈ digestInputs
      · rw [trialReq, fixed_aux_single D Nn g s (.trial x) (rowVal D x) (s.memory.readRow x (rowVal D x) false)
          ((rowStep_in _ _ _ _ hc hx).trans (map_pure _ _))] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [readRow_false]
      · rw [trialReq, fixed_aux_single D Nn g s (.trial x) 0 (s.memory.replayRow x false)
          (rowStep_out _ _ _ _ hc hx)] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        rw [hr]
        refine ⟨?_, ?_, ?_⟩ <;> simp [replayRow_false]
end Steps
section Programs
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable local instance instDecidableEqCache_g6LazyCount : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem queried_sign_search (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (hc : request.cache = published) (x : HashInput)
    (hx : (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
      SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g)
        (WCT9.digestSearch (nonceOf ω request.message) request.message 0 WCT9.digestAttemptLimit)) :
    (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈ SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g)
      (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  rw [SigGolfCandidate.T3M.SecurityExtraction.queried_bind, if_pos hc]
  change _ ∈ _ ++ SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g)
    (WCT9.Rev3.signPayload request.cache request.message)
  rw [WCT9.Rev3.signPayload_eq, SigGolfCandidate.T3M.SecurityExtraction.queried_bind,
    SigGolfCandidate.T3M.SecurityExtraction.queried_bind, eval_nonce hU ω g request.message]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hx))
theorem queried_wctDigestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    SigGolfCandidate.T3M.SecurityExtraction.queried A (WCT9.digestSearch rho m counter (fuel + 1)) =
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) : SigGolfCandidate.T3.Spec.Domain) ::
        SigGolfCandidate.T3M.SecurityExtraction.queried A
          (if WCT9.admissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
            then pure (some (BitVec.ofNat 32 counter,
              A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))))
            else WCT9.digestSearch rho m (counter + 1) fuel) := by
  rw [WCT9.digestSearch]
  exact SigGolfCandidate.T3M.SecurityExtraction.queried_query_bind A _ _
theorem searchL_counts (g : Guess.GCoord → Digest) (rho : Digest) (m : Message) (counter fuel : Nat) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option (BitVec 32 × HashOutput) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (searchL rho m counter fuel) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures = s.memory.exposures ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
        SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g) (WCT9.digestSearch rho m counter fuel) := by
  induction fuel generalizing counter s r with
  | zero =>
      rw [runL_pure_nonzero _ g _ s r hr]
      exact ⟨rfl, rfl, fun x hx => Or.inl hx⟩
  | succ fuel ih =>
      rw [searchL] at hr
      obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
      obtain ⟨hb1, he1, ht1⟩ := fixed_trial_counts _ _ g _ s m1 h1
      have g1 := run_good _ _ g _ s hs m1 h1
      have hv1 : m1.1 = wA hU ω g (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) := by
        have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) g _ s hs.1 m1 h1
        rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω)) (trialReq (pad64 (digestInput rho m
            (BitVec.ofNat 32 counter)))) =
              pure (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))
          from by simp only [trialReq, simulateQ_spec_query, inlineWith]] at h
        rw [congrArg Prod.fst (fixedRun_pure_nonzero g _ _ _ h),
          answers_digest hU ω g _ (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _)]
      rw [queried_wctDigestSearch_succ, ← hv1]
      by_cases hadm : WCT9.admissible m1.1 = true
      · simp only [hadm, ↓reduceIte] at hr ⊢
        rw [runL_pure_nonzero _ g _ _ r hr]
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
theorem finishL_state (g : Guess.GCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (finishL hU ω request rho found) s r ≠ 0) :
    r.2.memory = s.memory := by
  cases found with
  | none => rw [runL_pure_nonzero _ g _ s r hr]
  | some found =>
      obtain ⟨c, out⟩ := found
      simp only [finishL] at hr
      cases hl : signerLayersW hU ω request out with
      | none =>
          rw [hl] at hr
          rw [runL_pure_nonzero _ g _ s r hr]
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, hm, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
          rw [runL_pure_nonzero _ g _ _ r hr]
          exact fixed_discloseAll_state _ _ g _ s mid hm
theorem signL_counts (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (signL hU ω published request) s r ≠ 0) :
    r.2.memory.births = s.memory.births ∧ r.2.memory.exposures.length ≤ s.memory.exposures.length + 1 ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
        SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g) (FullGame.authenticatedSign published request) := by
  unfold signL at hr
  by_cases hc : request.cache = published
  · rw [if_pos hc] at hr
    obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
    obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
    obtain ⟨m3, h3, hr⟩ := runL_bind_nonzero _ g _ _ m2.2 r hr
    have k1 := fixed_nonce_keeps _ _ g request.message s m1 h1
    have g1 := run_good _ _ g _ s hs m1 h1
    have hv1 : m1.1 = nonceOf ω request.message := fixed_nonce_value ω g request.message s hs.1 m1 h1
    obtain ⟨hb2, he2, ht2⟩ := searchL_counts hU ω g m1.1 request.message 0 WCT9.digestAttemptLimit m1.2 g1.1 m2 h2
    have hm3 := fixed_expose_mem _ _ g _ m2.2 m3 h3
    have hr4 := finishL_state hU ω g request m1.1 m2.1 m3.2 r hr
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
        exact Or.inr (queried_sign_search hU ω g published request hc x hx)
  · rw [if_neg hc] at hr
    rw [runL_pure_nonzero _ g _ s r hr]
    exact ⟨rfl, Nat.le_succ _, fun x hx => Or.inl hx⟩
theorem hashL_counts (g : Guess.GCoord → Digest) (x : HashInput) (s : WStateL) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (hashL hU ω x) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + 1 ∧ r.2.memory.exposures = s.memory.exposures ∧
      r.2.memory.trials = s.memory.trials := by
  unfold hashL at hr
  cases hd : Guess.decodeProbe x with
  | some q =>
      rw [hd] at hr
      dsimp only at hr
      rw [fixed_probeW_state _ _ g _ _ _ _ _ _ s r hr]
      exact ⟨Nat.le_succ _, rfl, rfl⟩
  | none =>
      rw [hd] at hr
      dsimp only at hr
      by_cases hx : x ∈ digestInputs
      · rw [if_pos hx] at hr
        exact fixed_birth_counts _ _ g x s r hr
      · rw [if_neg hx] at hr
        rw [runL_pure_nonzero _ g _ s r hr]
        exact ⟨Nat.le_succ _, rfl, rfl⟩
theorem interactionL_counts (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (s : WStateL) (hs : Good (digestOf ω) (nonceOf ω) s.memory)
    (r : (α × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (interactionL hU ω published program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.2.length ∧
      r.2.memory.exposures.length ≤ s.memory.exposures.length + r.1.2.1.length ∧
      ∀ x ∈ r.2.memory.trials, x ∈ s.memory.trials ∨ ∃ entry ∈ r.1.2.1,
        (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
          SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g) (FullGame.authenticatedSign published entry.1) := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [interactionL_pure] at hr
      rw [runL_pure_nonzero _ g _ s r hr]
      exact ⟨by simp, by simp, fun x hx => Or.inl hx⟩
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        have hm := fixed_coin_state _ _ g n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [interactionL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω g x s m1 h1
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
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := signL_counts hU ω g published request s hs m1 h1
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
theorem programL_counts (g : Guess.GCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (programL hU ω program) s r ≠ 0) :
    r.2.memory.births.length ≤ s.memory.births.length + r.1.2.length ∧
      r.2.memory.exposures = s.memory.exposures ∧ r.2.memory.trials = s.memory.trials := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ g _ s r hr]
      exact ⟨by simp, rfl, rfl⟩
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        have hm := fixed_coin_state _ _ g n s m1 h1
        have := ih m1.1 m1.2 (by rw [hm]; exact hs) r hr
        rw [hm] at this
        exact this
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
        rw [runL_pure_nonzero _ g _ _ r hr]
        have g1 := run_good _ _ g _ s hs m1 h1
        obtain ⟨hb1, he1, ht1⟩ := hashL_counts hU ω g x s m1 h1
        obtain ⟨i1, i2, i3⟩ := ih m1.1 m1.2 g1.1 m2 h2
        refine ⟨?_, i2.trans he1, i3.trans ht1⟩
        change m2.2.memory.births.length ≤ s.memory.births.length + (m2.1.2.length + 1)
        omega
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr
theorem worldGameL_counts (g : Guess.GCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.memory.births.length ≤ r.1.2.2.length ∧
      (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
        SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g)
          (FullGame.authenticatedSign (evalWithAnswerFn (wA hU ω g) SigGolfCandidate.T3.keygen).2 entry.1)) ∧
      r.2.memory.exposures.length ≤ r.1.2.1.length := by
  unfold worldGameL worldGameCore at hr
  obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ g _ _ initL r hr
  obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ g _ _ m1.2 r hr
  rw [runL_pure_nonzero _ g _ _ r hr]
  have g1 := run_good _ _ g _ initL (good_empty _ _) m1 h1
  obtain ⟨i1, i2, i3⟩ := interactionL_counts hU ω g _ _ initL (good_empty _ _) m1 h1
  obtain ⟨p1, p2, p3⟩ := programL_counts hU ω g _ m1.2 g1.1 m2 h2
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
    · rw [keygen_answers hU ω g]
      exact hx
  · change m2.2.memory.exposures.length ≤ m1.1.2.1.length
    rw [p2]
    change m1.2.memory.exposures.length ≤ 0 + m1.1.2.1.length at i2
    omega
theorem worldGameL_bank (g : Guess.GCoord → Digest) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL r ≠ 0) :
    (∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
        CaseC.signedOutput (wA hU ω g) entry.1.message σ = some output → output ∈ r.2.memory.exposures) ∧
    (∀ x a, (x, a) ∈ r.1.2.2 → x ∈ digestInputs →
        r.2.memory.rows x = some a ∧ (a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)) ∧
    r.2.probes ≤ r.1.2.2.length ∧
    (∀ c, GuessedIn (wA hU ω g) r.1.2.1 r.1.2.2 c → Guess.PrefixIn r.2.guesses c.1 c.2.val) ∧
    r.2.memory.births.length ≤ r.1.2.2.length ∧
    (∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈
      SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU ω g)
        (FullGame.authenticatedSign (evalWithAnswerFn (wA hU ω g) SigGolfCandidate.T3.keygen).2 entry.1)) ∧
    r.2.memory.exposures.length ≤ r.1.2.1.length := by
  obtain ⟨g1, g2⟩ := worldGameL_ghosts hU ω g adversary r hr
  obtain ⟨t1, t2⟩ := worldGameL_tracking hU ω g adversary r hr
  obtain ⟨c1, c2, c3⟩ := worldGameL_counts hU ω g adversary r hr
  exact ⟨g1, g2, t1, t2, c1, c2, c3⟩
end Programs
end ClaudeWCT.W9.T3.Security.WPair
end
