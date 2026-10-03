import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearMem
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyDefs

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Generic
variable {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
def SuperProg {β : Type} (W : OracleComp WPair.WSpecL β) : Prop :=
  ∀ s, expectedValue (SecretGuessObservation.runWith impl W s) (fun r => Φ r.2) ≤ Φ s
theorem runWith_bind' {β γ : Type} (W : OracleComp WPair.WSpecL β) (K : β → OracleComp WPair.WSpecL γ)
    (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (W >>= K) s =
      SecretGuessObservation.runWith impl W s >>= fun r => SecretGuessObservation.runWith impl (K r.1) r.2 := by
  simp only [SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]
theorem runWith_pure' {β : Type} (b : β) (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (pure b) s = pure (b, s) := by
  simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure]
theorem superProg_pure {β : Type} (b : β) : SuperProg impl Φ (pure b : OracleComp WPair.WSpecL β) := by
  intro s
  rw [runWith_pure', expectedValue_pure]
theorem superProg_bind {β γ : Type} {W : OracleComp WPair.WSpecL β} {K : β → OracleComp WPair.WSpecL γ}
    (hW : SuperProg impl Φ W) (hK : ∀ b, SuperProg impl Φ (K b)) : SuperProg impl Φ (W >>= K) := by
  intro s
  rw [runWith_bind', expectedValue_bind]
  exact (expectedValue_mono _ fun (r : β × SecretGuessObservation.State Guess.GCoord Digest Mem) =>
    hK r.1 r.2).trans (hW s)
end Generic
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
noncomputable local instance instDecidableEqCache_w9caseCNearWorld : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem interactionL_pure (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    WPair.interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (x : HashInput) (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (WPair.signL hU ω published request >>= fun signature => WPair.interactionL hU ω published (next signature) >>=
        fun rest => pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : CanonTable.Omega U) {β : Type} (value : β) :
    WPair.programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : CanonTable.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.programL hU ω (next coin)) := rfl
theorem programL_public (ω : CanonTable.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : CanonTable.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr c)) >>= next) =
      WPair.programL hU ω (next 0) := rfl
theorem interactionL_super (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ request, SuperProg impl Φ (WPair.signL hU ω published request)) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) : SuperProg impl Φ (WPair.interactionL hU ω published oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      rw [interactionL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [interactionL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [interactionL_request]
        exact superProg_bind impl Φ (hsign request) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
theorem programL_super (ω : CanonTable.Omega U)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x)) {β : Type}
    (program : M β) : SuperProg impl Φ (WPair.programL hU ω program) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [programL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [programL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [programL_private]
        exact ih (0 : HashOutput)
theorem worldGameCore_super (ω : CanonTable.Omega U) (adversary : AdversaryP)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ published request, SuperProg impl Φ (WPair.signL hU ω published request)) :
    SuperProg impl Φ (WPair.worldGameCore hU ω adversary) := by
  unfold WPair.worldGameCore
  exact superProg_bind impl Φ (interactionL_super hU impl Φ ω _ hcoin hhash (hsign _) _) fun _ =>
    superProg_bind impl Φ (programL_super hU impl Φ ω hcoin hhash _) fun _ => superProg_pure impl Φ _
end World
theorem expectedValue_liftM_pmf {α : Type} (p : PMF α) (g : α → ENNReal) :
    expectedValue (liftM p : SPMF α) g = expectedValue p g := by
  unfold expectedValue
  simp [SPMF.probOutput_eq_apply, PMF.probOutput_eq_apply]
theorem expectedValue_uniformOfFintype {α : Type} [Fintype α] [Nonempty α] (g : α → ENNReal) :
    expectedValue (PMF.uniformOfFintype α) g = BPORS.finiteAverage g := by
  unfold expectedValue BPORS.finiteAverage
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure NearGhost where
  reused : Bool
  lastFresh : Bool
  fresh : List HashOutput
def NearGhost.empty : NearGhost := ⟨false, false, []⟩
noncomputable def ghostStep (mem : LazyMem) : (i : AuxL) → AuxSpecL.Range i → NearGhost → NearGhost
  | .nonce m, v, g =>
      { g with lastFresh := decide (mem.nonces m = none),
               reused := g.reused || (decide (mem.nonces m = none) && decide (nearSpec.Reuse mem.rows v m)) }
  | .expose o, _, g => if g.lastFresh then { g with fresh := g.fresh ++ o.toList } else g
  | _, _, g => g
def projS (s : SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)) : WPair.WStateL :=
  ⟨s.allowed, s.retired, s.guesses, s.probes, s.memory.1⟩
noncomputable def envG (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest (LazyMem × NearGhost) where
  auxiliary st i := (fun r => (r.1, (r.2, ghostStep st.memory.1 i r.1 st.memory.2))) <$> env.auxiliary (projS st) i
  trial mem c v hit := (env.trial mem.1 c v hit, mem.2)
  disclosure mem c v := (env.disclosure mem.1 c v, mem.2)
abbrev GState := SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)
def initG : GState := SecretGuessObservation.initialState (LazyMem.empty, NearGhost.empty)
theorem projS_initG : projS initG = WPair.initL := rfl
section Project
variable (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat)
theorem liftM_map_pmf {α β : Type} (f : α → β) (p : PMF α) :
    (liftM (f <$> p) : SPMF β) = f <$> (liftM p : SPMF α) :=
  evalSPMF_map p f
theorem step_project (q : WPair.WSpecL.Domain) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> (SecretGuessObservation.forcedImpl (envG env) slot q).run s =
      (SecretGuessObservation.forcedImpl env slot q).run (projS s) := by
  rcases q with i | (⟨c, v⟩ | c)
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    change (fun r => (r.1, projS r.2)) <$> ((fun result => (result.1, { s with memory := result.2 })) <$>
      (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> env.auxiliary (projS s) i) :
        SPMF _)) =
      (fun result => (result.1, { projS s with memory := result.2 })) <$> (liftM (env.auxiliary (projS s) i) : SPMF _)
    rw [liftM_map_pmf, Functor.map_map, Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk]
    rw [Functor.map_map]
    have h1 : SecretGuessObservation.forcedTrial slot s c v =
        SecretGuessObservation.forcedTrial slot (projS s) c v := by
      have hA : (projS s).allowed = s.allowed := rfl
      have hP : (projS s).probes = s.probes := rfl
      have hR : (projS s).retired = s.retired := rfl
      unfold SecretGuessObservation.forcedTrial SecretGuessObservation.EligibleAt
      rw [hA, hP, hR]
    rw [h1]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    rw [Functor.map_map]
    rfl
theorem run_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState) :
    (fun r => (r.1, projS r.2)) <$>
        SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s =
      SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure b =>
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      rw [SecretGuessObservation.runWith_query_bind, SecretGuessObservation.runWith_query_bind, map_bind]
      simp_rw [ih]
      rw [← step_project env slot q s, bind_map_left]
theorem expectedValue_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState)
    (payoff : β × WPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s)) payoff =
      expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s)
        (fun r => payoff (r.1, projS r.2)) := by
  rw [← run_project env slot W s, expectedValue_map]
end Project
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev implG (slot : Nat) := SecretGuessObservation.forcedImpl (envG WPair.envL) slot
theorem ev_aux_bind {β : Type} (slot : Nat) (i : AuxL) (k : AuxSpecL.Range i → OracleComp WPair.WSpecL β)
    (s : GState) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i)) >>= k) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k r.1)
          { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) }) G) := by
  rw [SecretGuessObservation.runWith_query_bind, expectedValue_bind]
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
  change expectedValue ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) _ = _
  rw [expectedValue_map, expectedValue_liftM_pmf, expectedValue_map]
theorem searchL_succ (rho : Digest) (m : Message) (c fuel : Nat) :
    WPair.searchL rho m c (fuel + 1) =
      (liftM (WPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m c)))) >>= fun output =>
        if WCT9.admissible output = true then pure (some (BitVec.ofNat 32 c, output))
        else WPair.searchL rho m (c + 1) fuel) := rfl
theorem ev_uniform_eq (g : HashOutput → ENNReal) :
    expectedValue (PMF.uniformOfFintype HashOutput) g = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem nearSpec_decode_some {a : HashOutput} (h : WCT9.admissible a = true) : nearSpec.decode a = some a := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_admissible, h]
theorem nearSpec_decode_none {a : HashOutput} (h : ¬WCT9.admissible a = true) : nearSpec.decode a = none := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_admissible, h]
theorem search_law (slot : Nat) (rho : Digest) (m : Message)
    (F : Option (BitVec 32 × HashOutput) → Sampling.RCache → ENNReal) :
    ∀ fuel c (s : GState),
      expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s)
          (fun r => F r.1 r.2.memory.1.rows) =
        expectedValue (Sampling.roRun 0 (nearSpec.search rho m c fuel) s.memory.1.rows) (fun r => F r.1 r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s
      change expectedValue (SecretGuessObservation.runWith (implG slot) (pure none) s) _ =
        expectedValue (Sampling.roRun 0 (pure none) s.memory.1.rows) _
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
        expectedValue_pure]
  | succ fuel ih =>
      intro c s
      rw [searchL_succ, ev_aux_bind]
      unfold ClaudeWCT.Bank.FtsBankSpec.search
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind,
        randomOracle.run_eq]
      change expectedValue (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
        (PMF.uniformOfFintype HashOutput)) _ = _
      cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
      | some a =>
          simp only [BPair.rowStep, hx]
          rw [expectedValue_pure, expectedValue_pure]
          dsimp only
          by_cases had : WCT9.admissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
      | none =>
          have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
          simp only [BPair.rowStep, hx, hdi, if_true]
          rw [expectedValue_map, expectedValue_bind, ev_uniform_eq]
          apply congrArg
          funext a
          rw [expectedValue_pure]
          dsimp only
          by_cases had : WCT9.admissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
def RowsFrame (s s' : GState) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.2 = s.memory.2 ∧ s'.memory.1.nonces = s.memory.1.nonces ∧ s'.memory.1.births = s.memory.1.births ∧
    s'.memory.1.exposures = s.memory.1.exposures
theorem RowsFrame.refl (s : GState) : RowsFrame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem RowsFrame.trans {s s' s'' : GState} (h : RowsFrame s s') (h' : RowsFrame s' s'') : RowsFrame s s'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2⟩
theorem runWith_bind_nonzero {β γ : Type} (slot : Nat) (W : OracleComp WPair.WSpecL β)
    (K : β → OracleComp WPair.WSpecL γ) (s : GState) (r : γ × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith (implG slot) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith (implG slot) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runWith_pure_nonzero {β : Type} (slot : Nat) (b : β) (s : GState) (r : β × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem aux_nonzero (slot : Nat) (i : AuxL) (s : GState) (r : AuxSpecL.Range i × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, WPair.envL.auxiliary (projS s) i res ≠ 0 ∧
      r = (res.1, { s with memory := (res.2, ghostStep s.memory.1 i res.1 s.memory.2) }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) r ≠ 0 at hr
  rw [liftM_map_pmf, Functor.map_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  refine ⟨res, ?_, hr⟩
  simpa [SPMF.liftM_apply] using hres
theorem search_frame (slot : Nat) (rho : Digest) (m : Message) :
    ∀ fuel c (s : GState) r, SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s r ≠ 0 →
      RowsFrame s r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr
      rw [runWith_pure_nonzero slot none s r hr]
      exact RowsFrame.refl s
  | succ fuel ih =>
      intro c s r hr
      rw [searchL_succ] at hr
      obtain ⟨mid, hmid, hr⟩ := runWith_bind_nonzero slot _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hf : RowsFrame s { s with memory := (res.2, ghostStep s.memory.1 (.trial (Sampling.digestTrial rho m c))
          res.1 s.memory.2) } := by
        have hres' : res ∈ (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
            (PMF.uniformOfFintype HashOutput)).support := (PMF.mem_support_iff _ _).mpr hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold BPair.rowStep at hres'
        cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨rfl, rfl, rfl⟩
        | none =>
            simp only [hx] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            exact ⟨rfl, rfl, rfl⟩
      dsimp only at hr
      split_ifs at hr
      · rw [runWith_pure_nonzero slot _ _ r hr]
        exact hf
      · exact hf.trans (ih (c + 1) _ r hr)
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Extends (rows rows' : Sampling.RCache) : Prop := ∀ x a, rows x = some a → rows' x = some a
theorem Extends.refl (rows : Sampling.RCache) : Extends rows rows := fun _ _ h => h
theorem Extends.trans {r1 r2 r3 : Sampling.RCache} (h1 : Extends r1 r2) (h2 : Extends r2 r3) : Extends r1 r3 :=
  fun x a h => h2 x a (h1 x a h)
theorem search_replays_gen {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      Extends cache r.2 ∧ ∀ cache', Extends r.2 cache' → ∀ r' ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache'),
          r' = (r.1, cache') := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨Extends.refl _, fun cache' _ r' hr' => ?_⟩
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr'
      change r' ∈ support (Sampling.roRun secret (pure none) cache') at hr'
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
      exact hr'
  | succ fuel ih =>
      intro counter cache r hr
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfirst' : Extends cache first.2 ∧ first.2 (inputs counter) = some first.1 := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            subst hfirst
            exact ⟨Extends.refl _, hc⟩
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            subst hfa
            refine ⟨fun x b hx => ?_, QueryCache.cacheQuery_self _ _ _⟩
            have hne : x ≠ inputs counter := fun he => by rw [he, hc] at hx; cases hx
            exact (QueryCache.cacheQuery_of_ne cache a hne).trans hx
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          obtain ⟨h1, h2⟩ := ih (counter + 1) first.2 r hr
          refine ⟨hfirst'.1.trans h1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ (h1 _ _ hfirst'.2)
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          exact h2 cache' hc' r' hr'
      | some value =>
          rw [hd] at hr
          simp only at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨hfirst'.1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ hfirst'.2
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
          exact hr'
def Replays (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) cache'), r' = (found, cache')
theorem Replays.mono {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : Replays rows rho m found) (hext : Extends rows rows') : Replays rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) rows)) :
    Extends rows r.2 ∧ Replays r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) nearSpec.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, Replays M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty : InvM (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  nearMemPotential q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (q : Nat) (s : GState) : ENNReal := if InvM s.memory then ghostPot q s.memory else ⊤
theorem ΦI_initial (q : Nat) : ΦI q initG ≤ (q : ENNReal) * 404 / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial q
theorem nearCoveredBy_mono {X Y : List HashOutput} (h : ∀ v ∈ X, v ∈ Y) {N : HashOutput}
    (hN : Guess.NearCoveredBy X N) : Guess.NearCoveredBy Y N := by
  obtain ⟨k, t, hkt⟩ := hN
  exact ⟨k, t, hkt.mono_log h⟩
theorem payoff_le_ΦI (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × GState) :
    WPair.nearPayoff q (r.1, projS r.2) ≤ ΦI q r.2 := by
  unfold ΦI
  split_ifs with hinv
  · unfold WPair.nearPayoff
    split_ifs with hp
    · obtain ⟨hb, hl, N, hN, hadm, hcov⟩ := hp
      exact mem_win q _ _ _ _ _ hb (hinv.2.1.trans hl) (Or.inr ⟨N, hN, hadm, nearCoveredBy_mono hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_mono {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  rw [SPMF.probOutput_eq_apply]
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul' le_rfl (h x hx)
theorem spmf_ev_le {α : Type} (p : SPMF α) {f : α → ENNReal} {c : ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ c) :
    expectedValue p f ≤ c :=
  (spmf_ev_mono p h).trans (expectedValue_le_of_le p fun _ => le_rfl)
theorem spmf_ev_congr {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x = g x) :
    expectedValue p f = expectedValue p g :=
  le_antisymm (spmf_ev_mono p fun x hx => (h x hx).le) (spmf_ev_mono p fun x hx => (h x hx).ge)
theorem superProg_of_memory {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implG slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg (implG slot) (ΦI q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory {β : Type} (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk, map_eq_bind_pure_comp,
      RetainedObservation.bind_nonzero, Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk,
      map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (slot q n : Nat) : SuperProg (implG slot) (ΦI q) (WPair.coinReqL n) :=
  superProg_of_memory slot q _ fun s r hr => coin_memory slot n s r hr
theorem guess_ΦI (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Bool) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (slot q : Nat) (c : Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Digest) slot (.inr c) s r hr
theorem mapM_ΦI {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg (implG slot) (ΦI q) (f a)) :
    ∀ l : List α, SuperProg (implG slot) (ΦI q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ (mapM_ΦI slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  mapM_ΦI slot q _ (fun c => disclose_ΦI slot q c) cs
theorem probeW_ΦI (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 3 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 3) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ (guess_ΦI slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ (disclose_ΦI slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem finishL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    SuperProg (implG slot) (ΦI q) (WPair.finishL hU ω request rho found) := by
  rcases found with _ | ⟨c, output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.finishL]
    generalize WPair.signerLayersW hU ω request output = g
    cases g with
    | none => exact superProg_pure _ _ _
    | some pieces =>
        refine superProg_bind _ _ (discloseAll_ΦI slot q _) ?_
        intro values
        exact superProg_pure _ _ _
theorem ev_uniform_digest (g : Digest → ENNReal) :
    expectedValue (PMF.uniformOfFintype Digest) g = expectedValue ($ᵗ Digest : ProbComp Digest) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem ev_single_aux (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) })) := by
  have h := ev_aux_bind slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (slot q : Nat) (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [ev_single_aux]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq]
        have hpt : ∀ a : HashOutput, ΦI q { s with memory := (s.memory.1.readRow x a true,
            ghostStep s.memory.1 (.birth x) a s.memory.2) } =
            nearMemPotential q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : InvM (s.memory.1.readRow x a true, ghostStep s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact mem_birth q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact probeW_ΦI slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_ΦI slot q x
      · exact superProg_pure _ _ _
end ClaudeWCT.W9.T3.Security.CaseC
end
