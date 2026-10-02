import SigGolfCandidate.T3.Secc.CaseCNearGSteps

/-!
# Stream CC: the signer is a supermartingale step of the ghost bank potential

`signL_ΦI`: a published signing request is a supermartingale step of `ΦI q` in the ghost lazy world:

* first signing of `m` (nonce undrawn): uniform nonce, reuse flag, the search law (`search_law`), the exposure, and
  `mem_sign_fresh`; the invariant is re-established by `replays_of_search`;
* repeated signing: the search replays (`Replays`), nothing changes but a duplicated world exposure.

Then `worldGame_ΦI`: the whole world game, and `forced_payoff_le`: under B-PAIR's lazy forced world,
`E[nearPayoff q] ≤ q·(203 + 1/16)/2^128` from the initial state.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem spmf_ev_zero {α : Type} (p : SPMF α) {f : α → ENNReal} (h : expectedValue p f = 0) :
    ∀ x, p x ≠ 0 → f x = 0 := by
  intro x hx
  unfold expectedValue at h
  have h0 := ENNReal.tsum_eq_zero.mp h x
  rw [SPMF.probOutput_eq_apply] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hx
  · exact h1

theorem pc_ev_offsupport {α : Type} (p : ProbComp α) :
    expectedValue p (fun r => if r ∈ support p then 0 else 1) = 0 := by
  unfold expectedValue
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support p
  · simp [hr]
  · simp [hr, probOutput_eq_zero_of_not_mem_support hr]

/-- World search results are support points of SEC's lazy search. -/
theorem search_support (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith (implG slot) (BPair.searchL rho m 0 attemptLimit) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈ support (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) s.memory.1.rows) := by
  have hlaw := search_law slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) s.memory.1.rows) then 0 else 1)
    attemptLimit 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0

theorem attemptLimit_le : attemptLimit ≤ 2 ^ 32 := by
  unfold attemptLimit
  norm_num

/-- A cached nonce is replayed (stated for an abstract continuation, so that no program is compared). -/
theorem ev_nonce_cached {β : Type} (slot : Nat) (m : Message) (rho : Digest) (k : Digest → OracleComp BPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = some rho) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (BPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith (implG slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, ghostStep s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold BPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]

/-- A fresh nonce is uniform. -/
theorem ev_nonce_fresh {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp BPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (BPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold BPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]

/-- The exposure step followed by the end of the signing. -/
theorem ev_expose_finish_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat)
    (ω : BPair.Omega U) (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith (implG slot)
      (BPair.exposeReq (found.map Prod.snd) >>= fun _ => BPair.finishL hU ω request rho found) s2)
      (fun r => ΦI q r.2) ≤
    ΦI q ⟨s2.allowed, s2.retired, s2.guesses, s2.probes, (s2.memory.1.expose (found.map Prod.snd),
      ghostStep s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold BPair.exposeReq
  rw [ev_aux_bind]
  change expectedValue (pure ((), s2.memory.1.expose (found.map Prod.snd)) : PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact finishL_ΦI hU slot q ω request rho found _

/-- **The signer.** -/
theorem signL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : BPair.Omega U)
    (published : T3.Cache) (request : Request) :
    SuperProg (implG slot) (ΦI q) (BPair.signL hU ω published request) := by
  unfold BPair.signL
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte]
    exact superProg_pure _ _ _
  simp only [hc, ↓reduceIte]
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  set m := request.message with hm
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI q s = ghostPot q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      -- repeated signing: the search replays
      rw [ev_nonce_cached slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := search_support slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot rho m attemptLimit 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [BPair.LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [BPair.LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [BPair.LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, BPair.LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      -- first signing
      rw [ev_nonce_fresh slot m _ s hn, hΦs]
      refine le_trans ?_ (mem_sign_fresh q _ _ _ _ _ m hn 0 attemptLimit attemptLimit_le)
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ (search_law slot v m (fun found rows' =>
        nearMemPotential q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) attemptLimit 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := search_support slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := replays_of_search v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot v m attemptLimit 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [BPair.LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [BPair.LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [BPair.LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, BPair.LazyMem.expose]
      rw [hbir1, hnon1]

end SigGolfCandidate.T3.Security.CaseC
