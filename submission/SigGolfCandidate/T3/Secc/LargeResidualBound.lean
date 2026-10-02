import SigGolfCandidate.T3.Secc.LargeResidualWorld

/-!
# LR-34 (3/4): every residual step is one of LR-1's four kinds

`residualStep aux q` is the lazy world as an LR-1 `Step` (monad `SPMF`, stop = `none`), `charges` reads LR-1's
counters off the state, and `Inv` is the posterior invariant: every coordinate is disclosed (one candidate) or keeps
at least `2^128 − probes` candidates.

* `run_residual`: LR-1's `run` of the step is the world's `lazyRun`.
* `residual_step_bound`: on `Inv` states, auxiliary queries, reads, disclosures and ticks are free steps (mass
  steps for `Charge.mass`), probes are probe steps with rate `hazard (2^128) probes` (`lazyResponse_failure_le_hazard`
  through the guard `Probe.effective`).
* `residual_preserve`: `Inv` is preserved along continuing steps.
* `residual_potential`: LR-1's product potential for every world program from the empty state:
  `Pr[stop ∧ calls ≤ q] + E[mass]/2^128 ≤ ofReal (2x − x²)`.
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open LargePotential (Step Charges StepBound FreeStep MassStep ProbeStep hazard)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Bound
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

/-- The lazy world as an LR-1 step. -/
noncomputable def residualStep (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    Step SPMF (World auxSpec Coord Cell) (State Coord Cell) :=
  fun request state => ((lazyImpl aux q request).run).run state

/-- LR-1's counters of the residual world. -/
def charges : Charges (State Coord Cell) :=
  ⟨fun state => state.counters.calls, fun state => state.counters.probes, fun state => state.counters.mass⟩

/-- The posterior invariant. -/
def Inv (state : State Coord Cell) : Prop :=
  ∀ c, (state.candidates c).card = 1 ∨ 2 ^ 128 - state.counters.probes ≤ (state.candidates c).card

/-- The empty initial state: every coordinate hidden with all candidates, no cached row, zero counters. -/
def initial : State Coord Cell := ⟨fun _ => Finset.univ, fun _ => none, ⟨0, 0, 0⟩⟩

theorem initial_inv : Inv (initial : State Coord Cell) := by
  intro c
  right
  simp only [initial, Finset.card_univ, Nat.sub_zero]
  simp [SphincsSecurity.digestBits]

theorem run_residual {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (program : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    LargePotential.run (residualStep aux q) program state = lazyRun aux q program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rw [LargePotential.run_pure, lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [LargePotential.run_query_bind, lazyRun, runWith_query_bind]
      apply _root_.bind_congr
      intro middle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none => rfl
      | some answer => exact ih answer after

/-! ## Step shapes -/

/-- A never-stopping step whose every result carries the counters `counters`. -/
theorem stop_zero_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell) :
    Pr[fun result : Option R × State Coord Cell => result.1 = none | p >>= fun a => pure (some (g a), f a)] = 0 := by
  apply probEvent_eq_zero
  intro result hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  subst hr
  simp

theorem support_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell)
    (result : Option R × State Coord Cell) (hresult : result ∈ support (p >>= fun a => pure (some (g a), f a))) :
    ∃ a, result = (some (g a), f a) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  exact ⟨a, hr⟩

/-- A charged never-stopping step is a free step (no charge, one call) or a mass step (`Charge.mass`). -/
theorem stepBound_of_charge (q : Nat) {X : Type} (step : Step SPMF (World auxSpec Coord Cell) (State Coord Cell))
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (charge : Charge)
    (p : SPMF X) (g : X → (World auxSpec Coord Cell).Range input) (f : X → State Coord Cell)
    (hstep : step input state = p >>= fun a => pure (some (g a), f a))
    (hcounters : ∀ a, (f a).counters = state.counters.charge q charge) :
    StepBound step charges (2 ^ 128) q input state := by
  have hstop : Pr[fun result => result.1 = none | step input state] = 0 := by
    rw [hstep]; exact stop_zero_of_shape p g f
  cases charge with
  | none =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge, le_refl, and_self]
  | call =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega
  | mass =>
      right; left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega

/-- The stop probability of an observed response is its failure mass. -/
theorem observe_stop {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S) :
    Pr[fun result : Option HashOutput × S => result.1 = none |
        observe response (pure (none, stopped)) (fun answer => pure (some answer, continued answer))] =
      response.toPMF none := by
  rw [observe, probEvent_bind_eq_tsum, tsum_option _ ENNReal.summable]
  simp

theorem observe_support {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S)
    (result : Option HashOutput × S)
    (hresult : result ∈ support (observe response (pure (none, stopped))
      (fun answer => pure (some answer, continued answer)))) :
    result = (none, stopped) ∨ ∃ answer, response answer ≠ 0 ∧ result = (some answer, continued answer) := by
  rw [observe, mem_support_bind_iff] at hresult
  obtain ⟨o, ho, hr⟩ := hresult
  cases o with
  | none =>
      rw [mem_support_pure_iff] at hr
      exact Or.inl hr
  | some answer =>
      rw [mem_support_pure_iff] at hr
      refine Or.inr ⟨answer, ?_, hr⟩
      rw [SPMF.apply_eq_toPMF_some response answer]
      rw [mem_support_iff] at ho
      simpa using ho

/-- The guard makes every surviving guess test a hidden coordinate (`Inv`: at least `2^128 − probes` candidates). -/
theorem effective_guess_card (state : State Coord Cell) (hinv : Inv state) (test : Probe Coord) :
    ∀ g ∈ (test.effective state.candidates).guess, 2 ^ 128 - state.counters.probes ≤ (state.candidates g.1).card := by
  intro g hg
  simp only [Probe.effective, Option.mem_def, Option.filter_eq_some_iff, decide_eq_true_eq] at hg
  obtain ⟨_, hadm⟩ := hg
  rcases hinv g.1 with h1 | h2
  · exact absurd hadm.1 (by omega)
  · exact h2

/-- **Every residual step is one of the four kinds** (rates for `space = 2^128`). -/
theorem residual_step_bound (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state) :
    StepBound (residualStep aux q) charges (2 ^ 128) q input state := by
  cases input with
  | inl input =>
      apply stepBound_of_charge q (residualStep aux q) (.inl input) state .none (liftM (aux input) : SPMF _)
        id (fun _ => state)
      · rfl
      · intro a; rfl
  | inr request =>
      cases request with
      | read row charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.read row charge)) state charge
            (reply state.rows row) id (fun a => readState q state row a charge)
          · rfl
          · intro a; rfl
      | disclose coord charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.disclose coord charge)) state charge
            (cell (state.candidates coord)) id (fun v => disclosedState q state coord v charge)
          · rfl
          · intro a; rfl
      | tick charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.tick charge)) state charge
            (pure ()) id (fun _ => tickState q state charge)
          · change pure (some (), tickState q state charge) = _
            rw [pure_bind]
          · intro a; rfl
      | probe row test =>
          cases hcache : state.rows row with
          | some answer =>
              apply stepBound_of_charge q (residualStep aux q) (.inr (.probe row test)) state .call
                (pure answer) id (fun a => readState q state row a .call)
              · change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache, pure_bind]
                rfl
              · intro a; rfl
          | none =>
              right; right; right
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResponse state.candidates (test.effective state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effective state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              refine ⟨fun result hresult => ?_, ?_⟩
              · rw [hstep] at hresult
                rcases observe_support _ _ _ result hresult with rfl | ⟨answer, _, rfl⟩
                · simp only [charges, stoppedState, Counters.probe]; omega
                · simp only [charges, probeState, Counters.probe]; omega
              · rw [hstep]
                erw [observe_stop]
                by_cases hp : state.counters.probes < 2 ^ 128
                · have ha : ∀ c, (state.candidates c).Nonempty := by
                    intro c
                    rcases hinv c with h1 | h2
                    · exact Finset.card_pos.mp (by omega)
                    · exact Finset.card_pos.mp (by omega)
                  exact lazyResponse_failure_le_hazard state.candidates ha _ state.counters.probes
                    (effective_guess_card state hinv test)
                · have hzero : (((2 ^ 128 - state.counters.probes : Nat) : ENNReal))⁻¹ = ⊤ := by
                    rw [show 2 ^ 128 - state.counters.probes = 0 by omega, Nat.cast_zero, ENNReal.inv_zero]
                  have hh : hazard (2 ^ 128) state.counters.probes = 1 := by
                    simp only [LargePotential.hazard, hzero]
                    simp
                  change _ ≤ hazard (2 ^ 128) state.counters.probes
                  rw [hh]
                  exact PMF.coe_le_one _ _

/-! ## The invariant is preserved -/

@[simp] theorem Counters.charge_probes (q : Nat) (counters : Counters) (charge : Charge) :
    (counters.charge q charge).probes = counters.probes := by
  cases charge <;> rfl

omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem inv_of_same (state after : State Coord Cell) (hc : after.candidates = state.candidates)
    (hp : after.counters.probes = state.counters.probes) (hinv : Inv state) : Inv after := by
  intro c
  rw [hc, hp]
  exact hinv c

omit [Fintype Coord] in
theorem card_erase_ge (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    (allowed c).card - 1 ≤ (eraseTableValue allowed c0 v c).card := by
  by_cases h : c = c0
  · subst h
    simpa only [eraseTableValue, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed c) (a := v))
  · simp only [eraseTableValue, Function.update_of_ne h]
    omega

omit [Fintype Coord] in
theorem card_erase_of_ne (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) (h : c ≠ c0) :
    (eraseTableValue allowed c0 v c).card = (allowed c).card := by
  simp only [eraseTableValue, Function.update_of_ne h]

omit [Fintype Coord] in
/-- An admissible probe removes at most one candidate from each coordinate. -/
theorem card_restrict_ge (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (hadm : ∀ g ∈ probe.guess, ∀ parent, probe.hit = Hit.label parent → g.1 ≠ parent) (c : Coord) :
    (allowed c).card - 1 ≤ (probe.restrict allowed answer c).card := by
  unfold Probe.restrict
  cases hhit : probe.hit with
  | target t =>
      simp only [Hit.restrict]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => simp
      | some g => exact card_erase_ge _ _ _ _
  | label parent =>
      simp only [Hit.restrict]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => exact card_erase_ge _ _ _ _
      | some g =>
          have hne : g.1 ≠ parent := hadm g (by rw [hg]; rfl) parent hhit
          by_cases hc : c = parent
          · subst hc
            have h1 := card_erase_ge (eraseTableValue allowed g.1 g.2) c (low answer) c
            rw [card_erase_of_ne allowed g.1 g.2 c (Ne.symm hne)] at h1
            exact h1
          · rw [card_erase_of_ne _ parent (low answer) c hc]
            exact card_erase_ge _ _ _ _

omit [Fintype Coord] [Fintype Cell] [DecidableEq Cell] in
theorem effective_admissible (candidates : Coord → Finset Digest) (test : Probe Coord) :
    ∀ g ∈ (test.effective candidates).guess, ∀ parent, (test.effective candidates).hit = Hit.label parent →
      g.1 ≠ parent := by
  intro g hg parent hp
  simp only [Probe.effective, Option.mem_def, Option.filter_eq_some_iff, decide_eq_true_eq] at hg
  exact hg.2.2 parent hp

omit [Fintype Coord] in
theorem restrict_subset_card (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    (probe.restrict allowed answer c).card ≤ (allowed c).card :=
  Finset.card_le_card (restrict_subset probe allowed answer c)

/-- **The posterior invariant is preserved along continuing steps.** -/
theorem residual_preserve (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state)
    (answer : (World auxSpec Coord Cell).Range input) (after : State Coord Cell)
    (hafter : (some answer, after) ∈ support (residualStep aux q input state)) : Inv after := by
  cases input with
  | inl input =>
      obtain ⟨a, ha⟩ := support_of_shape (liftM (aux input) : SPMF _) id (fun _ => state) _ hafter
      simp only [Prod.mk.injEq] at ha
      rw [ha.2]; exact hinv
  | inr request =>
      cases request with
      | read row charge =>
          obtain ⟨a, ha⟩ := support_of_shape (reply state.rows row) id (fun a => readState q state row a charge) _ hafter
          simp only [Prod.mk.injEq] at ha
          rw [ha.2]
          exact inv_of_same state _ rfl (Counters.charge_probes _ _ _) hinv
      | tick charge =>
          change (some answer, after) ∈ support (pure (some (), tickState q state charge) : SPMF _) at hafter
          rw [mem_support_pure_iff, Prod.mk.injEq] at hafter
          rw [hafter.2]
          exact inv_of_same state _ rfl (Counters.charge_probes _ _ _) hinv
      | disclose coord charge =>
          obtain ⟨v, hv⟩ := support_of_shape (cell (state.candidates coord)) id
            (fun v => disclosedState q state coord v charge) _ hafter
          simp only [Prod.mk.injEq] at hv
          rw [hv.2]
          intro c
          by_cases hc : c = coord
          · subst hc
            left
            simp only [disclosedState, discloseTableValue, Function.update_self, Finset.card_singleton]
          · simp only [disclosedState, discloseTableValue, Function.update_of_ne hc, Counters.charge_probes]
            exact hinv c
      | probe row test =>
          cases hcache : state.rows row with
          | some cached =>
              change (some answer, after) ∈ support (match state.rows row with
                | some answer => (pure (some answer, readState q state row answer .call) : SPMF _)
                | none => _) at hafter
              rw [hcache, mem_support_pure_iff, Prod.mk.injEq] at hafter
              rw [hafter.2]
              exact inv_of_same state _ rfl (Counters.charge_probes _ _ _) hinv
          | none =>
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResponse state.candidates (test.effective state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effective state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              rw [hstep] at hafter
              rcases observe_support _ _ _ _ hafter with h | ⟨a, ha, h⟩
              · simp at h
              · simp only [Prod.mk.injEq] at h
                rw [h.2]
                have hne := lazyResponse_nonempty state.candidates _ a ha
                intro c
                have hge := card_restrict_ge (test.effective state.candidates) state.candidates a
                  (effective_admissible state.candidates test) c
                have hle := restrict_subset_card (test.effective state.candidates) state.candidates a c
                have hpos := (hne c).card_pos
                simp only [probeState, Counters.probe]
                rcases hinv c with h1 | h2
                · left; omega
                · right; omega

/-- **LR-1 for the residual world**: from the empty state, every world program stops inside the budget plus its
expected mass at most `2x − x²` (`q ≤ 2^127`). -/
theorem residual_potential {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 127) (program : OracleComp (World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q | lazyRun aux q program initial] +
      (∑' result, Pr[= result | lazyRun aux q program initial] * (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := LargePotential.run_potential_initial (residualStep aux q) charges q hq Inv
    (fun input state hinv _ answer after hafter => residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => residual_step_bound aux q input state hinv) program initial initial_inv rfl rfl
  rw [run_residual] at h
  exact h

end Bound

end SigGolfCandidate.T3.Security.LargeResidual
