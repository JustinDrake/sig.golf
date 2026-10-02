import SigGolfCandidate.SphincsSecurity.Proof.Fts.PrimitiveMessagePotential

/-!
# LR-1: the stoppable run and the product-form potential of the large route

The large route of the T3 SecurityP proof (BP-C, plan/BP-C.md) charges **every query at most two units in product
form**: with `n = space` (`2^128` for T3) and `x = q/n`,

    Pr[some contact within the first q charged queries] + E[creation mass]/n ≤ 2x − x².

A union bound over per-query rates `2/(n − p)` gives at least `2x` and cannot pay the BPORS excess, the cache
allowance or SEC's `2^-18`; the bound must be the exact first-success form. This module proves it generically, for
**any** oracle specification, **any** program `OracleComp spec α` and **any** residual state type `σ`:

* `run step program` is the residual run: every oracle query of `program` is answered by `step input state :
  ProbComp (Option answer × state)`; `none` is a contact and stops the whole run (first-success semantics).
* `Charges` are three counters read off the state: `calls` (charged queries, compared with the budget `q`),
  `probes` (posterior probes so far; the hidden candidate sets have lost at most `probes` values, so a guess has
  posterior rate at most `1/(n − probes)` — sampling without replacement), `mass` (digest queries before the stop).
* Every step must be one of four kinds (`StepBound`), stated on the support of the step and its stop probability
  given the pre-query state:
  - `FreeStep`: never stops, never raises probes or mass (honest, known, private and uncharged queries);
  - `MassStep`: one call, never stops, at most one unit of mass while inside the budget (digest query, mass form);
  - `TestStep`: one call, stops with probability at most `1/n` (digest query, one-unit test form of BP-B §1.4);
  - `ProbeStep`: one call, one probe, stops with probability at most `hazard n probes = 1 − (1 − 1/(n − probes))²`
    (contact union: a guess of a hidden value or a hit on an honest output).
* `potential ch n q state = [calls ≤ q]·V(n, probes, q − calls) + mass/n` with the pinned record potential
  `V(n, p, r) = 1 − ((n − p − r)/(n − p))²` (`PrimitiveMessagePotential.value`); `V(n, 0, q) = 2x − x²`.

Main results:

* `run_expected_le` — generic supermartingale bound for the stoppable run (any potential).
* `run_potential_of_bound` — **LR-1**: for `0 < n`, `2q ≤ n`, an invariant preserved along continuing steps and every
  step of one of the four kinds, `Pr[stop ∧ calls ≤ q] + E[mass]/n ≤ potential`.
* `run_potential_initial` — at a state with no probe and no mass: `≤ ofReal (2x − x²)` with `n = 2^128`, the exact
  `hpotential` shape of `SeccClosing.largeBound_of_parts` / `large_route_of_contact`.
* `Contract`, `run_potential` — the statements of the BP-C prototype (`checks/BPC_LargeRoute.lean`), any spec.
* Test form: `testStep impl test` stops at the first hit of a per-query test on a stateful oracle
  `impl : QueryImpl spec (StateT σ m)`; its stop probability is the test's conditional rate given the pre-query
  state (`testStep_stop`); `FreeStep.of_test`, `MassStep.of_test`, `TestStep.of_test`, `ProbeStep.of_test` build the
  kinds from per-query facts about `impl` and `test`.
* Unstopped form: `observeRun impl test program` runs `simulateQ impl program` to the end and records the state right
  after the first hit; `observeRun_erasure` (forgetting the record gives `(simulateQ impl program).run`),
  `observeRun_cut` (cut at the first hit it is the stopped run), `observeRun_potential_of_bound` /
  `observeRun_potential_initial` (the potential bound for the first hit of the unstopped run).

The real algebra (`value`, `initial`, `message_payment`, `nonmessage_step`, `mono_remaining`, `mono_probes`,
`toReal_hazard`, `bounds`) is imported from the pinned record (`SphincsSecurity.Concrete.PrimitiveMessagePotential`);
the record's private helper `ennreal_mixture_le` is re-proved here.
-/

namespace SigGolfCandidate.T3.Security.LargePotential
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-! ## Potential algebra -/

/-- Two units per probe: the stop probability allowed for a probe after `probes` earlier probes, when the hidden
candidate sets have at least `space − probes` values (`1 − (1 − 1/(space − probes))²`, the record's `probeHazard`). -/
noncomputable def hazard (space probes : Nat) : ENNReal :=
  1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2

/-- The continuation part of the potential: `V(space, probes, q − calls)` inside the budget, `0` outside. -/
noncomputable def continuation (space q calls probes : Nat) : ENNReal :=
  if calls ≤ q then ENNReal.ofReal (PrimitiveMessagePotential.value space probes ((q : ℝ) - calls)) else 0

theorem hazard_le_one (space probes : Nat) : hazard space probes ≤ 1 := tsub_le_self

/-- A posterior guess (rate `1/(space − probes)`, sampling without replacement) is within the two-unit hazard. -/
theorem inv_sub_le_hazard (space probes : Nat) (hprobes : probes < space) :
    ((space - probes : Nat) : ENNReal)⁻¹ ≤ hazard space probes := by
  have hone : ((space - probes : Nat) : ENNReal)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr (by exact_mod_cast Nat.sub_pos_of_lt hprobes)
  have hsq : (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 ≤ 1 - ((space - probes : Nat) : ENNReal)⁻¹ := by
    rw [pow_two]
    exact mul_le_of_le_one_left' tsub_le_self
  calc
    ((space - probes : Nat) : ENNReal)⁻¹ = 1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) :=
      (ENNReal.sub_sub_cancel ENNReal.one_ne_top hone).symm
    _ ≤ hazard space probes := tsub_le_tsub_left hsq 1

/-- One unit `1/space` (e.g. a hit on an honest output by a fresh uniform answer) is within the two-unit hazard. -/
theorem inv_space_le_hazard (space probes : Nat) (hprobes : probes < space) :
    (space : ENNReal)⁻¹ ≤ hazard space probes :=
  (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.sub_le space probes)).trans (inv_sub_le_hazard space probes hprobes)

private theorem real_facts (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) :
    (0 : ℝ) < space ∧ 2 * (q : ℝ) ≤ space ∧ (probes : ℝ) ≤ calls ∧ (q : ℝ) < space := by
  have h1 : (0 : ℝ) < space := by exact_mod_cast hspace
  have h2 : 2 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have h3 : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  refine ⟨h1, h2, h3, by linarith⟩

/-- The continuation is antitone in `calls` and monotone in `probes` (inside the admissible range
`probes ≤ calls`, `2q ≤ space`). -/
theorem continuation_anti (space q calls probes calls' probes' : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : probes ≤ calls) (hcalls : calls ≤ calls') (hprobes' : probes' ≤ probes) :
    continuation space q calls' probes' ≤ continuation space q calls probes := by
  unfold continuation
  by_cases h' : calls' ≤ q
  · rw [if_pos h', if_pos (le_trans hcalls h')]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
    have hc : (calls : ℝ) ≤ calls' := by exact_mod_cast hcalls
    have hc' : (calls' : ℝ) ≤ q := by exact_mod_cast h'
    have hp' : (probes' : ℝ) ≤ probes := by exact_mod_cast hprobes'
    have hm1 := PrimitiveMessagePotential.mono_probes space probes' probes ((q : ℝ) - calls')
      (by linarith) hp' (by linarith)
    have hm2 := PrimitiveMessagePotential.mono_remaining space probes ((q : ℝ) - calls') ((q : ℝ) - calls)
      (by linarith) (by linarith) (by linarith)
    exact hm1.trans hm2
  · rw [if_neg h']
    exact zero_le

/-- Message payment: one unit `1/space` plus the continuation after one more call is paid by the continuation
before it (`PrimitiveMessagePotential.message_payment`). -/
theorem continuation_pay (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + (space : ENNReal)⁻¹ ≤ continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := PrimitiveMessagePotential.message_payment space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs
    (by positivity) (by push_cast; linarith) (by push_cast; linarith)
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  rw [ENNReal.ofReal_add (by positivity) hv, one_div, ENNReal.ofReal_inv_of_pos hs, ENNReal.ofReal_natCast] at hfinal
  rw [add_comm]
  exact hfinal

/-- Mixture conversion between `ENNReal` and the real potential (re-proof of the record's private helper of
`RetainedResidualPrimitivePotential`). -/
theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h

/-- Probe payment (product form): a stop with probability at most `hazard space probes`, followed by the
continuation after one more call and one more probe, is paid by the continuation before it
(`PrimitiveMessagePotential.nonmessage_step`, which telescopes `∏ (1 − 1/(space − p))²`). -/
theorem continuation_probe (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) (probability : ENNReal)
    (hhazard : probability ≤ hazard space probes) :
    probability + (1 - probability) * continuation space q (calls + 1) (probes + 1) ≤
      continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  have hpl : probes < space := by omega
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hone : probability ≤ 1 := hhazard.trans (hazard_le_one space probes)
  have hreal : probability.toReal ≤ PrimitiveMessagePotential.value space probes 1 := by
    have h := ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (hazard_le_one space probes)) hhazard
    rwa [hazard, PrimitiveMessagePotential.toReal_hazard space probes hpl] at h
  have hstep := PrimitiveMessagePotential.nonmessage_step space probes ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) probability.toReal (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) hreal
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hstep
  have hnext := (PrimitiveMessagePotential.bounds space ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)).1
  have hbefore := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - calls)
    (by linarith) (by linarith)).1
  exact ennreal_mixture_le probability hone _ _ hnext hbefore hstep

/-- Initial value: `V(2^128, 0, q) = 2x − x²` with `x = q/2^128`. -/
theorem initial_potential (q : Nat) :
    ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ 128) 0 ((q : ℝ) - 0)) =
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  rw [sub_zero, PrimitiveMessagePotential.initial _ _ (by positivity)]

/-! ## The stoppable run

The step monad `m` is generic: any monad with the VCVio evaluation semantics (`ProbComp`, `SPMF`, ...). With
`m = SPMF` a step may be built from the record's hidden-label posteriors, e.g.
`(fun answer => (answer, …)) <$> liftM (HiddenLabelObservation.lazyResponse allowed probe).toPMF`, whose `none` is the
probe's failure (`lazyResponse_pair_failure_le_rounds`). -/

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]

/-- One residual step: the answer to `input` from `state`, or `none` for a contact (stop), with the next state. -/
abbrev Step (m : Type → Type) (spec : OracleSpec ι) (σ : Type) :=
  (input : spec.Domain) → σ → m (Option (spec.Range input) × σ)

/-- The residual run of `program`: every query is answered by `step`; a contact stops the whole run
(first-success semantics). Built with `OracleComp.construct`, like `FirstHit.observe`. -/
noncomputable def run {α σ : Type} (step : Step m spec σ) (program : OracleComp spec α) :
    σ → m (Option α × σ) :=
  OracleComp.construct
    (fun value state => pure (some value, state))
    (fun input _ next state => do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => next answer middle.2) program

theorem run_pure {α σ : Type} (step : Step m spec σ) (value : α) (state : σ) :
    run step (pure value : OracleComp spec α) state = pure (some value, state) := rfl

theorem run_query_bind {α σ : Type} (step : Step m spec σ) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (state : σ) :
    run step (liftM (spec.query input) >>= next) state = (do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => run step (next answer) middle.2) := rfl

variable [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

/-- Terminal value of a run result: `stopValue` of the state after a contact, `doneValue` of the final state
after normal termination. -/
def terminal {β σ : Type} (stopValue doneValue : σ → ENNReal) (result : Option β × σ) : ENNReal :=
  result.1.elim (stopValue result.2) (fun _ => doneValue result.2)

/-- **Generic supermartingale bound.** If, on states satisfying `inv` (preserved along continuing steps), one step
never increases the expected value of `terminal stopValue potential`, and a terminated state is worth at most its
potential, then the run's expected terminal value is at most the initial potential. -/
theorem run_expected_le {α σ : Type} (step : Step m spec σ) (inv : σ → Prop)
    (potential stopValue doneValue : σ → ENNReal)
    (hdone : ∀ state, inv state → doneValue state ≤ potential state)
    (hpreserve : ∀ input state, inv state → ∀ answer after,
      (some answer, after) ∈ support (step input state) → inv after)
    (hstep : ∀ input state, inv state →
      expectedValue (step input state) (terminal stopValue potential) ≤ potential state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state) :
    expectedValue (run step program state) (terminal stopValue doneValue) ≤ potential state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [run_pure, expectedValue_pure]
      exact hdone state hstate
  | query_bind input next ih =>
      rw [run_query_bind, expectedValue_bind]
      refine le_trans ?_ (hstep input state hstate)
      apply expectedValue_mono_of_support
      rintro ⟨answer, after⟩ hmiddle
      cases answer with
      | none => simp [terminal]
      | some answer => exact ih answer after (hpreserve input state hstate answer after hmiddle)

/-! ## Charges, potential and the four step kinds -/

/-- Counters of the residual run, read off its state: charged calls (compared with the budget), posterior
probes (two-unit steps), creation mass (one unit per digest query before the first contact, mass form). -/
structure Charges (σ : Type) where
  calls : σ → Nat
  probes : σ → Nat
  mass : σ → Nat

/-- The product potential `[calls ≤ q]·V(space, probes, q − calls) + mass/space`. -/
noncomputable def potential {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (ch.mass state : ENNReal) / space

/-- Value of a stopped state: one unit if the contact is inside the budget, plus its mass. -/
noncomputable def stopValue {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (ch.mass state : ENNReal) / space

/-- Value of a terminated state: its mass. -/
noncomputable def doneValue {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (ch.mass state : ENNReal) / space

/-- Free step (honest, known, private or uncharged query): never stops; calls do not decrease; probes and mass do
not increase. -/
def FreeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (input : spec.Domain) (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] = 0

/-- Mass step (digest query, mass form): at least one call; never stops; probes do not increase; at most one unit
of mass, and none once the call is outside the budget `q`. -/
def MassStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat) (input : spec.Domain) (state : σ) :
    Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧
    ch.mass result.2 ≤ ch.mass state + (if ch.calls state + 1 ≤ q then 1 else 0)) ∧
  Pr[fun result => result.1 = none | step input state] = 0

/-- Test step (digest query, one-unit test form of BP-B §1.4): at least one call; probes and mass do not increase;
stops with probability at most `1/space` given the pre-query state. -/
def TestStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ (space : ENNReal)⁻¹

/-- Probe step (contact union, two units): at least one call; at most one more probe; mass does not increase;
stops with probability at most `hazard space probes` given the pre-query state. -/
def ProbeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state + 1 ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ hazard space (ch.probes state)

/-- Every step is one of the four kinds. -/
def StepBound {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  FreeStep step ch input state ∨ MassStep step ch q input state ∨ TestStep step ch space input state ∨
    ProbeStep step ch space input state

theorem StepBound.probes_le {σ : Type} {step : Step m spec σ} {ch : Charges σ} {space q : Nat}
    {input : spec.Domain} {state : σ} (h : StepBound step ch space q input state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    ∀ result ∈ support (step input state), ch.probes result.2 ≤ ch.calls result.2 := by
  intro result hresult
  rcases h with h | h | h | h
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega

/-- Outside the budget every result of a step that adds a call and no mass is worth at most the old mass. -/
theorem terminal_le_of_over {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue ch space q) (potential ch space q) result ≤ (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (ch.mass result.2 : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (by exact_mod_cast hmass) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue, hnot] using hm
  · simpa [terminal, potential, continuation, hnot] using hm

/-- The expectation of `[stop]·1 + [¬stop]·value + rest` is at most `p + (1 − p)·value + rest`, `p = Pr[stop]`
(re-proof of the record's private `expected_indicator_value_le`). -/
theorem expected_stop_le {β σ : Type} (law : m (Option β × σ)) (value rest : ENNReal) :
    expectedValue law (fun result => (if result.1 = none then 1 else value) + rest) ≤
      Pr[fun result => result.1 = none | law] +
        (1 - Pr[fun result => result.1 = none | law]) * value + rest := by
  have hcompl : Pr[fun result => ¬result.1 = none | law] ≤ 1 - Pr[fun result => result.1 = none | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  rw [expectedValue_add]
  have hsplit : expectedValue law (fun result => if result.1 = none then 1 else value) =
      Pr[fun result => result.1 = none | law] + Pr[fun result => ¬result.1 = none | law] * value := by
    rw [expectedValue_def, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases h : result.1 = none <;> simp [h]
  rw [hsplit]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' hcompl le_rfl)) ?_
  exact expectedValue_le_of_le law (fun _ => le_rfl)

section payments
variable {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain) (state : σ)

/-- A free step does not increase the potential. -/
theorem FreeStep.payment (h : FreeStep step ch input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  have hsome : answer ≠ none := by
    have := (probEvent_eq_zero_iff.mp h.2) _ hresult
    simpa using this
  obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
  simp only [terminal, Option.elim_some, potential]
  exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
    (ENNReal.div_le_div_right (by exact_mod_cast hmass) _)

/-- A mass step pays its unit of mass from the potential (`continuation_pay`). -/
theorem MassStep.payment (h : MassStep step ch q input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  by_cases hc : ch.calls state + 1 ≤ q
  · rw [if_pos hc] at hmass
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential]
    have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
      (ch.probes after) hspace hq (by omega) hcalls hp
    have hpay := continuation_pay space q (ch.calls state) (ch.probes state) hspace hq hprobes hc
    have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹ := by
      rw [← one_div, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast hmass) _
    calc
      _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
          ((ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹) := add_le_add hcont hm
      _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (space : ENNReal)⁻¹) +
          (ch.mass state : ENNReal) / space := by ring
      _ ≤ _ := add_le_add hpay le_rfl
  · rw [if_neg hc, add_zero] at hmass
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

/-- A one-unit test step pays its stop probability from the potential (`continuation_pay`). -/
theorem TestStep.payment (h : TestStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
          (ch.mass state : ENNReal) / space := by
        refine add_le_add (add_le_add h.2 ?_) le_rfl
        exact mul_le_of_le_one_left' tsub_le_self
      _ ≤ _ := by
        rw [add_comm ((space : ENNReal)⁻¹)]
        exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

/-- A probe step pays its stop probability in product form (`continuation_probe`). -/
theorem ProbeStep.payment (h : ProbeStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state + 1) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

/-- Every bounded step does not increase the potential. -/
theorem StepBound.payment (h : StepBound step ch space q input state) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  rcases h with h | h | h | h
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes

end payments

/-- The left-hand side of the potential bound (stop inside the budget plus mass) is one expectation of
`terminal`. -/
theorem stop_add_mass_eq {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue ch space q) (doneValue ch space)) := by
  have hfun : terminal (stopValue ch space q) (doneValue ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) + (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue]
    · simp [terminal, doneValue]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]

/-- **LR-1, product form (general).** For `0 < space` and `2q ≤ space`, if every step from a state satisfying the
invariant `inv` (preserved along continuing steps) and `probes ≤ calls` is one of the four kinds, then the
probability of a contact inside the budget plus the expected creation mass (in units of `1/space`) is at most the
potential `[calls ≤ q]·V(space, probes, q − calls) + mass/space` of the start state. -/
theorem run_potential_of_bound {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (hspace : 0 < space) (hq : 2 * q ≤ space) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch space q input state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program state] +
      (∑' result, Pr[= result | run step program state] * (ch.mass result.2 : ENNReal)) / space ≤
      potential ch space q state := by
  rw [stop_add_mass_eq]
  refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
    (potential ch space q) (stopValue ch space q) (doneValue ch space) ?_ ?_ ?_ program state ⟨hstate, hprobes⟩
  · intro state _
    exact le_add_self
  · rintro input state ⟨hi, hp⟩ answer after hmem
    exact ⟨hpreserve input state hi hp answer after hmem,
      (hbound input state hi hp).probes_le hp _ hmem⟩
  · rintro input state ⟨hi, hp⟩
    exact (hbound input state hi hp).payment step ch space q input state hspace hq hp

/-! ## The initial value `2x − x²` -/

/-- At a state with no probe and no mass (any number of calls), the potential is at most `2x − x²`. -/
theorem potential_initial_le {σ : Type} (ch : Charges σ) (q : Nat) (hq : q ≤ 2 ^ 127) (state : σ)
    (hprobes : ch.probes state = 0) (hmass : ch.mass state = 0) :
    potential ch (2 ^ 128) q state ≤ ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls state) (ch.probes state) (by positivity)
    (by omega) le_rfl (Nat.zero_le _) (by omega)
  unfold potential
  rw [hmass, Nat.cast_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q

/-- **LR-1 at the initial state** (`space = 2^128`, `q ≤ 2^127`, no probe and no mass at the start): a contact inside
the budget plus the expected creation mass costs at most `2x − x²` — the `hpotential` shape of
`SeccClosing.largeBound_of_parts` / `SeccClosing.large_route_of_contact`. -/
theorem run_potential_initial {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq : q ≤ 2 ^ 127) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program init] +
      (∑' result, Pr[= result | run step program init] * (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_of_bound step ch (2 ^ 128) q (by positivity) (by omega) inv hpreserve hbound program init
    hinit (by omega)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (potential_initial_le ch q hq init hprobes hmass)

/-! ## The BP-C prototype contract (`checks/BPC_LargeRoute.lean`) -/

/-- Per-step contract of the BP-C prototype: a charged step costs one call; a charged non-message step may probe
once and stops with probability at most `hazard 2^128 probes`; a charged message step never stops and adds one unit
of mass while inside the budget; uncharged steps are free. -/
def Contract {σ : Type} (step : Step m spec σ) (ch : Charges σ) (charged : spec.Domain → Prop)
    (message : σ → spec.Domain → Prop) (q : Nat) : Prop :=
  ∀ input state, ch.probes state ≤ ch.calls state →
    (∀ result ∈ support (step input state),
      ch.calls result.2 = ch.calls state + (if charged input then 1 else 0) ∧
      ch.probes result.2 ≤ ch.probes state + (if charged input ∧ ¬message state input then 1 else 0) ∧
      ch.mass result.2 ≤ ch.mass state +
        (if charged input ∧ message state input ∧ ch.calls state + 1 ≤ q then 1 else 0)) ∧
    Pr[fun result => result.1 = none | step input state] ≤
      (if charged input ∧ ¬message state input then hazard (2 ^ 128) (ch.probes state) else 0)

/-- The prototype contract is a special case of the four kinds (uncharged = free, charged message = mass,
charged non-message = probe). -/
theorem Contract.stepBound {σ : Type} {step : Step m spec σ} {ch : Charges σ} {charged : spec.Domain → Prop}
    {message : σ → spec.Domain → Prop} {q : Nat} (h : Contract step ch charged message q)
    (input : spec.Domain) (state : σ) (hprobes : ch.probes state ≤ ch.calls state) :
    StepBound step ch (2 ^ 128) q input state := by
  obtain ⟨hsupport, hstop⟩ := h input state hprobes
  by_cases hc : charged input
  · by_cases hm : message state input
    · right; left
      refine ⟨fun result hresult => ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hsupport result hresult
        simp only [hc, hm, if_true, not_true_eq_false, and_false, if_false, add_zero, true_and] at h1 h2 h3
        exact ⟨h1.ge, h2, h3⟩
      · simpa [hc, hm] using hstop
    · right; right; right
      refine ⟨fun result hresult => ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hsupport result hresult
        simp only [hc, hm, if_true, not_false_eq_true, and_self, false_and, and_false, if_false, add_zero]
          at h1 h2 h3
        exact ⟨h1.ge, h2, h3⟩
      · simpa [hc, hm] using hstop
  · left
    refine ⟨fun result hresult => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hsupport result hresult
      simp only [hc, if_false, false_and, add_zero] at h1 h2 h3
      exact ⟨h1.ge, h2, h3⟩
    · simpa [hc] using hstop

/-- **LR-1, prototype statement** (`run_potential` of `checks/BPC_LargeRoute.lean`, for any oracle spec):
contacts within the budget plus the creation mass are paid by `V(2^128, probes, q − calls)`. -/
theorem run_potential {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (charged : spec.Domain → Prop)
    (message : σ → spec.Domain → Prop) (q : Nat) (hq : 2 * q ≤ 2 ^ 128)
    (hcontract : Contract step ch charged message q) (program : OracleComp spec α) (state : σ)
    (hprobes : ch.probes state ≤ ch.calls state) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program state] +
      (∑' result, Pr[= result | run step program state] * (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      (if ch.calls state ≤ q then
        ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ 128) (ch.probes state) ((q : ℝ) - ch.calls state))
        else 0) + (ch.mass state : ENNReal) / 2 ^ 128 := by
  have h := run_potential_of_bound step ch (2 ^ 128) q (by positivity) hq (fun _ => True)
    (fun _ _ _ _ _ _ _ => trivial) (fun input state _ hp => hcontract.stepBound input state hp) program state
    trivial hprobes
  simpa only [potential, continuation, Nat.cast_pow, Nat.cast_ofNat] using h

/-! ## Test form: a stateful oracle and a per-query test -/

/-- The stop-at-first-hit step of a stateful oracle implementation `impl` and a per-query `test` on
(pre-query state, input, answer, post-query state). -/
noncomputable def testStep {σ : Type} (impl : QueryImpl spec (StateT σ m))
    (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop) : Step m spec σ :=
  fun input state =>
    (fun result => (if test state input result.1 result.2 then none else some result.1, result.2)) <$>
      (impl input).run state

section testForm
variable {σ : Type} (impl : QueryImpl spec (StateT σ m))
  (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop)

/-- The stop probability of a test-form step is the test's conditional rate given the pre-query state. -/
theorem testStep_stop (input : spec.Domain) (state : σ) :
    Pr[fun result => result.1 = none | testStep impl test input state] =
      Pr[fun result => test state input result.1 result.2 | (impl input).run state] := by
  rw [testStep, probEvent_map]
  congr 1
  funext result
  by_cases h : test state input result.1 result.2 <;> simp [h]

theorem mem_support_testStep (input : spec.Domain) (state : σ) (result : Option (spec.Range input) × σ)
    (hresult : result ∈ support (testStep impl test input state)) :
    ∃ answer, (answer, result.2) ∈ support ((impl input).run state) ∧
      (result.1 = none ↔ test state input answer result.2) ∧ (result.1 = none ∨ result.1 = some answer) := by
  rw [testStep, support_map] at hresult
  obtain ⟨⟨answer, after⟩, hmem, rfl⟩ := hresult
  refine ⟨answer, hmem, ?_, ?_⟩
  · by_cases h : test state input answer after <;> simp [h]
  · by_cases h : test state input answer after <;> simp [h]

/-- A continuing result of a test-form step is an untested result of the oracle. -/
theorem mem_support_testStep_some (input : spec.Domain) (state : σ) (answer : spec.Range input) (after : σ)
    (hresult : (some answer, after) ∈ support (testStep impl test input state)) :
    (answer, after) ∈ support ((impl input).run state) ∧ ¬test state input answer after := by
  obtain ⟨answer', hmem, hiff, hcase⟩ := mem_support_testStep impl test input state _ hresult
  have heq : answer' = answer := by
    rcases hcase with h | h
    · exact absurd h (by simp)
    · exact (Option.some_inj.mp h).symm
  subst heq
  exact ⟨hmem, fun ht => absurd (hiff.mpr ht) (by simp)⟩

variable (ch : Charges σ) (space q : Nat) (input : spec.Domain) (state : σ)

theorem FreeStep.of_test
    (hsupport : ∀ result ∈ support ((impl input).run state), ch.calls state ≤ ch.calls result.2 ∧
      ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state)
    (hrate : Pr[fun result => test state input result.1 result.2 | (impl input).run state] = 0) :
    FreeStep (testStep impl test) ch input state := by
  refine ⟨fun result hresult => ?_, by rw [testStep_stop]; exact hrate⟩
  obtain ⟨answer, hmem, -, -⟩ := mem_support_testStep impl test input state result hresult
  exact hsupport _ hmem

theorem MassStep.of_test
    (hsupport : ∀ result ∈ support ((impl input).run state), ch.calls state + 1 ≤ ch.calls result.2 ∧
      ch.probes result.2 ≤ ch.probes state ∧
      ch.mass result.2 ≤ ch.mass state + (if ch.calls state + 1 ≤ q then 1 else 0))
    (hrate : Pr[fun result => test state input result.1 result.2 | (impl input).run state] = 0) :
    MassStep (testStep impl test) ch q input state := by
  refine ⟨fun result hresult => ?_, by rw [testStep_stop]; exact hrate⟩
  obtain ⟨answer, hmem, -, -⟩ := mem_support_testStep impl test input state result hresult
  exact hsupport _ hmem

theorem TestStep.of_test
    (hsupport : ∀ result ∈ support ((impl input).run state), ch.calls state + 1 ≤ ch.calls result.2 ∧
      ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state)
    (hrate : Pr[fun result => test state input result.1 result.2 | (impl input).run state] ≤
      (space : ENNReal)⁻¹) :
    TestStep (testStep impl test) ch space input state := by
  refine ⟨fun result hresult => ?_, by rw [testStep_stop]; exact hrate⟩
  obtain ⟨answer, hmem, -, -⟩ := mem_support_testStep impl test input state result hresult
  exact hsupport _ hmem

theorem ProbeStep.of_test
    (hsupport : ∀ result ∈ support ((impl input).run state), ch.calls state + 1 ≤ ch.calls result.2 ∧
      ch.probes result.2 ≤ ch.probes state + 1 ∧ ch.mass result.2 ≤ ch.mass state)
    (hrate : Pr[fun result => test state input result.1 result.2 | (impl input).run state] ≤
      hazard space (ch.probes state)) :
    ProbeStep (testStep impl test) ch space input state := by
  refine ⟨fun result hresult => ?_, by rw [testStep_stop]; exact hrate⟩
  obtain ⟨answer, hmem, -, -⟩ := mem_support_testStep impl test input state result hresult
  exact hsupport _ hmem

end testForm

/-! ## Unstopped form: the first hit of a test along `simulateQ impl` -/

/-- The unstopped run of `impl` on `program` that records the state right after the first test hit
(`none` if no query hits). -/
noncomputable def observeRun {α σ : Type} (impl : QueryImpl spec (StateT σ m))
    (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop) (program : OracleComp spec α) :
    σ → m (Option σ × α × σ) :=
  OracleComp.construct
    (fun value state => pure (none, value, state))
    (fun input next rest state => do
      let middle ← (impl input).run state
      if test state input middle.1 middle.2 then
        (fun last => (some middle.2, last)) <$> (simulateQ impl (next middle.1)).run middle.2
      else rest middle.1 middle.2) program

section observe
variable {α σ : Type} (impl : QueryImpl spec (StateT σ m))
  (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop)

theorem observeRun_pure (value : α) (state : σ) :
    observeRun impl test (pure value : OracleComp spec α) state = pure (none, value, state) := rfl

theorem observeRun_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec α) (state : σ) :
    observeRun impl test (liftM (spec.query input) >>= next) state = (do
      let middle ← (impl input).run state
      if test state input middle.1 middle.2 then
        (fun last => (some middle.2, last)) <$> (simulateQ impl (next middle.1)).run middle.2
      else observeRun impl test (next middle.1) middle.2) := rfl

/-- Forgetting the first-hit record gives the ordinary simulated run. -/
theorem observeRun_erasure (program : OracleComp spec α) (state : σ) :
    (fun result => result.2) <$> observeRun impl test program state = (simulateQ impl program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [observeRun_pure]
  | query_bind input next ih =>
      rw [observeRun_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      apply bind_congr
      intro middle
      split
      · simp [Functor.map_map]
      · exact ih middle.1 middle.2

/-- Cut of an observed result at its first hit: `(none, state after the hit)` or `(some value, final state)`. -/
def cut : Option σ × α × σ → Option α × σ
  | (some hit, _, _) => (none, hit)
  | (none, value, final) => (some value, final)

/-- Cut at its first hit, the observed unstopped run is dominated by the stopped run of the test-form step (for
every functional; the continuation after the hit can only lose mass). -/
theorem observeRun_cut_le (program : OracleComp spec α) (state : σ) (f : Option α × σ → ENNReal) :
    expectedValue (observeRun impl test program state) (fun result => f (cut result)) ≤
      expectedValue (run (testStep impl test) program state) f := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [observeRun_pure, run_pure, cut]
  | query_bind input next ih =>
      rw [observeRun_query_bind, run_query_bind, expectedValue_bind, testStep, bind_map_left,
        expectedValue_bind]
      apply expectedValue_mono
      intro middle
      by_cases h : test state input middle.1 middle.2
      · simp only [h, if_true, expectedValue_map, cut, expectedValue_pure]
        exact expectedValue_le_of_le _ (fun _ => le_rfl)
      · simp only [h, if_false]
        exact ih middle.1 middle.2

/-- If the oracle never fails (e.g. `m = ProbComp`), the cut observed run IS the stopped run. -/
theorem observeRun_cut (hfail : ∀ (β : Type) (computation : m β), Pr[⊥ | computation] = 0)
    (program : OracleComp spec α) (state : σ) (f : Option α × σ → ENNReal) :
    expectedValue (observeRun impl test program state) (fun result => f (cut result)) =
      expectedValue (run (testStep impl test) program state) f := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [observeRun_pure, run_pure, cut]
  | query_bind input next ih =>
      rw [observeRun_query_bind, run_query_bind, expectedValue_bind, testStep, bind_map_left,
        expectedValue_bind]
      apply congrArg (expectedValue ((impl input).run state))
      funext middle
      by_cases h : test state input middle.1 middle.2
      · simp only [h, if_true, expectedValue_map, cut, expectedValue_pure]
        exact expectedValue_const (hfail _ _) _
      · simp only [h, if_false]
        exact ih middle.1 middle.2

/-- **LR-1, unstopped form.** For the first hit of a per-query `test` along `simulateQ impl program`: the probability
that a hit occurs with the hit state inside the budget, plus the expected mass at the first hit (or at the end if no
hit), is at most the potential, provided every test-form step from an invariant state is one of the four kinds. -/
theorem observeRun_potential_of_bound (ch : Charges σ) (space q : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ result ∈ support ((impl input).run state), ¬test state input result.1 result.2 → inv result.2)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound (testStep impl test) ch space q input state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    Pr[fun result => ∃ hit, result.1 = some hit ∧ ch.calls hit ≤ q | observeRun impl test program state] +
      (∑' result, Pr[= result | observeRun impl test program state] * (ch.mass (cut result).2 : ENNReal)) /
        space ≤ potential ch space q state := by
  have hlhs : Pr[fun result => ∃ hit, result.1 = some hit ∧ ch.calls hit ≤ q |
        observeRun impl test program state] +
      (∑' result, Pr[= result | observeRun impl test program state] * (ch.mass (cut result).2 : ENNReal)) /
        space = expectedValue (observeRun impl test program state)
          (fun result => terminal (stopValue ch space q) (doneValue ch space) (cut result)) := by
    have hfun : (fun result : Option σ × α × σ => terminal (stopValue ch space q) (doneValue ch space) (cut result)) =
        fun result => (if ∃ hit, result.1 = some hit ∧ ch.calls hit ≤ q then 1 else 0) +
          (ch.mass (cut result).2 : ENNReal) / space := by
      funext result
      rcases result with ⟨_ | hit, value, final⟩
      · simp [terminal, doneValue, cut]
      · by_cases hc : ch.calls hit ≤ q <;> simp [terminal, stopValue, cut, hc]
    rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
    congr 1
    simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
  rw [hlhs]
  refine (observeRun_cut_le impl test program state _).trans ?_
  rw [← stop_add_mass_eq]
  refine run_potential_of_bound (testStep impl test) ch space q hspace hq inv ?_ hbound program state hstate hprobes
  intro input state hi hp answer after hmem
  obtain ⟨hmem', htest⟩ := mem_support_testStep_some impl test input state answer after hmem
  exact hpreserve input state hi hp (answer, after) hmem' htest

/-- **LR-1, unstopped form at the initial state** (`space = 2^128`): `≤ 2x − x²`. -/
theorem observeRun_potential_initial (ch : Charges σ) (q : Nat) (hq : q ≤ 2 ^ 127) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ result ∈ support ((impl input).run state), ¬test state input result.1 result.2 → inv result.2)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound (testStep impl test) ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => ∃ hit, result.1 = some hit ∧ ch.calls hit ≤ q | observeRun impl test program init] +
      (∑' result, Pr[= result | observeRun impl test program init] * (ch.mass (cut result).2 : ENNReal)) /
        2 ^ 128 ≤ ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := observeRun_potential_of_bound impl test ch (2 ^ 128) q (by positivity) (by omega) inv hpreserve hbound
    program init hinit (by omega)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (potential_initial_le ch q hq init hprobes hmass)

end observe

end SigGolfCandidate.T3.Security.LargePotential
