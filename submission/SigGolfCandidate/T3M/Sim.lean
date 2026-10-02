import SigGolfCandidate.T3M.Bytes
import SigGolfCandidate.Rv

/-!
# T3M simulation judgments

Machine runs refine oracle computations (adapted from the five-layer `Keygen/XSim` and
`Sign/Sim`, without their `Ref` dependency):

* `countWith` / `countCalls` / `countBlocks` and the joint counter `countBoth`;
* `Sim image s W oa Q` : the machine performs exactly the queries of `oa`, at most `W` cycles
  (bounded; searches), with `Sim.run_eq`, `Sim.runWith`;
* `XSim image s k c n b oa Q` : exactly the queries of `oa`, exactly `k` steps, `c` cycles, `n`
  calls, `b` compressions (control flow independent of the answers), with `XSim.run_eq`;
  `XSim.toSim` turns an exact run into a bounded one;
* `machineHandler sk` / `mrealize sk` : Core's programs (`T3.M`) as organizer computations:
  public inputs relabeled by `toQ`, private coordinates realized by the secret, coins never
  occur (MACH-PLAN §1.2);
* `TSim image sk s k c n b p Q := XSim image s k c n b (mrealize sk p) Q` (exact) and
  `TBSim image sk s W p Q := Sim image s W (mrealize sk p) Q` (bounded) with combinators along
  Core's structure: `bind`, `steps`, `foldlM_range'`, `mapM_list`, and one HASH `ECALL` for
  `publicHash`, `shortHash`, `privatePair`, `privateMac`, `privateNonce`, `mask`.
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateMac privateNonce mask
  privateInput header pad64 Coordinate HashOutput Digest Region)

/-! ## Counters -/

/-- Forward a query and add its weight to the counter. -/
def countImpl (wt : Query → Nat) : QueryImpl HashSpec (StateT Nat (OracleComp HashSpec)) :=
  fun q => do
    modify (· + wt q)
    liftM (HashSpec.query q)

/-- The result and the total weight `wt q` of the queries made. -/
def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0

/-- The result and the number of oracle calls. -/
def countCalls {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith (fun _ => 1) oa

/-- The result and the number of compressions (64-byte blocks). -/
def countBlocks {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith Query.blocks oa

section countw
variable (wt : Query → Nat) {α β : Type}

theorem countImpl_run (oa : OracleComp HashSpec α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp HashSpec α) = pure (a, 0) :=
  rfl

theorem countWith_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)

@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, wt q)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

@[simp] theorem fst_countWith (oa : OracleComp HashSpec α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a

end countw

theorem countCalls_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countCalls (oa >>= f) =
      countCalls oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countCalls (f p.1) :=
  countWith_bind _ oa f

@[simp] theorem countCalls_query (q : Query) :
    countCalls (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) :=
  countWith_query _ q

@[simp] theorem fst_countCalls {α : Type} (oa : OracleComp HashSpec α) :
    Prod.fst <$> countCalls oa = oa := fst_countWith _ oa

/-- Forward a query, counting one call and its blocks. -/
def countImpl2 : QueryImpl HashSpec (StateT (Nat × Nat) (OracleComp HashSpec)) :=
  fun q => do
    modify (fun p => (p.1 + 1, p.2 + Query.blocks q))
    liftM (HashSpec.query q)

/-- The result, the number of oracle calls and the number of compressions. -/
def countBoth {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat × Nat) :=
  (simulateQ countImpl2 oa).run (0, 0)

section count
variable {α β : Type}

theorem countImpl2_run (oa : OracleComp HashSpec α) (c b : Nat) :
    (simulateQ countImpl2 oa).run (c, b) =
      (fun p => (p.1, c + p.2.1, b + p.2.2)) <$> countBoth oa := by
  unfold countBoth
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl2]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT (Nat × Nat) (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left]
    congr 1; funext a
    rw [ih a (c + 1) (b + Query.blocks q), ih a (0 + 1) (0 + Query.blocks q), Functor.map_map]
    congr 1; funext p
    simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countBoth_pure (a : α) :
    countBoth (pure a : OracleComp HashSpec α) = pure (a, 0, 0) := rfl

theorem countBoth_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countBoth (oa >>= f) =
      countBoth oa >>= fun p => (fun r => (r.1, p.2.1 + r.2.1, p.2.2 + r.2.2)) <$> countBoth (f p.1) := by
  conv_lhs => unfold countBoth
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl2_run (f p.1) p.2.1 p.2.2)

@[simp] theorem countBoth_query (q : Query) :
    countBoth (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1, q.blocks)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countBoth
  rw [simulateQ_spec_query]
  simp only [countImpl2, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

/-- The joint counter projects to `countCalls`. -/
theorem countBoth_calls (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.1)) <$> countBoth oa = countCalls oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countCalls_bind, countBoth_query, countCalls_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [← ih a, Functor.map_map]

/-- The joint counter projects to `countBlocks`. -/
theorem countBoth_blocks (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.2)) <$> countBoth oa = countBlocks oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countBlocks, countWith_bind, countBoth_query, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [show countWith Query.blocks (oa a) = countBlocks (oa a) from rfl, ← ih a, Functor.map_map]

@[simp] theorem fst_countBoth (oa : OracleComp HashSpec α) : Prod.fst <$> countBoth oa = oa := by
  have := congrArg (fun x => Prod.fst <$> x) (countBoth_calls oa)
  simp only [Functor.map_map] at this
  rw [this, fst_countCalls]

end count

/-! ## `Sim`: bounded refinement -/

/-- An outcome of a machine segment: spec value, calls, blocks, steps (fuel), cycles, state. -/
structure Out (α : Type) where
  val : α
  calls : Nat
  blocks : Nat
  steps : Nat
  cycles : Nat
  st : MachineState

/-- Admissible outcomes: steps ≤ cycles ≤ W and the postcondition. -/
def Out.Good {α : Type} (W : Nat) (Q : α → MachineState → Prop) (o : Out α) : Prop :=
  o.steps ≤ o.cycles ∧ o.cycles ≤ W ∧ Q o.val o.st

/-- `Sim image s W oa Q`: running the machine from `s` performs exactly the oracle queries of
`oa` (query for query) and reaches a state `t` with `Q a t` (`a` the value of `oa`), at most `W`
cycles (and steps). There is a computation `oc` over the outcomes whose projection to
`(value, calls, blocks)` is `countBoth oa`, and for every `fuel ≥ W`, `execute fuel image s` is `oc`
followed by the rest of the execution charged with the outcome's costs. -/
def Sim {α : Type} (image : Image) (s : MachineState) (W : Nat) (oa : OracleComp HashSpec α)
    (Q : α → MachineState → Prop) : Prop :=
  ∃ oc : OracleComp HashSpec {o : Out α // o.Good W Q},
    (fun o => (o.1.val, o.1.calls, o.1.blocks)) <$> oc = countBoth oa ∧
    ∀ fuel, W ≤ fuel → Riscv.execute fuel image s =
      oc >>= fun o => (fun r => r.charge o.1.cycles o.1.calls o.1.blocks) <$>
        Riscv.execute (fuel - o.1.steps) image o.1.st

theorem steps_le_cycles {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) : k ≤ c := by
  induction h with
  | refl => exact le_refl _
  | @step s t u i k c _ _ _ ih =>
    have : 1 ≤ instructionCycles i := by
      unfold instructionCycles; split <;> omega
    omega

section sim
variable {α β : Type} {image : Image}

theorem Sim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : Sim image s c (pure a) Q := by
  refine ⟨pure ⟨⟨a, 0, 0, k, c, t⟩, steps_le_cycles h, le_refl _, hQ⟩, rfl, ?_⟩
  intro fuel hf
  rw [pure_bind, h.execute_le (le_trans (steps_le_cycles h) hf)]

theorem Sim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    Sim image s 0 (pure a) Q :=
  Sim.pure_steps (Steps.refl s) hQ

theorem Sim.mono {s : MachineState} {W W' : Nat} {oa : OracleComp HashSpec α}
    {Q Q' : α → MachineState → Prop} (h : Sim image s W oa Q) (hW : W ≤ W')
    (hQ : ∀ a t, Q a t → Q' a t) : Sim image s W' oa Q' := by
  obtain ⟨oc, hp, hf⟩ := h
  refine ⟨(fun o => ⟨o.1, o.2.1, le_trans o.2.2.1 hW, hQ _ _ o.2.2.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact hp
  · intro fuel hfuel
    rw [hf fuel (le_trans hW hfuel), bind_map_left]

theorem Sim.of_eq {s : MachineState} {W : Nat} {oa ob : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Sim image s W oa Q) (he : oa = ob) : Sim image s W ob Q :=
  he ▸ h

theorem Sim.bind {s : MachineState} {W₁ W₂ : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} {Q₁ : α → MachineState → Prop}
    {Q₂ : β → MachineState → Prop} (h₁ : Sim image s W₁ oa Q₁)
    (h₂ : ∀ a t, Q₁ a t → Sim image t W₂ (f a) Q₂) : Sim image s (W₁ + W₂) (oa >>= f) Q₂ := by
  classical
  obtain ⟨oc₁, hp₁, hf₁⟩ := h₁
  have h₂' : ∀ o : {o : Out α // o.Good W₁ Q₁}, Sim image o.1.st W₂ (f o.1.val) Q₂ :=
    fun o => h₂ _ _ o.2.2.2
  let oc₂ := fun o => Classical.choose (h₂' o)
  have hp₂ := fun o => (Classical.choose_spec (h₂' o)).1
  have hf₂ := fun o => (Classical.choose_spec (h₂' o)).2
  let comb : (o₁ : {o : Out α // o.Good W₁ Q₁}) → {o : Out β // o.Good W₂ Q₂} →
      {o : Out β // o.Good (W₁ + W₂) Q₂} := fun o₁ o₂ =>
    ⟨⟨o₂.1.val, o₁.1.calls + o₂.1.calls, o₁.1.blocks + o₂.1.blocks, o₁.1.steps + o₂.1.steps,
      o₁.1.cycles + o₂.1.cycles, o₂.1.st⟩,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega, o₂.2.2.2⟩
  refine ⟨oc₁ >>= fun o₁ => comb o₁ <$> oc₂ o₁, ?_, ?_⟩
  · rw [countBoth_bind, ← hp₁, map_bind, bind_map_left]
    congr 1; funext o₁
    rw [← hp₂ o₁, Functor.map_map, Functor.map_map]
  · intro fuel hfuel
    rw [hf₁ fuel (le_trans (Nat.le_add_right _ _) hfuel), bind_assoc]
    congr 1; funext o₁
    have hs : o₁.1.steps ≤ W₁ := le_trans o₁.2.1 o₁.2.2.1
    rw [hf₂ o₁ (fuel - o₁.1.steps) (by omega), map_bind, bind_map_left]
    congr 1; funext o₂
    simp only [Functor.map_map, Execution.charge_charge, comb]
    rw [Nat.sub_sub]

theorem Sim.steps {s t : MachineState} {k c W : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : Sim image t W oa Q) :
    Sim image s (c + W) oa Q := by
  have := Sim.bind (Sim.pure_steps (Q := fun _ t' => t' = t) (a := ()) h rfl)
    (f := fun _ => oa) (fun _ t' ht => ht ▸ h₂)
  simpa using this

/-- One HASH `ECALL`. -/
theorem Sim.query {s : MachineState} {q : Query}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q) :
    Sim image s (8 * q.blocks) (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun a t => t = writeHash s a) := by
  subst hq
  have hb : 1 ≤ (hashInput s).blocks := by unfold Query.blocks; omega
  refine ⟨(fun a => ⟨⟨a, 1, (hashInput s).blocks, 1, 8 * (hashInput s).blocks, writeHash s a⟩,
      by show 1 ≤ 8 * _; omega, le_refl _, rfl⟩) <$> (liftM (HashSpec.query (hashInput s)) : OracleComp HashSpec _),
      ?_, ?_⟩
  · rw [Functor.map_map, countBoth_query]
  · intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [execute_hash f hf ht0 hv, bind_map_left]
    rfl

theorem Sim.query_bind {s : MachineState} {q : Query} {W : Nat}
    {f : BitVec 256 → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q)
    (h : ∀ a, Sim image (writeHash s a) W (f a) Q) :
    Sim image s (8 * q.blocks + W) ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= f) Q :=
  Sim.bind (Sim.query hf ht0 hv hq) (fun a _ ht => ht ▸ h a)

theorem Sim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (W₂ := W) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    refine this.mono ?_ (fun _ _ h => h)
    rw [Nat.succ_mul]

theorem Sim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc j) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range n).foldlM f init) (Inv n) := by
  have := Sim.foldlM_range' 0 n f init Inv W (fun j hj acc t h => by simpa using hbody j hj acc t h) h0
  rwa [List.range_eq_range']

end sim

/-! ## Whole phases (bounded) -/

section run
variable {α : Type}

/-- **Refinement of a whole phase.** -/
theorem Sim.run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧
      F a = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout phase t)
        else none) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit, hf CYCLE_LIMIT (le_of_lt hW), ← hp,
    Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1; funext o
  obtain ⟨h1, h2, h3⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := lt_of_le_of_lt (le_trans o.2.1 o.2.2.1) hW
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', execute_halt f h1 h2]
  simp only [map_pure, Function.comp, toRunResult, Execution.charge, h3]
  congr 2
  split <;> simp_all

/-- **Termination of a whole phase** under every fixed oracle: finished, and at most `W + 1`
cycles (`W + 1 < CYCLE_LIMIT`). -/
theorem Sim.runWith (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W + 1 < CYCLE_LIMIT)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧ t.getReg .x5 = 1)
    (hash : Hash) :
    (submission.runWith hash phase input).finished = true ∧
      (submission.runWith hash phase input).cycles ≤ W + 1 := by
  obtain ⟨oc, _, hf⟩ := hsim
  rw [runWith_eq submission hash phase input s hinit, hf CYCLE_LIMIT (by omega),
    evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨h1, h2⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := by have := o.2.1; have := o.2.2.1; omega
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', evalWith_halt hash f h1 h2]
  have := o.2.2.1
  simp only [toRunResult, Execution.charge]
  constructor
  · split <;> rfl
  · omega

end run

/-! ## `XSim`: exact refinement -/

/-- `XSim image s k c n b oa Q` : from `s` the machine performs exactly the oracle queries of
`oa`, in exactly `k` steps (fuel) and `c` cycles, with exactly `n` HASH calls and `b`
compressions, independently of the answers; the final state `t` satisfies `Q a t`. -/
def XSim {α : Type} (image : Image) (s : MachineState) (k c n b : Nat)
    (oa : OracleComp HashSpec α) (Q : α → MachineState → Prop) : Prop :=
  ∃ oc : OracleComp HashSpec {p : α × MachineState // Q p.1 p.2},
    (fun p => (p.1.1, n, b)) <$> oc = countBoth oa ∧
    ∀ fuel, Riscv.execute (fuel + k) image s =
      oc >>= fun p => (fun r => r.charge c n b) <$> Riscv.execute fuel image p.1.2

section
variable {α β : Type} {image : Image}

theorem XSim.val {n b : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} {oc : OracleComp HashSpec {p : α × MachineState // Q p.1 p.2}}
    (h : (fun p => (p.1.1, n, b)) <$> oc = countBoth oa) :
    (fun p => p.1.1) <$> oc = oa := by
  have := congrArg (fun x => Prod.fst <$> x) h
  simp only [Functor.map_map, fst_countBoth] at this
  exact this

theorem XSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : XSim image s k c 0 0 (pure a) Q := by
  refine ⟨pure ⟨(a, t), hQ⟩, rfl, ?_⟩
  intro fuel
  rw [pure_bind, h.execute]

theorem XSim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    XSim image s 0 0 0 0 (pure a) Q :=
  XSim.pure_steps (Steps.refl s) hQ

theorem XSim.mono {s : MachineState} {k c n b : Nat} {oa : OracleComp HashSpec α}
    {Q Q' : α → MachineState → Prop} (h : XSim image s k c n b oa Q)
    (hQ : ∀ a t, Q a t → Q' a t) : XSim image s k c n b oa Q' := by
  obtain ⟨oc, h1, h3⟩ := h
  refine ⟨(fun p => ⟨p.1, hQ _ _ p.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact h1
  · intro fuel; rw [h3 fuel, bind_map_left]

theorem XSim.of_eq {s : MachineState} {k c n b k' c' n' b' : Nat} {oa ob : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) (he : oa = ob)
    (hk : k = k') (hc : c = c') (hn : n = n') (hb : b = b') : XSim image s k' c' n' b' ob Q := by
  subst he hk hc hn hb; exact h

private theorem count_bind_aux {P₁ : α × MachineState → Prop}
    {P₂ : β × MachineState → Prop} (oc₁ : OracleComp HashSpec {p // P₁ p})
    (oc₂ : {p // P₁ p} → OracleComp HashSpec {q // P₂ q}) (f : α → OracleComp HashSpec β)
    (n₁ b₁ n₂ b₂ : Nat) (oa : OracleComp HashSpec α)
    (h₁ : (fun p => (p.1.1, n₁, b₁)) <$> oc₁ = countBoth oa)
    (h₂ : ∀ p, (fun q => (q.1.1, n₂, b₂)) <$> oc₂ p = countBoth (f p.1.1)) :
    (fun q => (q.1.1, n₁ + n₂, b₁ + b₂)) <$> (oc₁ >>= oc₂) = countBoth (oa >>= f) := by
  rw [countBoth_bind, ← h₁, bind_map_left, map_bind]
  congr 1; funext p
  rw [← h₂ p, Functor.map_map]

theorem XSim.bind {s : MachineState} {k₁ c₁ n₁ b₁ k₂ c₂ n₂ b₂ : Nat}
    {oa : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    {Q₁ : α → MachineState → Prop} {Q₂ : β → MachineState → Prop}
    (h₁ : XSim image s k₁ c₁ n₁ b₁ oa Q₁)
    (h₂ : ∀ a t, Q₁ a t → XSim image t k₂ c₂ n₂ b₂ (f a) Q₂) :
    XSim image s (k₁ + k₂) (c₁ + c₂) (n₁ + n₂) (b₁ + b₂) (oa >>= f) Q₂ := by
  classical
  obtain ⟨oc₁, hc₁, he₁⟩ := h₁
  have h₂' : ∀ p : {p : α × MachineState // Q₁ p.1 p.2}, XSim image p.1.2 k₂ c₂ n₂ b₂ (f p.1.1) Q₂ :=
    fun p => h₂ _ _ p.2
  let oc₂ := fun p => Classical.choose (h₂' p)
  have spec := fun p => Classical.choose_spec (h₂' p)
  refine ⟨oc₁ >>= oc₂, count_bind_aux oc₁ oc₂ f n₁ b₁ n₂ b₂ oa hc₁ (fun p => (spec p).1), ?_⟩
  intro fuel
  rw [show fuel + (k₁ + k₂) = (fuel + k₂) + k₁ by omega, he₁, bind_assoc]
  congr 1; funext p
  rw [(spec p).2 fuel, map_bind]
  congr 1; funext q
  rw [Functor.map_map]
  congr 1; funext r
  rw [Execution.charge_charge]

theorem XSim.steps {s t : MachineState} {k c k' c' n b : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : XSim image t k' c' n b oa Q) :
    XSim image s (k + k') (c + c') n b oa Q := by
  have := XSim.bind (XSim.pure_steps (Q := fun _ t' => t' = t) (a := ()) h rfl)
    (f := fun _ => oa) (fun _ t' ht => ht ▸ h₂)
  simpa using this

/-- One HASH `ECALL`. -/
theorem XSim.query {s : MachineState} {q : Query}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q) :
    XSim image s 1 (8 * q.blocks) 1 q.blocks (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun a t => t = writeHash s a) := by
  subst hq
  refine ⟨(fun a => ⟨(a, writeHash s a), rfl⟩) <$>
      (liftM (HashSpec.query (hashInput s)) : OracleComp HashSpec _), ?_, ?_⟩
  · rw [Functor.map_map, countBoth_query]
  · intro fuel
    rw [execute_hash fuel hf ht0 hv, bind_map_left]

/-- One HASH `ECALL` followed by a continuation. -/
theorem XSim.query_bind {s : MachineState} {q : Query} {k c n b : Nat}
    {f : BitVec 256 → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q)
    (h : ∀ a, XSim image (writeHash s a) k c n b (f a) Q) :
    XSim image s (1 + k) (8 * q.blocks + c) (1 + n) (q.blocks + b)
      ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= f) Q :=
  XSim.bind (XSim.query hf ht0 hv hq) (fun a _ ht => ht ▸ h a)

/-- Sum `f 0 + … + f (n-1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_const (c n : Nat) : sumTo (fun _ => c) n = n * c := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [sumTo, ih, Nat.succ_mul]

theorem sumTo_congr (f g : Nat → Nat) (n : Nat) (h : ∀ j < n, f j = g j) : sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- Loop over `List.range' a n` with an invariant indexed by the number `j` of processed
elements and iteration costs depending on `j`. -/
theorem XSim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → XSim image t (K j) (C j) (N j) (B j) (f acc (a + j))
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    XSim image s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa [sumTo] using XSim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := XSim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    exact this

theorem XSim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → XSim image t (K j) (C j) (N j) (B j) (f acc j)
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    XSim image s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range n).foldlM f init) (Inv n) := by
  have := XSim.foldlM_range' 0 n f init Inv K C N B (fun j hj acc t h => by
    simpa using hbody j hj acc t h) h0
  rwa [List.range_eq_range']

/-- `mapM` over a list, with an invariant on the results so far (`pre ++ results`). -/
theorem XSim.mapM_list {γ δ : Type} (f : γ → OracleComp HashSpec δ) (K C N B : γ → Nat)
    (Inv : List δ → MachineState → Prop) :
    ∀ (xs : List γ) (pre : List δ) {s : MachineState},
    (∀ x ∈ xs, ∀ (pre' : List δ) t, Inv pre' t →
      XSim image t (K x) (C x) (N x) (B x) (f x) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s →
    XSim image s (xs.map K).sum (xs.map C).sum (xs.map N).sum (xs.map B).sum (xs.mapM f)
      (fun ds u => Inv (pre ++ ds) u)
  | [], pre, s, _, h0 => by simpa using XSim.pure (image := image) (Q := fun ds u => Inv (pre ++ ds) u) (a := []) (by simpa using h0)
  | x :: xs, pre, s, hb, h0 => by
    rw [List.mapM_cons]
    have h1 := hb x (by simp) pre s h0
    have key : ∀ d t, Inv (pre ++ [d]) t → XSim image t (xs.map K).sum (xs.map C).sum
        (xs.map N).sum (xs.map B).sum (do let ds ← xs.mapM f; Pure.pure (d :: ds))
        (fun ds u => Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := XSim.mapM_list f K C N B Inv xs (pre ++ [d]) (fun y hy => hb y (by simp [hy])) ht
      refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => XSim.pure (by simpa using hu))).of_eq rfl (by simp) (by simp) (by simp) (by simp)
    exact (XSim.bind h1 key).of_eq rfl (by simp) (by simp) (by simp) (by simp)

theorem sumTo_succ_left (f : Nat → Nat) (n : Nat) : sumTo f (n + 1) = f 0 + sumTo (fun j => f (j + 1)) n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo, ih, sumTo]; omega

/-- `mapM` over `List.range' a n` whose body depends on the position: the invariant is indexed by
the results so far (`pre`, of length `a + j` after `j` elements). -/
theorem XSim.mapM_range' {δ : Type} (f : Nat → OracleComp HashSpec δ) (K C N B : Nat → Nat)
    (Inv : List δ → MachineState → Prop) :
    ∀ (n a : Nat) (pre : List δ) {s : MachineState}, pre.length = a →
    (∀ (pre' : List δ) t, a ≤ pre'.length → pre'.length < a + n → Inv pre' t →
      XSim image t (K pre'.length) (C pre'.length) (N pre'.length) (B pre'.length) (f pre'.length)
        (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s →
    XSim image s (sumTo (fun j => K (a + j)) n) (sumTo (fun j => C (a + j)) n)
      (sumTo (fun j => N (a + j)) n) (sumTo (fun j => B (a + j)) n) ((List.range' a n).mapM f)
      (fun ds u => ds.length = n ∧ Inv (pre ++ ds) u)
  | 0, a, pre, s, _, _, h0 => by
    simpa [sumTo] using XSim.pure (image := image) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | n + 1, a, pre, s, hlen, hb, h0 => by
    rw [List.range'_succ, List.mapM_cons]
    have h1 := hb pre s (by omega) (by omega) h0
    rw [hlen] at h1
    have key : ∀ d t, Inv (pre ++ [d]) t → XSim image t (sumTo (fun j => K (a + 1 + j)) n)
        (sumTo (fun j => C (a + 1 + j)) n) (sumTo (fun j => N (a + 1 + j)) n)
        (sumTo (fun j => B (a + 1 + j)) n) (do let ds ← (List.range' (a + 1) n).mapM f; Pure.pure (d :: ds))
        (fun ds u => ds.length = n + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := XSim.mapM_range' f K C N B Inv n (a + 1) (pre ++ [d]) (by simp [hlen])
        (fun pre' t' h1' h2' => hb pre' t' (by omega) (by omega)) ht
      refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => XSim.pure ⟨by simp [hu.1], by simpa using hu.2⟩)).of_eq rfl (by simp) (by simp)
        (by simp) (by simp)
    refine (XSim.bind h1 key).of_eq rfl ?_ ?_ ?_ ?_ <;>
      (rw [sumTo_succ_left]; simp only [Nat.add_zero]; congr 1; apply sumTo_congr; intro j _; congr 1; omega)

/-- The counts of a refined computation are constant. -/
theorem XSim.countBoth_eq {s : MachineState} {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) :
    countBoth oa = (fun a => (a, n, b)) <$> oa := by
  obtain ⟨oc, hc, _⟩ := h
  rw [← hc, ← XSim.val hc, Functor.map_map]

/-- An exact refinement is a bounded one (`k ≤ c`: every step costs at least one cycle). -/
theorem XSim.toSim {s : MachineState} {k c n b : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) (hkc : k ≤ c) :
    Sim image s c oa Q := by
  obtain ⟨oc, hc, he⟩ := h
  refine ⟨(fun p => ⟨⟨p.1.1, n, b, k, c, p.1.2⟩, hkc, le_refl _, p.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact hc
  · intro fuel hf
    have := he (fuel - k)
    rw [Nat.sub_add_cancel (le_trans hkc hf)] at this
    rw [this, bind_map_left]

end

/-! ## Whole phases (exact) -/

/-- **A whole phase, exactly.** -/
theorem XSim.run_eq {α : Type} (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : XSim (submission.image phase) s k c n b oa Q) (hk : k < CYCLE_LIMIT)
    (F : α → Output submission.sizes phase)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      readOutput submission.sizes submission.layout phase t = F a) :
    submission.run phase input = (fun a => ⟨some (F a), true, c + 1, n, b⟩) <$> oa := by
  obtain ⟨oc, hc, he⟩ := hsim
  have e1 := he (CYCLE_LIMIT - k - 1 + 1)
  rw [show CYCLE_LIMIT - k - 1 + 1 + k = CYCLE_LIMIT by omega] at e1
  rw [Rv.run_eq submission phase input s hinit, e1, map_bind, ← XSim.val hc,
    Functor.map_map, map_eq_bind_pure_comp]
  refine congrArg (oc >>= ·) (funext fun p => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hQ _ _ p.2
  rw [execute_halt _ h1 h2, map_pure, map_pure]
  simp only [Function.comp, toRunResult, Execution.charge, h3, if_true, h4]
  rfl

/-! ## Core programs on the machine -/

/-- Core's queries as organizer queries: public inputs relabeled by `toQ`, private coordinates
realized by the secret first (`privateInput`). Coins never occur in Core's hash-only programs
(their answer here is an arbitrary constant). -/
def machineHandler (sk : BitVec 256) : QueryImpl Spec (OracleComp HashSpec)
  | .inl (.inl n) => (Pure.pure (0 : Fin (n + 1)) : OracleComp HashSpec (Fin (n + 1)))
  | .inl (.inr input) => (HashSpec.query (toQ input) : OracleComp HashSpec _)
  | .inr c => (HashSpec.query (toQ (privateInput sk c)) : OracleComp HashSpec _)

/-- The machine-facing reference of a Core program. -/
def mrealize {α : Type} (sk : BitVec 256) (p : M α) : OracleComp HashSpec α :=
  simulateQ (machineHandler sk) p

section mrealize
variable {α β : Type} (sk : BitVec 256)

@[simp] theorem mrealize_pure (a : α) : mrealize sk (Pure.pure a : M α) = Pure.pure a := rfl

theorem mrealize_bind (p : M α) (f : α → M β) :
    mrealize sk (p >>= f) = mrealize sk p >>= fun a => mrealize sk (f a) := by
  unfold mrealize; rw [simulateQ_bind]

theorem mrealize_map (f : α → β) (p : M α) : mrealize sk (f <$> p) = f <$> mrealize sk p := by
  unfold mrealize; rw [simulateQ_map]

theorem mrealize_publicHash (input : List UInt8) :
    mrealize sk (publicHash input) =
      (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _) := by
  unfold mrealize publicHash
  exact simulateQ_spec_query _ _

theorem mrealize_privateHash (c : Coordinate) :
    mrealize sk (privateHash c) =
      (liftM (HashSpec.query (toQ (privateInput sk c))) : OracleComp HashSpec _) := by
  unfold mrealize privateHash
  exact simulateQ_spec_query _ _

theorem mrealize_shortHash (input : List UInt8) :
    mrealize sk (shortHash input) = (fun a : BitVec 256 => a.extractLsb' 0 128) <$>
      (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _) := by
  unfold shortHash
  rw [mrealize_bind, mrealize_publicHash]
  simp only [mrealize_pure, bind_pure_comp]

theorem mrealize_privatePair (tag lay tree position index : Nat) :
    mrealize sk (privatePair tag lay tree position index) =
      (fun a : BitVec 256 => (a.extractLsb' 0 128, a.extractLsb' 128 128)) <$>
        (liftM (HashSpec.query (toQ (privateInput sk (.inl (header tag lay tree position index)))))
          : OracleComp HashSpec _) := by
  unfold privatePair
  rw [mrealize_bind, mrealize_privateHash]
  simp only [mrealize_pure, bind_pure_comp]

theorem mrealize_mask (level index : Nat) :
    mrealize sk (mask level index) = (fun a : BitVec 256 => a.extractLsb' 0 128) <$>
      (liftM (HashSpec.query (toQ (privateInput sk (.inl (header 13 0 0 level index)))))
        : OracleComp HashSpec _) := by
  unfold mask
  rw [mrealize_bind, mrealize_privatePair]
  simp only [mrealize_pure, bind_pure_comp, Functor.map_map]

theorem mrealize_privateMac (region : Region) :
    mrealize sk (privateMac region) =
      (liftM (HashSpec.query (toQ (privateInput sk (.inr (.inr region))))) : OracleComp HashSpec _) :=
  mrealize_privateHash sk _

theorem mrealize_privateNonce (m : T3.Message) :
    mrealize sk (privateNonce m) = (fun a : BitVec 256 => a.extractLsb' 0 128) <$>
      (liftM (HashSpec.query (toQ (privateInput sk (.inr (.inl m))))) : OracleComp HashSpec _) := by
  unfold privateNonce
  rw [mrealize_bind, mrealize_privateHash]
  simp only [mrealize_pure, bind_pure_comp]

theorem mrealize_foldlM {γ δ : Type} (l : List δ) (f : γ → δ → M γ) (init : γ) :
    mrealize sk (l.foldlM f init) = l.foldlM (fun acc x => mrealize sk (f acc x)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih => simp only [List.foldlM_cons, mrealize_bind, ih]

theorem mrealize_mapM {γ δ : Type} (l : List γ) (f : γ → M δ) :
    mrealize sk (l.mapM f) = l.mapM (fun x => mrealize sk (f x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.mapM_cons, mrealize_bind, ih, mrealize_pure]

end mrealize

/-! ## `TSim` and `TBSim`: machine runs of Core programs -/

/-- Exact refinement of a Core program (realized with the secret `sk`). -/
def TSim {α : Type} (image : Image) (sk : BitVec 256) (s : MachineState) (k c n b : Nat) (p : M α)
    (Q : α → MachineState → Prop) : Prop :=
  XSim image s k c n b (mrealize sk p) Q

/-- Bounded refinement of a Core program. -/
def TBSim {α : Type} (image : Image) (sk : BitVec 256) (s : MachineState) (W : Nat) (p : M α)
    (Q : α → MachineState → Prop) : Prop :=
  Sim image s W (mrealize sk p) Q

section tsim
variable {α β : Type} {image : Image} {sk : BitVec 256}

theorem TSim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    TSim image sk s 0 0 0 0 (Pure.pure a) Q := XSim.pure hQ

theorem TSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TSim image sk s k c 0 0 (Pure.pure a) Q :=
  XSim.pure_steps h hQ

theorem TSim.mono {s : MachineState} {k c n b : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TSim image sk s k c n b p Q) (hQ : ∀ a t, Q a t → Q' a t) : TSim image sk s k c n b p Q' :=
  XSim.mono h hQ

theorem TSim.of_eq {s : MachineState} {k c n b k' c' n' b' : Nat} {p q : M α}
    {Q : α → MachineState → Prop} (h : TSim image sk s k c n b p Q) (he : p = q)
    (hk : k = k') (hc : c = c') (hn : n = n') (hb : b = b') : TSim image sk s k' c' n' b' q Q := by
  subst he hk hc hn hb; exact h

theorem TSim.bind {s : MachineState} {k₁ c₁ n₁ b₁ k₂ c₂ n₂ b₂ : Nat} {p : M α} {f : α → M β}
    {Q₁ : α → MachineState → Prop} {Q₂ : β → MachineState → Prop}
    (h₁ : TSim image sk s k₁ c₁ n₁ b₁ p Q₁)
    (h₂ : ∀ a t, Q₁ a t → TSim image sk t k₂ c₂ n₂ b₂ (f a) Q₂) :
    TSim image sk s (k₁ + k₂) (c₁ + c₂) (n₁ + n₂) (b₁ + b₂) (p >>= f) Q₂ := by
  unfold TSim; rw [mrealize_bind]; exact XSim.bind h₁ h₂

theorem TSim.steps {s t : MachineState} {k c k' c' n b : Nat} {p : M α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : TSim image sk t k' c' n b p Q) :
    TSim image sk s (k + k') (c + c') n b p Q := XSim.steps h h₂

theorem TSim.map {s : MachineState} {k c n b : Nat} {p : M α} (f : α → β)
    {Q : β → MachineState → Prop} (h : TSim image sk s k c n b p (fun a t => Q (f a) t)) :
    TSim image sk s k c n b (f <$> p) Q := by
  rw [map_eq_bind_pure_comp]
  exact (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) h (fun a t ht => TSim.pure ht)).of_eq rfl
    rfl rfl rfl rfl

/-- One HASH `ECALL` answering a public query `publicHash input`. -/
theorem TSim.publicHash_bind {s : MachineState} {input : List UInt8} {k c n b : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TSim image sk (writeHash s a) k c n b (f a) Q) :
    TSim image sk s (1 + k) (8 * (toQ (pad64 input)).blocks + c) (1 + n) ((toQ (pad64 input)).blocks + b)
      (publicHash input >>= f) Q := by
  unfold TSim; rw [mrealize_bind, mrealize_publicHash]
  exact XSim.query_bind hf ht0 hv hq h

/-- One HASH `ECALL` answering `shortHash input` (the low 16 bytes). -/
theorem TSim.shortHash_bind {s : MachineState} {input : List UInt8} {k c n b : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b (f (a.extractLsb' 0 128)) Q) :
    TSim image sk s (1 + k) (8 * (toQ (pad64 input)).blocks + c) (1 + n) ((toQ (pad64 input)).blocks + b)
      (shortHash input >>= f) Q := by
  unfold TSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine XSim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TSim at this
  simpa only [Function.comp, pure_bind] using this

/-- One HASH `ECALL` answering a private coordinate. -/
theorem TSim.privateHash_bind {s : MachineState} {co : Coordinate} {k c n b : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TSim image sk (writeHash s a) k c n b (f a) Q) :
    TSim image sk s (1 + k) (8 * (toQ (privateInput sk co)).blocks + c) (1 + n)
      ((toQ (privateInput sk co)).blocks + b) (privateHash co >>= f) Q := by
  unfold TSim; rw [mrealize_bind, mrealize_privateHash]
  exact XSim.query_bind hf ht0 hv hq h

/-- One HASH `ECALL` answering `privatePair` (both 16-byte halves). -/
theorem TSim.privatePair_bind {s : MachineState} {tag lay tree position index : Nat} {k c n b : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TSim image sk s (1 + k) (8 + c) (1 + n) (1 + b) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  unfold TSim; rw [mrealize_bind, mrealize_privatePair, map_eq_bind_pure_comp, bind_assoc]
  refine (XSim.query_bind hf ht0 hv hq (fun a => ?_)).of_eq rfl rfl (by rw [hb]) rfl (by rw [hb])
  have := h a
  unfold TSim at this
  simpa only [Function.comp, pure_bind] using this

/-- One HASH `ECALL` answering `mask level index` (the low half of a tag-13 pair). -/
theorem TSim.mask_bind {s : MachineState} {level index : Nat} {k c n b : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header 13 0 0 level index))))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b (f (a.extractLsb' 0 128)) Q) :
    TSim image sk s (1 + k) (8 + c) (1 + n) (1 + b) (mask level index >>= f) Q := by
  have : mask level index >>= f = privatePair 13 0 0 level index >>= fun x => f x.1 := by
    unfold mask; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TSim.privatePair_bind hf ht0 hv hq h

/-- One HASH `ECALL` answering the 513-block MAC. -/
theorem TSim.privateMac_bind {s : MachineState} {region : Region} {k c n b : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inr region))))
    (h : ∀ a, TSim image sk (writeHash s a) k c n b (f a) Q) :
    TSim image sk s (1 + k) (8 * 513 + c) (1 + n) (513 + b) (privateMac region >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inr region)))).blocks = 513 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_mac_length]
  refine (TSim.privateHash_bind hf ht0 hv hq h).of_eq rfl rfl (by rw [hb]) rfl (by rw [hb])

/-- One HASH `ECALL` answering the nonce (`privateNonce`, the low 16 bytes). -/
theorem TSim.privateNonce_bind {s : MachineState} {m : T3.Message} {k c n b : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inl m))))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b (f (a.extractLsb' 0 128)) Q) :
    TSim image sk s (1 + k) (8 * (toQ (privateInput sk (.inr (.inl m)))).blocks + c) (1 + n)
      ((toQ (privateInput sk (.inr (.inl m)))).blocks + b) (privateNonce m >>= f) Q := by
  have : privateNonce m >>= f = privateHash (.inr (.inl m)) >>= fun a => f (a.extractLsb' 0 128) := by
    unfold privateNonce; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TSim.privateHash_bind hf ht0 hv hq h

theorem TSim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → M γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → TSim image sk t (K j) (C j) (N j) (B j) (f acc (a + j))
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TSim image sk s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range' a n).foldlM f init) (Inv n) := by
  unfold TSim; rw [mrealize_foldlM]
  exact XSim.foldlM_range' a n (fun acc x => mrealize sk (f acc x)) init Inv K C N B hbody h0

theorem TSim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → M γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → TSim image sk t (K j) (C j) (N j) (B j) (f acc j)
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TSim image sk s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range n).foldlM f init) (Inv n) := by
  unfold TSim; rw [mrealize_foldlM]
  exact XSim.foldlM_range n (fun acc x => mrealize sk (f acc x)) init Inv K C N B hbody h0

theorem TSim.mapM_list {γ δ : Type} (f : γ → M δ) (K C N B : γ → Nat)
    (Inv : List δ → MachineState → Prop) (xs : List γ) (pre : List δ) {s : MachineState}
    (hbody : ∀ x ∈ xs, ∀ (pre' : List δ) t, Inv pre' t →
      TSim image sk t (K x) (C x) (N x) (B x) (f x) (fun d u => Inv (pre' ++ [d]) u))
    (h0 : Inv pre s) :
    TSim image sk s (xs.map K).sum (xs.map C).sum (xs.map N).sum (xs.map B).sum (xs.mapM f)
      (fun ds u => Inv (pre ++ ds) u) := by
  unfold TSim; rw [mrealize_mapM]
  exact XSim.mapM_list (fun x => mrealize sk (f x)) K C N B Inv xs pre hbody h0

theorem TSim.mapM_range {δ : Type} (n : Nat) (f : Nat → M δ) (K C N B : Nat → Nat)
    (Inv : List δ → MachineState → Prop) {s : MachineState}
    (hbody : ∀ (pre : List δ) t, pre.length < n → Inv pre t →
      TSim image sk t (K pre.length) (C pre.length) (N pre.length) (B pre.length) (f pre.length)
        (fun d u => Inv (pre ++ [d]) u))
    (h0 : Inv [] s) :
    TSim image sk s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n) ((List.range n).mapM f)
      (fun ds u => ds.length = n ∧ Inv ds u) := by
  unfold TSim; rw [mrealize_mapM, List.range_eq_range']
  have := XSim.mapM_range' (image := image) (fun x => mrealize sk (f x)) K C N B Inv n 0 [] rfl
    (fun pre' t _ h2 h3 => hbody pre' t (by omega) h3) h0
  simpa using this

theorem TSim.toTBSim {s : MachineState} {k c n b : Nat} {p : M α} {Q : α → MachineState → Prop}
    (h : TSim image sk s k c n b p Q) (hkc : k ≤ c) : TBSim image sk s c p Q := XSim.toSim h hkc

/-! Bounded combinators. -/

theorem TBSim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    TBSim image sk s 0 (Pure.pure a) Q := Sim.pure hQ

theorem TBSim.mono {s : MachineState} {W W' : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (hW : W ≤ W') (hQ : ∀ a t, Q a t → Q' a t) :
    TBSim image sk s W' p Q' := Sim.mono h hW hQ

theorem TBSim.bind {s : MachineState} {W₁ W₂ : Nat} {p : M α} {f : α → M β}
    {Q₁ : α → MachineState → Prop} {Q₂ : β → MachineState → Prop}
    (h₁ : TBSim image sk s W₁ p Q₁) (h₂ : ∀ a t, Q₁ a t → TBSim image sk t W₂ (f a) Q₂) :
    TBSim image sk s (W₁ + W₂) (p >>= f) Q₂ := by
  unfold TBSim; rw [mrealize_bind]; exact Sim.bind h₁ h₂

theorem TBSim.steps {s t : MachineState} {k c W : Nat} {p : M α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (h₂ : TBSim image sk t W p Q) : TBSim image sk s (c + W) p Q :=
  Sim.steps h h₂

theorem TBSim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → M γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → TBSim image sk t W (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (n * W) ((List.range' a n).foldlM f init) (Inv n) := by
  unfold TBSim; rw [mrealize_foldlM]
  exact Sim.foldlM_range' a n (fun acc x => mrealize sk (f acc x)) init Inv W hbody h0

end tsim

end SigGolfCandidate.T3M
