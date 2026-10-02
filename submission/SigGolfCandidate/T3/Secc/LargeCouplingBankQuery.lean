import SigGolfCandidate.T3.Secc.LargeCouplingBankState

/-!
# LR-34 (bank, one query): an adversary/verifier query is a supermartingale step of the bank

**`bank_routeQuery`**: for a lazy world state and a router state in the bank invariant (`BankInv`), within the
budget, the routed query's expected continuation value is at most `psi q st + slackT q ws` whenever every stop pays at
most its own `slackT` and every continuation `(y, st', ws')` in the invariant pays at most `psi q st' + slackT q ws'`.

* non-digest rows (and inputs outside the universe): one charged request at the row itself (`QFrame`), the bank
  unchanged (`psi_after`);
* a fresh digest row: a uniform answer, a birth (`psi_birth_le`, CC's `core_birth`) paid by one unit of mass
  (`θ + 1/16 ≤ 1`);
* a repeated digest row: its cached answer (or a trial row), one unit of mass, the bank unchanged.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Frame
variable (U : Finset HashInput)

/-- What one charged request at row `X` keeps: the other rows, the mass and the nonce candidate sets (one call). -/
def QFrame (X : HashInput) (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (∀ row : Cell U, row.1 ≠ X → s'.rows row = s.rows row) ∧ s'.counters.calls = s.counters.calls + 1 ∧
    s'.counters.mass = s.counters.mass ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)

theorem QFrame.of_disc {X : HashInput} {s1 s2 s3 : LargeResidual.State WCoord (Cell U)} (h1 : DiscFrame U s1 s2)
    (h2 : QFrame U X s2 s3) : QFrame U X s1 s3 :=
  ⟨fun row hr => (h2.1 row hr).trans (by rw [h1.1]), by rw [h2.2.1, h1.2.1], by rw [h2.2.2.1, h1.2.1],
    fun m => (h2.2.2.2 m).trans (h1.2.2 m)⟩

/-- A probe testing only label/secret coordinates. -/
def InlTest (test : Probe WCoord) : Prop :=
  (∀ g ∈ test.guess, ∃ c : Coord, g.1 = Sum.inl c) ∧ ∀ p, test.hit = .label p → ∃ c : Coord, p = Sum.inl c

theorem restrict_inr (test : Probe WCoord) (htest : InlTest test) (cand : WCoord → Finset Digest)
    (y : LargeResidual.HashOutput) (m : Message) :
    (test.effective cand).restrict cand y (.inr m) = cand (.inr m) := by
  have hg : (test.effective cand).guessRestrict cand (.inr m) = cand (.inr m) := by
    unfold Probe.guessRestrict
    cases hgs : (test.effective cand).guess with
    | none => rfl
    | some g =>
        have hmem : g ∈ test.guess := by
          have : (test.effective cand).guess = test.guess.filter _ := rfl
          rw [this] at hgs
          exact (Option.filter_eq_some_iff.mp hgs).1
        obtain ⟨c, hc⟩ := htest.1 g hmem
        simp only [eraseTableValue]
        rw [Function.update_of_ne (by rw [hc]; simp)]
  unfold Probe.restrict
  have hh : (test.effective cand).hit = test.hit := rfl
  cases hhit : test.hit with
  | label p =>
      obtain ⟨c, hc⟩ := htest.2 p hhit
      rw [hh, hhit]
      simp only [Hit.restrict, eraseTableValue]
      rw [Function.update_of_ne (by rw [hc]; simp), hg]
  | target t =>
      rw [hh, hhit]
      simp only [Hit.restrict]
      exact hg

variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)

theorem ev_lazy_map {α β : Type} (f : α → β) (comp : OracleComp (RWorld U) α) (s : LargeResidual.State WCoord (Cell U))
    (g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal) :
    expectedValue (lazyRun aux q (f <$> comp) s) g = expectedValue (lazyRun aux q comp s) (fun r => g (r.1.map f, r.2)) := by
  rw [lazyRun, runWith_map, expectedValue_map]
  rfl

/-- The outcome bound of one charged request at `X`. -/
def OutcomeLe {α : Type} (X : HashInput) (s : LargeResidual.State WCoord (Cell U))
    (g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal) : Prop :=
  (∀ v s', QFrame U X s s' → g (some v, s') ≤ B) ∧ ∀ s', s'.counters.mass = s.counters.mass → g (none, s') ≤ B

theorem ev_probeReq_le (row : Cell U) (test : Probe WCoord) (htest : InlTest test) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (probeReq U row test) s) g ≤ B := by
  rw [← bind_pure (probeReq U row test)]
  cases hr : s.rows row with
  | some v =>
      rw [lazy_probeReq_cached U aux q row test _ s v hr, lazy_pure, expectedValue_pure]
      apply h.1
      refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
      simp only [readState]
      rw [Function.update_of_ne (fun he => hne (by rw [he]))]
  | none =>
      rw [lazy_probeReq_fresh U aux q row test _ s hr]
      apply ev_observe_le
      · rw [expectedValue_pure]
        exact h.2 _ rfl
      · intro y
        rw [lazy_pure, expectedValue_pure]
        apply h.1
        refine ⟨fun row' hne => ?_, rfl, rfl, fun m => restrict_inr test htest _ y m⟩
        simp only [probeState]
        rw [Function.update_of_ne (fun he => hne (by rw [he]))]

theorem ev_readReq_call_le (row : Cell U) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (readReq U row .call) s) g ≤ B := by
  rw [← bind_pure (readReq U row .call), lazy_readReq]
  apply ev_bind_le
  intro y
  rw [lazy_pure, expectedValue_pure]
  apply h.1
  refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
  simp only [readState]
  rw [Function.update_of_ne (fun he => hne (by rw [he]))]

theorem ev_testReq_le (first : Bool) (row : Cell U) (test : Probe WCoord) (htest : InlTest test)
    (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (testReq U first row test) s) g ≤ B := by
  unfold testReq
  split
  · exact ev_probeReq_le U aux q row test htest s g B h
  · exact ev_readReq_call_le U aux q row s g B h

theorem OutcomeLe.map {α β : Type} {X : HashInput} {s : LargeResidual.State WCoord (Cell U)}
    {g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (f : α → β)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s (fun r => g (r.1.map f, r.2)) B :=
  ⟨fun v s' hs => h.1 (f v) s' hs, fun s' hs => h.2 s' hs⟩

theorem OutcomeLe.of_disc {α : Type} {X : HashInput} {s s1 : LargeResidual.State WCoord (Cell U)}
    {g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (hd : DiscFrame U s s1)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s1 g B :=
  ⟨fun v s' hs => h.1 v s' (QFrame.of_disc U hd hs), fun s' hs => h.2 s' (by rw [hs, hd.2.1])⟩

end Frame

/-! ## The bank invariant under one query -/

section Invariant
variable {U : Finset HashInput}

theorem BankInv.after {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hX : ¬(X ∈ U ∧ IsDigestRow X)) (hf : QFrame U X ws ws') : BankInv U ws' (st.after X) := by
  have hne : ∀ X' (hX' : X' ∈ U), IsDigestRow X' → X' ≠ X := fun X' hX' hd he => hX ⟨he ▸ hX', he ▸ hd⟩
  refine ⟨by rw [hf.2.1, h.calls]; rfl, by rw [hf.2.2.1, hf.2.1]; exact (h.mass).trans (Nat.le_succ _),
    (h.births).trans (Nat.le_succ _), fun m hm => by rw [hf.2.2.2 m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    have hs' : X' ∈ st.seen := by
      rcases List.mem_cons.mp hs with he | hm
      · exact absurd he (hne X' hX' hd)
      · exact hm
    exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)

theorem BankInv.cache_none {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    {X : HashInput} (hs : X ∉ st.seen) : st.cache X = none := by
  unfold RouterState.cache
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  intro he
  exact hs (he ▸ h.bornSeen p hp)

theorem BankInv.born {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st) (q : Nat)
    (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) (hs : X ∉ st.seen) (y : LargeResidual.HashOutput) :
    BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.born X y) := by
  refine ⟨?_, ?_, ?_, fun m hm => h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · simp only [readState, Counters.charge, RouterState.born, RouterState.after, h.calls]
  · simp only [readState, Counters.charge]
    have := h.mass
    split_ifs <;> omega
  · simp only [RouterState.born, RouterState.after, List.length_cons]
    exact Nat.succ_le_succ h.births
  · intro X' hX' hd' hs' ht'
    have hne : X' ≠ X := fun he => hs' (by rw [he]; exact List.mem_cons_self)
    simp only [readState]
    rw [Function.update_of_ne (fun he => hne (congrArg Subtype.val he))]
    exact h.fresh X' hX' hd' (fun hm => hs' (List.mem_cons_of_mem _ hm)) ht'
  · intro X' hX' hd' hs' ht'
    by_cases hxe : X' = X
    · subst hxe
      refine ⟨y, ?_, ?_⟩
      · rw [cache_birth, if_pos rfl]
      · simp only [readState, Function.update_self]
    · have hs2 : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs' with he | hm
        · exact absurd he hxe
        · exact hm
      obtain ⟨v, hv1, hv2⟩ := h.seenRows X' hX' hd' hs2 ht'
      refine ⟨v, ?_, ?_⟩
      · rw [cache_birth, if_neg hxe]; exact hv1
      · simp only [readState]
        rw [Function.update_of_ne (fun he => hxe (congrArg Subtype.val he))]
        exact hv2
  · intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · rw [he]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.bornSeen p hm)

end Invariant

end SigGolfCandidate.T3.Security.LargeCoupling
