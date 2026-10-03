import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessForced
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessErasure
import SigGolfCandidate.ClaudeWCT.GuessV2.WCTCoords

section

namespace ClaudeWCT.Guess
open SphincsSecurity.Concrete.SecretGuessObservation
section Prefix
variable {Chain : Type} {w : ℕ}
def PrefixIn (S : Finset (Chain × Fin w)) (a : Chain) (p : ℕ) : Prop :=
  ∃ q : Fin w, q.val ≤ p ∧ (a, q) ∈ S
theorem PrefixIn.mono_set {S S' : Finset (Chain × Fin w)} {a : Chain} {p : ℕ} (h : S ⊆ S')
    (hp : PrefixIn S a p) : PrefixIn S' a p := by
  obtain ⟨q, hq, hm⟩ := hp
  exact ⟨q, hq, h hm⟩
theorem PrefixIn.mono_pos {S : Finset (Chain × Fin w)} {a : Chain} {p p' : ℕ} (h : p ≤ p')
    (hp : PrefixIn S a p) : PrefixIn S a p' := by
  obtain ⟨q, hq, hm⟩ := hp
  exact ⟨q, hq.trans h, hm⟩
theorem not_prefixIn_empty (a : Chain) (p : ℕ) : ¬PrefixIn (∅ : Finset (Chain × Fin w)) a p := by
  rintro ⟨q, -, hm⟩
  exact Finset.notMem_empty _ hm
theorem prefixIn_of_mem {S : Finset (Chain × Fin w)} {a : Chain} {q : Fin w} (h : (a, q) ∈ S) :
    PrefixIn S a q.val :=
  ⟨q, le_rfl, h⟩
theorem prefixIn_insert [DecidableEq Chain] {S : Finset (Chain × Fin w)} {x : Chain × Fin w} {a : Chain} {p : ℕ} :
    PrefixIn (insert x S) a p ↔ (x.1 = a ∧ x.2.val ≤ p) ∨ PrefixIn S a p := by
  constructor
  · rintro ⟨q, hq, hm⟩
    rcases Finset.mem_insert.mp hm with h | h
    · left
      subst h
      exact ⟨rfl, hq⟩
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (⟨h1, h2⟩ | h)
    · refine ⟨x.2, h2, ?_⟩
      rw [← h1]
      exact Finset.mem_insert_self _ _
    · exact h.mono_set (Finset.subset_insert _ _)
theorem nonempty_of_prefixIn {S : Finset (Chain × Fin w)} {a : Chain} {p : ℕ} (h : PrefixIn S a p) :
    S.Nonempty := by
  obtain ⟨q, -, hm⟩ := h
  exact ⟨_, hm⟩
theorem two_le_card_of_prefixIn [DecidableEq Chain] {S : Finset (Chain × Fin w)} {a b : Chain} {p p' : ℕ}
    (hab : a ≠ b) (ha : PrefixIn S a p) (hb : PrefixIn S b p') : 2 ≤ S.card := by
  obtain ⟨q, -, hq⟩ := ha
  obtain ⟨q', -, hq'⟩ := hb
  have hne : ((a, q) : Chain × Fin w) ≠ (b, q') := fun h => hab (Prod.ext_iff.mp h).1
  have hsub : ({(a, q), (b, q')} : Finset (Chain × Fin w)) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hq
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact hq'
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this
end Prefix
section Tracks
variable {Chain Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {w : ℕ}
structure PrefixTracks (Cov : Chain → ℕ → Prop) (before after : State (Chain × Fin w) Value Memory) : Prop where
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ a p, PrefixIn after.retired a p →
    PrefixIn before.retired a p ∨ PrefixIn after.guesses a p ∨ Cov a p
theorem PrefixTracks.refl (Cov : Chain → ℕ → Prop) (state : State (Chain × Fin w) Value Memory) :
    PrefixTracks Cov state state :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ h => Or.inl h⟩
theorem PrefixTracks.mono {Cov Cov' : Chain → ℕ → Prop} {s s' : State (Chain × Fin w) Value Memory}
    (hc : ∀ a p, Cov a p → Cov' a p) (h : PrefixTracks Cov s s') : PrefixTracks Cov' s s' := by
  refine ⟨h.guesses, h.retired, fun a p hp => ?_⟩
  rcases h.origin a p hp with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (hc a p h1))
theorem PrefixTracks.trans {C1 C2 : Chain → ℕ → Prop} {s1 s2 s3 : State (Chain × Fin w) Value Memory}
    (first : PrefixTracks C1 s1 s2) (second : PrefixTracks C2 s2 s3) :
    PrefixTracks (fun a p => C1 a p ∨ C2 a p) s1 s3 := by
  refine ⟨first.guesses.trans second.guesses, first.retired.trans second.retired, fun a p hp => ?_⟩
  rcases second.origin a p hp with h | h | h
  · rcases first.origin a p h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.mono_set second.guesses))
    · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
theorem PrefixTracks.trans_false {C : Chain → ℕ → Prop} {s1 s2 s3 : State (Chain × Fin w) Value Memory}
    (first : PrefixTracks C s1 s2) (second : PrefixTracks (fun _ _ => False) s2 s3) : PrefixTracks C s1 s3 :=
  (first.trans second).mono fun _ _ h => h.elim id False.elim
theorem prefixIn_guesses_of_tracks {Cov : Chain → ℕ → Prop} {init final : State (Chain × Fin w) Value Memory}
    (h : PrefixTracks Cov init final) (hinit : init.retired = ∅) {a : Chain} {p : ℕ}
    (hr : PrefixIn final.retired a p) (hc : ¬Cov a p) : PrefixIn final.guesses a p := by
  rcases h.origin a p hr with h1 | h1 | h1
  · rw [hinit] at h1
    exact absurd h1 (not_prefixIn_empty a p)
  · exact h1
  · exact absurd h1 hc
variable [DecidableEq Chain] [Fintype Chain] [DecidableEq Value]
omit [Fintype Chain] in
theorem afterTrial_tracks (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (candidate : Value) (hit : Bool) :
    PrefixTracks (fun _ _ => False) state (afterTrial environment state coordinate candidate hit) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [afterTrial]
    split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
  · simp only [afterTrial]
    split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
  · intro a p hp
    simp only [afterTrial] at hp ⊢
    by_cases hh : hit = true
    · rw [if_pos hh, prefixIn_insert] at hp
      rcases hp with ⟨h1, h2⟩ | hp
      · by_cases hret : coordinate ∈ state.retired
        · left
          refine ⟨coordinate.2, h2, ?_⟩
          rw [← h1]
          exact hret
        · right; left
          rw [if_pos ⟨hh, hret⟩]
          refine ⟨coordinate.2, h2, ?_⟩
          rw [← h1]
          exact Finset.mem_insert_self _ _
      · exact Or.inl hp
    · rw [if_neg hh] at hp
      exact Or.inl hp
omit [Fintype Chain] [DecidableEq Value] in
theorem afterDisclosure_tracks_next (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (value : Value)
    (hprev : PrefixIn state.retired coordinate.1 coordinate.2.val) :
    PrefixTracks (fun _ _ => False) state (afterDisclosure environment state coordinate value) := by
  refine ⟨Finset.Subset.refl _, Finset.subset_insert _ _, ?_⟩
  intro a p hp
  simp only [afterDisclosure] at hp ⊢
  rw [prefixIn_insert] at hp
  rcases hp with ⟨h1, h2⟩ | hp
  · left
    rw [← h1]
    exact hprev.mono_pos h2
  · exact Or.inl hp
omit [Fintype Chain] [DecidableEq Value] in
theorem afterDisclosure_tracks_cov (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (value : Value) :
    PrefixTracks (fun a p => coordinate.1 = a ∧ coordinate.2.val ≤ p) state
      (afterDisclosure environment state coordinate value) := by
  refine ⟨Finset.Subset.refl _, Finset.subset_insert _ _, ?_⟩
  intro a p hp
  simp only [afterDisclosure] at hp ⊢
  rw [prefixIn_insert] at hp
  rcases hp with h | hp
  · exact Or.inr (Or.inr h)
  · exact Or.inl hp
omit [Fintype Chain] in
theorem mem_retired_afterTrial_hit (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (candidate : Value) :
    coordinate ∈ (afterTrial environment state coordinate candidate true).retired := by
  simp only [afterTrial, if_true]
  exact Finset.mem_insert_self _ _
end Tracks
end ClaudeWCT.Guess
end

section


namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option backward.isDefEq.respectTransparency false
section ChainWorld
variable {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {Chain V R : Type} {w : ℕ}
def trialQ (c : Chain × Fin w) (v : V) : OracleComp (World auxSpec (Chain × Fin w) V) Bool :=
  liftM ((World auxSpec (Chain × Fin w) V).query (.inr (.inl (c, v))))
def discloseQ (c : Chain × Fin w) : OracleComp (World auxSpec (Chain × Fin w) V) V :=
  liftM ((World auxSpec (Chain × Fin w) V).query (.inr (.inr c)))
def succPos (p : Fin w) : Option (Fin w) := if h : p.val + 1 < w then some ⟨p.val + 1, h⟩ else none
theorem succPos_val {p p' : Fin w} (h : succPos p = some p') : p'.val = p.val + 1 := by
  unfold succPos at h
  split at h
  · cases h; rfl
  · cases h
def probeW (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V) :
    OracleComp (World auxSpec (Chain × Fin w) V) R := do
  let hit ← trialQ (auxSpec := auxSpec) (a, p) v
  if hit then
    match succPos p with
    | some p' => do
        let next ← discloseQ (auxSpec := auxSpec) (a, p')
        pure (step a p next)
    | none => pure (top a)
  else pure miss
def probeAnswer [DecidableEq V] (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R)
    (g : Chain × Fin w → V) (a : Chain) (p : Fin w) (v : V) : R :=
  if g (a, p) = v then
    (match succPos p with
      | some p' => step a p (g (a, p'))
      | none => top a)
  else miss
def discloseAll (cs : List (Chain × Fin w)) : OracleComp (World auxSpec (Chain × Fin w) V) (List V) :=
  cs.mapM fun c => discloseQ (auxSpec := auxSpec) c
variable [DecidableEq Chain] [DecidableEq V]
omit [DecidableEq Chain] in
theorem fixed_probeW (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V)
    (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V) :
    simulateQ (fixedAnswers auxiliary g) (probeW (auxSpec := auxSpec) step top miss a p v) =
      pure (probeAnswer step top miss g a p v) := by
  unfold probeW probeAnswer trialQ
  rw [simulateQ_bind, simulateQ_spec_query]
  change (pure (decide (g (a, p) = v)) >>= _) = _
  rw [pure_bind]
  by_cases hv : g (a, p) = v
  · simp only [hv, decide_true, if_true]
    cases succPos p with
    | none => simp only [simulateQ_pure]
    | some p' =>
        simp only
        unfold discloseQ
        rw [simulateQ_bind, simulateQ_spec_query]
        change (pure (g (a, p')) >>= _) = _
        rw [pure_bind, simulateQ_pure]
  · simp only [hv, decide_false, Bool.false_eq_true, if_false, simulateQ_pure]
omit [DecidableEq Chain] in
theorem fixed_discloseQ (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V) (c : Chain × Fin w) :
    simulateQ (fixedAnswers auxiliary g) (discloseQ (auxSpec := auxSpec) c) = pure (g c) := by
  unfold discloseQ
  rw [simulateQ_spec_query]
  rfl
omit [DecidableEq Chain] in
theorem fixed_discloseAll (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V)
    (cs : List (Chain × Fin w)) :
    simulateQ (fixedAnswers auxiliary g) (discloseAll (auxSpec := auxSpec) cs) = pure (cs.map g) := by
  induction cs with
  | nil => simp [discloseAll]
  | cons c rest ih =>
      unfold discloseAll at ih ⊢
      rw [List.mapM_cons, simulateQ_bind, fixed_discloseQ, pure_bind, simulateQ_bind, ih, pure_bind,
        simulateQ_pure]
      simp
variable {Memory : Type}
theorem fixedRun_bind_nonzero' {First Result : Type} (environment : Environment auxSpec (Chain × Fin w) V Memory)
    (g : Chain × Fin w → V) (first : OracleComp (World auxSpec (Chain × Fin w) V) First)
    (next : First → OracleComp (World auxSpec (Chain × Fin w) V) Result) (state : State (Chain × Fin w) V Memory)
    (result : Result × State (Chain × Fin w) V Memory) (hr : fixedRun environment g (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun environment g first state middle ≠ 0 ∧ fixedRun environment g (next middle.1) middle.2 result ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem fixedRun_pure_nonzero' {Result : Type} (environment : Environment auxSpec (Chain × Fin w) V Memory)
    (g : Chain × Fin w → V) (value : Result) (state : State (Chain × Fin w) V Memory)
    (result : Result × State (Chain × Fin w) V Memory) (hr : fixedRun environment g (pure value) state result ≠ 0) :
    result = (value, state) := by
  unfold fixedRun at hr
  rw [runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_trialQ (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (c : Chain × Fin w) (v : V) (state : State (Chain × Fin w) V Memory) (result : Bool × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (trialQ (auxSpec := auxSpec) c v) state result ≠ 0) :
    result = (decide (g c = v), afterTrial environment state c v (decide (g c = v))) := by
  unfold fixedRun runWith trialQ at hr
  rw [simulateQ_spec_query] at hr
  simpa only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_discloseQ (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (c : Chain × Fin w) (state : State (Chain × Fin w) V Memory) (result : V × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (discloseQ (auxSpec := auxSpec) c) state result ≠ 0) :
    result = (g c, afterDisclosure environment state c (g c)) := by
  unfold fixedRun runWith discloseQ at hr
  rw [simulateQ_spec_query] at hr
  simpa only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_probeW (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V)
    (state : State (Chain × Fin w) V Memory) (result : R × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (probeW (auxSpec := auxSpec) step top miss a p v) state result ≠ 0) :
    result.1 = probeAnswer step top miss g a p v ∧
      PrefixTracks (fun _ _ => False) state result.2 ∧
      result.2.probes = state.probes + 1 ∧
      result.2.guesses ⊆ insert (a, p) state.guesses ∧
      (g (a, p) = v → (a, p) ∈ result.2.retired) := by
  unfold probeW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero' environment g _ _ state result hr
  have hmid := fixedRun_trialQ environment g (a, p) v state middle hm
  subst hmid
  have htrial := afterTrial_tracks environment state (a, p) v (decide (g (a, p) = v))
  have hguess1 : (afterTrial environment state (a, p) v (decide (g (a, p) = v))).guesses ⊆
      insert (a, p) state.guesses := by
    simp only [afterTrial]
    split <;> simp only [Finset.Subset.refl, Finset.subset_insert]
  by_cases hv : g (a, p) = v
  · have hhit : decide (g (a, p) = v) = true := decide_eq_true hv
    simp only [hhit, if_true] at hr
    have hret : (a, p) ∈ (afterTrial environment state (a, p) v true).retired :=
      mem_retired_afterTrial_hit environment state (a, p) v
    rw [hhit] at htrial hguess1
    cases hs : succPos p with
    | none =>
        rw [hs] at hr
        have h := fixedRun_pure_nonzero' environment g _ _ result hr
        subst h
        refine ⟨by simp [probeAnswer, hv, hs], htrial, by simp [afterTrial], hguess1, fun _ => hret⟩
    | some p' =>
        rw [hs] at hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero' environment g _ _ _ result hr
        have htl := fixedRun_discloseQ environment g (a, p') _ tail ht
        subst htl
        have h := fixedRun_pure_nonzero' environment g _ _ result hr
        subst h
        have hnext := afterDisclosure_tracks_next environment (afterTrial environment state (a, p) v true) (a, p')
          (g (a, p')) ⟨p, by rw [succPos_val hs]; omega, hret⟩
        refine ⟨by simp [probeAnswer, hv, hs], htrial.trans_false hnext, by simp [afterDisclosure, afterTrial],
          by simpa [afterDisclosure] using hguess1, fun _ => Finset.mem_insert_of_mem hret⟩
  · have hmiss : decide (g (a, p) = v) = false := decide_eq_false hv
    simp only [hmiss, Bool.false_eq_true, if_false] at hr
    have h := fixedRun_pure_nonzero' environment g _ _ result hr
    subst h
    rw [hmiss] at htrial hguess1
    exact ⟨by simp [probeAnswer, hv], htrial, by simp [afterTrial], hguess1, fun h => absurd h hv⟩
theorem fixedRun_discloseAll (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (cs : List (Chain × Fin w)) (state : State (Chain × Fin w) V Memory)
    (result : List V × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (discloseAll (auxSpec := auxSpec) cs) state result ≠ 0) :
    result.1 = cs.map g ∧ result.2.probes = state.probes ∧ result.2.guesses = state.guesses ∧
      PrefixTracks (fun a p => ∃ c ∈ cs, c.1 = a ∧ c.2.val ≤ p) state result.2 := by
  induction cs generalizing state result with
  | nil =>
      have h := fixedRun_pure_nonzero' environment g _ state result hr
      subst h
      exact ⟨rfl, rfl, rfl, PrefixTracks.refl _ _⟩
  | cons c rest ih =>
      unfold discloseAll at hr
      rw [List.mapM_cons] at hr
      obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero' environment g _ _ state result hr
      have hmid := fixedRun_discloseQ environment g c state middle hm
      subst hmid
      obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero' environment g _ _ _ result hr
      have h := fixedRun_pure_nonzero' environment g _ _ result hr
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := ih _ tail ht
      refine ⟨by simp [h1], by rw [h2]; rfl, by rw [h3]; rfl, ?_⟩
      refine ((afterDisclosure_tracks_cov environment state c (g c)).trans h4).mono ?_
      rintro a p (⟨h1, h2⟩ | ⟨c', hc', h1, h2⟩)
      · exact ⟨c, List.mem_cons_self, h1, h2⟩
      · exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩
end ChainWorld
end ClaudeWCT.Guess
end

section

namespace ClaudeWCT.Guess
open OracleComp OracleSpec
open SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem eval_shortHash (A : Correctness.Answers) (input : HashInput) :
    evalWithAnswerFn A (shortHash input) = (A (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl
theorem eval_chain_walk (A : Correctness.Answers) (index coord selected i : Nat) (val : Nat → Digest) (s n : Nat)
    (hstep : ∀ p, s ≤ p → p < s + n →
      (A (.inl (.inr (WCT9.chainInput index coord selected i p (val p))))).extractLsb' 0 128 = val (p + 1)) :
    evalWithAnswerFn A (WCT9.chain index coord selected i s n (val s)) = val (s + n) := by
  induction n generalizing s with
  | zero => simp [WCT9.chain, evalWithAnswerFn_pure]
  | succ n ih =>
      unfold WCT9.chain
      rw [List.range'_succ, List.foldlM_cons, evalWithAnswerFn_bind, eval_shortHash, pad64_wctChainInput,
        hstep s le_rfl (by omega)]
      have := ih (s + 1) (fun p h1 h2 => hstep p (by omega) (by omega))
      unfold WCT9.chain at this
      rw [this]
      congr 1
      omega
theorem queried_chain_walk (A : Correctness.Answers) (index coord selected i : Nat) (val : Nat → Digest) (s n : Nat)
    (hstep : ∀ p, s ≤ p → p < s + n →
      (A (.inl (.inr (WCT9.chainInput index coord selected i p (val p))))).extractLsb' 0 128 = val (p + 1))
    (p : Nat) (h1 : s ≤ p) (h2 : p < s + n) :
    (.inl (.inr (WCT9.chainInput index coord selected i p (val p))) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.chain index coord selected i s n (val s)) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
      unfold WCT9.chain
      rw [List.range'_succ, List.foldlM_cons, Security.SourceReplay.queried_bind, queried_shortHash,
        pad64_wctChainInput]
      by_cases hp : p = s
      · subst hp
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [eval_shortHash, pad64_wctChainInput, hstep s le_rfl (by omega)]
        have := ih (s + 1) (fun p h1 h2 => hstep p (by omega) (by omega)) (by omega) (by omega)
        unfold WCT9.chain at this
        exact this
theorem chainValue_walk (A : Correctness.Answers) (a : ChainAddr) (s n : Nat) :
    evalWithAnswerFn A (WCT9.chain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s n (chainValue A a s)) =
      chainValue A a (s + n) := by
  unfold chainValue WCT9.chain
  have hr : List.range' 0 (s + n) = List.range' 0 s ++ List.range' s n := by
    have := List.range'_append (s := 0) (m := s) (n := n) (step := 1)
    simpa [Nat.add_comm] using this.symm
  rw [hr, List.foldlM_append, evalWithAnswerFn_bind]
theorem chainValue_succ (A : Correctness.Answers) (a : ChainAddr) (p : Nat) :
    (A (.inl (.inr (WCT9.chainInput a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p (chainValue A a p))))).extractLsb' 0 128 =
      chainValue A a (p + 1) := by
  have h := chainValue_walk A a p 1
  unfold WCT9.chain at h
  simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, evalWithAnswerFn_bind, eval_shortHash,
    evalWithAnswerFn_pure] at h
  rw [pad64_wctChainInput] at h
  exact h
end ClaudeWCT.Guess
end

section


namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
structure ChainTable where
  answers : (GCoord → Digest) → Correctness.Answers
  step : ChainAddr → Fin 3 → Digest → HashOutput
  top : ChainAddr → HashOutput
  miss : HashInput → HashOutput
  answers_probe : ∀ g a p c, answers g (.inl (.inr (probeInput a p c))) =
    probeAnswer step top (miss (probeInput a p c)) g a p c
  answers_public : ∀ g g' x, decodeProbe x = none → answers g (.inl (.inr x)) = answers g' (.inl (.inr x))
  step_low : ∀ a p v, (step a p v).extractLsb' 0 128 = v
  seed : ∀ g a, seedOf (answers g) a = g (a, 0)
namespace ChainTable
variable (T : ChainTable)
noncomputable def walkVal (g : GCoord → Digest) (a : ChainAddr) (p : Nat) : Digest :=
  if h : p < 3 then g (a, ⟨p, h⟩) else (T.top a).extractLsb' 0 128
theorem walk_step (g : GCoord → Digest) (a : ChainAddr) (p : Nat) (hp : p < 3) :
    (T.answers g (.inl (.inr (WCT9.chainInput a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p
      (T.walkVal g a p))))).extractLsb' 0 128 = T.walkVal g a (p + 1) := by
  have hq := T.answers_probe g a ⟨p, hp⟩ (T.walkVal g a p)
  unfold probeInput at hq
  simp only at hq
  rw [hq]
  have hv : g (a, ⟨p, hp⟩) = T.walkVal g a p := by simp [walkVal, hp]
  unfold probeAnswer
  rw [if_pos hv]
  unfold succPos
  by_cases h1 : p + 1 < 3
  · rw [dif_pos h1]
    simp only
    rw [T.step_low]
    simp [walkVal, h1]
  · rw [dif_neg h1]
    simp only
    simp [walkVal, h1]
theorem chainValue_answers (g : GCoord → Digest) (a : ChainAddr) (p : Nat) (hp : p ≤ 3) :
    chainValue (T.answers g) a p = T.walkVal g a p := by
  have h0 : seedOf (T.answers g) a = T.walkVal g a 0 := by rw [T.seed]; simp [walkVal]
  unfold chainValue
  rw [h0]
  have := eval_chain_walk (T.answers g) a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (T.walkVal g a) 0 p
    (fun q _ hq => T.walk_step g a q (by omega))
  simpa using this
theorem chainValue_answers_fin (g : GCoord → Digest) (c : GCoord) :
    chainValue (T.answers g) c.1 c.2.val = g c := by
  rw [T.chainValue_answers g c.1 c.2.val (by omega)]
  simp [walkVal, c.2.isLt]
theorem honestProbe_answers (g : GCoord → Digest) (c : GCoord) :
    honestProbe (T.answers g) c = probeInput c.1 c.2 (g c) := by
  unfold honestProbe
  rw [T.chainValue_answers_fin]
variable {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
noncomputable def hashW (x : HashInput) : OracleComp (World auxSpec GCoord Digest) HashOutput :=
  match decodeProbe x with
  | none => pure (T.answers (fun _ => 0) (.inl (.inr x)))
  | some q => probeW (auxSpec := auxSpec) T.step T.top (T.miss x) q.1.1 q.1.2 q.2
theorem fixed_hashW (auxiliary : QueryImpl auxSpec ProbComp) (g : GCoord → Digest) (x : HashInput) :
    simulateQ (fixedAnswers auxiliary g) (T.hashW (auxSpec := auxSpec) x) =
      pure (T.answers g (.inl (.inr x))) := by
  unfold hashW
  cases hd : decodeProbe x with
  | none =>
      simp only [simulateQ_pure]
      rw [T.answers_public g (fun _ => 0) x hd]
  | some q =>
      simp only
      rw [fixed_probeW, eq_of_decodeProbe hd, T.answers_probe]
theorem fixedRun_hashW {Memory : Type} (environment : Environment auxSpec GCoord Digest Memory)
    (g : GCoord → Digest) (x : HashInput) (state : State GCoord Digest Memory)
    (result : HashOutput × State GCoord Digest Memory)
    (hr : fixedRun environment g (T.hashW (auxSpec := auxSpec) x) state result ≠ 0) :
    result.1 = T.answers g (.inl (.inr x)) ∧
      PrefixTracks (fun _ _ => False) state result.2 ∧
      result.2.probes ≤ state.probes + 1 ∧
      (∀ c : GCoord, x = honestProbe (T.answers g) c → c ∈ result.2.retired) := by
  unfold hashW at hr
  cases hd : decodeProbe x with
  | none =>
      rw [hd] at hr
      have h := fixedRun_pure_nonzero' environment g _ state result hr
      subst h
      refine ⟨T.answers_public _ g x hd, PrefixTracks.refl _ _, Nat.le_succ _, ?_⟩
      intro c hc
      rw [hc, honestProbe, decodeProbe_probeInput] at hd
      cases hd
  | some q =>
      rw [hd] at hr
      obtain ⟨h1, h2, h3, -, h5⟩ := fixedRun_probeW environment g T.step T.top (T.miss x) q.1.1 q.1.2 q.2
        state result hr
      have hx := eq_of_decodeProbe hd
      refine ⟨?_, h2, h3.le, ?_⟩
      · rw [h1, hx, T.answers_probe]
      · intro c hc
        rw [T.honestProbe_answers, hx] at hc
        obtain ⟨ha, hp, hv⟩ := probeInput_injective hc
        have hcq : c = q.1 := Prod.ext ha.symm hp.symm
        subst hcq
        exact h5 hv.symm
end ChainTable
end ClaudeWCT.Guess
end
