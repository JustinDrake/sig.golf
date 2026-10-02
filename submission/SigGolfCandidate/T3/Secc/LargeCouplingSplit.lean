import SigGolfCandidate.T3.Secc.LargeCouplingTrace

/-!
# LR-34 (trace side): tagged records are the actual recorded interactions; splits are unique

* `taggedRecord_world`, `taggedRecord_request` — one-step equations.
* `taggedRecord_untag` — the untagged events of a tagged record are a lazy record of the logged interaction
  (so a `TaggedSplit` is F2's `Wots.GameSplit`).
* `record_prefix_unique` — prefix determinism of `FirstHit.record`: two supported records of one program from one
  state whose event lists are prefixes of a common list are equal.
* `taggedSplit_unique` — two tagged splits of one recorded run coincide.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem taggedRecord_pure {α : Type} (published : T3.Cache) (value : α) (state : LazyPrivate.State) :
    taggedRecord published (pure value : OracleComp LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl

theorem taggedRecord_world {α : Type} (published : T3.Cache) (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedRecord published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query (.inl input))) state
      (fun last => (⟨last.value, .world ⟨state, .inl input, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next middle.1) middle.2) := rfl

theorem taggedRecord_request {α : Type} (published : T3.Cache) (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedRecord published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← FirstHit.record (FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next block.value) block.state) := rfl

/-- The untagged record of a tagged interaction. -/
def Tagged.untag {α : Type} (tagged : Tagged α) : FirstHit.Recorded (α × QueryLog Requests) :=
  ⟨tagged.value, tagged.events, tagged.state⟩

/-- **Tagged records are actual records**: the untagged events of a supported tagged record form a supported lazy
record of the logged interaction. -/
theorem taggedRecord_untag {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (tagged : Tagged α) (h : tagged ∈ support (taggedRecord published program state)) :
    tagged.untag ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign published) program)
      state) := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h
      subst h
      rw [FullGame.loggedWith_pure, FirstHit.record_pure, mem_support_pure_iff]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h
          obtain ⟨middle, hm, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih middle.1 middle.2 last hl
          rw [FullGame.loggedWith_world]
          change _ ∈ support (FirstHit.record (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state)
          rw [FirstHit.record_query_bind, mem_support_bind_iff]
          refine ⟨middle, hm, ?_⟩
          rw [support_map]
          exact ⟨last.untag, hu, rfl⟩
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih block.value block.state last hl
          rw [FullGame.loggedWith_request, FirstHit.record_bind, mem_support_bind_iff]
          refine ⟨block, hb, ?_⟩
          rw [mem_support_bind_iff]
          rw [FirstHit.record_map, support_map] at *
          refine ⟨⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2), last.events, last.state⟩,
            ⟨last.untag, hu, rfl⟩, ?_⟩
          rw [mem_support_pure_iff]
          simp only [Tagged.untag, Tagged.events, List.flatMap_cons, TaggedStep.events]

/-- A tagged split is a `GameSplit`-shaped decomposition (untagged interaction). -/
theorem TaggedSplit.untag {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)} {tagged : Tagged (Option ForgeryP)}
    {checked : FirstHit.Recorded Bool} (h : TaggedSplit adversary result generated tagged checked) :
    generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
    tagged.untag ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
    checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.untag.value)
      tagged.untag.state) ∧
    result = ⟨checked.value, generated.events ++ (tagged.untag.events ++ checked.events), checked.state⟩ := by
  obtain ⟨hg, ht, hc, hr⟩ := h
  exact ⟨hg, taggedRecord_untag _ _ _ _ ht, hc, hr⟩

/-! ## Prefix determinism and uniqueness of splits -/

theorem queryEvent_answer_eq {state : LazyPrivate.State} {input : T3.Spec.Domain} {a b : T3.Spec.Range input}
    (h : (⟨state, input, a⟩ : FirstHit.QueryEvent) = ⟨state, input, b⟩) : a = b := by
  simp only [FirstHit.QueryEvent.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- **Prefix determinism of the recorder.** -/
theorem record_prefix_unique {α : Type} (program : M α) (state : LazyPrivate.State)
    (r1 r2 : FirstHit.Recorded α) (h1 : r1 ∈ support (FirstHit.record program state))
    (h2 : r2 ∈ support (FirstHit.record program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : r1.events ++ rest1 = r2.events ++ rest2) : r1 = r2 := by
  induction program using OracleComp.inductionOn generalizing state r1 r2 rest1 rest2 with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at h1 h2
      obtain ⟨m1, hm1, h1⟩ := h1
      obtain ⟨m2, hm2, h2⟩ := h2
      rw [support_map] at h1 h2
      obtain ⟨l1, hl1, rfl⟩ := h1
      obtain ⟨l2, hl2, rfl⟩ := h2
      simp only [List.cons_append, List.cons.injEq] at heq
      have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
      have hs1 := FirstHit.query_advance state input m1 hm1
      have hs2 := FirstHit.query_advance state input m2 hm2
      have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
      subst hm
      have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
      rw [hl]

/-- Prefix determinism of the tagged recorder. -/
theorem taggedRecord_prefix_unique {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (t1 t2 : Tagged α) (h1 : t1 ∈ support (taggedRecord published program state))
    (h2 : t2 ∈ support (taggedRecord published program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : t1.events ++ rest1 = t2.events ++ rest2) : t1 = t2 := by
  induction program using OracleComp.inductionOn generalizing state t1 t2 rest1 rest2 with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h1 h2
          obtain ⟨m1, hm1, h1⟩ := h1
          obtain ⟨m2, hm2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events,
            List.cons_append, List.cons.injEq] at heq
          have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
          have hs1 := FirstHit.query_advance state (.inl input) m1 hm1
          have hs2 := FirstHit.query_advance state (.inl input) m2 hm2
          have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
          subst hm
          have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
          rw [hl]
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h1 h2
          obtain ⟨b1, hb1, h1⟩ := h1
          obtain ⟨b2, hb2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events, List.append_assoc] at heq
          have hb := record_prefix_unique _ state b1 b2 hb1 hb2 _ _ heq
          subst hb
          have heq' := List.append_cancel_left heq
          have hl := ih b1.value b1.state l1 l2 hl1 hl2 rest1 rest2 heq'
          rw [hl]

/-- **Uniqueness of tagged splits.** -/
theorem taggedSplit_unique {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {g1 g2 : FirstHit.Recorded (Digest × T3.Cache)} {t1 t2 : Tagged (Option ForgeryP)}
    {c1 c2 : FirstHit.Recorded Bool}
    (h1 : TaggedSplit adversary result g1 t1 c1) (h2 : TaggedSplit adversary result g2 t2 c2) :
    g1 = g2 ∧ t1 = t2 ∧ c1 = c2 := by
  obtain ⟨hg1, ht1, hc1, hr1⟩ := h1
  obtain ⟨hg2, ht2, hc2, hr2⟩ := h2
  have hevents : g1.events ++ (t1.events ++ c1.events) = g2.events ++ (t2.events ++ c2.events) := by
    have := congrArg FirstHit.Recorded.events (hr1.symm.trans hr2)
    simpa using this
  have hg := record_prefix_unique keygen (∅, ∅) g1 g2 hg1 hg2 _ _ hevents
  subst hg
  have hevents' := List.append_cancel_left hevents
  have ht := taggedRecord_prefix_unique _ _ _ t1 t2 ht1 ht2 _ _ hevents'
  subst ht
  have hevents'' := List.append_cancel_left hevents'
  have hc := record_prefix_unique _ _ c1 c2 hc1 hc2 [] [] (by simpa using hevents'')
  exact ⟨rfl, rfl, hc⟩

/-- On a sample with a tagged split, `digests` is the monitor's count of that split. -/
theorem digests_of_split {adversary : AdversaryP} {q : Nat} {z : PaddedGame.TraceResult × Answers}
    {g : FirstHit.Recorded (Digest × T3.Cache)} {t : Tagged (Option ForgeryP)} {c : FirstHit.Recorded Bool}
    (h : TaggedSplit adversary (QueryRecorded.recordedTrace z.1) g t c) :
    digests adversary q z = (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).digests := by
  have hex : ∃ generated tagged checked,
      TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked := ⟨g, t, c, h⟩
  unfold digests
  rw [dif_pos hex]
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))
  obtain ⟨hg, ht, hc⟩ := taggedSplit_unique hspec h
  rw [hc, ht, hg]

/-- On a sample with a tagged split, `Contact` is the monitor's contact of that split. -/
theorem contact_of_split {adversary : AdversaryP} {q : Nat} {z : PaddedGame.TraceResult × Answers}
    {g : FirstHit.Recorded (Digest × T3.Cache)} {t : Tagged (Option ForgeryP)} {c : FirstHit.Recorded Bool}
    (h : TaggedSplit adversary (QueryRecorded.recordedTrace z.1) g t c) :
    Contact adversary q z ↔ (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).contact = true := by
  constructor
  · intro hc
    exact hc g t c h
  · intro hm g' t' c' h'
    obtain ⟨hg, ht, hc⟩ := taggedSplit_unique h h'
    rw [← hg, ← ht, ← hc]
    exact hm

end SigGolfCandidate.T3.Security.LargeCoupling
