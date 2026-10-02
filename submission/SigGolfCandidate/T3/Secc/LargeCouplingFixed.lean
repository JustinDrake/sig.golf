import SigGolfCandidate.T3.Secc.LargeCouplingSplit
import SigGolfCandidate.T3.Secc.WotsTransportTable

/-!
# LR-34 (coupling, real side): the tagged interaction in a fixed world

`taggedFixed F published program state` is the tagged record (`taggedRecord`) with every hash query answered by the
total table `F` (coins uniform): F2's `Ref.fixedRecord` with the interaction tagged.

* `taggedFixed_untag`: untagging gives F2's fixed-world record of the logged interaction;
* `taggedFixed_support`: if `F` agrees with the starting caches, every fixed-world tagged record is a lazy tagged
  record (`taggedRecord`) and `F` agrees with its final caches.
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

/-- The tagged record of the logged interaction in the fixed world of `F`. -/
noncomputable def taggedFixed {α : Type} (F : Answers) (published : T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) : LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let answer ← Wots.Ref.fixedWorld F (.inl world)
          (fun last => (⟨last.value, .world ⟨state, .inl world, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next answer (FirstHit.advance state (.inl world) answer)
      | .inr request, next => do
          let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program

section Fixed
variable {α : Type} (F : Answers) (published : T3.Cache)

theorem taggedFixed_pure (value : α) (state : LazyPrivate.State) :
    taggedFixed F published (pure value : OracleComp LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl

theorem taggedFixed_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let answer ← Wots.Ref.fixedWorld F (.inl input)
      (fun last => (⟨last.value, .world ⟨state, .inl input, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next answer) (FirstHit.advance state (.inl input) answer)) := rfl

theorem taggedFixed_request (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next block.value) block.state) := rfl

/-- **Fixed-world tagged records are lazy tagged records.** -/
theorem taggedFixed_support (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State)
    (hF : Wots.Ref.Agrees F state) (tagged : Tagged α) (h : tagged ∈ support (taggedFixed F published program state)) :
    tagged ∈ support (taggedRecord published program state) ∧ Wots.Ref.Agrees F tagged.state := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedFixed_pure, mem_support_pure_iff] at h
      subst h
      exact ⟨by rw [taggedRecord_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, mem_support_bind_iff] at h
          obtain ⟨answer, ha, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hcons : ∀ cached, SourceReplay.known state (.inl input) = some cached → cached = answer := by
            intro cached hc
            rcases input with n | x
            · cases hc
            · have h1 := hF _ _ hc
              rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              rw [ha, ← h1]
          have hadv : Wots.Ref.Agrees F (FirstHit.advance state (.inl input) answer) := by
            rcases input with n | x
            · exact hF
            · rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              subst ha
              exact Wots.Ref.agrees_advance hF _
          obtain ⟨h1, h2⟩ := ih answer _ hadv last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_world, mem_support_bind_iff]
          refine ⟨(answer, FirstHit.advance state (.inl input) answer),
            Wots.Ref.lazy_query_mem state (.inl input) answer hcons, ?_⟩
          rw [support_map]
          exact ⟨last, h1, rfl⟩
      | inr request =>
          rw [taggedFixed_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          obtain ⟨hb1, hb2⟩ := Wots.Ref.fixedRecord_mem_record F _ state hF block hb
          obtain ⟨h1, h2⟩ := ih block.value block.state hb2 last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_request, mem_support_bind_iff]
          exact ⟨block, hb1, by rw [support_map]; exact ⟨last, h1, rfl⟩⟩

/-- **Untagging the fixed-world tagged record** gives F2's fixed-world record of the logged interaction. -/
theorem taggedFixed_untag (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    Tagged.untag <$> taggedFixed F published program state =
      Wots.Ref.fixedRecord F (FullGame.loggedWith (FullGame.authenticatedSign published) program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [taggedFixed_pure, map_pure, FullGame.loggedWith_pure, Wots.Ref.fixedRecord_pure]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, FullGame.loggedWith_world]
          change _ = Wots.Ref.fixedRecord F (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state
          rw [Wots.Ref.fixedRecord_query_bind, map_bind]
          apply bind_congr
          intro answer
          rw [Functor.map_map, ← ih answer]
          simp only [Functor.map_map]
          rfl
      | inr request =>
          rw [taggedFixed_request, FullGame.loggedWith_request, Wots.Ref.fixedRecord_bind, map_bind]
          apply bind_congr
          intro block
          rw [Wots.Ref.fixedRecord_map, ← ih block.value, Functor.map_map, Functor.map_map,
            map_eq_bind_pure_comp]
          simp only [Function.comp_def, bind_pure_comp, Functor.map_map]
          rfl

end Fixed

end SigGolfCandidate.T3.Security.LargeCoupling
