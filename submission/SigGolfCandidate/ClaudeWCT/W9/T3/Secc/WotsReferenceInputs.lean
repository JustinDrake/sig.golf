import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportR3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem offlineSign_support (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (answer : Option Signature)
    (h : answer ∈ support (offlineSign T published request)) :
    answer = evalWithAnswerFn T (FullGame.authenticatedSign published request) := by
  unfold offlineSign at h
  rw [mem_support_bind_iff] at h
  obtain ⟨_, -, h⟩ := h
  rwa [mem_support_pure_iff] at h
theorem offlineSign_allQueries (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (query : RefWorld.Domain)
    (h : query ∈ allQueries (offlineSign T published request)) : query = .inr () := by
  unfold offlineSign at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact ticks_allQueries _ query h
  · exact absurd h (by simp [allQueries_pure])
theorem interaction_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (published : SigGolfCandidate.T3.Cache) {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    (∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineInteraction T published program) →
      x ∈ hashInputs (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program))) ∧
    ∀ value ∈ support (offlineInteraction T published program),
      value ∈ support (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [offlineInteraction_pure, FullGame.loggedWith_pure]
      refine ⟨fun x hx => absurd hx (by rw [allQueries_pure]; exact id), fun v hv => ?_⟩
      rw [mem_support_pure_iff] at hv
      subst hv
      simp [Derivation.tableRun]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [offlineInteraction_world, FullGame.loggedWith_world]
        have hreal : Derivation.tableRun t (forwardWorld input >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) =
            (liftM (OracleWorld.query input) >>= fun answer =>
              Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) := by
          change Derivation.tableRun t ((liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= _ : M _)) = _
          rw [tableRun_query_bind, tableHandler_world]
          rfl
        rw [hreal]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
          · cases heq
            exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
          · exact SphincsSecurity.Concrete.hashInputs_next_subset input _ u ((ih u).1 x hu)
        · rw [mem_support_bind_iff] at hv ⊢
          obtain ⟨u, -, hu⟩ := hv
          exact ⟨u, by simp, (ih u).2 v hu⟩
      · rw [offlineInteraction_request, FullGame.loggedWith_request]
        have hans := eval_mem_support_tableRun T t ht _ (authenticatedSign_hashOnly published request)
        rw [tableRun_bind]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases allQueries_bind _ _ _ hx with h | ⟨answer, ha, h⟩
          · exact absurd (offlineSign_allQueries T published request _ h) (by simp)
          · rw [offlineSign_support T published request answer ha] at h
            have h' := (ih _).1 x (allQueries_map _ _ _ h)
            refine hashInputs_bind_of_mem _ _ _ hans ?_
            unfold Derivation.tableRun at h' ⊢
            rw [simulateQ_map, hashInputs_map]
            exact h'
        · rw [mem_support_bind_iff] at hv
          obtain ⟨answer, ha, hv⟩ := hv
          rw [offlineSign_support T published request answer ha] at hv
          rw [support_map] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          rw [mem_support_bind_iff]
          refine ⟨_, hans, ?_⟩
          unfold Derivation.tableRun
          rw [simulateQ_map, support_map]
          exact ⟨w, (ih _).2 w hw, rfl⟩
theorem offlineGame_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (adversary : AdversaryP) (x : HashInput)
    (hx : (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineGame T adversary)) :
    x ∈ hashInputs (Derivation.tableRun t (GameWith.idealGame PaddedGame.checker adversary)) := by
  have hkey := eval_mem_support_tableRun T t ht keygen SourceReplay.keygen_hashOnly
  unfold offlineGame at hx
  unfold GameWith.idealGame
  rw [tableRun_bind]
  refine hashInputs_bind_of_mem _ _ _ hkey ?_
  rw [tableRun_bind]
  rcases allQueries_bind _ _ _ hx with h | ⟨_, -, h⟩
  · exact absurd (ticks_allQueries _ _ h) (by simp)
  rcases allQueries_bind _ _ _ h with h | ⟨result, hres, h⟩
  · exact hashInputs_bind_left _ _ ((interaction_queries T t ht _ _).1 x h)
  · exact hashInputs_bind_of_mem _ _ _ ((interaction_queries T t ht _ _).2 result hres)
      (verdict_queries t _ (PaddedGame.verdict_public _ _) x h)
theorem offlineRun_query_mem (adversary : AdversaryP) (q : Nat) (T : Answers) (privateTable : FullGame.FullTable)
    (ht : ∀ c, T (.inr c) = privateTable c) (run : Option (Bool × Nat) × List RefWorld.Domain)
    (hrun : run ∈ support (offlineRun T adversary q))
    (x : HashInput) (hx : (.inl (.inr x) : RefWorld.Domain) ∈ run.2) : x ∈ referenceInputs adversary := by
  have h1 := recorded_mem_allQueries _ _ run hrun _ hx
  have h2 := allQueries_run_subset RefCharged _ q h1
  have h3 := offlineGame_queries T privateTable ht adversary x h2
  rw [← hashInputs_tableRun_sourceRecord privateTable _ (∅, ∅)] at h3
  exact Finset.mem_union_right _ (ChainGraph.program_subset_recordedInputs _ privateTable h3)
end ClaudeWCT.W9.T3.Security.Wots.Ref
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem reference_trace_mem (adversary : AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) (entry : Entry) (he : entry ∈ sample.trace) :
    entry.1 ∈ referenceInputs adversary := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace] at he
  exact Ref.offlineRun_query_mem adversary q _ privateTable (fun _ => rfl) run hrun entry.1 (traceOf_mem he)
end ClaudeWCT.W9.T3.Security.Wots
