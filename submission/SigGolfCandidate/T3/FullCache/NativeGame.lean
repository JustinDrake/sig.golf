import SigGolfCandidate.T3.FullCache.NativeBudget
import SigGolfCandidate.T3.FullCache.NativeTables
import SigGolfCandidate.T3.FullCache.NativePublicQueries

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits

-- SEC full-game composition: FullGameVerdict
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed
  SourceQueries.map_allowed SourceQueries.foldlM_allowed SourceQueries.mapM_allowed
  shortHash_nonMac nodeHash_nonMac leafHash_nonMac chain_nonMac ftsLeaf_nonMac forestPk_nonMac
  digest_nonMac digestSearch_nonMac counterSearch_nonMac
macro "verdict_queries" : tactic => `(tactic|
  aesop (config := { maxRuleApplications := 1000 }) (add simp MacGame.NonMac))

theorem recoverChild_nonMac (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 118 → Digest) (level node used : Nat) :
    NonMac (recoverChild index coord leaves values proof level node used) := by
  induction level generalizing node used with
  | zero => unfold recoverChild;verdict_queries
  | succ level ih => unfold recoverChild;verdict_queries
attribute [local aesop safe apply] recoverChild_nonMac

theorem recoverFts_nonMac (sig : Signature) (index : Nat) (chosen : List Selection) :
    NonMac (recoverFts sig index chosen) := by
  unfold recoverFts;verdict_queries
attribute [local aesop safe apply] recoverFts_nonMac

theorem recoverLayer_nonMac (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    NonMac (recoverLayer sig index lay digits) := by
  unfold recoverLayer;verdict_queries
attribute [local aesop safe apply] recoverLayer_nonMac

theorem expandLayers_nonMac (sig : Signature) (index n : Nat) (value : Digest) :
    NonMac (expandLayers sig index n value) := by
  induction n generalizing value with
  | zero => unfold expandLayers;verdict_queries
  | succ n ih => unfold expandLayers;verdict_queries
attribute [local aesop safe apply] expandLayers_nonMac

theorem expand_nonMac (message : Message) (pk : Digest) (sig : Signature) :
    NonMac (expand message pk sig) := by
  unfold expand;verdict_queries
attribute [local aesop safe apply] expand_nonMac

theorem verifyLayers_nonMac (witness : Witness) (index n : Nat) (root : Digest) :
    NonMac (verifyLayers witness index n root) := by
  induction n generalizing root with
  | zero => unfold verifyLayers;verdict_queries
  | succ n ih => unfold verifyLayers;verdict_queries
attribute [local aesop safe apply] verifyLayers_nonMac

theorem verify_nonMac (message : Message) (pk : Digest) (witness : Witness) :
    NonMac (verify message pk witness) := by
  unfold verify;verdict_queries
attribute [local aesop safe apply] verify_nonMac

theorem checkForgery_nonMac (publicKey : Digest) (log : QueryLog Requests) (forgery : Forgery) :
    NonMac (checkForgery publicKey log forgery) := by
  cases forgery <;> unfold checkForgery <;> verdict_queries

/-- Exactly the verdict of the source game, including failed adversary output,
both forgery forms, the signed-message/signature freshness rule and the lifetime. -/
noncomputable def verdict (publicKey : Digest) (result : Option Forgery × QueryLog Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checkForgery publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)

theorem verdict_nonMac (publicKey : Digest) (result : Option Forgery × QueryLog Requests) :
    NonMac (verdict publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checkForgery_nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)

noncomputable def logged (program : OracleComp LazyPrivate.Interaction (Option Forgery)) :
    M (Option Forgery × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl SphincsSecurity.OracleWorld (WriterT (QueryLog Requests) M))+signingOracle) program).run

theorem game_expansion (adversary : Adversary) : game adversary=(do
    let generated ← keygen
    let result ← logged (adversary generated.1 generated.2)
    verdict generated.1 result) := rfl

theorem logged_pure (value : Option Forgery) : logged (pure value)=pure (value,[]) := rfl

theorem logged_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction (Option Forgery)) :
    logged (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => logged (next answer)) := by
  unfold logged
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]

theorem logged_request (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction (Option Forgery)) :
    logged (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (sign request.cache request.message >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> logged (next answer)) := by
  unfold logged
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp [signingOracle,WriterT.run_bind']

/-- RequestHop retains precisely the source signing log, not just the returned forgery. -/
theorem logged_interpretation {State : Type} (handler : QueryImpl T3.Spec (StateT State ProbComp))
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : State) :
    (simulateQ handler (logged program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (sign request.cache request.message)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [logged_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [logged_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [logged_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]

end SigGolfCandidate.T3.Security.FullGame
end


-- SEC full-game composition: FullGameBudget
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def plainResult {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (cache : RCache) : ProbComp α := (simulateQ handler program).run' cache

theorem plainResult_pure {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (value : α) (cache : RCache) : plainResult handler (pure value) cache=pure value := by
  simp [plainResult,StateT.run'_eq]

theorem plainResult_map {α β : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (f : α → β) (program : M α) (cache : RCache) :
    plainResult handler (f <$> program) cache=f <$> plainResult handler program cache := by
  simp [plainResult,StateT.run'_eq,StateT.run_map,Functor.map_map]

theorem plainResult_query_bind {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) (cache : RCache) :
    plainResult handler (liftM (T3.Spec.query input) >>= next) cache=
      ((handler input).run cache >>= fun result => plainResult handler (next result.1) result.2) := by
  simp only [plainResult,simulateQ_bind,simulateQ_spec_query,StateT.run'_eq,StateT.run_bind,map_bind]

theorem countedResult_query_bind {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) (cache : RCache) :
    plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged
        (liftM (T3.Spec.query input) >>= next)) cache=
      ((handler input).run cache >>= fun result =>
        (fun outcome => (outcome.1,queryCharge input+outcome.2)) <$>
          plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged (next result.1)) result.2) := by
  rw [SphincsSecurity.QueryCap.counted_query_bind,plainResult_query_bind]
  apply bind_congr
  intro result
  rw [bind_pure_comp,plainResult_map]
  rfl

/-- The capped source game retains exactly the counted executions within budget.
The statement holds for an arbitrary stateful interpreter, not just independent queries. -/
theorem cap_count_event {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (cache : RCache) (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged program) cache]=
    Pr[fun outcome => ∃ result,outcome=some result ∧ event result.1 |
      plainResult handler (Derivation.cap program budget) cache] := by
  unfold Derivation.cap
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp [Derivation.cap,SphincsSecurity.QueryCap.counted_pure,
        SphincsSecurity.QueryCap.run_pure,plainResult_pure]
  | query_bind input next ih =>
      rw [countedResult_query_bind]
      change _=Pr[_ | plainResult handler (SphincsSecurity.QueryCap.run Derivation.charged
        (liftM (T3.Spec.query input) >>= next) budget) cache]
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : Derivation.charged input
      · rw [if_pos hc]
        cases budget with
        | zero =>
            rw [plainResult_pure,probEvent_pure]
            simp only [reduceCtorEq,false_and,exists_false,if_false]
            apply probEvent_eq_zero
            intro result hresult hevent
            rw [mem_support_bind_iff] at hresult
            obtain ⟨step,_,hresult⟩ := hresult
            rw [support_map] at hresult
            obtain ⟨inner,_,rfl⟩ := hresult
            have := hevent.2
            simp [queryCharge,hc] at this
        | succ remaining =>
            rw [plainResult_query_bind,probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
            apply tsum_congr
            intro step
            apply congrArg
            rw [probEvent_map,← ih step.1 step.2 remaining]
            apply probEvent_ext
            intro result _
            simp only [Function.comp_def,queryCharge,hc,if_true]
            constructor <;> rintro ⟨he,hq⟩ <;> exact ⟨he,by omega⟩
      · rw [if_neg hc,plainResult_query_bind,probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
        apply tsum_congr
        intro step
        apply congrArg
        rw [probEvent_map,← ih step.1 step.2 budget]
        apply probEvent_ext
        intro result _
        simp only [Function.comp_def,queryCharge,hc,if_false,Nat.zero_add]

theorem table_cap_event {α : Type} (table : FullTable) (program : M α) (cache : RCache)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2.1 ≤ budget | run table program (0,cache)]=
    Pr[fun outcome => ∃ result,outcome=some result ∧ event result.1 |
      (simulateQ romImpl (Derivation.tableRun table (Derivation.cap program budget))).run' cache] := by
  have h := cap_count_event (plainHandler table) program cache budget event
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simpa only [plainResult,StateT.run'_eq,probEvent_map,Function.comp_def,Nat.zero_add,plain_run] using h

noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler

noncomputable def countedTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game adversary) (0,∅)

theorem counted_table_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game adversary) ∅ q (·=true)

/-- Real seeded security now reduces to an unrestricted counted table game,
retaining key generation, all requests, both forgery forms and the exact budget event. -/
theorem real_to_counted_table (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound adversary q hq

noncomputable def splitTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game adversary) (0,∅)

theorem table_experiment_split (adversary : Adversary) :
    𝒮[countedTableExperiment adversary]=𝒮[splitTableExperiment adversary] :=
  uniform_table_split_bind (fun table => run table (game adversary) (0,∅))

end SigGolfCandidate.T3.Security.FullGame
end


-- SEC full-game composition: FullGameAuthentication
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable local instance : DecidableEq Region := Classical.decEq _

noncomputable def worldHandler (other : OtherTable) : RequestHop.Public CountState :=
  fun input => baseHandler other (.inl input)

noncomputable def checkContinuation (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict publicKey result.1)).run result.2

noncomputable def realRest (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation other publicKey

noncomputable def idealRest (other : OtherTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation other publicKey

theorem keygenPayload_nonMac : NonMac keygenPayload :=
  SiggolfT3Mac4.Source.Payload.keygenPayload_allowed

theorem base_key_run (other : OtherTable) (i : Fin 2) (state : CountState) :
    (baseHandler other (.inr (SiggolfT3Mac4.Source.keyCoordinate i))).run state=
      pure ((0 : HashOutput),(state.1+1,state.2)) := by
  simp only [baseHandler,tableHandler,countHandler,plainHandler,PrivateTable.fixedImpl,
    StateT.run_mk,queryCharge,Derivation.charged,ite_true]
  dsimp only [HAdd.hAdd,QueryImpl.instHAddSumHAddOracleSpec,QueryImpl.add]
  simp only [StateT.run_pure,pure_bind,joinTable,SiggolfT3Mac4.Source.joinTable_key]


theorem base_overhead_run (other : OtherTable) (state : CountState) :
    (MacGame.overhead (baseHandler other)).run state=pure ((),(state.1+2,state.2)) := by
  simp only [MacGame.overhead,StateT.run_bind,base_key_run,pure_bind,StateT.run_pure,Nat.add_assoc]

theorem source_mac_run (other : OtherTable) (mac : MacTable) (region : Region) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (privateMac region)).run state=
      pure (MacGame.tagAt mac region,(state.1+2,state.2)) := by
  simp only [privateMac,simulateQ_bind,MacGame.source_key_eq,StateT.run_bind,
    base_overhead_run,pure_bind,StateT.run_pure,simulateQ_pure]
  rfl

theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (logged program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [logged_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)

theorem source_rest_run (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← logged (adversary publicKey published)
      verdict publicKey result)).run state=
      realRest other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac publicKey result.1)]
  rfl

/-- Expand actual key generation and the actual logged forgery game. The MAC
derivations cost two and the public cache is retained through the whole execution. -/
theorem fixed_game_expansion (other : OtherTable) (mac : MacTable) (adversary : Adversary) :
    run (joinTable other mac) (game adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game_expansion]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)

/-- The published tag is uniform even though its region was selected during
actual key generation. The conditional key law is the proved four-lane retagging law. -/
theorem refresh_published_mac (other : OtherTable) (adversary : Adversary)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest other (MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))

structure Setup where
  other : OtherTable
  publicKey : Digest
  published : T3.Cache
  state : CountState

noncomputable def setup : ProbComp Setup := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
  let tag ← ($ᵗ HashOutput : ProbComp _)
  pure ⟨other,generated.1.1,⟨tag,generated.1.2⟩,(generated.2.1+2,generated.2.2)⟩

noncomputable def preparedExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest prepared.other (MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state

noncomputable def authenticatedExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest prepared.other adversary prepared.publicKey prepared.published prepared.state

theorem split_experiment_prepared (adversary : Adversary) :
    𝒮[splitTableExperiment adversary]=𝒮[preparedExperiment adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac other adversary generated

theorem checkContinuation_long (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)

theorem rest_authentication_bound (adversary : Adversary) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest prepared.other (MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := MacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]

theorem probEvent_bind_le_add {α β : Type} (source : ProbComp α)
    (left right : α → ProbComp β) (event : β → Prop) (error : ENNReal)
    (h : ∀ value,Pr[event | left value] ≤ Pr[event | right value]+error) :
    Pr[event | source >>= left] ≤ Pr[event | source >>= right]+error := by
  simp only [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value,Pr[=value | source]*(Pr[event | right value]+error) :=
      ENNReal.tsum_le_tsum (fun value => mul_le_mul' le_rfl (h value))
    _ = (∑' value,Pr[=value | source]*Pr[event | right value])+
        (∑' value,Pr[=value | source])*error := by
      simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)

theorem prepared_authentication_bound (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound adversary prepared q)

/-- A full-game reduction, with no independent-tag or authenticated-request
premise on the adversary. Key generation, failed requests, both forgery forms,
all query charges, signed-output freshness and the lifetime limit are retained. -/
theorem real_to_authenticated (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table adversary q hq
  have he := (table_experiment_split adversary).trans (split_experiment_prepared adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound adversary q) le_rfl)

end SigGolfCandidate.T3.Security.FullGame
end


-- SEC full-game composition: FullGameIdealSource
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler

/-- The authenticated source still issues and charges the MAC query on every
request. Only the published cache is eligible for payload signing. -/
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none

noncomputable def authenticatedRecord (published : T3.Cache) (request : Request) :
    M (Option Signature × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then payloadRecord request.cache request.message else pure (none,none)

theorem authenticatedRecord_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> authenticatedRecord published request=authenticatedSign published request := by
  unfold authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure request.cache request.message
  · rfl

noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run

theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl

theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]

theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp

theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl T3.Spec (StateT State ProbComp)) (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]

noncomputable def idealGame (adversary : Adversary) : M Bool := do
  let generated ← keygen
  let result ← loggedWith (authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict generated.1 result

theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : T3.Cache) (request : Request) :
    simulateQ (MacGame.sourceHandler (baseHandler other) mac) (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,MacGame.source_key_eq,bind_assoc,pure_bind]
  unfold MacGame.idealSigner SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [SiggolfT3Mac4.Source.fromCoreRequest]
  have he : SiggolfT3Mac4.Source.fromCoreCache request.cache =
      SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [SiggolfT3Mac4.Source.corePayload,SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      MacGame.simulate_no_mac (baseHandler other) mac _ (MacGame.payload_no_mac request.cache request.message)
  · rfl

theorem ideal_rest_run (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← loggedWith (authenticatedSign published) (adversary publicKey published)
      verdict publicKey result)).run state=idealRest other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => authenticatedSign_interpretation other mac published request
  rw [hs]
  change RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac publicKey result.1)]
  rfl

theorem fixed_ideal_expansion (other : OtherTable) (mac : MacTable) (adversary : Adversary) :
    run (joinTable other mac) (idealGame adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest other adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)

theorem sample_mac_at_bind {α : Type} (region : Region) (next : HashOutput → ProbComp α) :
    𝒮[do let mac ← ($ᵗ MacTable : ProbComp _); next (MacGame.tagAt mac region)]=
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] :=
  MacGame.sample_mac_at_bind region next

noncomputable def idealTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame adversary) (0,∅)

/-- The authenticated experiment is an ordinary source game in the same private
and public tables. Off-cache requests reject, but their MAC query remains charged. -/
theorem ideal_table_authenticated (adversary : Adversary) :
    𝒮[idealTableExperiment adversary]=𝒮[authenticatedExperiment adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))

noncomputable def idealLazyExperiment (adversary : Adversary) :
    ProbComp ((Bool × Nat) × LazyPrivate.State) :=
  LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)) (∅,∅)

/-- The exact budget event is preserved when the ideal source game switches
back to lazy private tables, which the concrete proposal model can inspect. -/
theorem ideal_lazy_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary] := by
  have h := LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]

/-- Full real-game authentication reduction in the lazy source state used for
the adaptive disclosure trace. No authenticated-cache premise is assumed. -/
theorem real_to_ideal_lazy (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated adversary q hq

end SigGolfCandidate.T3.Security.FullGame
end


