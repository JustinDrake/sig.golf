import SigGolfCandidate.T3.FullCache.SourcePrelude

namespace SigGolfCandidate.T3.Security.RequestHop
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {State : Type}
abbrev Public (State : Type) := QueryImpl SphincsSecurity.OracleWorld (StateT State ProbComp)
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)

/-- Full adaptive request log, with arbitrary world/private/cost state in the handlers. -/
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state

theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl

theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl

theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl

theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2

theorem probEvent_bind_le_add_bind {α β γ : Type} (mx : ProbComp α)
    (left right : α → ProbComp β) (badRun : α → ProbComp γ)
    (event : β → Prop) (bad : γ → Prop)
    (hle : ∀ value ∈ support mx,Pr[event | left value] ≤
      Pr[event | right value]+Pr[bad | badRun value]) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right]+Pr[bad | mx >>= badRun] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hv : value ∈ support mx
  · rw [← mul_add]
    exact mul_le_mul' le_rfl (hle value hv)
  · simp [probOutput_eq_zero_of_not_mem_support hv]

def BadIn (bad : Request → Prop) (limit : Nat) (log : QueryLog Requests) : Prop :=
  ∃ entry ∈ log.take limit,bad entry.1

/-- Identical until a bad request. No syntactic lifetime restriction is assumed:
only the scored continuation must reject transcripts longer than the remaining limit. -/
theorem identical_until_bad {α β : Type} (world : Public State) (bad : Request → Prop)
    (left right : Signer State) (hagree : ∀ request,¬bad request → left request=right request)
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ (limit : Nat) (state : State) (cont : ((α × QueryLog Requests) × State) → ProbComp β)
      (event : β → Prop),
      (∀ result,limit < result.1.2.length → Pr[event | cont result]=0) →
      Pr[event | run world left program state >>= cont] ≤
        Pr[event | run world right program state >>= cont]+
          Pr[fun result => BadIn bad limit result.1.2 | run world right program state] := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro limit state cont event _
      exact le_self_add
  | query_bind input next ih =>
      intro limit state cont event hlong
      cases input with
      | inl input =>
          rw [run_public,run_public,bind_assoc,bind_assoc]
          apply probEvent_bind_le_add_bind
          intro result _
          exact ih result.1 limit result.2 cont event hlong
      | inr request =>
          by_cases hbad : bad request
          · cases limit with
            | zero =>
                refine le_trans (le_of_eq ?_) zero_le
                rw [probEvent_eq_zero_iff]
                intro value hv
                rw [run_request,bind_assoc,mem_support_bind_iff] at hv
                obtain ⟨head,_,hv⟩ := hv
                rw [bind_map_left,mem_support_bind_iff] at hv
                obtain ⟨tail,_,hv⟩ := hv
                have hz := hlong ((tail.1.1,⟨request,head.1⟩::tail.1.2),tail.2) (by simp)
                rw [probEvent_eq_zero_iff] at hz
                exact hz value hv
            | succ limit =>
                have hone : Pr[fun result => BadIn bad (limit+1) result.1.2 |
                    run world right (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state]=1 := by
                  rw [probEvent_eq_one_iff]
                  refine ⟨by simp,?_⟩
                  intro result hr
                  rw [run_request,mem_support_bind_iff] at hr
                  obtain ⟨head,_,hr⟩ := hr
                  rw [support_map] at hr
                  obtain ⟨tail,_,rfl⟩ := hr
                  exact ⟨⟨request,head.1⟩,by simp,hbad⟩
                exact probEvent_le_one.trans (hone.symm.le.trans le_add_self)
          · rw [run_request,run_request,hagree request hbad,bind_assoc,bind_assoc]
            apply probEvent_bind_le_add_bind
            intro head _
            rw [bind_map_left,bind_map_left,probEvent_map]
            refine (ih head.1 (limit-1) head.2 _ event (fun result hr => hlong _ (by simp;omega))).trans
              (add_le_add le_rfl (probEvent_mono fun result _ hr => ?_))
            obtain ⟨entry,he,hbadEntry⟩ := hr
            cases limit with
            | zero => simp at he
            | succ limit =>
                simp only [Nat.add_sub_cancel] at he
                exact ⟨entry,by simp [he],hbadEntry⟩

end SigGolfCandidate.T3.Security.RequestHop
