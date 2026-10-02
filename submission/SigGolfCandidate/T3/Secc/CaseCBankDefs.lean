import SigGolfCandidate.T3.Secc.CaseCSearch
import SigGolfCandidate.T3.Secc.CreationSharedLaw

/-!
# Stream CC: the certificate bank as a ghost of the actual padded run

The bank runs the actual interaction (adversary world queries, authenticated signing requests, the final
verifier's public queries — SEC's `CreationGame.rest`) on SEC's query-recorded state, and keeps a ghost:

* `targets`: the answers of fresh digest-format public queries made within the budget (adversary or verifier);
* `exposures`: the selected digest outputs of fresh-nonce signing requests on the published cache;
* `reused`: some such signing reused a cached admissible digest row (`Reuse`);
* `dead`: more fresh signings than the forecast horizon (never on a winning run);
* `log`: the requests with their responses (the actual signing log).

`bank_project` / `bank_traced`: forgetting the ghost gives exactly the original query-recorded run, hence the
projection of SEC's traced experiment (`PaddedGame.tracedExperiment`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankDefs : DecidableEq T3.Cache := Classical.decEq _

/-- A digest-format public input. -/
def IsDigestInput (x : HashInput) : Prop :=
  ∃ (rho : Digest) (m : Message) (c : BitVec 32), x = pad64 (digestInput rho m c)

/-- The bank's ghost data. -/
structure Ghost where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  dead : Bool
  log : QueryLog Requests

def Ghost.empty : Ghost := ⟨[], [], false, false, []⟩

abbrev BankState := Ghost × QueryRecorded.State

/-- Charged source count of a recorded state. -/
def countOf (s : QueryRecorded.State) : Nat := s.base.source.1

/-- Lazy tables (private cache, public cache) of a recorded state. -/
def lazyOf (s : QueryRecorded.State) : LazyPrivate.State := s.base.source.2

/-- The forecast horizon: signer selections beyond the proposal length are never needed on a winning run. -/
def horizon : Nat := BPORS.Numeric.proposalLength

/-- A fresh digest-format public query within the budget creates a target. -/
def Birth (budget : Nat) (x : HashInput) (before : QueryRecorded.State) : Prop :=
  IsDigestInput x ∧ (lazyOf before).2 x = none ∧ countOf before < budget

/-- Ghost update of a world query (coins or public hash). -/
noncomputable def ghostWorld (budget : Nat) :
    (input : SphincsSecurity.OracleWorld.Domain) → Ghost → QueryRecorded.State →
      SphincsSecurity.OracleWorld.Range input → Ghost
  | .inl _, g, _, _ => g
  | .inr x, g, before, answer =>
      if Birth budget x before then { g with targets := g.targets ++ [show HashOutput from answer] } else g

/-- A signing request on the published cache whose message nonce is not yet cached. -/
def FreshSigning (published : T3.Cache) (request : Request) (before : QueryRecorded.State) : Prop :=
  request.cache = published ∧ (lazyOf before).1 (.inr (.inl request.message)) = none

/-- Ghost update of a signing request (the record carries the selected digest). -/
noncomputable def ghostSign (published : T3.Cache) (request : Request) (g : Ghost) (before : QueryRecorded.State)
    (record : (Option Signature × Option HashOutput) × QueryRecorded.State) : Ghost :=
  if FreshSigning published request before then
    if horizon ≤ g.exposures.length then
      { g with dead := true, log := g.log ++ [⟨request, record.1.1⟩] }
    else
      { g with exposures := g.exposures ++ record.1.2.toList,
               reused := g.reused || decide (Reuse (lazyOf before).2 (nonceOf (lazyOf record.2) request.message)
                 request.message),
               log := g.log ++ [⟨request, record.1.1⟩] }
  else { g with log := g.log ++ [⟨request, record.1.1⟩] }

/-- **The bank implementation**: the actual source query, with the ghost updated from its outcome. -/
noncomputable def bankImpl (published : T3.Cache) (budget : Nat) :
    QueryImpl LazyPrivate.Interaction (StateT BankState PMF)
  | .inl input => StateT.mk fun st =>
      (liftM (QueryRecorded.run (forwardWorld input) st.2) : PMF _).map fun r =>
        (r.1, (ghostWorld budget input st.1 st.2 r.1, r.2))
  | .inr request => StateT.mk fun st =>
      (liftM (QueryRecorded.run (FullGame.authenticatedRecord published request) st.2) : PMF _).map fun r =>
        (r.1.1, (ghostSign published request st.1 st.2 r, r.2))

theorem bank_query_project (published : T3.Cache) (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (st : BankState) :
    Prod.map id Prod.snd <$> (bankImpl published budget input).run st =
      (liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) st.2) : PMF _) := by
  cases input with
  | inl input =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change PMF.map id _ = _
      rw [PMF.map_id]
      rfl
  | inr request =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      have hsign : Prod.map Prod.fst id <$> QueryRecorded.run (FullGame.authenticatedRecord published request) st.2 =
          QueryRecorded.run (FullGame.authenticatedSign published request) st.2 := by
        rw [← QueryRecorded.run_map, FullGame.authenticatedRecord_erasure]
      change _ = (liftM (QueryRecorded.run (FullGame.authenticatedSign published request) st.2) : PMF _)
      rw [← hsign, liftM_map, ← PMF.monad_map_eq_map]
      rfl

theorem bank_project {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState) :
    Prod.map id Prod.snd <$> (simulateQ (bankImpl published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure, liftM_pure, map_pure]
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [simulateQ_bind, simulateQ_spec_query, QueryRecorded.run_bind, liftM_bind]
      rw [← bank_query_project published budget input st, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2

/-- The bank experiment: SEC's key generation, then the bank run of the interaction and the final verdict. -/
noncomputable def bankExperiment (adversary : AdversaryP) (budget : Nat) : PMF (Bool × BankState) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ (bankImpl generated.1.2 budget) (CreationGame.rest adversary generated.1.1 generated.1.2)).run
    (Ghost.empty, generated.2)

/-- **Forgetting the ghost** gives the traced padded experiment, forgetting its proposal history. -/
theorem bank_traced (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : Bool × BankState => (r.1, r.2.2)) <$> bankExperiment adversary budget =
      (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget := by
  rw [CreationGame.padded_trace_eq, bankExperiment, map_bind, map_bind]
  apply bind_congr
  intro generated
  have hb := bank_project generated.1.2 budget (CreationGame.rest adversary generated.1.1 generated.1.2)
    (Ghost.empty, generated.2)
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  change Prod.map id Prod.snd <$> _ = Prod.map id Prod.snd <$> _
  rw [hb, ht]

end SigGolfCandidate.T3.Security.CaseC
