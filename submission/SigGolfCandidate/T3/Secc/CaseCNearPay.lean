import SigGolfCandidate.T3.Secc.CaseCNear
import SigGolfCandidate.T3.Secc.CaseCNearHandlers

/-!
# Stream CC: the near payoff on the lazy world's final state, and `1 ≤ payoff` on the event

* `pairRun_log_honest` / `pairRun_entries_honest`: in the reference run on a table `T`, every logged signature is the
  honest one and every entry carries `T`'s answer;
* `nearPayoff q r`: the indicator of an alive memory (births ≤ q, exposures ≤ the horizon) with an admissible birth
  near-covered by the exposures;
* `payoff_of_ghosts`: on a world result satisfying `NearIn` (with `T`), given the world ghost facts (returned outputs
  are exposures; digest-row entries are cached births or signer trial rows; trial rows are honest signer queries;
  births ≤ entries; exposures ≤ log), the probes contain a guess and `1 ≤ nearPayoff q r`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The reference run on a fixed table -/

theorem interactionT_honest (T : Correctness.Answers) (published : T3.Cache) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (BPair.interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [BPair.interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [BPair.interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [BPair.interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [BPair.interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he

theorem entriesOf_honest (T : Correctness.Answers) (qs : List T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq

/-- **The reference run is honest**: logged signatures and entry answers are `T`'s. -/
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP) (r : Bool × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (BPair.pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold BPair.pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he

/-! ## The payoff -/

/-- **The near payoff**: an alive memory with an admissible birth near-covered by the exposures. -/
noncomputable def nearPayoff (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × BPair.WStateL) : ENNReal :=
  if r.2.memory.births.length ≤ q ∧ r.2.memory.exposures.length ≤ BPORS.Numeric.proposalLength ∧
      ∃ N ∈ r.2.memory.births, admissible (selections N) = true ∧ NearCoveredBy r.2.memory.exposures N then 1 else 0

/-- **`1 ≤ nearPayoff` on the near event**, from the world ghost facts. -/
theorem payoff_of_ghosts (q : Nat) (T : Correctness.Answers) (published : T3.Cache)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × BPair.WStateL)
    (hlog : ∀ e ∈ r.1.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1))
    (hent : ∀ e ∈ r.1.2.2, e.2 = T (.inl (.inr e.1)))
    (hexp : ∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
      BPair.signedOutput T entry.1.message σ = some output → output ∈ r.2.memory.exposures)
    (hrows : ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ BPair.digestInputs →
      a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)
    (htrials : ∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1,
      (.inl (.inr x) : T3.Spec.Domain) ∈ queried T (FullGame.authenticatedSign published entry.1))
    (hbirths : r.2.memory.births.length ≤ r.1.2.2.length)
    (hexplen : r.2.memory.exposures.length ≤ r.1.2.1.length)
    (hq : r.1.2.2.length ≤ q) (hP : NearIn T r.1.2.1 r.1.2.2) : 1 ≤ nearPayoff q r := by
  obtain ⟨m, w, N, f, hx, hN, hS, hgood, hsd, hlen, hf, hguess, hdis⟩ := hP
  -- the forgery digest is a birth
  have hbirth : N ∈ r.2.memory.births := by
    rcases hrows _ N hx (BPair.digestInput_mem _ _ _) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨entry, he, hqe⟩ := htrials _ ht
      exact caseC_not_signer_eval T published r.1.2.1 hlog m w N hN hS hgood hsd entry he hqe
  -- twenty openings are exposed
  have hcov : NearCoveredBy r.2.memory.exposures N := by
    refine ⟨f, hf, fun g hg hne => ?_⟩
    obtain ⟨entry, he, σ, output, hσ, hout, hgo⟩ := hdis g hg hne
    exact ⟨output, hexp entry he σ output hσ hout, hgo⟩
  unfold nearPayoff
  rw [if_pos ⟨hbirths.trans hq, hexplen.trans (hlen.trans (by unfold BPORS.Numeric.proposalLength; norm_num)),
    N, hbirth, hS.2.1, hcov⟩]

end SigGolfCandidate.T3.Security.CaseC
