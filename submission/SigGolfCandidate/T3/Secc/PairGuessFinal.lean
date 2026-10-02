import SigGolfCandidate.T3.Secc.PairGuessEager

/-!
# B-PAIR (final): `pair_guess_bound` and `one_guess_bound` on SECC's shared law

* `pairExperiment` (R3's eager tables, F2's samplers) is G's canonical experiment: uniform chain seeds, other
  private halves, labels, residual table, and — innermost — uniform FTS secrets (`pairExperiment_le`);
* per `ω` the world bounds `fts_pair_le` / `fts_one_le` apply;
* the transport `shared_le_pair` brings the shared-law events `PairGuess` / `OneGuess` (actual run, actual log,
  final verifier's entries) to the reference experiment.
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Samplers -/

/-- Two uniform samplers of the same finite type have the same law. -/
theorem uniform_congr {X : Type} [Fintype X] (I J : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = 𝒮[(@uniformSample X J : ProbComp X)] := by
  apply evalSPMF_ext
  intro x
  rw [@probOutput_uniformSample X I _ x, @probOutput_uniformSample X J _ x]

theorem bind_uniform_congr {X β : Type} [Fintype X] (I J : SampleableType X) (f : X → ProbComp β) :
    𝒮[(@uniformSample X I : ProbComp X) >>= f] = 𝒮[(@uniformSample X J : ProbComp X) >>= f] := by
  rw [evalSPMF_bind, evalSPMF_bind, uniform_congr I J]

/-- The uniform FTS secrets are the world's initial completion. -/
theorem uniform_secretsLaw (I : SampleableType (FtsCoord → Digest)) (fts : FtsCoord → Digest) :
    Pr[= fts | (@uniformSample (FtsCoord → Digest) I : ProbComp _)] = Pr[= fts | secretsLaw] := by
  rw [@probOutput_uniformSample _ I _ fts, secretsLaw, SPMF.probOutput_eq_apply,
    UniformTableCompletion.complete_apply]
  have hmem : ∀ coordinate, fts coordinate ∈ init.allowed coordinate := fun _ => Finset.mem_univ _
  rw [if_pos hmem]
  have hcard : (∏ coordinate, (init.allowed coordinate).card) = Fintype.card (FtsCoord → Digest) := by
    change (∏ _coordinate : FtsCoord, (Finset.univ : Finset Digest).card) = _
    rw [Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fun]
  rw [hcard]

/-! ## Joining the secrets -/

/-- Chain seeds and FTS secrets as G's secrets. -/
def joinSecrets (seeds : ChainGraph.Seeds) (fts : FtsCoord → Digest) : CanonGraph.Secrets
  | .inl a => seeds a
  | .inr p => fts (ofLeafPos p)

theorem omega_secrets {U : Finset HashInput} (ω : Omega U) (fts : FtsCoord → Digest) :
    ω.secrets fts = joinSecrets ω.seeds fts := by
  funext i
  cases i <;> rfl

theorem joinSecrets_bijective :
    Function.Bijective (fun p : ChainGraph.Seeds × (FtsCoord → Digest) => joinSecrets p.1 p.2) := by
  constructor
  · rintro ⟨s1, f1⟩ ⟨s2, f2⟩ h
    have h1 : s1 = s2 := funext fun a => congrFun h (.inl a)
    have h2 : f1 = f2 := funext fun f => congrFun h (.inr (toLeafPos f))
    rw [h1, h2]
  · intro s
    refine ⟨(fun a => s (.inl a), fun f => s (.inr (toLeafPos f))), ?_⟩
    funext i
    cases i <;> rfl

theorem eager_omega {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (seeds : ChainGraph.Seeds)
    (other : CanonGraph.OtherHalves) (labels : CanonGraph.Labels) (residual : U → HashOutput)
    (fts : FtsCoord → Digest) :
    Wots.eagerAnswers U (CanonGraph.privateEquiv.symm (joinSecrets seeds fts, other))
        (CanonGraph.programmed U hU (joinSecrets seeds fts) labels residual) =
      Omega.answers hU ⟨seeds, other, labels, residual⟩ fts := by
  unfold Omega.answers
  rw [omega_secrets]
  funext query
  rcases query with (n | x) | c <;> rfl


/-! ## The reference experiment is G's canonical experiment with the FTS secrets innermost -/

section Chain
noncomputable local instance instSampleableTypeSeeds_pairGuessFinal : SampleableType ChainGraph.Seeds := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallFtsCoordDigest_pairGuessFinal : SampleableType (FtsCoord → Digest) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdSeedsForallFtsCoordDigest_pairGuessFinal : SampleableType (ChainGraph.Seeds × (FtsCoord → Digest)) := SampleableType.ofFintype _
attribute [local instance] CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves
  CanonGraph.instSampleableTypeLabels_1

theorem secrets_bind {R : Type} (next : CanonGraph.Secrets → ProbComp R) :
    𝒮[($ᵗ CanonGraph.Secrets : ProbComp _) >>= next] =
      𝒮[($ᵗ ChainGraph.Seeds : ProbComp _) >>= fun seeds => ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun fts =>
        next (joinSecrets seeds fts)] := by
  have hb := evalSPMF_map_bijective_uniform_cross (α := ChainGraph.Seeds × (FtsCoord → Digest))
    (β := CanonGraph.Secrets) (fun p => joinSecrets p.1 p.2) joinSecrets_bijective
  have hp := FullGame.uniform_product (A := ChainGraph.Seeds) (B := FtsCoord → Digest)
  calc _ = 𝒮[((fun p : ChainGraph.Seeds × (FtsCoord → Digest) => joinSecrets p.1 p.2) <$>
          ($ᵗ (ChainGraph.Seeds × (FtsCoord → Digest)) : ProbComp _)) >>= next] := by
        rw [evalSPMF_bind, evalSPMF_bind, hb]
    _ = 𝒮[($ᵗ (ChainGraph.Seeds × (FtsCoord → Digest)) : ProbComp _) >>= fun p => next (joinSecrets p.1 p.2)] := by
        rw [bind_map_left]
    _ = 𝒮[(($ᵗ ChainGraph.Seeds : ProbComp _) >>= fun a => ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun b =>
          pure (a, b)) >>= fun p => next (joinSecrets p.1 p.2)] := by
        rw [evalSPMF_bind, evalSPMF_bind, hp]
    _ = _ := by simp only [bind_assoc, pure_bind]

theorem canon_subset (adversary : AdversaryP) : CanonGraph.canonInputs ⊆ Wots.referenceInputs adversary :=
  CanonGraph.canonInputs_subset_publicUniverse.trans (referenceInputs_universe' adversary)

/-- **The reference experiment, rearranged**: R3's tables are G's canonical experiment (`tables_bind`) with the
secrets split into chain seeds and FTS secrets, the FTS secrets drawn last. -/
theorem pairExperiment_eq (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] =
      𝒮[($ᵗ ChainGraph.Seeds : ProbComp _) >>= fun seeds =>
        ($ᵗ CanonGraph.OtherHalves : ProbComp _) >>= fun other =>
        ($ᵗ CanonGraph.Labels : ProbComp _) >>= fun labels =>
        (@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _) >>=
          fun residual =>
        ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun fts =>
          (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
              (Omega.answers (canon_subset adversary) ⟨seeds, other, labels, residual⟩ fts, run.2.1, run.2.2)) <$>
            pairRun (Omega.answers (canon_subset adversary) ⟨seeds, other, labels, residual⟩ fts) adversary] := by
  let K : FullGame.FullTable → (Wots.referenceInputs adversary → HashOutput) →
      ProbComp (Answers × QueryLog Requests × List Wots.Entry) := fun privateTable publicTable =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
        (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable, run.2.1, run.2.2)) <$>
      pairRun (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable) adversary
  have h1 : 𝒮[pairExperiment adversary] =
      𝒮[(@uniformSample FullGame.FullTable CanonGraph.instSampleableTypeFullTable_canonGraph : ProbComp _) >>=
        fun privateTable => (@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _) >>=
          fun publicTable => K privateTable publicTable] := by
    unfold pairExperiment
    rw [bind_uniform_congr Wots.Ref.instSampleableTypeFullTable_wotsTransportCompletion
      CanonGraph.instSampleableTypeFullTable_canonGraph]
  rw [h1, CanonGraph.tables_bind (Wots.referenceInputs adversary) (canon_subset adversary) K, secrets_bind]
  apply evalSPMF_bind_congr_left
  intro seeds
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr_left
  intro other
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr_left
  intro labels
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr_left
  intro residual
  apply evalSPMF_bind_congr_left
  intro fts
  simp only [K, eager_omega]

/-- The inner FTS expectation of a reference-experiment event is the `ftsRun` probability. -/
theorem inner_fts_eq {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U) (adversary : AdversaryP)
    (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun fts =>
        (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (Omega.answers hU ω fts, run.2.1, run.2.2)) <$>
          pairRun (Omega.answers hU ω fts) adversary] =
      Pr[fun x => E (Omega.answers hU ω x.1, x.2.2.1, x.2.2.2) | ftsRun hU ω adversary] := by
  unfold ftsRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro fts
  rw [uniform_secretsLaw, probEvent_map, probEvent_map]
  rfl

theorem pairExperiment_event_le (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop)
    (bound : ENNReal)
    (h : ∀ ω : Omega (Wots.referenceInputs adversary),
      Pr[fun x => E (Omega.answers (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] ≤ bound) :
    Pr[E | pairExperiment adversary] ≤ bound := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_eq adversary)]
  apply probEvent_bind_le_of_forall_le
  intro seeds _
  apply probEvent_bind_le_of_forall_le
  intro other _
  apply probEvent_bind_le_of_forall_le
  intro labels _
  apply probEvent_bind_le_of_forall_le
  intro residual _
  rw [inner_fts_eq]
  exact h ⟨seeds, other, labels, residual⟩

/-- **The pair bound on the reference experiment.** -/
theorem pairExperiment_pair (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => s.2.2.length ≤ q ∧ PairGuessIn s.1 s.2.1 s.2.2 | pairExperiment adversary] ≤ pairTerm q :=
  pairExperiment_event_le adversary _ _ fun ω => fts_pair_le (canon_subset adversary) ω adversary q

/-- **The one-guess bound on the reference experiment.** -/
theorem pairExperiment_one (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => s.2.2.length ≤ q ∧ OneGuessIn s.1 s.2.1 s.2.2 | pairExperiment adversary] ≤ guessTerm q :=
  pairExperiment_event_le adversary _ _ fun ω => fts_one_le (canon_subset adversary) ω adversary q

end Chain

/-! ## The guess events read the answers only on short queries -/

section Short
open SourceQueries

theorem digest_short (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) Wots.Ref.ShortQuery := by
  unfold digest publicHash
  refine (allQueriesSatisfy_query_iff _ _).mpr ?_
  apply Wots.Ref.short_of_le
  simp [digestInput, SphincsSecurity.bytesLE_length]

theorem digestSearch_short (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) Wots.Ref.ShortQuery := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold digestSearch
      apply bind_allowed Wots.Ref.ShortQuery (digest_short _ _ _)
      intro output
      split
      · exact pure_allowed _ _
      · exact ih _

theorem signedOutput_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (message : Message) (signature : Signature) :
    signedOutput A message signature = signedOutput T message signature := by
  unfold signedOutput
  rw [eval_congr_allowed (digestSearch_short _ _ _ _) h]

theorem secretAt_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (f : FtsCoord) : secretAt A f = secretAt T f := by
  unfold secretAt CanonGraph.ftsSecretOf
  have hp : evalWithAnswerFn A (privatePair 8 (toLeafPos f).coord.val (toLeafPos f).index.val 0
      ((toLeafPos f).leaf.val / 2)) = evalWithAnswerFn T (privatePair 8 (toLeafPos f).coord.val (toLeafPos f).index.val 0
      ((toLeafPos f).leaf.val / 2)) := by
    apply eval_congr_allowed _ h
    unfold privatePair privateHash
    exact bind_allowed _ ((allQueriesSatisfy_query_iff _ _).mpr trivial) fun _ => pure_allowed _ _
  simp only [hp]

theorem disclosed_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (log : QueryLog Requests) (f : FtsCoord)
    (hd : Disclosed A log f) : Disclosed T log f := by
  obtain ⟨entry, he, signature, output, hs, ho, hf⟩ := hd
  exact ⟨entry, he, signature, output, hs, by rw [← signedOutput_short h]; exact ho, hf⟩

theorem guessedIn_short {A T : Answers} (h : Wots.Ref.ShortAgree A T) (log : QueryLog Requests)
    (entries : List Wots.Entry) (f : FtsCoord) (hg : GuessedIn A log entries f) : GuessedIn T log entries f := by
  obtain ⟨hnd, answer, he⟩ := hg
  refine ⟨fun hd => hnd (disclosed_short h.symm log f hd), answer, ?_⟩
  rw [← secretAt_short h]
  exact he

theorem guessedIn_mono (A : Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (f : FtsCoord) (hg : GuessedIn A log entries f) :
    GuessedIn A log entries' f :=
  ⟨hg.1, hg.2.elim fun answer he => ⟨answer, hsub _ he⟩⟩

end Short

/-! ## Main results on SECC's shared law -/

/-- **Two or more guessed secrets** (BP-B §2.2): the final verifier of the actual run queried the honest leaf
inputs of two distinct FTS secrets that no returned signature of the actual log opened. -/
theorem pair_guess_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PairGuess adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      pairTerm q := by
  refine (shared_le_pair adversary q hq PairGuessIn ?_ ?_).trans (pairExperiment_pair adversary q)
  · rintro A T log entries h ⟨f, g, hfg, hf, hg⟩
    exact ⟨f, g, hfg, guessedIn_short h log entries f hf, guessedIn_short h log entries g hg⟩
  · rintro A log entries entries' hsub ⟨f, g, hfg, hf, hg⟩
    exact ⟨f, g, hfg, guessedIn_mono A log entries entries' hsub f hf, guessedIn_mono A log entries entries' hsub g hg⟩

/-- **One guessed secret** (the single-guess interface): the final verifier of the actual run queried the honest
leaf input of an FTS secret that no returned signature of the actual log opened. -/
theorem one_guess_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ OneGuess adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      guessTerm q := by
  refine (shared_le_pair adversary q hq OneGuessIn ?_ ?_).trans (pairExperiment_one adversary q)
  · rintro A T log entries h ⟨f, hf⟩
    exact ⟨f, guessedIn_short h log entries f hf⟩
  · rintro A log entries entries' hsub ⟨f, hf⟩
    exact ⟨f, guessedIn_mono A log entries entries' hsub f hf⟩
end SigGolfCandidate.T3.Security.BPair
