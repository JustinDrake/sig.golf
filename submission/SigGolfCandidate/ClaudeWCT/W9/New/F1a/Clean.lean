import SigGolfCandidate.T3M.Final.Relabel
import SigGolfCandidate.T3M.Final.RO
import SigGolfCandidate.T3M.Final.Pipeline
import SigGolfCandidate.T3M.Final.Source
import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.Legacy.Security

set_option Elab.async false
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize privateInput)
open SigGolfCandidate.T3.Security (forwardWorld)
open SphincsSecurity (OracleWorld)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
theorem calls_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)}
    {X : OracleComp HashSpec γ} {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => (r.value, r.hashCalls)) <$> run = (fun p => (F p.1, p.2)) <$> SigGolfCandidate.Bridge.countCalls X := by
  have h2 := congrArg (fun x => (fun t : Option β × Nat × Nat => (t.1, t.2.1)) <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2, ← countCalls_eq, ← countBoth_calls, Functor.map_map]
theorem ofQ_countCalls {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (SigGolfCandidate.Bridge.countCalls (relabel toQ X)) = SigGolfCandidate.Bridge.countCalls X := by
  rw [relabel_countCalls, relabel_ofQ_toQ h]
def costW : AW.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1
theorem countHashQueries_eq {α : Type} (X : OracleComp SphincsSecurity.OracleWorld α) :
    SphincsSecurity.countHashQueries X = countFrom costW X 0 := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [SphincsSecurity.countHashQueries_query_bind, countFrom_query_bind]
    refine bind_congr fun u => ?_
    rw [ih u, countFrom_shift _ _ (0 + costW t)]
    rcases t with n | x <;> simp [costW]
theorem derivation_realize {α : Type} (secret : BitVec 256) (p : M α) :
    SigGolfCandidate.T3.Derivation.realize (privateInput secret) p = realize secret p := by
  unfold SigGolfCandidate.T3.Derivation.realize realize
  congr 1
  funext q
  rcases q with q | c <;> rfl
theorem sampleSecretKey_eq : (sampleSecretKey : ProbComp SecretKey) = SphincsSecurity.sampleMasterSeed := rfl
lemma relabel_ofQ_countCalls {α : Type} (X : OracleComp AHash α) (hX : AllQ Aligned X) :
    relabel ofQ (SigGolfCandidate.Bridge.countCalls (relabel toQ X)) = SigGolfCandidate.Bridge.countCalls X :=
  ofQ_countCalls hX
lemma relabelW_liftM_proj {α β γ : Type} (Y : OracleComp HashSpec α) (proj : α → β)
    (K' : β → OracleComp World γ) (K : α → OracleComp World γ) (hK : ∀ r, K r = K' (proj r)) :
    relabelW ofQ ((liftM Y : OracleComp World α) >>= K) =
      (liftM (relabel ofQ (proj <$> Y)) : OracleComp AW β) >>= fun p => relabelW ofQ (K' p) := by
  rw [relabelW_bind, relabelW_liftM_hash, relabel_map, liftM_map, bind_map_left]
  simp only [hK]
lemma bind_eq_of_proj {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (Y : OracleComp spec α)
    (proj : α → β) (K' : β → OracleComp spec γ) (K : α → OracleComp spec γ)
    (hK : ∀ r, K r = K' (proj r)) : Y >>= K = (proj <$> Y) >>= K' := by
  rw [bind_map_left]; exact bind_congr hK
lemma liftM_map_bind {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (X : OracleComp spec α)
    (f : α → β) (K : β → OracleComp (unifSpec + spec) γ) :
    (liftM (f <$> X) : OracleComp (unifSpec + spec) β) >>= K =
      (liftM X : OracleComp (unifSpec + spec) α) >>= fun x => K (f x) := by
  rw [liftM_map, bind_map_left]
def recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (value : Option (Bytes sizes.signature)) (calls : ℕ) : Transcript sizes :=
  { signed := match value with
      | none => T.signed
      | some signature => (message, signature) :: T.signed
    signingRequests := T.signingRequests + 1
    hashCalls := T.hashCalls + calls }
lemma record_eq_recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (r : RunResult (Bytes sizes.signature)) :
    T.record message r = recordVC T message r.value r.hashCalls := rfl
lemma ofQ_injective : Function.Injective ofQ := fun x y h => by
  rw [← toQ_ofQ x, ← toQ_ofQ y, h]
theorem realize_pure' {α : Type} (secret : SecretKey) (a : α) :
    realize secret (pure a : M α) = pure a := rfl
theorem realize_forward_bind {α : Type} (secret : SecretKey) (t : OracleWorld.Domain)
    (g : OracleWorld.Range t → M α) :
    realize secret ((forwardWorld t : M _) >>= g) =
      (liftM (OracleWorld.query t) : OracleComp OracleWorld _) >>= fun a => realize secret (g a) := by
  simp only [realize, simulateQ_bind, forwardWorld, simulateQ_spec_query]
  rfl
def RFin (r : AttackResult) (b : Bool × ℕ) : Prop :=
  r.won = true → b.1 = true ∧ b.2 = r.hashCalls
lemma rfin_false (h : ℕ) (b : Bool × ℕ) : RFin ⟨false, h⟩ b := fun h => by cases h
lemma liftM_countFrom_shift {α : Type} (X : OracleComp AHash α) (c : ℕ) :
    (liftM (countFrom (fun _ => 1) X c) : OracleComp AW (α × ℕ)) =
      (fun p => (p.1, c + p.2)) <$> (liftM (SigGolfCandidate.Bridge.countCalls X) : OracleComp AW (α × ℕ)) := by
  rw [countFrom_shift, liftM_map]
  rfl
lemma probEvent_bind_le' {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {E₁ : β → Prop} {E₂ : γ → Prop}
    (h : ∀ x, Pr[E₁ | f x] ≤ Pr[E₂ | g x]) : Pr[E₁ | mx >>= f] ≤ Pr[E₂ | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
theorem value_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => r.value) <$> run = F <$> X := by
  have h2 := congrArg (fun x => Prod.fst <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2]
  conv_rhs => rw [← fst_countBoth X]
  rw [Functor.map_map]
theorem allSucceed_foldlM (Pr : Message → OracleComp HashSpec HonestResult) (L : List Message)
    (s : HonestSummary) :
    HonestSummary.allSucceed <$> L.foldlM (fun summary message => do
        let result ← Pr message
        return (⟨summary.allSucceed && result.success,
          fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) s =
      foldAll L (fun m => HonestResult.success <$> Pr m) s.allSucceed := by
  induction L generalizing s with
  | nil => simp [foldAll]
  | cons m L ih =>
    rw [List.foldlM_cons, foldAll_cons, map_bind, bind_assoc, bind_map_left]
    refine bind_congr fun r => ?_
    rw [pure_bind, ih]
theorem allSucceed_allMessages (sub : Submission) (sk : SecretKey) :
    HonestSummary.allSucceed <$> sub.allMessages sk =
      foldAll (Finset.univ : Finset Message).toList
        (fun m => HonestResult.success <$> sub.honest sk m) true := by
  unfold Submission.allMessages
  exact allSucceed_foldlM _ _ {}
theorem mrealize_foldAll {κ : Type} (sk : BitVec 256) (L : List κ) (Pr : κ → M Bool) (b : Bool) :
    mrealize sk (foldAll L Pr b) = foldAll L (fun k => mrealize sk (Pr k)) b := by
  induction L generalizing b with
  | nil => rfl
  | cons k L ih =>
    rw [foldAll_cons, foldAll_cons, mrealize_bind]
    exact bind_congr fun c => ih _
noncomputable def msgs : List SigGolfCandidate.T3.Message := (Finset.univ : Finset SigGolfCandidate.T3.Message).toList
def machineAnswers (hash : Hash) (sk : BitVec 256) : SigGolfCandidate.T3.Correctness.Answers :=
  fun q => evalWithAnswerFn hash (machineHandler sk q)
theorem eval_mrealize {α : Type} (hash : Hash) (sk : BitVec 256) (p : M α) :
    evalWithAnswerFn hash (mrealize sk p) = evalWithAnswerFn (machineAnswers hash sk) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [mrealize_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    have hq : evalWithAnswerFn hash (mrealize sk (liftM (Spec.query q) : M _)) = machineAnswers hash sk q := by
      rw [mrealize, simulateQ_spec_query]; rfl
    have hq' : evalWithAnswerFn (machineAnswers hash sk) (liftM (Spec.query q) : M _) =
        machineAnswers hash sk q := simulateQ_spec_query _ _
    rw [hq, hq']
    exact ih _
theorem allQ_foldAll' {κ : Type} {Q : Spec.Domain → Prop} (L : List κ) (Pr : κ → M Bool)
    (h : ∀ k, AllQueriesSatisfy (Pr k) Q) (b : Bool) : AllQueriesSatisfy (foldAll L Pr b) Q := by
  unfold foldAll
  exact SigGolfCandidate.T3M.allQ_foldlM _ _ (fun _ k => SigGolfCandidate.T3M.allQ_map _ (h k)) _
theorem withRandomOracle_map' {α β : Type} (f : α → β) (oa : OracleComp HashSpec α) :
    withRandomOracle (f <$> oa) = f <$> withRandomOracle oa := by
  unfold withRandomOracle
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]
theorem mrealize_query_coin (sk : BitVec 256) (n : ℕ) :
    mrealize sk (liftM (Spec.query (.inl (.inl n))) : M (Fin (n + 1))) = pure 0 := by
  simp [mrealize, machineHandler]
theorem mrealize_query_public (sk : BitVec 256) (input : List UInt8) :
    mrealize sk (liftM (Spec.query (.inl (.inr input))) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ input)) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]
theorem mrealize_query_private (sk : BitVec 256) (c : SigGolfCandidate.T3.Coordinate) :
    mrealize sk (liftM (Spec.query (.inr c)) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ (privateInput sk c))) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]
theorem countBlocks_query_bind {α : Type} (x : Query) (g : BitVec 256 → OracleComp HashSpec α) :
    countBlocks ((liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= g) =
      (liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= fun a =>
        (fun r => (r.1, x.blocks + r.2)) <$> countBlocks (g a) := by
  unfold countBlocks
  rw [countWith_bind, countWith_query, bind_map_left]
theorem mrealize_countBlocks {α : Type} (sk : BitVec 256) {p : M α}
    (h : AllQueriesSatisfy p SigGolfCandidate.T3.Cost.GoodQuery) :
    countBlocks (mrealize sk p) = mrealize sk (SigGolfCandidate.T3.Cost.countBlocks p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [mrealize_bind]
    unfold SigGolfCandidate.T3.Cost.countBlocks
    rw [SigGolfCandidate.T3.Cost.countWith_bind, SigGolfCandidate.T3.Cost.countWith_query, mrealize_bind, mrealize_map, bind_map_left]
    rcases q with (n | input) | c
    · rw [mrealize_query_coin, pure_bind, pure_bind]
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k (0 : Fin (n + 1))) = SigGolfCandidate.T3.Cost.countBlocks (k (0 : Fin (n + 1)))
        from rfl, ← ih (0 : Fin (n + 1)) (h.2 _)]
      simp only [SigGolfCandidate.T3.Cost.weight, Nat.zero_add]
      exact (id_map _).symm
    · rw [mrealize_query_public, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k a) = SigGolfCandidate.T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ h.1]
      rfl
    · rw [mrealize_query_private, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k a) = SigGolfCandidate.T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ (privateInput_aligned sk c), SigGolfCandidate.T3.Cost.private_realization_weight]
theorem allQ_countWith {α : Type} {Q : Spec.Domain → Prop} (wt : SigGolfCandidate.T3.Cost.Query → ℕ) {p : M α}
    (h : AllQueriesSatisfy p Q) : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countWith wt p) Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [SigGolfCandidate.T3.Cost.countWith_bind, SigGolfCandidate.T3.Cost.countWith_query, bind_map_left]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨h.1, fun u => SigGolfCandidate.T3M.allQ_map _ (ih u (h.2 u))⟩
set_option maxRecDepth 100000 in
theorem withRandomOracle_mrealize {α : Type} (sk : SecretKey) {Y : M α}
    (hgood : AllQueriesSatisfy Y SigGolfCandidate.T3.Cost.GoodQuery) (hhash : AllQueriesSatisfy Y isHash) :
    withRandomOracle (mrealize sk Y) = Prod.fst <$> SigGolfCandidate.T3.Sampling.roRun sk Y ∅ := by
  unfold withRandomOracle SigGolfCandidate.T3.Sampling.roRun
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right, StateT.run'_eq]
theorem eval_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) (hash : Hash) :
    (evalWithAnswerFn hash run).value = F (evalWithAnswerFn hash X) ∧
      (evalWithAnswerFn hash run).hashCompressions = (evalWithAnswerFn hash (countBlocks X)).2 := by
  have h1 := congrArg (evalWithAnswerFn hash) h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map] at h1
  simp only [Prod.mk.injEq] at h1
  have h2 := congrArg (evalWithAnswerFn hash) (fst_countBoth X)
  rw [evalWithAnswerFn_map] at h2
  have h3 := congrArg (evalWithAnswerFn hash) (countBoth_blocks X)
  rw [evalWithAnswerFn_map] at h3
  refine ⟨h1.1.trans (by rw [h2]), h1.2.2.trans ?_⟩
  rw [← h3]
theorem abstract_count_refinement {α β : Type} (sk : SecretKey) (hash : Hash)
    (X : M α) (run : OracleComp HashSpec (RunResult β)) (F : α → Option β)
    (h : (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> run =
      (fun p => (F p.1,p.2.1,p.2.2)) <$> countBoth (mrealize sk X))
    (hg : AllQueriesSatisfy X SigGolfCandidate.T3.Cost.GoodQuery) :
    (evalWithAnswerFn hash run).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks X))).2 := by
  exact (eval_of_counts h hash).2.trans
    (congrArg (fun p => (evalWithAnswerFn hash p).2) (mrealize_countBlocks sk hg))
theorem eval_cost_fst {α : Type} (answers : SigGolfCandidate.T3.Correctness.Answers) (wt : SigGolfCandidate.T3.Cost.Query → ℕ) (p : M α) :
    (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countWith wt p)).1 = evalWithAnswerFn answers p := by
  have := congrArg (evalWithAnswerFn answers) (SigGolfCandidate.T3.Cost.fst_countWith wt p)
  rw [evalWithAnswerFn_map] at this
  exact this
theorem countWith_map' {α β : Type} (wt : SigGolfCandidate.T3.Cost.Query → ℕ) (f : α → β) (p : M α) :
    SigGolfCandidate.T3.Cost.countWith wt (f <$> p) = (fun q => (f q.1, q.2)) <$> SigGolfCandidate.T3.Cost.countWith wt p := by
  rw [map_eq_bind_pure_comp, SigGolfCandidate.T3.Cost.countWith_bind, map_eq_bind_pure_comp]
  refine bind_congr fun q => ?_
  simp
theorem generic_outer_sign_cost {κ : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encode : κ → PublicKey × Bytes sub.sizes.cache)
    (counts : κ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encode (evalWithAnswerFn hash keys)))
    (hcounts : ∀ key, (sub.runWith hash .sign (sk, (encode key).2, message)).hashCompressions =
      evalWithAnswerFn hash (counts key)) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= counts) := by
  rw [evalWithAnswerFn_map, eval_costs_sign, hkeys, evalWithAnswerFn_bind]
  exact hcounts (evalWithAnswerFn hash keys)
theorem generic_count_pipeline {κ α : Type} (sk : SecretKey) (keys : SigGolfCandidate.T3.M κ)
    (signer : κ → SigGolfCandidate.T3.M α) (charge : α → Nat) :
    mrealize sk keys >>= (fun key => charge <$> mrealize sk (signer key)) =
      charge <$> mrealize sk (keys >>= signer) := by
  rw [mrealize_bind, map_bind]
theorem generic_outer_expand_cost {κ σ α : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encodeKey : κ → PublicKey × Bytes sub.sizes.cache)
    (signer : κ → OracleComp HashSpec α) (selected : α → Option σ)
    (encodeSig : σ → Bytes sub.sizes.signature)
    (counts : κ → σ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encodeKey (evalWithAnswerFn hash keys)))
    (hsign : ∀ key, (sub.runWith hash .sign (sk, (encodeKey key).2, message)).value =
      (selected (evalWithAnswerFn hash (signer key))).map encodeSig)
    (hexpand : ∀ key sig, (sub.runWith hash .expand (message, (encodeKey key).1, encodeSig sig)).hashCompressions =
      evalWithAnswerFn hash (counts key sig)) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= fun key => signer key >>= fun signed =>
        match selected signed with
        | none => pure 0
        | some sig => counts key sig) := by
  rw [evalWithAnswerFn_map, eval_costs_expand, hkeys, evalWithAnswerFn_bind]
  simp only
  rw [hsign, evalWithAnswerFn_bind]
  cases selected (evalWithAnswerFn hash (signer (evalWithAnswerFn hash keys))) with
  | none => rfl
  | some sig => exact hexpand _ sig
theorem generic_joint_count_pipeline {κ σ ω : Type} (sk : SecretKey)
    (initial : SigGolfCandidate.T3.M κ) (signer : κ → SigGolfCandidate.T3.M (Option σ)) (expander : κ → σ → SigGolfCandidate.T3.M ω) :
    (mrealize sk initial >>= fun key => mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (signer key)) >>= fun signed =>
      match signed.1 with
      | none => pure 0
      | some sig => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expander key sig))) =
      Prod.snd <$> mrealize sk (jointCounts initial signer expander) := by
  unfold jointCounts
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro key
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro signed
  rcases signed with ⟨_ | sig, count⟩
  · simp only [mrealize_pure, map_pure]
  · simp only [mrealize_bind, map_bind, mrealize_pure, map_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
theorem two_rpow_eq' (x : ℝ) : (2 : ℝ≥0∞) ^ x = ENNReal.ofReal (Real.rpow 2 x) := by
  rw [Real.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp
theorem withRandomOracle_pure {α : Type} (a : α) : withRandomOracle (pure a : OracleComp HashSpec α) = pure a := by
  simp [withRandomOracle]
end ClaudeWCT.W9.T3M.Final
