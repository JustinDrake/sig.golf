import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.ClaudeWCT.W9.New.F1a.Clean

section


namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen Cache Digest privateInput realize)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SigGolfCandidate.T3M (mrealize countBoth cacheB cacheDec isHash isPublic toQ)
open SigGolfCandidate.T3M.Final (hrealize mrealize_eq_relabel hrealize_map)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
structure QFacts : Prop where
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (c : Cache) (m : SigGolfCandidate.T3.Message), AllQueriesSatisfy (sign c m) isHash
  hashOnly_expandB : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
    AllQueriesSatisfy (expandB m pk σ) isHash
  hashOnly_verifyP : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
    AllQueriesSatisfy (verifyP m pk w) isHash
  public_expandB : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
    AllQueriesSatisfy (expandB m pk σ) isPublic
  public_verifyP : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
    AllQueriesSatisfy (verifyP m pk w) isPublic
  good_keygen : AllQueriesSatisfy keygen SigGolfCandidate.T3.Cost.GoodQuery
  good_sign : ∀ (c : Cache) (m : SigGolfCandidate.T3.Message),
    AllQueriesSatisfy (sign c m) SigGolfCandidate.T3.Cost.GoodQuery
  good_expandB : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
    AllQueriesSatisfy (expandB m pk σ) SigGolfCandidate.T3.Cost.GoodQuery
  good_verifyP : ∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
    AllQueriesSatisfy (verifyP m pk w) SigGolfCandidate.T3.Cost.GoodQuery
section eqs
variable {I : Images}
set_option maxRecDepth 100000 in
theorem keygen_eq (P : Pending I) (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize sk keygen)) := by
  have h := calls_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2))
    (P.keygen_run_counts sk)
  rw [mrealize_eq_relabel] at h
  exact h
set_option maxRecDepth 100000 in
theorem sign_eq (P : Pending I) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .sign (sk, cache, m) =
      (fun p => (p.1.map sigB, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize sk (sign (cacheDec cache) m))) := by
  have h := calls_of_counts (F := Option.map sigB) (P.sign_refines sk cache m)
  rw [mrealize_eq_relabel] at h
  exact h
set_option maxRecDepth 100000 in
theorem expand_eq (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5456) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .expand (m, pk, s) =
      SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (expandB m pk (sigDec s)))) := by
  have h := calls_of_counts
    (F := Option.map (fun x : SigGolfCandidate.T3.HashOutput × ClaudeWCT.WCT9.Witness => witEnc x.1 x.2))
    (P.expand_refines m pk s)
  rw [mrealize_eq_relabel] at h
  refine h.trans ?_
  rw [expandB, hrealize_map, relabel_map]
  unfold SigGolfCandidate.Bridge.countCalls
  rw [countFrom_map]
set_option maxRecDepth 100000 in
theorem verify_eq (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 24264) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (verifyP m pk w))) := by
  rw [P.verify_refines m pk w, SigGolfCandidate.T3M.Final.countCalls_eq, mrealize_eq_relabel]
end eqs
end ClaudeWCT.W9.T3M.Final
end

section

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (keygen Cache Digest)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize allQ_hrealize)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
section
variable (I : Images) (A : Adversary (submission I).sizes) (sk : SecretKey) (pk : PublicKey)
def orgK (n : ℕ) (s : A.State) (T : Transcript (submission I).sizes) : OracleComp AW AttackResult :=
  relabelW ofQ ((submission I).interact A sk pk n s T)
variable {I A sk pk}
lemma orgK_zero (s : A.State) (T : Transcript (submission I).sizes) :
    orgK I A sk pk 0 s T = pure ⟨false, T.hashCalls⟩ := rfl
lemma orgK_hash {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    orgK I A sk pk (n + 1) s T =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        orgK I A sk pk n (resume a) { T with hashCalls := T.hashCalls + 1 } := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl
lemma orgK_sample {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    orgK I A sk pk (n + 1) s T =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        orgK I A sk pk n (resume a) T := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl
lemma orgK_step {n : ℕ} {s s' : A.State} {T : Transcript (submission I).sizes} (h : A.step s = .step s') :
    orgK I A sk pk (n + 1) s T = orgK I A sk pk n s' T := by
  simp only [orgK, Submission.interact, h]
lemma orgK_sign_ge {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : ¬ T.signingRequests < LIFETIME) :
    orgK I A sk pk (n + 1) s T = pure ⟨false, T.hashCalls⟩ := by
  simp only [orgK, Submission.interact, h, hk, if_false]
  rfl
lemma orgK_sign_lt (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : T.signingRequests < LIFETIME) :
    orgK I A sk pk (n + 1) s T =
      (liftM (SigGolfCandidate.Bridge.countCalls (hrealize sk (sign (cacheDec req.cache) req.message))) :
          OracleComp AW _) >>= fun p =>
        orgK I A sk pk n (resume (p.1.map sigB))
          (recordVC T req.message (p.1.map sigB) p.2) := by
  simp only [orgK, Submission.interact, h, hk, if_true, Submission.signingOracle, record_eq_recordVC]
  refine (relabelW_liftM_proj ((submission I).run .sign (sk, req.cache, req.message))
    (fun r => (r.value, r.hashCalls))
    (fun p => (submission I).interact A sk pk n (resume p.1) (recordVC T req.message p.1 p.2))
    _ (fun _ => rfl)).trans ?_
  rw [sign_eq P sk req.cache req.message]
  erw [relabel_map]
  rw [relabel_ofQ_countCalls _ (allQ_hrealize sk (F.good_sign _ _))]
  erw [liftM_map, bind_map_left]
  rfl
lemma relabel_verify (F : QFacts) (P : Pending I) (m : Message) (w : Bytes (submission I).sizes.witness)
    (fresh : Bool) (calls : ℕ) :
    relabel ofQ (((submission I).run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1 && fresh, calls + p.2⟩ : AttackResult)) <$>
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w)) := by
  have e : (((submission I).run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1.isSome && fresh, calls + p.2⟩ : AttackResult)) <$>
        ((fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]
    rfl
  rw [e, verify_eq P m pk w]
  erw [Functor.map_map, relabel_map]
  erw [relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_verifyP m pk w))]
  refine congrArg (· <$> _) ?_
  funext a
  rcases a with ⟨b, c⟩
  cases b <;> rfl
lemma orgK_submit_witness (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State}
    {T : Transcript (submission I).sizes} {m : Message} {w : Bytes (submission I).sizes.witness}
    (h : A.step s = .submit (.witness m w)) :
    orgK I A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshMessage m, T.hashCalls + p.2⟩ : AttackResult)) <$>
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  rw [← relabel_verify F P m w]
  rfl
lemma orgK_submit_signature (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State}
    {T : Transcript (submission I).sizes} {m : Message} {σ : Bytes (submission I).sizes.signature}
    (h : A.step s = .submit (.signature m σ)) :
    orgK I A sk pk (n + 1) s T =
      (liftM (SigGolfCandidate.Bridge.countCalls (hrealize 0 (expandB m pk (sigDec σ)))) : OracleComp AW _) >>=
        fun p =>
        match p.1 with
        | none => pure ⟨false, T.hashCalls + p.2⟩
        | some w =>
          (liftM ((fun q => (⟨q.1 && T.freshSignature m σ, T.hashCalls + p.2 + q.2⟩ :
              AttackResult)) <$> SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w))) :
            OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash, Submission.checkForgery]
  have hE : relabel ofQ ((fun r => (r.value, r.hashCalls)) <$>
      (submission I).run .expand (m, pk, σ)) =
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (expandB m pk (sigDec σ))) := by
    erw [expand_eq P m pk σ]
    exact relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_expandB _ _ _))
  refine (congrArg (fun X => (liftM (relabel ofQ X) : OracleComp AW AttackResult))
    (bind_eq_of_proj ((submission I).run .expand (m, pk, σ)) (fun r => (r.value, r.hashCalls))
      (fun (p : Option (Output (submission I).sizes .expand) × ℕ) =>
          (match p.1 with
          | none => pure ⟨false, T.hashCalls + p.2⟩
          | some witness => (do
              let verify ← (submission I).run .verify (m, pk, witness)
              pure ⟨verify.value.isSome && T.freshSignature m σ,
                T.hashCalls + p.2 + verify.hashCalls⟩) : OracleComp HashSpec AttackResult))
      _ (fun r => by rcases r with ⟨v, f, c, h, hc⟩; cases v <;> rfl))).trans ?_
  refine (congrArg liftM (relabel_bind ofQ _ _)).trans ?_
  refine (liftM_bind _ _).trans ?_
  rw [hE]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | w, c⟩
  · rfl
  · exact congrArg _ (relabel_verify F P m w _ _)
variable (I A)
noncomputable def orgGame (rounds : ℕ) : OracleComp AW AttackResult := do
  let sk ← (liftM sampleSecretKey : OracleComp AW _)
  let p ← (liftM (SigGolfCandidate.Bridge.countCalls (hrealize sk keygen)) : OracleComp AW _)
  orgK I A sk (p.1.1 : PublicKey) rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) { hashCalls := p.2 }
set_option maxRecDepth 100000 in
theorem securityExperiment_eq (F : QFacts) (P : Pending I) (rounds : ℕ) :
    (submission I).securityExperiment A rounds =
      (simulateQ (roImpl (List UInt8) (BitVec 256)) (orgGame I A rounds)).run' ∅ := by
  unfold Submission.securityExperiment withRandomness
  refine (run'_relabelW (R := BitVec 256) ofQ ofQ_injective _ ∅ ∅ (fun _ => rfl)).trans ?_
  refine congrArg (fun P => (simulateQ (roImpl (List UInt8) (BitVec 256)) P).run' ∅) ?_
  unfold orgGame
  rw [relabelW_bind, relabelW_liftM_unif]
  refine bind_congr fun sk => ?_
  refine (relabelW_liftM_proj ((submission I).run .keygen sk) (fun r => (r.value, r.hashCalls))
    (fun (p : Option (PublicKey × Bytes (submission I).sizes.cache) × ℕ) =>
      (match p.1 with
      | some (pk, cache) => (submission I).interact A sk pk rounds (A.initial pk cache) { hashCalls := p.2 }
      | none => pure ⟨false, p.2⟩ : OracleComp World AttackResult)) _ ?hK).trans ?_
  case hK =>
    intro r
    rcases r with ⟨v, f, c, h, hc⟩
    rcases v with _ | ⟨pk, cache⟩ <;> rfl
  rw [keygen_eq P sk]
  erw [relabel_map]
  rw [relabel_ofQ_countCalls _ (allQ_hrealize sk F.good_keygen)]
  refine (liftM_map_bind _ _ _).trans ?_
  refine bind_congr fun p => ?_
  rfl
end
end ClaudeWCT.W9.T3M.Final
end

section

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open ClaudeWCT.W9.T3.Security (Requests signingOracle)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize realize_eq_liftM)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local instance] instDecidableEqSignature_securityP
abbrev SSpec := OracleWorld + Requests
variable (I : Images) (A : Adversary (submission I).sizes)
def advLoop : ℕ → A.State → ℕ → OracleComp SSpec (Option ForgeryP)
  | 0, _, _ => pure none
  | n + 1, s, k =>
    match A.step s with
    | .submit (.witness m w) => pure (some (.witness m w))
    | .submit (.signature m σ) => pure (some (.signature m (sigDec σ)))
    | .hash y resume => do
        let a ← (liftM (SSpec.query (Sum.inl (Sum.inr (ofQ y)))) : OracleComp SSpec (BitVec 256))
        advLoop n (resume a) k
    | .sign req resume =>
        if k < LIFETIME then do
          let r ← (liftM (SSpec.query (Sum.inr ⟨req.message, cacheDec req.cache⟩)) :
            OracleComp SSpec (Option Signature))
          advLoop n (resume (r.map sigB)) (k + 1)
        else pure none
    | .sample m resume => do
        let u ← (liftM (SSpec.query (Sum.inl (Sum.inl m))) : OracleComp SSpec (Fin (m + 1)))
        advLoop n (resume u) k
    | .step next => advLoop n next k
def reductionP (rounds : ℕ) : AdversaryP :=
  fun pk cache => advLoop I A rounds (A.initial (pk : PublicKey) (cacheB cache)) 0
noncomputable def srcImpl : QueryImpl SSpec (WriterT (QueryLog Requests) M) :=
  (fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
    signingOracle
noncomputable def runA {α : Type} (X : OracleComp SSpec α) : M (α × QueryLog Requests) :=
  (simulateQ srcImpl X).run
noncomputable def srcRest (pk : Digest) (X : OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    M Bool := do
  let (forgery, log) ← runA X
  let some forgery := forgery | return false
  let verified ← checkForgeryP pk (lg ++ log) forgery
  pure (decide ((lg ++ log).length ≤ 2^32) && verified)
theorem gameP_eq (adversary : AdversaryP) :
    gameP adversary = keygen >>= fun kp => srcRest kp.1 (adversary kp.1 kp.2) [] := by
  unfold gameP srcRest runA srcImpl
  rfl
noncomputable def absK (secret : SecretKey) (pk : Digest) (n : ℕ) (s : A.State) (k : ℕ)
    (lg : QueryLog Requests) (c : ℕ) : OracleComp AW (Bool × ℕ) :=
  countFrom costW (realize secret (srcRest pk (advLoop I A n s k) lg)) c
theorem runA_pure {α : Type} (x : α) : runA (pure x : OracleComp SSpec α) = pure (x, []) := rfl
theorem runA_inl_bind {α : Type} (t : OracleWorld.Domain) (f : OracleWorld.Range t → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) =
      (forwardWorld t : M _) >>= fun a => runA (f a) := by
  simp only [runA, srcImpl, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : (((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) + signingOracle) (Sum.inl t)).run =
      (fun a => (a, [])) <$> (forwardWorld t : M _) := rfl
  rw [e, bind_map_left]
  simp
theorem runA_inr_bind {α : Type} (req : Request) (f : Option Signature → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) =
      (sign req.cache req.message : M _) >>= fun u =>
        (fun p => (p.1, [⟨req, u⟩] ++ p.2)) <$> runA (f u) := by
  simp [runA, srcImpl, signingOracle, WriterT.run_bind]
theorem srcRest_inl_bind (pk : Digest) (t : OracleWorld.Domain)
    (f : OracleWorld.Range t → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) lg =
      (forwardWorld t : M _) >>= fun a => srcRest pk (f a) lg := by
  unfold srcRest
  rw [runA_inl_bind, bind_assoc]
theorem srcRest_inr_bind (pk : Digest) (req : Request)
    (f : Option Signature → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) lg =
      (sign req.cache req.message : M _) >>= fun u => srcRest pk (f u) (lg ++ [⟨req, u⟩]) := by
  unfold srcRest
  rw [runA_inr_bind, bind_assoc]
  refine bind_congr fun u => ?_
  rw [bind_map_left]
  simp only [List.append_assoc]
theorem srcRest_none (pk : Digest) (lg : QueryLog Requests) :
    srcRest pk (pure none) lg = pure false := rfl
theorem srcRest_some (pk : Digest) (f : ForgeryP) (lg : QueryLog Requests) :
    srcRest pk (pure (some f)) lg =
      checkForgeryP pk lg f >>= fun v => pure (decide (lg.length ≤ 2^32) && v) := by
  unfold srcRest
  rw [runA_pure, pure_bind]
  simp only [List.append_nil]
noncomputable def freshW (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true)
noncomputable def freshS (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2 = some σ)
theorem freshW_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) :
    freshW log m = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true := by
  classical
  unfold freshW; exact decide_eq_true_iff
theorem freshS_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) :
    freshS log m σ = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2 = some σ := by
  classical
  unfold freshS; exact decide_eq_true_iff
theorem checkForgeryP_witness (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (wb : WBytes) :
    checkForgeryP pk log (.witness m wb) = verifyP m pk wb >>= fun v => pure (freshW log m && v) := rfl
theorem checkForgeryP_signature (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (σ : Signature) :
    checkForgeryP pk log (.signature m σ) = (do
      let wb ← expandB m pk σ
      let some wb := wb | return false
      let verified ← verifyP m pk wb
      pure (freshS log m σ && verified)) := rfl
variable {I A}
set_option maxRecDepth 100000 in
theorem src_top (F : QFacts) (secret : SecretKey) (rounds : ℕ) :
    countFrom costW (realize secret (gameP (reductionP I A rounds))) 0 =
      (liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
        absK I A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2 := by
  rw [gameP_eq, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret F.hashOnly_keygen, countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl)]
  rfl
theorem absK_zero (secret : SecretKey) (pk : Digest) (s : A.State) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) :
    absK I A secret pk 0 s k lg c = pure (false, c) := rfl
variable {secret : SecretKey} {pk : Digest}
theorem absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (h : A.step s = .step s') :
    absK I A secret pk (n + 1) s k lg c = absK I A secret pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]
theorem absK_sign_ge {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : ¬ k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c = pure (false, c) := by
  unfold absK
  simp only [advLoop, h, hk, if_false]
  rfl
theorem absK_sign_lt (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (sign (cacheDec req.cache) req.message)) c) :
          OracleComp AW _) >>= fun p =>
        absK I A secret pk n (resume (p.1.map sigB)) (k + 1)
          (lg ++ [⟨⟨req.message, cacheDec req.cache⟩, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [srcRest_inr_bind, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_sign _ _),
    countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
theorem absK_submit_witness (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {w : Bytes (submission I).sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK I A secret pk (n + 1) s k lg c =
      (fun p => (decide (lg.length ≤ 2^32) && (freshW lg m && p.1), p.2)) <$>
        (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_witness, bind_assoc]
  simp only [pure_bind]
  rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
  rfl
theorem absK_submit_signature (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {σ : Bytes (submission I).sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (expandB m pk (sigDec σ))) c) : OracleComp AW _) >>=
        fun p =>
          match p.1 with
          | none => pure (decide (lg.length ≤ 2^32) && false, p.2)
          | some wb => (fun q => (decide (lg.length ≤ 2^32) && (freshS lg m (sigDec σ) && q.1), q.2)) <$>
              (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk wb)) p.2) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_signature, bind_assoc, SigGolfCandidate.T3.Cost.realize_bind,
    realize_eq_liftM secret (F.hashOnly_expandB _ _ _), countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | wb, e⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
      countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
    rfl
end ClaudeWCT.W9.T3M.Final
end
