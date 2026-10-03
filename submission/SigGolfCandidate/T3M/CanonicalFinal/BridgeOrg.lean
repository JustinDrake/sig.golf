import SigGolfCandidate.T3M.CanonicalFinal.BridgeSetup

/-!
# The organizer experiment, relabeled onto the source oracle (port of five-layer `Bridge/Org`)

`orgK` is the organizer's `interact` loop with every hash input renamed by `ofQ`. With the implementation
equations (`BridgeSetup`) it unfolds into the source programs on `AHash`: signing is `hrealize sk (sign …)`
(the organizer's own secret key realizes the private coordinates), the final check runs `hrealize 0` of the
byte-level verifier `CanonicalSource.verifyC` and of `expandB` (both public-only).
-/

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge

namespace SigGolfCandidate.T3M.CanonicalFinal
open SigGolfCandidate.T3 (keygen sign Signature Cache Digest)

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.T3M.submission SphincsSecurity.hashOutputBits

section

lemma relabel_ofQ_countCalls {α : Type} (X : OracleComp AHash α) (hX : AllQ Aligned X) :
    relabel ofQ (Bridge.countCalls (relabel toQ X)) = Bridge.countCalls X :=
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

/-- `Transcript.record` only reads the value and hash-call count of the signing result. -/
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

variable (A : Adversary CanonicalNative.candidateSub.sizes) (sk : SecretKey) (pk : PublicKey)

/-- The organizer interaction against the public key `pk`, relabeled by `ofQ`. -/
def orgK (n : ℕ) (s : A.State) (T : Transcript CanonicalNative.candidateSub.sizes) : OracleComp AW AttackResult :=
  relabelW ofQ (CanonicalNative.candidateSub.interact A sk pk n s T)

variable {A sk pk}

lemma orgK_zero (s : A.State) (T : Transcript CanonicalNative.candidateSub.sizes) :
    orgK A sk pk 0 s T = pure ⟨false, T.hashCalls⟩ := rfl

lemma orgK_hash {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    orgK A sk pk (n + 1) s T =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        orgK A sk pk n (resume a) { T with hashCalls := T.hashCalls + 1 } := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl

lemma orgK_sample {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    orgK A sk pk (n + 1) s T =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        orgK A sk pk n (resume a) T := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl

lemma orgK_step {n : ℕ} {s s' : A.State} {T : Transcript CanonicalNative.candidateSub.sizes} (h : A.step s = .step s') :
    orgK A sk pk (n + 1) s T = orgK A sk pk n s' T := by
  simp only [orgK, Submission.interact, h]

lemma orgK_sign_ge {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes}
    {req : SigningRequest CanonicalNative.candidateSub.sizes}
    {resume : Option (Bytes CanonicalNative.candidateSub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : ¬ T.signingRequests < LIFETIME) :
    orgK A sk pk (n + 1) s T = pure ⟨false, T.hashCalls⟩ := by
  simp only [orgK, Submission.interact, h, hk, if_false]
  rfl

lemma orgK_sign_lt (F : QFacts) (P : Pending) {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes}
    {req : SigningRequest CanonicalNative.candidateSub.sizes}
    {resume : Option (Bytes CanonicalNative.candidateSub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : T.signingRequests < LIFETIME) :
    orgK A sk pk (n + 1) s T =
      (liftM (Bridge.countCalls (hrealize sk (sign (cacheDec req.cache) req.message))) :
          OracleComp AW _) >>= fun p =>
        orgK A sk pk n (resume (p.1.map sigB))
          (recordVC T req.message (p.1.map sigB) p.2) := by
  simp only [orgK, Submission.interact, h, hk, if_true, Submission.signingOracle, record_eq_recordVC]
  refine (relabelW_liftM_proj (CanonicalNative.candidateSub.run .sign (sk, req.cache, req.message))
    (fun r => (r.value, r.hashCalls))
    (fun p => CanonicalNative.candidateSub.interact A sk pk n (resume p.1) (recordVC T req.message p.1 p.2))
    _ (fun _ => rfl)).trans ?_
  rw [sign_eq P sk req.cache req.message]
  erw [relabel_map]
  rw [relabel_ofQ_countCalls _ (allQ_hrealize sk (F.good_sign _ _))]
  erw [liftM_map, bind_map_left]
  rfl

/-- The witness-form checker, relabeled. -/
lemma relabel_verify (F : QFacts) (P : Pending) (m : Message) (w : Bytes CanonicalNative.candidateSub.sizes.witness) (fresh : Bool)
    (calls : ℕ) :
    relabel ofQ ((CanonicalNative.candidateSub.run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1 && fresh, calls + p.2⟩ : AttackResult)) <$>
        Bridge.countCalls (hrealize 0 (CanonicalSource.verifyC m pk w)) := by
  have e : ((CanonicalNative.candidateSub.run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1.isSome && fresh, calls + p.2⟩ : AttackResult)) <$>
        ((fun r => (r.value, r.hashCalls)) <$> CanonicalNative.candidateSub.run .verify (m, pk, w)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]
    rfl
  rw [e, verify_eq P m pk w]
  erw [Functor.map_map, relabel_map]
  erw [relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_verifyP m pk w))]
  refine congrArg (· <$> _) ?_
  funext a
  rcases a with ⟨b, c⟩
  cases b <;> rfl

lemma orgK_submit_witness (F : QFacts) (P : Pending) {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes}
    {m : Message} {w : Bytes CanonicalNative.candidateSub.sizes.witness}
    (h : A.step s = .submit (.witness m w)) :
    orgK A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshMessage m, T.hashCalls + p.2⟩ : AttackResult)) <$>
        Bridge.countCalls (hrealize 0 (CanonicalSource.verifyC m pk w))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  rw [← relabel_verify F P m w]
  rfl

/-- The organizer's final check of a signature-form forgery: the counted source expansion of the decoded
signature, then (on success) the counted byte-level verification of the expanded witness. -/
lemma orgK_submit_signature (F : QFacts) (P : Pending) {n : ℕ} {s : A.State} {T : Transcript CanonicalNative.candidateSub.sizes}
    {m : Message} {σ : Bytes CanonicalNative.candidateSub.sizes.signature}
    (h : A.step s = .submit (.signature m σ)) :
    orgK A sk pk (n + 1) s T =
      (liftM (Bridge.countCalls (hrealize 0 (expandB m pk (sigDec σ)))) : OracleComp AW _) >>= fun p =>
        match p.1 with
        | none => pure ⟨false, T.hashCalls + p.2⟩
        | some w =>
          (liftM ((fun q => (⟨q.1 && T.freshSignature m σ, T.hashCalls + p.2 + q.2⟩ :
              AttackResult)) <$> Bridge.countCalls (hrealize 0 (CanonicalSource.verifyC m pk w))) :
            OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash, Submission.checkForgery]
  have hE : relabel ofQ ((fun r => (r.value, r.hashCalls)) <$>
      CanonicalNative.candidateSub.run .expand (m, pk, σ)) = Bridge.countCalls (hrealize 0 (expandB m pk (sigDec σ))) := by
    erw [expand_eq P m pk σ]
    exact relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_expandB _ _ _))
  refine (congrArg (fun X => (liftM (relabel ofQ X) : OracleComp AW AttackResult))
    (bind_eq_of_proj (CanonicalNative.candidateSub.run .expand (m, pk, σ)) (fun r => (r.value, r.hashCalls))
      (fun (p : Option (Output CanonicalNative.candidateSub.sizes .expand) × ℕ) =>
          (match p.1 with
          | none => pure ⟨false, T.hashCalls + p.2⟩
          | some witness => (do
              let verify ← CanonicalNative.candidateSub.run .verify (m, pk, witness)
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

variable (A)

/-- The organizer experiment, with hash inputs renamed onto the source oracle and key generation
substituted. -/
noncomputable def orgGame (rounds : ℕ) : OracleComp AW AttackResult := do
  let sk ← (liftM sampleSecretKey : OracleComp AW _)
  let p ← (liftM (Bridge.countCalls (hrealize sk keygen)) : OracleComp AW _)
  orgK A sk (p.1.1 : PublicKey) rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) { hashCalls := p.2 }

lemma ofQ_injective : Function.Injective ofQ := fun x y h => by
  rw [← toQ_ofQ x, ← toQ_ofQ y, h]

set_option maxRecDepth 100000 in
theorem securityExperiment_eq (F : QFacts) (P : Pending) (rounds : ℕ) :
    CanonicalNative.candidateSub.securityExperiment A rounds =
      (simulateQ (roImpl (List UInt8) (BitVec 256)) (orgGame A rounds)).run' ∅ := by
  unfold Submission.securityExperiment withRandomness
  refine (run'_relabelW (R := BitVec 256) ofQ ofQ_injective _ ∅ ∅ (fun _ => rfl)).trans ?_
  refine congrArg (fun P => (simulateQ (roImpl (List UInt8) (BitVec 256)) P).run' ∅) ?_
  unfold orgGame
  rw [relabelW_bind, relabelW_liftM_unif]
  refine bind_congr fun sk => ?_
  refine (relabelW_liftM_proj (CanonicalNative.candidateSub.run .keygen sk) (fun r => (r.value, r.hashCalls))
    (fun (p : Option (PublicKey × Bytes CanonicalNative.candidateSub.sizes.cache) × ℕ) =>
      (match p.1 with
      | some (pk, cache) => CanonicalNative.candidateSub.interact A sk pk rounds (A.initial pk cache) { hashCalls := p.2 }
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

end SigGolfCandidate.T3M.CanonicalFinal
