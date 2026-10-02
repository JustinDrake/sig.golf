import SigGolfCandidate.T3M.Final.BridgeOrg

/-!
# The reduction adversary and the padded source game (port of five-layer `Bridge/Abs`)

`reductionP A rounds` runs the organizer adversary `A` inside the padded source game `gameP`. A hash query `y`
becomes the source query `ofQ y`; a signing request `(m, cache bytes)` becomes `⟨m, cacheDec bytes⟩` and its answer
is returned as `Option.map sigB`; a witness submission is passed as bytes; a signature submission `(m, s)` becomes
`.signature m (sigDec s)`, which the game itself expands with `expandB` (as the organizer runs `expand`).

`absK` is the rest of the realized, counted source game after key generation, with the signing log so far `lg` and
the hash calls so far `c`; its step lemmas mirror `orgK`'s (`BridgeOrg`).
-/

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen sign Signature Cache Digest realize)
open SigGolfCandidate.T3.Security (Request Requests forwardWorld signingOracle)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SigGolfCandidate.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

/-- The source adversary's oracle world. -/
abbrev SSpec := OracleWorld + Requests

variable (A : Adversary submission.sizes)

/-- Replay of the organizer interaction: fuel, adversary state, number of signing requests. -/
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

/-- **The reduction**: a padded-game adversary built from an organizer adversary. -/
def reductionP (rounds : ℕ) : AdversaryP :=
  fun pk cache => advLoop A rounds (A.initial (pk : PublicKey) (cacheB cache)) 0

/-! ## The source game, after key generation -/

/-- The source game's handler for the adversary (as in `gameP`). -/
noncomputable def srcImpl : QueryImpl SSpec (WriterT (QueryLog Requests) M) :=
  (fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
    signingOracle

/-- Run a source adversary computation against the logged signing oracle. -/
noncomputable def runA {α : Type} (X : OracleComp SSpec α) : M (α × QueryLog Requests) :=
  (simulateQ srcImpl X).run

/-- The rest of `gameP` after key generation, with signing-log prefix `lg`. -/
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

/-- The rest of the realized, counted source game after key generation. -/
noncomputable def absK (secret : SecretKey) (pk : Digest) (n : ℕ) (s : A.State) (k : ℕ)
    (lg : QueryLog Requests) (c : ℕ) : OracleComp AW (Bool × ℕ) :=
  countFrom costW (realize secret (srcRest pk (advLoop A n s k) lg)) c

/-! ## `runA` -/

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

/-! ## `srcRest` -/

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

/-! ## Freshness and the two checks -/

/-- Weak freshness of the padded game's witness check. -/
noncomputable def freshW (log : QueryLog Requests) (m : T3.Message) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true)

/-- Strong freshness of the padded game's signature check. -/
noncomputable def freshS (log : QueryLog Requests) (m : T3.Message) (σ : Signature) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2 = some σ)

theorem freshW_iff (log : QueryLog Requests) (m : T3.Message) :
    freshW log m = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true := by
  classical
  unfold freshW; exact decide_eq_true_iff

theorem freshS_iff (log : QueryLog Requests) (m : T3.Message) (σ : Signature) :
    freshS log m σ = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2 = some σ := by
  classical
  unfold freshS; exact decide_eq_true_iff

theorem checkForgeryP_witness (pk : Digest) (log : QueryLog Requests) (m : T3.Message) (wb : WBytes) :
    checkForgeryP pk log (.witness m wb) = verifyP m pk wb >>= fun v => pure (freshW log m && v) := rfl

theorem checkForgeryP_signature (pk : Digest) (log : QueryLog Requests) (m : T3.Message) (σ : Signature) :
    checkForgeryP pk log (.signature m σ) = (do
      let wb ← expandB m pk σ
      let some wb := wb | return false
      let verified ← verifyP m pk wb
      pure (freshS log m σ && verified)) := rfl

/-! ## The realized, counted source game -/

theorem realize_pure' {α : Type} (secret : SecretKey) (a : α) :
    realize secret (pure a : M α) = pure a := rfl

theorem realize_forward_bind {α : Type} (secret : SecretKey) (t : OracleWorld.Domain)
    (g : OracleWorld.Range t → M α) :
    realize secret ((forwardWorld t : M _) >>= g) =
      (liftM (OracleWorld.query t) : OracleComp OracleWorld _) >>= fun a => realize secret (g a) := by
  simp only [realize, simulateQ_bind, forwardWorld, simulateQ_spec_query]
  rfl

variable {A}

set_option maxRecDepth 100000 in
/-- The realized, counted source game for the reduction, from key generation. -/
theorem src_top (F : QFacts) (secret : SecretKey) (rounds : ℕ) :
    countFrom costW (realize secret (gameP (reductionP A rounds))) 0 =
      (liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
        absK A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2 := by
  rw [gameP_eq, T3.Cost.realize_bind, realize_eq_liftM secret F.hashOnly_keygen, countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl)]
  rfl

theorem absK_zero (secret : SecretKey) (pk : Digest) (s : A.State) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) :
    absK A secret pk 0 s k lg c = pure (false, c) := rfl

variable {secret : SecretKey} {pk : Digest}

theorem absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        absK A secret pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl

theorem absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK A secret pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl

theorem absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (h : A.step s = .step s') :
    absK A secret pk (n + 1) s k lg c = absK A secret pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]

theorem absK_sign_ge {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest submission.sizes} {resume : Option (Bytes submission.sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : ¬ k < LIFETIME) :
    absK A secret pk (n + 1) s k lg c = pure (false, c) := by
  unfold absK
  simp only [advLoop, h, hk, if_false]
  rfl

theorem absK_sign_lt (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest submission.sizes} {resume : Option (Bytes submission.sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (sign (cacheDec req.cache) req.message)) c) :
          OracleComp AW _) >>= fun p =>
        absK A secret pk n (resume (p.1.map sigB)) (k + 1)
          (lg ++ [⟨⟨req.message, cacheDec req.cache⟩, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [srcRest_inr_bind, T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_sign _ _), countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl)]

theorem absK_submit_witness (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {w : Bytes submission.sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK A secret pk (n + 1) s k lg c =
      (fun p => (decide (lg.length ≤ 2^32) && (freshW lg m && p.1), p.2)) <$>
        (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_witness, bind_assoc]
  simp only [pure_bind]
  rw [T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
  rfl

theorem absK_submit_signature (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {σ : Bytes submission.sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (expandB m pk (sigDec σ))) c) : OracleComp AW _) >>=
        fun p =>
          match p.1 with
          | none => pure (decide (lg.length ≤ 2^32) && false, p.2)
          | some wb => (fun q => (decide (lg.length ≤ 2^32) && (freshS lg m (sigDec σ) && q.1), q.2)) <$>
              (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk wb)) p.2) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_signature, bind_assoc, T3.Cost.realize_bind,
    realize_eq_liftM secret (F.hashOnly_expandB _ _ _), countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | wb, e⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rw [T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
      countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
    rfl

end SigGolfCandidate.T3M.Final
