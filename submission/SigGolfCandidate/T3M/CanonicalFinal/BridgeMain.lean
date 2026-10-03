import SigGolfCandidate.T3M.CanonicalFinal.BridgeAbs

/-!
# The security bridge (port of five-layer `Bridge/Main`)

`submission_secure : QFacts → Pending → SecurityP → CanonicalNative.candidateSub.Secure`: the organizer experiment is dominated, for
every adversary, round count and call budget, by the padded source game for the reduction `reductionP`
(`probEvent_le`): a synchronized coupling (`Bridge.Rel`) of `orgK` and `absK` in which the organizer may stop early,
and every organizer win is a source win with the same number of hash calls (`rel_main`).
-/

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal

namespace SigGolfCandidate.T3M.CanonicalFinal
open SigGolfCandidate.T3 (M Spec keygen sign Signature Cache Digest realize)
open SigGolfCandidate.T3.Security (Request Requests)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.T3M.submission SphincsSecurity.hashOutputBits SigGolfCandidate.T3M.CanonicalNative.candidateSub
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

/-- The invariant linking the organizer transcript to the source signing log and counter. Every request is logged,
failed ones included; a successful entry's message and encoded signature are recorded by the organizer. -/
def Inv (T : Transcript CanonicalNative.candidateSub.sizes) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) : Prop :=
  T.hashCalls = c ∧ T.signingRequests = k ∧ lg.length = k ∧ k ≤ LIFETIME ∧
    ∀ e ∈ lg, ∀ σ : Signature, e.2 = some σ → (e.1.message, sigB σ) ∈ T.signed

/-- An organizer win is a source win with the same number of hash calls. -/
def RFin (r : AttackResult) (b : Bool × ℕ) : Prop :=
  r.won = true → b.1 = true ∧ b.2 = r.hashCalls

lemma rfin_false (h : ℕ) (b : Bool × ℕ) : RFin ⟨false, h⟩ b := fun h => by cases h

lemma length_of_inv {T : Transcript CanonicalNative.candidateSub.sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) : decide (lg.length ≤ 2 ^ 32) = true := by
  obtain ⟨-, -, hlen, hk, -⟩ := hI
  exact decide_eq_true (hlen ▸ hk)

lemma freshW_of_inv {T : Transcript CanonicalNative.candidateSub.sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) {m : Message} (hfresh : T.freshMessage m = true) : freshW lg m = true := by
  rw [freshW_iff]
  rintro ⟨e, he, h1, h2⟩
  rcases hs : e.2 with _ | σ
  · rw [hs] at h2; cases h2
  · have hmem := hI.2.2.2.2 e he σ hs
    rw [h1] at hmem
    unfold Transcript.freshMessage at hfresh
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hfresh
    exact hfresh _ hmem rfl

lemma freshS_of_inv {T : Transcript CanonicalNative.candidateSub.sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) {m : Message} {s : Bytes CanonicalNative.candidateSub.sizes.signature}
    (hfresh : T.freshSignature m s = true) : freshS lg m (sigDec s) = true := by
  rw [freshS_iff]
  rintro ⟨e, he, h1, h2⟩
  have hmem := hI.2.2.2.2 e he _ h2
  rw [h1, sigB_sigDec] at hmem
  unfold Transcript.freshSignature at hfresh
  simp only [Bool.not_eq_true'] at hfresh
  have : T.signed.contains (m, s) = true := List.contains_iff_mem.mpr hmem
  rw [this] at hfresh
  cases hfresh

lemma inv_record {T : Transcript CanonicalNative.candidateSub.sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) (hk : k < LIFETIME) (m : Message) (cache : Cache)
    (r : Option Signature) (calls : ℕ) :
    Inv (recordVC T m (r.map sigB) calls) (k + 1)
      (lg ++ [⟨⟨m, cache⟩, r⟩]) (c + calls) := by
  obtain ⟨hc, hs, hlen, -, hent⟩ := hI
  refine ⟨by simp [recordVC, hc], by simp [recordVC, hs], by simp [hlen], hk, ?_⟩
  intro e he σ hσ
  rw [List.mem_append] at he
  rcases he with he | he
  · have hmem := hent e he σ hσ
    cases r <;> simp [recordVC, hmem]
  · rw [List.mem_singleton] at he
    subst he
    change r = some σ at hσ
    subst hσ
    simp [recordVC]

lemma liftM_countFrom_shift {α : Type} (X : OracleComp AHash α) (c : ℕ) :
    (liftM (countFrom (fun _ => 1) X c) : OracleComp AW (α × ℕ)) =
      (fun p => (p.1, c + p.2)) <$> (liftM (Bridge.countCalls X) : OracleComp AW (α × ℕ)) := by
  rw [countFrom_shift, liftM_map]
  rfl

variable (A : Adversary CanonicalNative.candidateSub.sizes)

theorem rel_main (F : QFacts) (P : Pending) (sk : SecretKey) (pk : Digest) :
    ∀ (n : ℕ) (s : A.State) (T : Transcript CanonicalNative.candidateSub.sizes) (k : ℕ) (lg : QueryLog Requests) (c : ℕ),
      Inv T k lg c → Rel (orgK A sk (pk : PublicKey) n s T) (absK A sk pk n s k lg c) RFin := by
  intro n
  induction n with
  | zero =>
    intro s T k lg c _
    rw [orgK_zero]
    exact Rel.pure_left _ _ (rfin_false _)
  | succ n ih =>
    intro s T k lg c hI
    cases hstep : A.step s with
    | submit f =>
      cases f with
      | witness m w =>
        rw [orgK_submit_witness F P hstep, absK_submit_witness F hstep, liftM_countFrom_shift,
          hrealize_public 0 sk (F.public_verifyP _ _ _), Functor.map_map, liftM_map]
        refine Rel.of_map _ _ _ fun z => ?_
        intro hwon
        simp only [Bool.and_eq_true] at hwon
        refine ⟨?_, ?_⟩
        · simp only [length_of_inv hI, freshW_of_inv hI hwon.2, hwon.1, Bool.true_and]
        · simp [hI.1]
      | signature m σ =>
        rw [orgK_submit_signature F P hstep, absK_submit_signature F hstep, liftM_countFrom_shift,
          hrealize_public 0 sk (F.public_expandB _ _ _), bind_map_left]
        refine Rel.bind_eq _ fun p => ?_
        rcases p with ⟨_ | w, e⟩
        · exact Rel.pure_left _ _ (rfin_false _)
        · simp only
          rw [liftM_countFrom_shift, hrealize_public 0 sk (F.public_verifyP _ _ _), Functor.map_map,
            liftM_map]
          refine Rel.of_map _ _ _ fun z => ?_
          intro hwon
          simp only [Bool.and_eq_true] at hwon
          refine ⟨?_, ?_⟩
          · simp only [length_of_inv hI, freshS_of_inv hI hwon.2, hwon.1, Bool.true_and]
          · simp [hI.1, Nat.add_assoc]
    | hash y resume =>
      rw [orgK_hash hstep, absK_hash hstep]
      refine Rel.bind_eq _ fun a => ih _ _ _ _ _ ?_
      obtain ⟨hc, hs, hlen, hk, hent⟩ := hI
      exact ⟨by simp [hc], hs, hlen, hk, hent⟩
    | sample m resume =>
      rw [orgK_sample hstep, absK_sample hstep]
      exact Rel.bind_eq _ fun a => ih _ _ _ _ _ hI
    | step next =>
      rw [orgK_step hstep, absK_step hstep]
      exact ih _ _ _ _ _ hI
    | sign req resume =>
      by_cases hk : T.signingRequests < LIFETIME
      · have hk' : k < LIFETIME := hI.2.1 ▸ hk
        rw [orgK_sign_lt F P hstep hk, absK_sign_lt F hstep hk', liftM_countFrom_shift, bind_map_left]
        refine Rel.bind_eq _ fun p => ih _ _ _ _ _ ?_
        exact inv_record hI hk' req.message _ p.1 p.2
      · rw [orgK_sign_ge hstep hk]
        exact Rel.pure_left _ _ (rfin_false _)

lemma probEvent_bind_le' {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {E₁ : β → Prop} {E₂ : γ → Prop}
    (h : ∀ x, Pr[E₁ | f x] ≤ Pr[E₂ | g x]) : Pr[E₁ | mx >>= f] ≤ Pr[E₂ | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x

/-- The source experiment of the reduction, with the master secret sampled first. -/
theorem realExperimentP_eq (F : QFacts) (rounds : ℕ) :
    realExperimentP (reductionP A rounds) =
      SphincsSecurity.sampleMasterSeed >>= fun secret =>
        (simulateQ (roImpl (List UInt8) (BitVec 256))
          ((liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
            absK A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2)).run' ∅ := by
  unfold realExperimentP
  refine bind_congr fun secret => ?_
  rw [derivation_realize, countHashQueries_eq, src_top F secret rounds]
  rfl

/-- The key inequality: the organizer's event is dominated by the padded source game's event for the
reduction. -/
theorem probEvent_le (F : QFacts) (P : Pending) (rounds Q : ℕ) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ Q | CanonicalNative.candidateSub.securityExperiment A rounds] ≤
      Pr[fun r => r.1 = true ∧ r.2 ≤ Q | realExperimentP (reductionP A rounds)] := by
  rw [securityExperiment_eq A F P rounds, realExperimentP_eq A F rounds]
  unfold orgGame
  rw [simulateQ_bind, roSim.run'_liftM_bind, ← sampleSecretKey_eq]
  refine probEvent_bind_le' _ fun sk => ?_
  refine Rel.probEvent_le (R := RFin) (roImpl (List UInt8) (BitVec 256)) ?_ _ _ ?_ ∅
  · refine Rel.bind_eq _ fun a => ?_
    exact rel_main A F P sk a.1.1 rounds _ _ 0 [] a.2 ⟨rfl, rfl, rfl, Nat.zero_le _, by simp⟩
  · intro r b hR hE
    obtain ⟨h1, h2⟩ := hR hE.1
    exact ⟨h1, h2 ▸ hE.2⟩

/-- **The security bridge**: the padded source game's security (`SecurityP`) and the machine refinements give
the organizer's `Submission.Secure`. -/
theorem submission_secure (F : QFacts) (P : Pending) (hS : SecurityP) : CanonicalNative.candidateSub.Secure := by
  intro A rounds Q hQ
  calc _ ≤ _ := probEvent_le A F P rounds Q
    _ ≤ (Q : ℝ≥0∞) / 2 ^ 127 := hS _ Q hQ
    _ = (Q : ℝ≥0∞) / 2 ^ SECURITY_BITS := rfl

end SigGolfCandidate.T3M.CanonicalFinal
