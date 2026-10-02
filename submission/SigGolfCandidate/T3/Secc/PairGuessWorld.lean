import SigGolfCandidate.T3.Secc.CanonGraph
import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessPairBound
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessErasure
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessHitPayoff

/-!
# B-PAIR (1/4): the shared hidden-secret observation world for FTS secrets

The ONE FTS-secret world of the SecurityP proof (shared by B-PAIR's pair bound, SEC's near-certificate charge and
LR-34's contact probes): the pinned generic `SphincsSecurity.Concrete.SecretGuessObservation` world with
coordinates `FtsCoord = Fin (2^31) × Fin 7 × Fin 2048` (index, coordinate, global leaf), values `Digest`, and the
coin oracle as auxiliary oracle.

* **trials**: public queries of the adversary and of the final verifier that decode as an FTS leaf input
  (`decodeProbe`, inverse of `probeInput`), the candidate secret read from the input bytes;
* **disclosures**: the 21 secrets the honest signer opens in a returned signature;
* the honest signer is evaluated offline (as in F2's R3), so its own leaf queries are never trials;
* everything else (chain seeds, other private halves, G's canonical labels, the residual public table) is a
  parameter `ω : Omega U` of the world program (presampled with G's `tables_bind`).

This module: the coordinates, probes, the honest secret, disclosures and guess events, the generic world bounds
with the probe budget read from the event (`lazyRun_pair_le`, `lazyRun_guess_le`,
`lazyRun_event_le_forced_of`), and the world program (`worldGame`) with its reference run (`pairRun`).
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Generic world bounds with the probe budget read from the event -/

section Generic
open SecretGuessObservation
variable {Coordinate Value Memory AuxIndex Result : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value]

/-- Two or more guesses within `budget` probes: `C(budget, 2)·(|Value| − budget)^-2` (pinned pair potential). -/
theorem lazyRun_pair_le [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget |
      lazyRun environment computation (initialState memory)] ≤
      (budget.choose 2 : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotential (Fintype.card Value) budget result.2) ?_).trans
  · refine (lazyRun_pairPotential environment (Fintype.card Value) budget computation (initialState memory)
      (initialState_invariant memory) (fun _ => Finset.univ_nonempty)).trans (le_of_eq ?_)
    simp [pairPotential, initialState, pairValue]
  · intro result _ h
    exact pairPotential_two _ _ result.2 h.2 h.1

/-- The pinned `lazyRun_event_le_forced` with the budget read pointwise from the event. -/
theorem lazyRun_event_le_forced_of [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (event : Result × State Coordinate Value Memory → Prop) (payoff : Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ 1 ≤ payoff result) :
    Pr[event | lazyRun environment computation (initialState memory)] ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  have hstep : (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty ∧ result.2.probes ≤ budget then payoff result else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hz : lazyRun environment computation (initialState memory) result = 0
    · simp only [SPMF.probOutput_eq_apply, hz, zero_mul]
      exact bot_le
    by_cases hg : result.2.guesses.Nonempty ∧ result.2.probes ≤ budget
    · rw [if_pos hg]
      have h := lazyRun_new_guesses_le_sum environment computation (initialState memory) result budget hg.2
        (show result.2.guesses ≠ (initialState memory : State Coordinate Value Memory).guesses from hg.1.ne_empty)
      have hp := mul_le_mul' h (le_rfl : payoff result ≤ payoff result)
      simpa only [initialState, ← Finset.range_eq_Ico, Finset.sum_mul, SPMF.probOutput_eq_apply] using hp
    · simp only [if_neg hg, mul_zero]
      exact bot_le
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if result.2.guesses.Nonempty ∧ result.2.probes ≤ budget then payoff result else 0) ?_).trans
  · apply hstep.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro slot hslot
    exact hitRun_payoff_le_forced environment budget slot (Finset.mem_range.mp hslot).le computation memory payoff
  · intro result hr he
    have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
    rw [if_pos ⟨h.1, h.2.1⟩]
    exact h.2.2

/-- At least one guess within `budget` probes: `budget·(|Value| − budget)^-1`. -/
theorem lazyRun_guess_le [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat) :
    Pr[fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ budget |
      lazyRun environment computation (initialState memory)] ≤
      (budget : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ := by
  refine (lazyRun_event_le_forced_of environment computation memory budget
    (fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ budget) (fun _ => 1)
    (fun _ _ h => ⟨h.1, h.2, le_rfl⟩)).trans ?_
  rw [mul_comm]
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ ∑ _slot ∈ Finset.range budget, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro slot _
      simpa only [mul_one] using
        (tsum_probOutput_le_one (mx := forcedRun environment slot computation (initialState memory)))
    _ = budget := by simp

end Generic

/-! ## Coordinates and the shared world -/

/-- FTS secret positions: (index, coordinate, global leaf `256·bucket + leaf`). -/
abbrev FtsCoord := Fin (2^31) × Fin 7 × Fin 2048

def toLeafPos (f : FtsCoord) : CanonGraph.FtsLeafPos := ⟨f.1, f.2.1, f.2.2⟩
def ofLeafPos (p : CanonGraph.FtsLeafPos) : FtsCoord := (p.index, p.coord, p.leaf)

@[simp] theorem ofLeafPos_toLeafPos (f : FtsCoord) : ofLeafPos (toLeafPos f) = f := rfl
@[simp] theorem toLeafPos_ofLeafPos (p : CanonGraph.FtsLeafPos) : toLeafPos (ofLeafPos p) = p := rfl

/-- The world's oracle: coins + secret trials/disclosures. -/
abbrev WSpec := SecretGuessObservation.World unifSpec FtsCoord Digest
abbrev WState := SecretGuessObservation.State FtsCoord Digest PUnit

/-- Coins answered uniformly. -/
noncomputable def coinImpl : QueryImpl unifSpec ProbComp := fun n => liftM (unifSpec.query n)

/-- The shared environment (no memory). -/
noncomputable def env : SecretGuessObservation.Environment unifSpec FtsCoord Digest PUnit :=
  SecretGuessObservation.environment coinImpl

/-- Initial state: every secret uniform on all of `Digest`, nothing retired, no probe. -/
def init : WState := SecretGuessObservation.initialState PUnit.unit

theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp


/-! ## Probes -/

/-- The FTS leaf input of position `f` with candidate secret `c` (Core's `ftsLeaf` query, padded). -/
def probeInput (f : FtsCoord) (c : Digest) : HashInput :=
  pad64 (ftsLeafInputP f.1.val f.2.1.val f.2.2.val 0 c 0)

theorem probeInput_eq (f : FtsCoord) (c : Digest) :
    probeInput f c = block4 0 (header 9 f.2.1.val f.1.val 0 f.2.2.val) c 0 := by
  unfold probeInput ftsLeafInputP
  exact pad64_block4 _ _ _ _

@[simp] theorem probeInput_length (f : FtsCoord) (c : Digest) : (probeInput f c).length = 64 := by
  rw [probeInput_eq]; exact block4_length _ _ _ _

theorem probeInput_injective {f f' : FtsCoord} {c c' : Digest} (h : probeInput f c = probeInput f' c') :
    f = f' ∧ c = c' := by
  rw [probeInput_eq, probeInput_eq] at h
  obtain ⟨-, hh, hc, -⟩ := block4_injective h
  have hf1 := f.1.isLt
  have hf2 := f.2.1.isLt
  have hf3 := f.2.2.isLt
  have hg1 := f'.1.isLt
  have hg2 := f'.2.1.isLt
  have hg3 := f'.2.2.isLt
  have := header_injective (by decide : 9 < 256) (by omega : f.2.1.val < 256) (by omega : f.1.val < 2 ^ 40)
    (by decide : 0 < 2 ^ 32) (by omega : f.2.2.val < 2 ^ 32) (by decide : 9 < 256) (by omega : f'.2.1.val < 256)
    (by omega : f'.1.val < 2 ^ 40) (by decide : 0 < 2 ^ 32) (by omega : f'.2.2.val < 2 ^ 32) hh
  exact ⟨Prod.ext (Fin.ext this.2.2.1) (Prod.ext (Fin.ext this.2.1) (Fin.ext this.2.2.2.2)), hc⟩

/-- Decode a public input as a probe. The decision is classical on purpose: the `Fintype` decision procedure
would make the kernel enumerate `FtsCoord × Digest` whenever it unfolds `decodeProbe`. -/
noncomputable def decodeProbe (x : HashInput) : Option (FtsCoord × Digest) :=
  haveI := Classical.propDecidable (∃ p : FtsCoord × Digest, x = probeInput p.1 p.2)
  if h : ∃ p : FtsCoord × Digest, x = probeInput p.1 p.2 then some (Classical.choose h) else none

theorem decodeProbe_probeInput (f : FtsCoord) (c : Digest) : decodeProbe (probeInput f c) = some (f, c) := by
  have h : ∃ p : FtsCoord × Digest, probeInput f c = probeInput p.1 p.2 := ⟨(f, c), rfl⟩
  rw [decodeProbe, dif_pos h]
  obtain ⟨h1, h2⟩ := probeInput_injective (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext h1 h2)

theorem eq_of_decodeProbe {x : HashInput} {p : FtsCoord × Digest} (h : decodeProbe x = some p) :
    x = probeInput p.1 p.2 := by
  unfold decodeProbe at h
  split at h
  · rename_i hx
    cases h
    exact Classical.choose_spec hx
  · cases h

theorem decodeProbe_eq_none {x : HashInput} : decodeProbe x = none ↔ ∀ f c, x ≠ probeInput f c := by
  constructor
  · intro h f c hx
    rw [hx, decodeProbe_probeInput] at h
    cases h
  · intro h
    rw [decodeProbe, dif_neg]
    rintro ⟨p, hp⟩
    exact h p.1 p.2 hp

/-- The header block of a probe is a tag-9 header. -/
theorem hdrBlock_probeInput (f : FtsCoord) (c : Digest) :
    Extract.hdrBlock (probeInput f c) = bytesLE 16 (header 9 f.2.1.val f.1.val 0 f.2.2.val) := by
  rw [probeInput_eq]; exact FtsExtract.hdrBlock_block4 _ _ _ _

/-- An input whose header block is a header of another tag is never a probe. -/
theorem decodeProbe_of_hdr {x : HashInput} {t l tr p ix : Nat} (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr p ix))
    (ht : t % 256 ≠ 9) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro f c he
  rw [he, hdrBlock_probeInput] at hx
  have hh := bytesLE_injective hx
  apply ht
  have h1 := congrArg (fun v : BitVec 128 => v.toNat % 2 ^ 16 / 2 ^ 8) hh
  simp only [header, BitVec.toNat_ofNat] at h1
  split_ifs at h1 <;> omega

/-! ## Secrets, openings, disclosures, guesses -/

/-- The honest FTS secret at a position (half `leaf % 2` of `privatePair 8 coord index 0 (leaf / 2)`). -/
def secretAt (answers : Answers) (f : FtsCoord) : Digest := CanonGraph.ftsSecretOf answers (toLeafPos f)

/-- The secret half read by Core's `ftsRows` loop at a natural-number leaf. -/
def secretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2

section Rows
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows

/-- Core's `ftsRows` secrets list (G's `eval_ftsRows_secrets`, restated locally). -/
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          secretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = secretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, secretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, secretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl

/-- The `buildFts` secrets list read at a leaf. -/
theorem buildFts_secret (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0 = secretNat answers index coord leaf := by
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf

theorem buildFts_secrets_length (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (buildFts index coord)).2.length = 2048 := by
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).1

end Rows

theorem secretAt_eq (answers : Answers) (f : FtsCoord) :
    secretAt answers f = secretNat answers f.1.val f.2.1.val f.2.2.val := rfl

/-- The honest leaf input is the probe with the honest secret. -/
theorem honestInput_ftsLeaf (answers : Answers) (f : FtsCoord) :
    Extract.honestInput answers (.ftsLeaf f.1.val f.2.1.val f.2.2.val) = probeInput f (secretAt answers f) := by
  simp only [Extract.honestInput]
  have h := buildFts_secret answers f.1.val f.2.1.val f.2.2.val f.2.2.isLt
  unfold Extract.ftsSecret
  rw [h]
  rfl

/-- Global leaf of a selection (bucket < 8, leaf < 256 for every selection). -/
def leafIndex (bucket leaf : Nat) : Fin 2048 := ⟨(bucket * 256 + leaf) % 2048, Nat.mod_lt _ (by decide)⟩

/-- The signer's FTS index of a digest output. -/
def outputIndex (output : HashOutput) : Fin (2^31) := ⟨output.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩

/-- The 21 positions the signer opens for a selected digest output, in the signer's order. -/
def openedPositions (output : HashOutput) : List FtsCoord :=
  (List.finRange 7).flatMap fun c =>
    ((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
      (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)

/-- The digest output the signer selected for a returned signature (the signer's own search from `rho`). -/
noncomputable def signedOutput (answers : Answers) (message : Message) (signature : Signature) :
    Option HashOutput :=
  (evalWithAnswerFn answers (digestSearch signature.rho message 0 attemptLimit)).map Prod.snd

/-- `f` was opened by a signature of the log. -/
def Disclosed (answers : Answers) (log : QueryLog Requests) (f : FtsCoord) : Prop :=
  ∃ entry ∈ log, ∃ signature output, entry.2 = some signature ∧
    signedOutput answers entry.1.message signature = some output ∧ f ∈ openedPositions output

/-- An undisclosed secret whose honest leaf input occurs among `entries`. -/
def GuessedIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) (f : FtsCoord) : Prop :=
  ¬Disclosed answers log f ∧ ∃ answer, (probeInput f (secretAt answers f), answer) ∈ entries

def OneGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f, GuessedIn answers log entries f

def PairGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f g, f ≠ g ∧ GuessedIn answers log entries f ∧ GuessedIn answers log entries g

/-- `C(q,2)·(2^128−q)^-2` (record `FtsGuessHash.pairRate`). -/
noncomputable def pairTerm (q : Nat) : ENNReal := (q.choose 2 : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ^ 2

/-- `q·(2^128−q)^-1`. -/
noncomputable def guessTerm (q : Nat) : ENNReal := (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹


/-! ## The world program and the reference run (universe `U ⊇ canonInputs`) -/

section World
variable (U : Finset HashInput) (hU : CanonGraph.canonInputs ⊆ U)

/-- Everything except the FTS secrets: chain seed halves, other private halves, labels, residual table. -/
structure Omega where
  seeds : ChainGraph.Seeds
  other : CanonGraph.OtherHalves
  labels : CanonGraph.Labels
  residual : U → HashOutput

variable {U}

/-- G's secrets: chain seeds from `ω`, FTS secrets from `fts`. -/
def Omega.secrets (ω : Omega U) (fts : FtsCoord → Digest) : CanonGraph.Secrets
  | .inl a => ω.seeds a
  | .inr p => fts (ofLeafPos p)

/-- G's eager canonical table for `ω` and FTS secrets `fts`. -/
noncomputable def Omega.answers (ω : Omega U) (fts : FtsCoord → Digest) : Answers :=
  CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)) U
    (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual)

/-- A public query in the world: non-probes are answered from `ω` (they do not depend on `fts`); a probe is a
trial whose hit returns the honest label and whose miss returns the residual row. -/
noncomputable def hashW (ω : Omega U) (x : HashInput) : OracleComp WSpec HashOutput :=
  match decodeProbe x with
  | none => pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))
  | some p => do
      let hit ← (liftM (WSpec.query (.inr (.inl p))) : OracleComp WSpec Bool)
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else
        SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x)

/-- Positions opened by the signature returned for `request` (they do not depend on `fts`). -/
noncomputable def openedFor (ω : Omega U) (published : T3.Cache) (request : Request) : List FtsCoord :=
  match evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (FullGame.authenticatedSign published request) with
  | none => []
  | some signature =>
      match signedOutput (Omega.answers hU ω (fun _ => 0)) request.message signature with
      | none => []
      | some output => openedPositions output

/-- Overwrite the default secrets at the disclosed positions. -/
def overwrite (positions : List FtsCoord) (values : List Digest) (f : FtsCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = f))).elim 0 Prod.snd

/-- The signer in the world: disclose the opened secrets, then sign offline. -/
noncomputable def signW (ω : Omega U) (published : T3.Cache) (request : Request) :
    OracleComp WSpec (Option Signature) := do
  let positions := openedFor hU ω published request
  let values ← positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)
  pure (evalWithAnswerFn (Omega.answers hU ω (overwrite positions values))
    (FullGame.authenticatedSign published request))

/-- The adversary's interaction in the world: coins, public queries (`hashW`, recorded), signing (`signW`,
logged). -/
noncomputable def interactionW (ω : Omega U) (published : T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp WSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signW hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))

/-- A T3 program in the world (used for the verdict): public queries via `hashW` (recorded); coins via the
world; private coordinates answer `0` (the padded verdict makes none). -/
noncomputable def programW (ω : Omega U) {β : Type} : M β → OracleComp WSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))

/-- **The world program**: offline key generation, the adversary against `interactionW`, the padded verdict.
Result: (verdict, signing log, ordered public entries of the adversary and of the verdict). -/
noncomputable def worldGame (ω : Omega U) (adversary : AdversaryP) :
    OracleComp WSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen
  let interaction ← interactionW hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programW hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)

end World

/-- The adversary's interaction on a fixed table `T`: coins uniform, public queries answered by `T` (recorded),
signing requests answered offline by `T` (logged). -/
noncomputable def interactionT (T : Answers) (published : T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → ProbComp (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let rest ← next (T (.inl (.inr x)))
          pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)
      | .inr request => do
          let rest ← next (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ :: rest.2.1,
            rest.2.2))

/-- **The reference run on a fixed table** (R3 without cap and ticks): offline key generation, the adversary
against `interactionT`, the padded verdict (deterministic: public-only). -/
noncomputable def pairRun (T : Answers) (adversary : AdversaryP) :
    ProbComp (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn T keygen
  let interaction ← interactionT T generated.2 (adversary generated.1 generated.2)
  let verdict := GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1)
  pure (evalWithAnswerFn T verdict, interaction.2.1,
    interaction.2.2 ++ Wots.entriesOf T (SourceReplay.queried T verdict))

end SigGolfCandidate.T3.Security.BPair
