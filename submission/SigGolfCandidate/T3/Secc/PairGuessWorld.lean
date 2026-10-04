import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessObservation
import SigGolfCandidate.T3.Secc.CanonGraph
import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessErasure
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessHitPayoff

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def pairValue (rate : ENNReal) (remaining : Nat) : Nat → ENNReal
  | 0 => remaining.choose 2 * rate ^ 2
  | 1 => remaining * rate
  | _ + 2 => 1
theorem pairValue_mono (rate : ENNReal) (hits : Nat) {first second : Nat} (h : first ≤ second) :
    pairValue rate first hits ≤ pairValue rate second hits := by
  cases hits with
  | zero => exact mul_le_mul' (by exact_mod_cast Nat.choose_le_choose 2 h) le_rfl
  | succ hits =>
      cases hits with
      | zero => exact mul_le_mul' (by exact_mod_cast h) le_rfl
      | succ hits => exact le_rfl
private theorem expectation_const_le {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem pairValue_trial (law : SPMF Bool) (rate : ENNReal) (hrate : law true ≤ rate) (remaining hits : Nat) :
    (∑' hit, Pr[= hit | law] * pairValue rate remaining (hits + if hit then 1 else 0)) ≤
      pairValue rate (remaining + 1) hits := by
  have hfalse : law false ≤ 1 := by
    simpa only [SPMF.probOutput_eq_apply] using (show Pr[= false | law] ≤ 1 from probOutput_le_one)
  cases hits with
  | zero =>
      simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.zero_add,
        pairValue, SPMF.probOutput_eq_apply]
      calc
        _ ≤ rate * (remaining * rate) + ((remaining.choose 2 : Nat) : ENNReal) * rate ^ 2 :=
          add_le_add (mul_le_mul' hrate le_rfl) (mul_le_of_le_one_left' hfalse)
        _ = _ := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
          ring
  | succ hits =>
      cases hits with
      | zero =>
          simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            pairValue, SPMF.probOutput_eq_apply, mul_one]
          calc
            _ ≤ rate + (remaining : ENNReal) * rate := add_le_add hrate (mul_le_of_le_one_left' hfalse)
            _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
      | succ hits =>
          calc
            _ = ∑' hit, Pr[= hit | law] * 1 := by
              apply tsum_congr
              intro hit
              cases hit <;> rfl
            _ ≤ 1 := expectation_const_le law 1
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def pairPotential (size budget : Nat) (state : State Coordinate Value Memory) : ENNReal :=
  if state.probes ≤ budget then pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card else 0
theorem pairPotential_afterTrial (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (coordinate : Coordinate) (candidate : Value) :
    (∑' hit, Pr[= hit | trial state.allowed coordinate candidate] *
      pairPotential size budget (afterTrial environment state coordinate candidate hit)) ≤ pairPotential size budget state := by
  classical
  by_cases hroom : state.probes < budget
  · have hwithin : state.probes ≤ budget := Nat.le_of_lt hroom
    have hafter : state.probes + 1 ≤ budget := hroom
    have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    simp only [pairPotential, hp, afterTrial_guesses_card environment state hs.2, if_pos hafter, if_pos hwithin]
    by_cases hc : coordinate ∈ state.retired
    · simp only [hc, not_true_eq_false, and_false, if_false, Nat.add_zero]
      exact (expectation_const_le _ _).trans (pairValue_mono _ _ (Nat.sub_le_sub_left (by omega) _))
    · simp only [hc, not_false_eq_true, and_true]
      rw [hremaining]
      exact pairValue_trial _ _ (trial_true_le size budget state hs ha hwithin coordinate hc candidate) _ _
  · have hafter : ¬state.probes + 1 ≤ budget := by omega
    simp only [pairPotential, afterTrial, if_neg hafter, mul_zero, tsum_zero]
    exact bot_le
theorem lazyImpl_pairPotential (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (lazyImpl environment input).run state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
      exact expectation_const_le _ _
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact pairPotential_afterTrial environment size budget state hs ha coordinate candidate
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact expectation_const_le _ _
theorem lazyRun_pairPotential {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (∑' result, Pr[= result | lazyRun environment computation state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [lazyRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [lazyRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (lazyImpl_pairPotential environment size budget state hs ha input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (lazyImpl environment input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · have hrun : lazyRun environment (liftM ((World auxSpec Coordinate Value).query input)) state middle ≠ 0 := by
          simpa only [lazyRun, runWith, simulateQ_spec_query] using hm
        exact mul_le_mul' le_rfl (ih middle.1 middle.2
          (lazyRun_invariant environment size _ state hs middle hrun) (lazyRun_nonempty environment _ state ha middle hrun))
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem pairPotential_two (size budget : Nat) (state : State Coordinate Value Memory)
    (hbudget : state.probes ≤ budget) (hhits : 2 ≤ state.guesses.card) : 1 ≤ pairPotential size budget state := by
  rw [pairPotential, if_pos hbudget]
  obtain ⟨hits, heq⟩ := Nat.exists_eq_add_of_le hhits
  rw [heq, Nat.add_comm]
  exact le_rfl
theorem lazyRun_two_guesses [Fintype Value] [Nonempty Value] {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget) :
    Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun environment computation (initialState memory)] ≤
      (budget.choose 2 : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotential (Fintype.card Value) budget result.2) ?_).trans
      (lazyRun_pairPotential environment (Fintype.card Value) budget computation (initialState memory)
        (initialState_invariant memory) (fun _ => Finset.univ_nonempty))
  intro result hr htwo
  apply pairPotential_two _ _ result.2 _ htwo
  exact hbudget result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr)
end SphincsSecurity.Concrete.SecretGuessObservation
end

section





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
section Generic
open SecretGuessObservation
variable {Coordinate Value Memory AuxIndex Result : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value]
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
abbrev FtsCoord := Fin (2^31) × Fin 7 × Fin 2048
def toLeafPos (f : FtsCoord) : CanonGraph.FtsLeafPos := ⟨f.1, f.2.1, f.2.2⟩
def ofLeafPos (p : CanonGraph.FtsLeafPos) : FtsCoord := (p.index, p.coord, p.leaf)
@[simp] theorem ofLeafPos_toLeafPos (f : FtsCoord) : ofLeafPos (toLeafPos f) = f := rfl
@[simp] theorem toLeafPos_ofLeafPos (p : CanonGraph.FtsLeafPos) : toLeafPos (ofLeafPos p) = p := rfl
abbrev WSpec := SecretGuessObservation.World unifSpec FtsCoord Digest
abbrev WState := SecretGuessObservation.State FtsCoord Digest PUnit
noncomputable def coinImpl : QueryImpl unifSpec ProbComp := fun n => liftM (unifSpec.query n)
noncomputable def env : SecretGuessObservation.Environment unifSpec FtsCoord Digest PUnit :=
  SecretGuessObservation.environment coinImpl
def init : WState := SecretGuessObservation.initialState PUnit.unit
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
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
theorem hdrBlock_probeInput (f : FtsCoord) (c : Digest) :
    Extract.hdrBlock (probeInput f c) = bytesLE 16 (header 9 f.2.1.val f.1.val 0 f.2.2.val) := by
  rw [probeInput_eq]; exact FtsExtract.hdrBlock_block4 _ _ _ _
theorem decodeProbe_of_hdr {x : HashInput} {t l tr p ix : Nat} (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr p ix))
    (ht : t % 256 ≠ 9) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro f c he
  rw [he, hdrBlock_probeInput] at hx
  have hh := bytesLE_injective hx
  apply ht
  have h1 := congrArg (fun v : BitVec 128 => v.toNat % 2 ^ 16 / 2 ^ 8) hh
  have hw := nodeWord_lt t p ix
  have hw9 := nodeWord_lt 9 0 f.2.2.val
  simp only [header, BitVec.toNat_ofNat] at h1
  generalize nodeWord t p ix = g at *
  generalize nodeWord 9 0 f.2.2.val = g9 at *
  split_ifs at h1 <;> omega
def secretAt (answers : Answers) (f : FtsCoord) : Digest := CanonGraph.ftsSecretOf answers (toLeafPos f)
def secretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
section Rows
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows
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
theorem honestInput_ftsLeaf (answers : Answers) (f : FtsCoord) :
    Extract.honestInput answers (.ftsLeaf f.1.val f.2.1.val f.2.2.val) = probeInput f (secretAt answers f) := by
  simp only [Extract.honestInput]
  have h := buildFts_secret answers f.1.val f.2.1.val f.2.2.val f.2.2.isLt
  unfold Extract.ftsSecret
  rw [h]
  rfl
def leafIndex (bucket leaf : Nat) : Fin 2048 := ⟨(bucket * 128 + leaf) % 2048, Nat.mod_lt _ (by decide)⟩
def outputIndex (output : HashOutput) : Fin (2^31) := ⟨output.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def openedPositions (output : HashOutput) : List FtsCoord :=
  (List.finRange 7).flatMap fun c =>
    ((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
      (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)
noncomputable def signedOutput (answers : Answers) (message : Message) (signature : Signature) :
    Option HashOutput :=
  (evalWithAnswerFn answers (digestSearch signature.rho message 0 attemptLimit)).map Prod.snd
def Disclosed (answers : Answers) (log : QueryLog Requests) (f : FtsCoord) : Prop :=
  ∃ entry ∈ log, ∃ signature output, entry.2 = some signature ∧
    signedOutput answers entry.1.message signature = some output ∧ f ∈ openedPositions output
def GuessedIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) (f : FtsCoord) : Prop :=
  ¬Disclosed answers log f ∧ ∃ answer, (probeInput f (secretAt answers f), answer) ∈ entries
def OneGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f, GuessedIn answers log entries f
def PairGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f g, f ≠ g ∧ GuessedIn answers log entries f ∧ GuessedIn answers log entries g
noncomputable def pairTerm (q : Nat) : ENNReal := (q.choose 2 : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ^ 2
noncomputable def guessTerm (q : Nat) : ENNReal := (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹
section World
variable (U : Finset HashInput) (hU : CanonGraph.canonInputs ⊆ U)
structure Omega where
  seeds : ChainGraph.Seeds
  other : CanonGraph.OtherHalves
  labels : CanonGraph.Labels
  residual : U → HashOutput
variable {U}
def Omega.secrets (ω : Omega U) (fts : FtsCoord → Digest) : CanonGraph.Secrets
  | .inl a => ω.seeds a
  | .inr p => fts (ofLeafPos p)
noncomputable def Omega.answers (ω : Omega U) (fts : FtsCoord → Digest) : Answers :=
  CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)) U
    (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual)
noncomputable def hashW (ω : Omega U) (x : HashInput) : OracleComp WSpec HashOutput :=
  match decodeProbe x with
  | none => pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))
  | some p => do
      let hit ← (liftM (WSpec.query (.inr (.inl p))) : OracleComp WSpec Bool)
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else
        SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x)
noncomputable def openedFor (ω : Omega U) (published : T3.Cache) (request : Request) : List FtsCoord :=
  match evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (FullGame.authenticatedSign published request) with
  | none => []
  | some signature =>
      match signedOutput (Omega.answers hU ω (fun _ => 0)) request.message signature with
      | none => []
      | some output => openedPositions output
def overwrite (positions : List FtsCoord) (values : List Digest) (f : FtsCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = f))).elim 0 Prod.snd
noncomputable def signW (ω : Omega U) (published : T3.Cache) (request : Request) :
    OracleComp WSpec (Option Signature) := do
  let positions := openedFor hU ω published request
  let values ← positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)
  pure (evalWithAnswerFn (Omega.answers hU ω (overwrite positions values))
    (FullGame.authenticatedSign published request))
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
noncomputable def worldGame (ω : Omega U) (adversary : AdversaryP) :
    OracleComp WSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen
  let interaction ← interactionW hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programW hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
end World
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
noncomputable def pairRun (T : Answers) (adversary : AdversaryP) :
    ProbComp (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn T keygen
  let interaction ← interactionT T generated.2 (adversary generated.1 generated.2)
  let verdict := GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1)
  pure (evalWithAnswerFn T verdict, interaction.2.1,
    interaction.2.2 ++ Wots.entriesOf T (SourceReplay.queried T verdict))
end SigGolfCandidate.T3.Security.BPair
end
