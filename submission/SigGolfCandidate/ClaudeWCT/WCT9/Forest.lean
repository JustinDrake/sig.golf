import SigGolfCandidate.ClaudeWCT.WCT9.Correctness
import SigGolfCandidate.ClaudeWCT.WCT9.Limits

section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def openingStep (index : Nat) (output : HashOutput) (state : List Opening × List Digest)
    (coord : Coord) : M (List Opening × List Digest) := do
  let selected := child output coord
  let (levels, values) ← buildCoordinate index coord selected (rank output coord)
  let path := (List.range 7).map fun level =>
    (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
  let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
  pure (state.1 ++ [opening], state.2 ++ [(levels.getD 7 []).getD 0 0])
theorem signPayload_rows (cache : Cache) (message : Message) : signPayload cache message = (do
    let rho ← privateNonce message
    let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
    let index := output.toNat % 2 ^ 31
    let state ← (List.finRange 9).foldlM (openingStep index output) ([], [])
    let root ← forestPk index state.2
    let some layers ← signLayers cache index 4 root | pure none
    pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
      fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)) := rfl
theorem eval_openingStep (answers : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List Digest) (coord : Coord) :
    evalWithAnswerFn answers (openingStep index output state coord) =
      (state.1 ++ [expectedOpening answers index output coord],
        state.2 ++ [coordinateRoot answers index coord]) := by
  have hroot := built_root answers index coord (child output coord) (rank output coord)
  unfold openingStep expectedOpening
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn answers
    (buildCoordinate index coord (child output coord) (rank output coord)) = built at hroot ⊢
  obtain ⟨levels, values⟩ := built
  simp only [evalWithAnswerFn_pure] at hroot ⊢
  rw [← hroot]
  rfl
def SignerRows (answers : Answers) (index : Nat) (output : HashOutput) (done : Nat)
    (state : List Opening × List Digest) : Prop :=
  state.1.length = done ∧ state.2.length = done ∧
    (∀ c : Coord, c.val < done →
      state.1.getD c.val ⟨fun _ => 0, fun _ => 0⟩ = expectedOpening answers index output c) ∧
    (∀ c : Coord, c.val < done → state.2.getD c.val 0 = coordinateRoot answers index c)
theorem signerRows_step (answers : Answers) (index : Nat) (output : HashOutput) (c : Coord)
    (state : List Opening × List Digest) (hrows : SignerRows answers index output c.val state) :
    SignerRows answers index output (c.val + 1)
      (state.1 ++ [expectedOpening answers index output c],
        state.2 ++ [coordinateRoot answers index c]) := by
  rcases hrows with ⟨h1, h2, h3, h4⟩
  refine ⟨by simp [h1], by simp [h2], ?_, ?_⟩
  · intro d hd
    rw [getD_append_singleton, h1]
    by_cases hdc : d.val < c.val
    · rw [if_pos hdc]; exact h3 d hdc
    · have he : d = c := Fin.ext (by omega)
      subst d
      simp
  · intro d hd
    rw [getD_append_singleton, h2]
    by_cases hdc : d.val < c.val
    · rw [if_pos hdc]; exact h4 d hdc
    · have he : d = c := Fin.ext (by omega)
      subst d
      simp
theorem eval_signerRows (answers : Answers) (index : Nat) (output : HashOutput) :
    SignerRows answers index output 9
      (evalWithAnswerFn answers ((List.finRange 9).foldlM (openingStep index output) ([], []))) := by
  have h := eval_foldlM_list_inv answers (List.finRange 9) (openingStep index output)
    (SignerRows answers index output) ([], []) (by simp [SignerRows]) (by
      intro i hi state hstate
      have hi9 : i < 9 := by simpa using hi
      simp only [List.getElem_finRange, Fin.cast_mk]
      rw [eval_openingStep]
      exact signerRows_step answers index output ⟨i, hi9⟩ state hstate)
  simpa only [List.length_finRange] using h
theorem signerRows_roots (answers : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List Digest) (hrows : SignerRows answers index output 9 state) :
    state.2 = List.ofFn (coordinateRoot answers index) := by
  apply List.ext_getElem (by simp [hrows.2.1])
  intro i hi hj
  have hi9 : i < 9 := by simpa using hj
  rw [← List.getD_eq_getElem _ (0 : Digest) hi, hrows.2.2.2 ⟨i, hi9⟩ hi9, List.getElem_ofFn]
theorem signPayload_expands (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ w : Witness, evalWithAnswerFn answers
      (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w := by
  rw [signPayload_rows] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      have hrows := eval_signerRows answers (output.toNat % 2 ^ 31) output
      generalize evalWithAnswerFn answers ((List.finRange 9).foldlM
        (openingStep (output.toNat % 2 ^ 31) output) ([], [])) = state at he hrows
      rw [signerRows_roots answers _ output state hrows] at he
      cases hl : evalWithAnswerFn answers (signLayers cache (output.toNat % 2 ^ 31) 4
        (evalWithAnswerFn answers (forestPk (output.toNat % 2 ^ 31)
          (List.ofFn (coordinateRoot answers (output.toNat % 2 ^ 31)))))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          let sig : Signature := ⟨evalWithAnswerFn answers (privateNonce message),
            fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
            fun lay => piecesSignature lay (pieces.getD lay.val ([], []))⟩
          change ∃ w : Witness, evalWithAnswerFn answers
            (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w
          have hf := recoverFts_honest answers sig (output.toNat % 2 ^ 31) output
            (fun coord => hrows.2.2.1 coord coord.isLt)
          have hparts : PiecesAgree (toT3Signature sig) pieces 4 := fun _ _ => rfl
          obtain ⟨counters, _, hreplay⟩ := (signLayers_expandLayers answers cache
            (output.toNat % 2 ^ 31) hcache (Nat.mod_lt _ (by positivity)) 4 (by decide) _ pieces
            hl).2 (toT3Signature sig) hparts
          refine ⟨⟨sig, counter, fun lay => counters.getD lay.val 0⟩, ?_⟩
          unfold expand
          rw [show sig.rho = evalWithAnswerFn answers (privateNonce message) by rfl]
          simp only [evalWithAnswerFn_bind, hd, hf, hreplay, layerResultRoot,
            show ¬(4 : Nat) = 0 by decide, ite_false, ne_eq, not_true_eq_false,
            evalWithAnswerFn_pure]
theorem sign_valid_cache (answers : Answers) (result : Digest × Cache) (message : Message)
    (hvalid : CacheTagCorrect answers result) :
    evalWithAnswerFn answers (sign result.2 message) =
      evalWithAnswerFn answers (signPayload result.2 message) := by
  simp only [CacheTagCorrect] at hvalid
  simp only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false]
theorem signing_success_valid (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message) (sig : Signature)
    (hsign : evalWithAnswerFn answers (sign keys.2 message) = some sig) :
    ∃ w : Witness, evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true := by
  rw [sign_valid_cache answers keys message hkeys.2.2] at hsign
  obtain ⟨w, hw⟩ := signPayload_expands answers keys.2 message sig hkeys.2.1 hsign
  have he : evalWithAnswerFn answers (expand message keys.1 sig) = some w := by rwa [hkeys.1]
  exact ⟨w, he, expand_implies_verify answers message keys.1 sig w he⟩
def SigningCorrect (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (sign keys.2 message) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true
theorem keygen_correct (answers : Answers) :
    KeygenCorrect answers (evalWithAnswerFn answers keygen) :=
  SigGolfCandidate.T3.Correctness.keygen_correct answers
theorem honest_signing_success_valid (answers : Answers) :
    SigningCorrect answers (evalWithAnswerFn answers keygen) :=
  signing_success_valid answers _ (keygen_correct answers)
def RealizedSigningCorrect (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
      evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
theorem realized_honest_signing_success_valid (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) :
    RealizedSigningCorrect answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningCorrect
  simp only [realize_eval]
  exact honest_signing_success_valid (answers.compose (realHandler secret))
end ClaudeWCT.WCT9
end

section


namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def forestRows (index : Nat) (output : HashOutput) : M (List Opening × List Digest) :=
  (List.finRange 9).foldlM (openingStep index output) ([], [])
def signForest (index : Nat) (output : HashOutput) : M (List Opening × Digest) := do
  let state ← forestRows index output
  let root ← forestPk index state.2
  pure (state.1, root)
def assembledSignature (rho : Digest) (openings : List Opening) (pieces : List Pieces) : Signature :=
  ⟨rho, fun coord => openings.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (pieces.getD lay.val ([], []))⟩
@[simp] theorem assembledSignature_rho (rho : Digest) (openings : List Opening) (pieces : List Pieces) :
    (assembledSignature rho openings pieces).rho = rho := rfl
@[simp] theorem assembledSignature_openings (rho : Digest) (openings : List Opening)
    (pieces : List Pieces) (coord : Coord) :
    (assembledSignature rho openings pieces).openings coord =
      openings.getD coord.val ⟨fun _ => 0, fun _ => 0⟩ := rfl
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (forestPk index (List.ofFn (coordinateRoot answers index)))
theorem signPayloadWith_eq (limit : Nat) (cache : Cache) (message : Message) :
    signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 limit | pure none
      let forest ← signForest (output.toNat % 2 ^ 31) output
      let some pieces ← signLayers cache (output.toNat % 2 ^ 31) 4 forest.2 | pure none
      pure (some (assembledSignature rho forest.1 pieces))) := by
  unfold signPayloadWith signForest forestRows
  refine bind_congr fun rho => bind_congr fun found => ?_
  rcases found with _ | ⟨_, output⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rfl
theorem signPayload_eq (cache : Cache) (message : Message) :
    signPayload cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 SigGolfCandidate.T3.attemptLimit | pure none
      let forest ← signForest (output.toNat % 2 ^ 31) output
      let some pieces ← signLayers cache (output.toNat % 2 ^ 31) 4 forest.2 | pure none
      pure (some (assembledSignature rho forest.1 pieces))) :=
  signPayloadWith_eq SigGolfCandidate.T3.attemptLimit cache message
theorem Rev3.signPayload_eq (cache : Cache) (message : Message) :
    Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 digestAttemptLimit | pure none
      let forest ← signForest (output.toNat % 2 ^ 31) output
      let some pieces ← signLayers cache (output.toNat % 2 ^ 31) 4 forest.2 | pure none
      pure (some (assembledSignature rho forest.1 pieces))) :=
  signPayloadWith_eq digestAttemptLimit cache message
theorem eval_forestRows (answers : Answers) (index : Nat) (output : HashOutput) :
    evalWithAnswerFn answers (forestRows index output) =
      (List.ofFn (expectedOpening answers index output), List.ofFn (coordinateRoot answers index)) := by
  have hrows := eval_signerRows answers index output
  unfold forestRows
  generalize evalWithAnswerFn answers ((List.finRange 9).foldlM (openingStep index output) ([], [])) =
    state at hrows ⊢
  have h2 := signerRows_roots answers index output state hrows
  refine Prod.ext ?_ h2
  apply List.ext_getElem (by simp [hrows.1])
  intro i hi hj
  have hi9 : i < 9 := by simpa using hj
  rw [← List.getD_eq_getElem _ ⟨fun _ => 0, fun _ => 0⟩ hi, hrows.2.2.1 ⟨i, hi9⟩ hi9, List.getElem_ofFn]
theorem eval_signForest (answers : Answers) (index : Nat) (output : HashOutput) :
    evalWithAnswerFn answers (signForest index output) =
      (List.ofFn (expectedOpening answers index output), honestForest answers index) := by
  unfold signForest
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_forestRows]
  rfl
theorem signForest_root (answers : Answers) (index : Nat) (output : HashOutput) :
    (evalWithAnswerFn answers (signForest index output)).2 = honestForest answers index := by
  rw [eval_signForest]
theorem signForest_openings (answers : Answers) (index : Nat) (output : HashOutput) (coord : Coord) :
    (evalWithAnswerFn answers (signForest index output)).1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩ =
      expectedOpening answers index output coord := by
  rw [eval_signForest]
  simp only
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact coord.isLt), List.getElem_ofFn]
theorem signForest_length (answers : Answers) (index : Nat) (output : HashOutput) :
    (evalWithAnswerFn answers (signForest index output)).1.length = 9 := by
  rw [eval_signForest]
  simp only [List.length_ofFn]
theorem assembled_forest_recovery (answers : Answers) (rho : Digest) (index : Nat) (output : HashOutput)
    (pieces : List Pieces) :
    evalWithAnswerFn answers (recoverFts
      (assembledSignature rho (evalWithAnswerFn answers (signForest index output)).1 pieces) index output) =
      (evalWithAnswerFn answers (signForest index output)).2 := by
  rw [recoverFts_honest answers _ index output (fun coord => by
    rw [assembledSignature_openings, signForest_openings]), signForest_root]
  rfl
theorem expandWith_implies_verifyWith (limit : Nat) (hlimit : limit ≤ 2 ^ 32) (answers : Answers)
    (message : Message) (pk : Digest) (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expandWith limit message pk sig) = some w) :
    evalWithAnswerFn answers (verifyWith limit message pk w) = true := by
  simp only [expandWith, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 limit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (expandLayers (toT3Signature sig) (output.toNat % 2 ^ 31) 4
          (evalWithAnswerFn answers (recoverFts sig (output.toNat % 2 ^ 31) output))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hroot
            have hroot : root = pk := by simpa using hroot
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst w
            obtain ⟨_, hcounter, houtput, hadm⟩ := digestSearch_some_good answers sig.rho message
              limit 0 counter output (by omega) hd
            have hnot : ¬counter.toNat ≥ limit := by omega
            have hverified := (expandLayers_verified answers (toT3Signature sig)
              (output.toNat % 2 ^ 31) 4 (by decide) _ root counters hl).2
              (toT3Witness ⟨sig, counter, fun lay => counters.getD lay.val 0⟩) rfl (fun _ _ => rfl)
            simp only [verifyWith, hnot, ite_false, evalWithAnswerFn_bind, houtput, hadm,
              Bool.not_true, Bool.false_eq_true, hverified, evalWithAnswerFn_pure, hroot,
              beq_self_eq_true]
theorem signPayloadWith_expands (limit : Nat) (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayloadWith limit cache message) = some sig) :
    ∃ w : Witness, evalWithAnswerFn answers
      (expandWith limit message (treeValue (builtTree answers 0 0) 12 0) sig) = some w := by
  rw [signPayloadWith_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 limit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind, signForest_root] at he
      cases hl : evalWithAnswerFn answers (signLayers cache (output.toNat % 2 ^ 31) 4
        (honestForest answers (output.toNat % 2 ^ 31))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          have hf := assembled_forest_recovery answers (evalWithAnswerFn answers (privateNonce message))
            (output.toNat % 2 ^ 31) output pieces
          rw [signForest_root] at hf
          have hparts : PiecesAgree (toT3Signature (assembledSignature
              (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (signForest (output.toNat % 2 ^ 31) output)).1 pieces)) pieces 4 :=
            fun _ _ => rfl
          obtain ⟨counters, _, hreplay⟩ := (signLayers_expandLayers answers cache
            (output.toNat % 2 ^ 31) hcache (Nat.mod_lt _ (by positivity)) 4 (by decide) _ pieces
            hl).2 _ hparts
          refine ⟨⟨assembledSignature (evalWithAnswerFn answers (privateNonce message))
            (evalWithAnswerFn answers (signForest (output.toNat % 2 ^ 31) output)).1 pieces,
            counter, fun lay => counters.getD lay.val 0⟩, ?_⟩
          unfold expandWith
          simp only [assembledSignature_rho, evalWithAnswerFn_bind, hd, hf, hreplay, layerResultRoot,
            show ¬(4 : Nat) = 0 by decide, ite_false, ne_eq, not_true_eq_false, evalWithAnswerFn_pure]
theorem signWith_valid_cache (limit : Nat) (answers : Answers) (result : Digest × Cache)
    (message : Message) (hvalid : CacheTagCorrect answers result) :
    evalWithAnswerFn answers (signWith limit result.2 message) =
      evalWithAnswerFn answers (signPayloadWith limit result.2 message) := by
  simp only [CacheTagCorrect] at hvalid
  simp only [signWith, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false]
theorem signingWith_success_valid (limit : Nat) (hlimit : limit ≤ 2 ^ 32) (answers : Answers)
    (keys : Digest × Cache) (hkeys : KeygenCorrect answers keys) (message : Message) (sig : Signature)
    (hsign : evalWithAnswerFn answers (signWith limit keys.2 message) = some sig) :
    ∃ w : Witness, evalWithAnswerFn answers (expandWith limit message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verifyWith limit message keys.1 w) = true := by
  rw [signWith_valid_cache limit answers keys message hkeys.2.2] at hsign
  obtain ⟨w, hw⟩ := signPayloadWith_expands limit answers keys.2 message sig hkeys.2.1 hsign
  have he : evalWithAnswerFn answers (expandWith limit message keys.1 sig) = some w := by rwa [hkeys.1]
  exact ⟨w, he, expandWith_implies_verifyWith limit hlimit answers message keys.1 sig w he⟩
theorem digestSearch_none_iff (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter,
      evalWithAnswerFn answers (digestSearch rho message counter fuel) = none ↔
      ∀ offset, offset < fuel → admissible (evalWithAnswerFn answers
        (digest rho message (BitVec.ofNat 32 (counter + offset)))) = false := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [digestSearch]
  | succ fuel ih =>
      intro counter
      simp only [digestSearch, evalWithAnswerFn_bind]
      split
      · rename_i hgood
        simp only [evalWithAnswerFn_pure, reduceCtorEq, false_iff]
        intro hall
        have := hall 0 (by omega)
        simp only [Nat.add_zero, hgood, Bool.true_eq_false] at this
      · rename_i hbad
        have hbad : admissible (evalWithAnswerFn answers
          (digest rho message (BitVec.ofNat 32 counter))) = false := by simpa using hbad
        rw [ih]
        constructor
        · intro hall offset hoff
          cases offset with
          | zero => simpa using hbad
          | succ offset =>
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall offset (by omega)
        · intro hall offset hoff
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall (offset + 1) (by omega)
theorem verifyWith_counter_ge (limit : Nat) (answers : Answers) (message : Message) (pk : Digest) (w : Witness)
    (h : limit ≤ w.digestCounter.toNat) : evalWithAnswerFn answers (verifyWith limit message pk w) = false := by
  simp only [verifyWith, ge_iff_le, h, ite_true, evalWithAnswerFn_pure]
theorem verifyWith_inadmissible (limit : Nat) (answers : Answers) (message : Message) (pk : Digest) (w : Witness)
    (h : admissible (evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)) = false) :
    evalWithAnswerFn answers (verifyWith limit message pk w) = false := by
  by_cases hc : limit ≤ w.digestCounter.toNat
  · exact verifyWith_counter_ge limit answers message pk w hc
  · simp only [verifyWith, ge_iff_le, hc, ite_false, evalWithAnswerFn_bind, h, Bool.not_false, ite_true,
      evalWithAnswerFn_pure]
namespace Rev3
theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness) (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true :=
  expandWith_implies_verifyWith digestAttemptLimit digestAttemptLimit_le answers message pk sig w he
def SigningCorrect (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (sign keys.2 message) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true
theorem signing_success_valid (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) : SigningCorrect answers keys :=
  fun message sig hsign =>
    signingWith_success_valid digestAttemptLimit digestAttemptLimit_le answers keys hkeys message sig hsign
theorem honest_signing_success_valid (answers : Answers) :
    SigningCorrect answers (evalWithAnswerFn answers keygen) :=
  signing_success_valid answers _ (ClaudeWCT.WCT9.keygen_correct answers)
def RealizedSigningCorrect (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
      evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
theorem realized_honest_signing_success_valid (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) :
    RealizedSigningCorrect answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningCorrect
  simp only [realize_eval]
  exact honest_signing_success_valid (answers.compose (realHandler secret))
end Rev3
end ClaudeWCT.WCT9
end
