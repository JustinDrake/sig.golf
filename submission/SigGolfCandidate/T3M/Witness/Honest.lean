import SigGolfCandidate.T3M.Witness.Normal
import SigGolfCandidate.T3M.Witness.Roundtrip

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
def honestProgramCore (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
def honestProgramB (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let wb ← expandB message keys.1 sig
    match wb with
    | none => pure false
    | some wb => verifyP message keys.1 wb
def isHash : Spec.Domain → Prop
  | .inl (.inl _) => False
  | _ => True
def isPublic : Spec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False
def ExpandEqExpandN : Prop := ∀ (m : Message) (pk : Digest) (σ : Signature),
  expand m pk σ = Option.map Prod.snd <$> expandN m pk σ
def VerifyPWitEncEval : Prop := ∀ (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature)
    (N : HashOutput) (w : Witness),
  evalWithAnswerFn answers (expandN m pk σ) = some (N, w) →
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (verify m pk w))
def HonestBEval : Prop := ∀ (answers : Correctness.Answers) (m : Message),
  evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m)
theorem expand_eq_expandN (m : Message) (pk : Digest) (σ : Signature) :
    expand m pk σ = Option.map Prod.snd <$> expandN m pk σ := by
  unfold expand expandN
  rw [map_bind]; congr 1; funext r
  rcases r with _ | ⟨counter, output⟩
  · simp
  · simp only
    rw [map_bind]; congr 1; funext r
    rcases r with _ | root
    · simp
    · simp only
      rw [map_bind]; congr 1; funext r
      rcases r with _ | ⟨root, counters⟩
      · simp
      · simp only
        split <;> simp
theorem expandEqExpandN_holds : ExpandEqExpandN := expand_eq_expandN
theorem recoverFtsP_canon (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 115) :
    recoverFtsP sig pads index chosen = (do
      let roots ← (List.range 7).foldlM (fun roots c => (fun v => roots ++ [v]) <$>
        coordCanon index c (leafHP index c (selectedLeaves (chosen.getD c ⟨0, []⟩))
            ((List.range 3).map (fun j => sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
          (valOf sig.proof (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
          (valOf pads.fold (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
          (selLeaf (chosen.getD c ⟨0, []⟩) 0) (selLeaf (chosen.getD c ⟨0, []⟩) 1)
          (selLeaf (chosen.getD c ⟨0, []⟩) 2)) []
      if !(List.range (115 - slotBase chosen 7)).all (fun j =>
          decide (sig.proof ⟨(slotBase chosen 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
      pure (some (← forestPk index roots))) := by
  rw [recoverFtsP_eq]
  have B := foldlM_canon (ftsStepP sig pads index chosen) _ (fun c => slotBase chosen c)
    (fun c hc7 roots => by
      have hb1 := slotBase_mono chosen (show c + 1 ≤ 7 by omega)
      rw [slotBase_succ] at hb1 ⊢
      exact ftsStepP_canon sig pads index chosen roots _ c (hc c hc7) (by omega) _ _
        (slotsMatch_valOf _ _ _ _ (slotPositions_nodup _))) 7 le_rfl
  simp only [show slotBase chosen 0 = 0 from rfl] at B
  rw [B, bind_map_left]
theorem eval_recoverFtsP_tail (answers : Correctness.Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 115) (root : Digest)
    (h : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some root) :
    ∀ k : Fin 115, slotBase chosen 7 ≤ k.val → sig.proof k = 0 := by
  rw [recoverFtsP_canon sig pads index chosen hc hle, evalWithAnswerFn_bind] at h
  intro k hk
  by_contra hne
  have hall : ((List.range (115 - slotBase chosen 7)).all (fun j =>
      decide (sig.proof ⟨(slotBase chosen 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0))) = false := by
    by_contra hc
    rw [Bool.not_eq_false, List.all_eq_true] at hc
    have := hc (k.val - slotBase chosen 7) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    rw [show slotBase chosen 7 + (k.val - slotBase chosen 7) = k.val by omega] at this
    apply hne
    rw [← this]; congr 1; ext; simp [Nat.mod_eq_of_lt k.isLt]
  simp only [hall, Bool.not_false, if_true, evalWithAnswerFn_pure] at h
  exact absurd h (by simp)
theorem selectionsOk_of_admissible (N : HashOutput) (h : admissible (selections N) = true) :
    selectionsOk (selections N) = true := by
  unfold selectionsOk
  rw [List.all_eq_true]
  intro sel hm
  have hn : sel.leaves.Nodup := by
    simp only [admissible, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1 sel hm
  have hs := Correctness.selection_leaves_sorted N sel hm
  have hl := selection_leaves_length N sel hm
  obtain ⟨a, b, c, he⟩ := List.length_eq_three.mp hl
  rw [he] at hn hs ⊢
  rw [List.sortedLE_iff_pairwise] at hs
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
structure ExpandFacts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (w : Witness) : Prop where
  sig : w.signature = σ
  dc : w.digestCounter.toNat < attemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : admissible (selections N) = true
  root : ∃ root, evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some root
theorem expandN_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (w : Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ExpandFacts answers m pk σ N w := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hf : evalWithAnswerFn answers (recoverFts σ (output.toNat % 2 ^ 31) (selections output)) with
      | none => simp only [hf, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some forest =>
          simp only [hf, evalWithAnswerFn_bind] at he
          cases hl : evalWithAnswerFn answers (expandLayers σ (output.toNat % 2 ^ 31) 4 forest) with
          | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some layers =>
              obtain ⟨root, counters⟩ := layers
              simp only [hl] at he
              split at he
              · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
              · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                obtain ⟨_, hcounter, houtput, hadm⟩ := Correctness.digestSearch_some answers σ.rho m
                  attemptLimit 0 counter output (by decide) hd
                exact ⟨rfl, by simpa using hcounter, houtput, hadm, ⟨forest, hf⟩⟩
theorem eval_map (answers : Correctness.Answers) {α β : Type} (f : α → β) (oa : M α) :
    evalWithAnswerFn answers (f <$> oa) = f (evalWithAnswerFn answers oa) := by
  rw [map_eq_bind_pure_comp, evalWithAnswerFn_bind]; rfl
theorem eval_countCalls_fst (answers : Correctness.Answers) {α : Type} (oa : M α) :
    (evalWithAnswerFn answers (Cost.countCalls oa)).1 = evalWithAnswerFn answers oa := by
  have := congrArg (evalWithAnswerFn answers) (Cost.fst_countWith (fun _ => 1) oa)
  rw [eval_map] at this
  exact this
theorem eval_countCalls_bind_congr (answers : Correctness.Answers) {α β : Type} (oa : M α) (f g : α → M β)
    (h : f (evalWithAnswerFn answers oa) = g (evalWithAnswerFn answers oa)) :
    evalWithAnswerFn answers (Cost.countCalls (oa >>= f)) = evalWithAnswerFn answers (Cost.countCalls (oa >>= g)) := by
  have h1 := eval_countCalls_fst answers oa
  unfold Cost.countCalls at h1 ⊢
  rw [Cost.countWith_bind, Cost.countWith_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, h1, h]
theorem verifyP_witEnc_eval (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature)
    (N : HashOutput) (w : Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (verify m pk w)) := by
  have F := expandN_facts answers m pk σ N w he
  have hsel := selectionsOk_of_admissible N F.adm
  have hc := chosenOk_of N hsel
  have hle := slotBase_seven_le N hc F.adm
  obtain ⟨root, hroot⟩ := F.root
  have htail : ∀ k : Fin 115, slotBase (selections N) 7 ≤ k.val → w.signature.proof k = 0 := by
    rw [F.sig]
    exact eval_recoverFtsP_tail answers σ 0 _ _ hc hle root (by rw [recoverFtsP_zero]; exact hroot)
  have hv : verifyP m pk (witEnc N w) =
      digest w.signature.rho m w.digestCounter >>= verifyTailP pk (witEnc N w) := by
    rw [verifyP_eq_tail]
    unfold digestP
    rw [wdc_witEnc, wrho_witEnc, if_neg (by have := F.dc; omega), bind_map_left]
  have hw : verify m pk w = digest w.signature.rho m w.digestCounter >>= fun N' => verifyPadsTail pk N' w 0 := by
    rw [← verifyPads_zero]
    unfold verifyPads
    rw [if_neg (by have := F.dc; omega)]
  rw [hv, hw]
  apply eval_countCalls_bind_congr
  rw [F.sig, F.digest, verifyTailP_shaped pk N _ (shaped_witEnc N w hsel F.adm),
    witDecP_witEnc N w hc hle htail, padDecP_witEnc N w hc hle]
theorem verifyPWitEncEval_holds : VerifyPWitEncEval := verifyP_witEnc_eval
theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) :
    evalWithAnswerFn answers (expandB m pk σ) =
      (evalWithAnswerFn answers (expandN m pk σ)).map (fun x => witEnc x.1 x.2) := by
  unfold expandB; rw [eval_map]
theorem honestB_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m) := by
  unfold honestProgramB honestProgramCore
  simp only [evalWithAnswerFn_bind]
  cases hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 m) with
  | none => rfl
  | some sig =>
      simp only []
      rw [expand_eq_expandN, evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_map, eval_expandB]
      cases hx : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers keygen).1 sig) with
      | none => rfl
      | some x =>
          obtain ⟨N, w⟩ := x
          simp only [Option.map_some]
          have := verifyP_witEnc_eval answers m _ sig N w hx
          have h1 := congrArg Prod.fst this
          rwa [eval_countCalls_fst, eval_countCalls_fst] at h1
theorem honestBEval_holds : HonestBEval := honestB_eval
end SigGolfCandidate.T3M
