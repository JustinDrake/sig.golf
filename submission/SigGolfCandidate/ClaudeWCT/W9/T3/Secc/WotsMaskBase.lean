import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots
import SigGolfCandidate.T3.Secc.WotsMaskBase

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRow a step value then some (Classical.choose h) else none
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr (.inl tweak) =>
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (let output := answers (.inr (.inl tweak))
         if a.chain % 2 = 0 then ChainGraph.joinOutput 0 (output.extractLsb' 128 128)
         else ChainGraph.joinOutput (output.extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak))
  | .inr (.inr other) => answers (.inr (.inr other))
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
theorem referenceDigits_spec (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay ∧ Cost.ValidDigits L.lay (referenceDigits answers L) := by
  unfold referenceDigits
  cases h : referenceSearch answers L with
  | none => exact dummyDigits_spec L.lay
  | some found =>
      obtain ⟨counter, digits⟩ := found
      have hd := (Correctness.counterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L)
        counterLimit 0 counter digits (by decide) h).2.2
      exact ⟨(decode_length_sum hd).1, Cost.validDigits_decode hd⟩
theorem referenceDigits_of_search {answers : Answers} {L : LeafAddr} {counter : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (counter, digits)) : referenceDigits answers L = digits := by
  unfold referenceDigits
  rw [h]
  rfl
theorem depth_le_width (answers : Answers) (a : ChainAddr) (hc : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain :=
  (referenceDigits_spec answers a.key).2 a.chain hc
theorem chain_lt_of_depth (answers : Answers) (a : ChainAddr) (hd : 1 ≤ depth answers a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := (referenceDigits_spec answers a.key).1
  have h0 : depth answers a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (a : ChainAddr) : depth answers a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers a
  · exact (depth_le_width answers a (chain_lt_of_depth answers a hd)).trans (width_le _ _)
  · omega
theorem prefixStep_spec {answers : Answers} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers a input = some step) :
    step < depth answers a ∧ ∃ value, input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers a (chainRow a s v) = if s < depth answers a then some s else none := by
  have h7 := depth_le_seven answers a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers a ∧ chainRow a s v = chainRow a step value)
    exact congrArg some (chainRow_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers a (chainRow a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRow_inj hs (by omega) heq).1
        omega
theorem prefixStep_untouched {answers : Answers} {a : ChainAddr} {input : HashInput}
    (h : Untouched a (.inl (.inr input))) : prefixStep answers a input = none := by
  cases hp : prefixStep answers a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers a; omega))
theorem maskAt_public (answers : Answers) (a : ChainAddr) (input : HashInput) :
    maskAt answers a (.inl (.inr input)) = match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) =
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (if a.chain % 2 = 0 then ChainGraph.joinOutput 0 ((answers (.inr (.inl tweak))).extractLsb' 128 128)
         else ChainGraph.joinOutput ((answers (.inr (.inl tweak))).extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : Untouched a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rw [maskAt_tweak, if_neg (fun h' => h h'.1)]
  · rfl
theorem maskAt_prefix (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers a) :
    maskAt answers a (.inl (.inr (chainRow a s v))) =
      if s + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0 else 0 := by
  have h7 := depth_le_seven answers a
  rw [maskAt_public, prefixStep_chainRow answers a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers a ≤ s)
    (hs' : s < 256) : maskAt answers a (.inl (.inr (chainRow a s v))) = answers (.inl (.inr (chainRow a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers a v hs', if_neg (by omega)]
theorem maskAt_of_depth_zero (answers : Answers) (a : ChainAddr) (hd : depth answers a = 0) :
    maskAt answers a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rw [maskAt_tweak, if_neg (by omega)]
  · rfl
theorem eval_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (Untouched a) program) :
    evalWithAnswerFn (maskAt answers a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).1
theorem queried_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (Untouched a) program) :
    SourceReplay.queried (maskAt answers a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).2
section Programs
variable (a : ChainAddr)
theorem respects_forestPk (index : Nat) (roots : List Digest) :
    Respects (Untouched a) (ClaudeWCT.WCT9.forestPk index roots) :=
  ClaudeWCT.WCT9.Wots.Mask.respects_forestPk a index roots
theorem respects_signForest (index : Nat) (output : HashOutput) :
    Respects (Untouched a) (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.Mask.respects_signForest a index output
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (Untouched a) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_digest a _ _ _) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
end Programs
end Mask
end ClaudeWCT.W9.T3.Security.Wots
