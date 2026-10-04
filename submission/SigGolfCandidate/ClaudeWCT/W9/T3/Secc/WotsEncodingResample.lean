import SigGolfCandidate.T3.Secc.WotsEncodingResample
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingCongr
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraph

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def EncOk (lay : Layer) (msg : WCT9.LayerMsg) (pad : BitVec 96) : Prop :=
  Extract.msgFits lay msg ∧ (lay.val = 3 → pad = 0)
abbrev EncIndex := {e : CanonGraph.LeafPos × WCT9.LayerMsg × BitVec 32 × BitVec 96 // EncOk e.1.lay e.2.1 e.2.2.2}
instance encIndex_finite : Finite EncIndex := by
  haveI : Finite WCT9.LayerMsg := Finite.of_equiv _ CanonGraph.layerMsgEquiv.symm
  infer_instance
def encInput (e : EncIndex) : HashInput := encRow (leafOf e.1.1) e.1.2.1 e.1.2.2.1 e.1.2.2.2
def encIdx (L : CanonGraph.LeafPos) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96)
    (hfit : Extract.msgFits L.lay msg) : EncIndex :=
  ⟨(L, msg, counter, if L.lay.val = 3 then 0 else pad), hfit, fun h => if_pos h⟩
theorem encInput_encIdx (L : CanonGraph.LeafPos) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96)
    (hfit : Extract.msgFits L.lay msg) : encInput (encIdx L msg counter pad hfit) = encRow (leafOf L) msg counter pad := by
  unfold encInput encIdx
  dsimp only
  split_ifs with h3
  · cases msg with
    | forest root => rfl
    | pair l r =>
        change L.lay.val < 3 at hfit
        omega
  · rfl
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 :=
  ClaudeWCT.W9.T3M.BC.layerEncodingRow_length _ _ _ _ _ _
theorem encInput_injective : Function.Injective encInput := by
  rintro ⟨⟨L, m, c, p⟩, hf, hp⟩ ⟨⟨L', m', c', p'⟩, hf', hp'⟩ he
  have ht : L.tree.val < 2 ^ 40 := lt_of_lt_of_le L.tree.isLt (by norm_num)
  have ht' : L'.tree.val < 2 ^ 40 := lt_of_lt_of_le L'.tree.isLt (by norm_num)
  have hl : L.leaf.val < 2 ^ 32 := lt_of_lt_of_le L.leaf.isLt (by norm_num)
  have hl' : L'.leaf.val < 2 ^ 32 := lt_of_lt_of_le L'.leaf.isLt (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_injective ht hl ht' hl' hf hf' he
  obtain ⟨lay, tree, leaf⟩ := L
  obtain ⟨lay', tree', leaf'⟩ := L'
  simp only at h1 h2 h3 hf hp hf' hp'
  subst h1 h4 h5
  have : tree = tree' := Fin.ext h2
  have : leaf = leaf' := Fin.ext h3
  subst tree leaf
  have hpp : p = p' := by
    cases m with
    | forest root =>
        change lay.val = 3 at hf
        rw [hp hf, hp' hf]
    | pair l r => exact h6 l r rfl
  subst hpp
  rfl
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
theorem encInput_encHeader (e : EncIndex) : EncHeader (encInput e) :=
  ⟨e.1.1.lay.val, e.1.1.tree.val, 0, e.1.1.leaf.val,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _⟩
theorem reached_encInput {T : Answers} {L : CanonGraph.LeafPos} {input : HashInput}
    (h : Reached T (leafOf L) input) :
    ∃ c : BitVec 32, input = encInput ⟨(L, leafMsg T (leafOf L), c, 0), msgFits_leafMsg T (leafOf L), fun _ => rfl⟩ := by
  obtain ⟨c, -, rfl, -⟩ := h
  exact ⟨_, rfl⟩
def Free (T : Answers) (e : EncIndex) : Prop := ¬ Reached T (leafOf e.1.1) (encInput e)
def freeSet (T : Answers) : Set EncIndex := {e | Free T e}
theorem reached_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (L : CanonGraph.LeafPos)
    (input : HashInput) : Reached T' (leafOf L) input ↔ Reached T (leafOf L) input := by
  have hm : leafMsg T' (leafOf L) = leafMsg T (leafOf L) := leafMsg_congr_nonEnc (nonEnc_of_honest h) _
  have hrow : ∀ c, c < counterLimit → (∀ c' < c, decode (leafOf L).lay (low (T (.inl (.inr
      (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c') 0))))) = none) →
      T' (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0))) =
        T (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0))) := by
    intro c hc hprev
    exact h _ (Or.inr ⟨L, c, hc, rfl, hprev⟩)
  unfold Reached
  rw [hm]
  constructor
  · rintro ⟨c, hc, rfl, hprev⟩
    refine ⟨c, hc, rfl, fun c' hc' => ?_⟩
    by_contra hvalid
    have hex : ∃ c'', c'' < c ∧ decode (leafOf L).lay (low (T (.inl (.inr
        (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'') 0))))) ≠ none := ⟨c', hc', hvalid⟩
    classical
    let c₀ := Nat.find hex
    have hc₀ : c₀ < c ∧ _ := Nat.find_spec hex
    have hmin : ∀ c'' < c₀, decode (leafOf L).lay (low (T (.inl (.inr
        (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'') 0))))) = none := by
      intro c'' hc''
      have := Nat.find_min hex hc''
      push Not at this
      exact this (lt_trans hc'' hc₀.1)
    have hagree := hrow c₀ (lt_trans hc₀.1 hc) hmin
    apply hc₀.2
    rw [← hagree]
    exact hprev c₀ hc₀.1
  · rintro ⟨c, hc, rfl, hprev⟩
    refine ⟨c, hc, rfl, fun c' hc' => ?_⟩
    have hprev' : ∀ c'' < c', decode (leafOf L).lay (low (T (.inl (.inr
        (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'') 0))))) = none :=
      fun c'' hc'' => hprev c'' (lt_trans hc'' hc')
    rw [hrow c' (lt_trans hc' hc) hprev']
    exact hprev c' hc'
theorem free_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) : freeSet T' = freeSet T := by
  ext e
  simp only [freeSet, Set.mem_ofPred_eq, Free]
  rw [reached_congr h]
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
theorem ov_at (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput)
    (e : k) : ov k pub y ⟨encInput e.val, hU (encInput_short e.val)⟩ = y e := by
  unfold ov
  have h : ∃ e', e' ∈ k ∧ encInput e' = encInput e.val := ⟨e.val, e.property, rfl⟩
  rw [dif_pos h]
  have he : Classical.choose h = e.val := encInput_injective (Classical.choose_spec h).2
  congr 1
  exact Subtype.ext he
theorem ov_other (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) (u : U)
    (hu : ∀ e, e ∈ k → encInput e ≠ u.val) : ov k pub y u = pub u := by
  unfold ov
  rw [dif_neg]
  rintro ⟨e, he, heq⟩
  exact hu e he heq
theorem rd_ov (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) :
    rd hU k (ov k pub y) = y := by
  funext e
  exact ov_at hU k pub y e
theorem ov_ov_rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput)
    (y : k → HashOutput) : ov k (ov k pub y) (rd hU k pub) = pub := by
  funext u
  unfold ov
  split_ifs with h
  · unfold rd
    congr 1
    exact Subtype.ext ((Classical.choose_spec h).2)
  · rfl
end Overwrite
section Tables
variable (U : Finset HashInput)
theorem honest_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    ∀ q, HonestQ (eagerAnswers U privateTable pub) q →
      eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) q =
        eagerAnswers U privateTable pub q := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
        eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
      apply ov_other
      intro e he heq
      rcases hq with hnon | ⟨L, hr⟩
      · have h' : encInput e = input := heq
        exact hnon (h' ▸ encInput_encHeader e)
      · obtain ⟨c, hc⟩ := reached_encInput hr
        have hee := encInput_injective ((show encInput e = input from heq).trans hc)
        apply he
        rw [hee, ← hc]
        exact hr
    · rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · simp only [eagerAnswers]
theorem free_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    freeSet (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) =
      freeSet (eagerAnswers U privateTable pub) :=
  free_congr (honest_ov U privateTable pub y)
theorem public_resample (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput))
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
          F (ov (freeSet (eagerAnswers U privateTable pub)) pub y) :=
  @uniform_resample_tsum (U → HashOutput) (Set EncIndex) _ _ (fun k : Set EncIndex => k → HashOutput) iX _
    (fun pub => freeSet (eagerAnswers U privateTable pub)) (fun k pub y => ov k pub y) (fun k pub => rd hU k pub)
    (fun pub y => rd_ov hU _ pub y) (fun pub y => ov_ov_rd hU _ pub y) (fun pub y => free_ov U privateTable pub y) F
end Tables
end Enc
end ClaudeWCT.W9.T3.Security.Wots
