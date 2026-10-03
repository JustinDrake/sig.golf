import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.PaddedWitness
import SigGolfCandidate.T3.Secc.WotsExtractWord
import SigGolfCandidate.T3.Secc.WotsExtractLayer
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low encodingRow dummyDigits_valid)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceSearch_decode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    decode L.lay (low (answers (.inl (.inr (encodingRow L (leafMsg answers L) c))))) = some digits :=
  (Correctness.counterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L) counterLimit 0 c digits
    (by norm_num [counterLimit]) h).2.2
theorem referenceDigits_decode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, decode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact SigGolfCandidate.T3.Security.Wots.dummyDigits_valid L.lay
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_decode answers L hs⟩
theorem depth_le (answers : Answers) (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers a.key
  have := decode_digit_max hv a.chain ha
  unfold depth
  omega
theorem referenceDigits_length (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers L
  exact (decode_length_sum hv).1
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h1 hsub,
    SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, answer, hm, hne, hd⟩ := h
  exact ⟨message, counter, answer, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, answer, digits, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, answer, digits, hsub _ hm, hne, hd, hl, hu⟩
theorem structuralHit_mono (h : StructuralHit answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    StructuralHit answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hc, hh⟩
end mono
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
theorem WotsPrimitive.mono {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitive answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') : WotsPrimitive answers trace' := by
  rcases h with ⟨L, h⟩ | h | ⟨a, h⟩ | ⟨a, b, hab, h1, h2⟩ | ⟨a, hm, hc⟩
  · exact Or.inl ⟨L, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHit_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end ClaudeWCT.W9.T3.Security.Wots
namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] verifyP expandB
theorem check_hashOnly (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    Security.SourceReplay.HashOnly (checkForgeryP publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3.Security.PaddedGame.check_public publicKey log forgery)
  intro input h
  rcases input with (coin | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem check_accepting (answers : Answers) (publicKey : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (hw : evalWithAnswerFn answers (checkForgeryP publicKey log forgery) = true) :
    Fresh log forgery ∧ ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
      evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
      ∀ input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (verifyP message publicKey witness),
        input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (checkForgeryP publicKey log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.and_eq_true,
        decide_eq_true_eq] at hw
      refine ⟨hw.1, message, witness, ⟨rfl, rfl⟩, hw.2, ?_⟩
      intro input hi
      simpa only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
        List.append_nil] using hi
  | signature message signature =>
      cases he : evalWithAnswerFn answers (expandB message publicKey signature) with
      | none => simp [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure] at hw
      | some witness =>
          simp only [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure, Bool.and_eq_true,
            decide_eq_true_eq] at hw
          refine ⟨hw.1, message, witness, ⟨rfl, he⟩, hw.2, ?_⟩
          intro input hi
          simp only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, he, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
            List.append_nil]
          exact List.mem_append_right _ hi
end ClaudeWCT.W9.T3.Security.PaddedExtraction
