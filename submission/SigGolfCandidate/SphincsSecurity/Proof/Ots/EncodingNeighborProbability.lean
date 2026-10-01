import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingSelection
namespace SphincsSecurity.OtsCode

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decode digest = some word

theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decode digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]

theorem decodingDigests_card_le (words : Finset Encoding) : (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decode digest).getD defaultWord)
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)

theorem decodingDigests_padding (words : Finset Encoding) :
    ∀ digest ∈ decodingDigests words, (digest.getLsbD 63 || digest.getLsbD 127) = false := by
  intro digest hd
  obtain ⟨word, _, hdecode⟩ := mem_decodingDigests.mp hd
  rw [decode_def] at hdecode
  unfold TargetSum.decodeDigest at hdecode
  split at hdecode
  · rename_i hp
    exact Bool.or_eq_false_iff.mpr ⟨hp.1, hp.2.1⟩
  · simp at hdecode

theorem decodingDigests_uniform_le (words : Finset Encoding) :
    Pr[fun output : HashOutput => selectEncodingDigest output ∈ decodingDigests words | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      ((7 / 4 : ENNReal) * words.card) / Fintype.card Digest := by
  rw [EncodingSelection.prob_select_mem_of_padding _ (decodingDigests_padding words)]
  calc
    _ ≤ (7 / 4 : ENNReal) * ((words.card : ENNReal) / Fintype.card Digest) :=
      mul_le_mul' le_rfl
        (ENNReal.div_le_div_right (Nat.cast_le.mpr (decodingDigests_card_le words)) _)
    _ = _ := by simp only [div_eq_mul_inv, mul_assoc]

end SphincsSecurity.OtsCode
