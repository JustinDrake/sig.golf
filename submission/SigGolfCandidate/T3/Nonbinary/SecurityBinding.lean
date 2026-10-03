import SigGolfCandidate.T3.Nonbinary.Decoder
import SigGolfCandidate.T3.Nonbinary.Numeric

namespace SigGolfResearch.NonbinaryTop.SecurityBinding
open scoped BigOperators
open Codec Counting Decoder
set_option maxHeartbeats 1000000

abbrev Index := (Fin 17 × Fin 3) ⊕ Fin 3

def digit (w : Codec.Word) : Index → Nat
  | .inl (i,j) => (w.1 i j).val
  | .inr j => (w.2 j).val

theorem index_card : Fintype.card Index=54 := by decide

theorem digit_sum (w : Codec.Word) : (∑ i,digit w i)=weight w := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  rfl

theorem digit_injective : Function.Injective digit := by
  intro a b h
  apply Prod.ext
  · funext i j
    apply Fin.ext
    exact congrFun h (.inl (i,j))
  · funext j
    apply Fin.ext
    exact congrFun h (.inr j)

theorem digit_bound (w : Codec.Word) (i : Index) :
    digit w i<(match i with | .inl _ => 5 | .inr _ => 4) := by
  cases i with
  | inl p => exact (w.1 p.1 p.2).isLt
  | inr j => exact (w.2 j).isLt

theorem accepted_backward (a b : Codec.Word) (ha : weight a=126) (hb : weight b=126)
    (hne : a≠b) : ∃ i,digit b i<digit a i := by
  apply constant_sum_backward_witness
  · rw [digit_sum,digit_sum,ha,hb]
  · exact fun he => hne (digit_injective he)

/-- Different accepted digest inputs force a backwards chain step somewhere.
    This is the exact source-decoder antichain interface needed by the inherited
    backward-witness reduction.  It does not assert the full game theorem. -/
theorem decoded_backward (da db : Fin (2^128)) (a b : Codec.Word)
    (ha : decode da=some a) (hb : decode db=some b) (hne : da≠db) :
    ∃ i,digit b i<digit a i := by
  obtain ⟨hea,hwa⟩ := (decode_some_iff da a).mp ha
  obtain ⟨heb,hwb⟩ := (decode_some_iff db b).mp hb
  apply accepted_backward a b hwa hwb
  intro he
  apply hne
  rw [←hea,←heb,he]

theorem accepted_preimage_unique (da db : Fin (2^128)) (w : Codec.Word)
    (ha : decode da=some w) (hb : decode db=some w) : da=db := by
  exact ((decode_some_iff da w).mp ha).1.symm.trans ((decode_some_iff db w).mp hb).1

theorem count_floor : 2^116≤count := by norm_num [count]

open OracleComp OracleSpec ENNReal

theorem source_probability_eq_numeric :
    Pr[fun answer => (encodingDecode answer).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      ENNReal.ofReal (SigGolfResearch.NonbinaryTop.p1 : ℝ) := by
  rw [encoding_uniform_probability]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [count,SigGolfResearch.NonbinaryTop.p1,ENNReal.toReal_div]

end SigGolfResearch.NonbinaryTop.SecurityBinding
#print axioms SigGolfResearch.NonbinaryTop.SecurityBinding.decoded_backward
#print axioms SigGolfResearch.NonbinaryTop.SecurityBinding.accepted_preimage_unique
#print axioms SigGolfResearch.NonbinaryTop.SecurityBinding.count_floor
#print axioms SigGolfResearch.NonbinaryTop.SecurityBinding.source_probability_eq_numeric
