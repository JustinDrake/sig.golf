import SigGolfCandidate.T3.Nonbinary.Codec
import SigGolfCandidate.T3.Gate6.ChildCounting

namespace SigGolfResearch.NonbinaryTop.Counting
open scoped BigOperators
open Codec Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false

def tripleSum5 (d : Triple5) : Nat := ∑ i,(d i).val
def tripleSum4 (d : Triple4) : Nat := ∑ i,(d i).val
def weight (w : Word) : Nat := (∑ i,tripleSum5 (w.1 i))+tripleSum4 w.2

theorem weighted_tuples {α : Type} [Fintype α] (f : α → Nat) (y n : Nat) :
    (∑ d : Fin n → α,y^(∑ i,f (d i)))=(∑ a : α,y^f a)^n := by
  classical
  simpa only [Fintype.piFinset_univ,Finset.prod_pow_eq_pow_sum] using
    (Finset.sum_pow' (Finset.univ : Finset α) (fun a => y^f a) n).symm

def q4 (y : Nat) : Nat := 1+y+y^2+y^3
def q5 (y : Nat) : Nat := 1+y+y^2+y^3+y^4

theorem weighted5 (y : Nat) : (∑ d : Triple5,y^tripleSum5 d)=q5 y^3 := by
  simp only [tripleSum5]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q5]

theorem weighted4 (y : Nat) : (∑ d : Triple4,y^tripleSum4 d)=q4 y^3 := by
  simp only [tripleSum4]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q4]

theorem weighted_words (y : Nat) : (∑ w : Word,y^weight w)=q5 y^51*q4 y^3 := by
  rw [Fintype.sum_prod_type]
  simp only [weight,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted5,weighted4,←pow_mul]

def radix : Nat := 2^136
def packed : Nat := q5 radix^51*q4 radix^3

theorem word_card_small : Fintype.card Word<radix-1 := by
  norm_num [Word,Triple4,Triple5,Fintype.card_prod,Fintype.card_fun,radix]

theorem truncated_card (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun w : Word => weight w<cut).card=
      (packed%radix^cut)%(radix-1) := by
  classical
  unfold packed
  rw [←weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ weight
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

def count : Nat := 183707182173445436457863622839156476

theorem exact_packed_count :
    (packed%radix^127)%(radix-1)-(packed%radix^126)%(radix-1)=count := by decide +kernel

theorem accepted_card : (Finset.univ.filter fun w : Word => weight w=126).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w=126)=
      (Finset.univ.filter fun w : Word => weight w<127)\
        (Finset.univ.filter fun w : Word => weight w<126) := by
    ext w; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]; omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 127 (by decide),truncated_card 126 (by decide),exact_packed_count]
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega

def digest (w : Word) : Fin (2^128) :=
  ⟨encode w,lt_of_lt_of_le (encode_bound w) (by norm_num)⟩

theorem digest_injective : Function.Injective digest := by
  intro a b h
  apply encode_injective
  change (digest a).val=(digest b).val
  exact congrArg (fun x : Fin (2^128) => x.val) h

noncomputable def acceptedDigests : Finset (Fin (2^128)) := by
  classical
  exact (Finset.univ.filter fun w : Word => weight w=126).image digest

theorem accepted_digest_card : acceptedDigests.card=count := by
  classical
  unfold acceptedDigests
  rw [Finset.card_image_of_injective _ digest_injective,accepted_card]

theorem probability_fraction : (count : ℚ)/2^128=
    45926795543361359114465905709789119/85070591730234615865843651857942052864 := by
  norm_num [count]

end SigGolfResearch.NonbinaryTop.Counting
#print axioms SigGolfResearch.NonbinaryTop.Counting.weighted_words
#print axioms SigGolfResearch.NonbinaryTop.Counting.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.Counting.accepted_card
#print axioms SigGolfResearch.NonbinaryTop.Counting.accepted_digest_card
#print axioms SigGolfResearch.NonbinaryTop.Counting.probability_fraction
