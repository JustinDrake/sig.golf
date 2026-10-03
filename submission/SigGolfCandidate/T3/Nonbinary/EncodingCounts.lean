import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3.Nonbinary.SourceEncoding
import SigGolfCandidate.T3.Gate6.DigestCounting
import Mathlib.RingTheory.Polynomial.Pochhammer
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform

noncomputable section
namespace SigGolfCandidate.T3.EncodingCounting
open scoped BigOperators
open Polynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option backward.isDefEq.respectTransparency false

def fields (lay : Layer) : List Nat :=
  if lay=0 then List.replicate 49 2 ++ List.replicate 9 3 else List.replicate 42 3

def usedBits (widths : List Nat) : Nat := widths.sum

def decodeFields : List Nat → Nat → List Nat
  | [], _ => []
  | w::ws, n => n%2^w :: decodeFields ws (n/2^w)

theorem decodeFields_append (as bs : List Nat) (n : Nat) :
    decodeFields (as++bs) n = decodeFields as n ++ decodeFields bs (n/2^as.sum) := by
  induction as generalizing n with
  | nil => simp [decodeFields]
  | cons w ws ih =>
    simp only [List.cons_append,decodeFields,ih,List.sum_cons,Nat.pow_add,Nat.div_div_eq_div_mul]

theorem decodeFields_replicate (k w n : Nat) :
    decodeFields (List.replicate k w) n = (List.range k).map (fun i => n/2^(w*i)%2^w) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,decodeFields,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro i _
      simp [Nat.div_div_eq_div_mul,Nat.mul_succ,Nat.pow_add,Nat.mul_comm]

theorem decodeFields_fields (lay : Layer) (value : Digest) (hl : lay≠0) :
    decodeFields (fields lay) value.toNat = dataDigits lay value := by
  simp only [fields,hl,ite_false,decodeFields_replicate,dataDigits,dataCount]
  apply List.map_congr_left
  intro i _
  simp [coreDigit,hl]


def wordSum (widths : List Nat) (n : Nat) : Nat := (decodeFields widths n).sum

def wordPoly (widths : List Nat) : Polynomial Nat :=
  ∑ n : Fin (2^usedBits widths), X^(wordSum widths n.val)

def fieldPoly (w : Nat) : Polynomial Nat := ∑ n : Fin (2^w), X^n.val

theorem wordPoly_cons (w : Nat) (ws : List Nat) :
    wordPoly (w::ws) = fieldPoly w * wordPoly ws := by
  classical
  let e : Fin (2^usedBits ws) × Fin (2^w) ≃ Fin (2^usedBits (w::ws)) :=
    finProdFinEquiv.trans (finCongr (by simp [usedBits,pow_add,Nat.mul_comm]))
  have he : ∀ p : Fin (2^usedBits ws) × Fin (2^w),
      (e p).val = p.2.val + 2^w*p.1.val := by intro p; rfl
  rw [wordPoly,← e.sum_comp]
  simp only [Fintype.sum_prod_type,he,wordSum,decodeFields,List.sum_cons]
  have hm (n : Fin (2^w)) (m : Nat) : (n.val+2^w*m)%2^w=n.val := by
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt n.isLt]
  have hd (n : Fin (2^w)) (m : Nat) : (n.val+2^w*m)/2^w=m := by
    rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt n.isLt,Nat.zero_add]
  simp_rw [hm,hd,pow_add]
  simp only [fieldPoly,wordPoly,wordSum,Finset.sum_mul,Finset.mul_sum]

@[simp] theorem wordPoly_nil : wordPoly [] = 1 := by
  norm_num [wordPoly,usedBits,wordSum,decodeFields]

def fieldsPoly : List Nat → Polynomial Nat
  | [] => 1
  | w::ws => fieldPoly w * fieldsPoly ws

theorem wordPoly_eq_fieldsPoly (ws : List Nat) : wordPoly ws=fieldsPoly ws := by
  induction ws with
  | nil => simp [fieldsPoly]
  | cons w ws ih => simp [fieldsPoly,wordPoly_cons,ih]

theorem fieldsPoly_append (a b : List Nat) : fieldsPoly (a++b)=fieldsPoly a*fieldsPoly b := by
  induction a with
  | nil => simp [fieldsPoly]
  | cons w ws ih => simp [fieldsPoly,ih,mul_assoc]

theorem fieldsPoly_replicate (w n : Nat) : fieldsPoly (List.replicate n w)=fieldPoly w^n := by
  induction n with
  | zero => simp [fieldsPoly]
  | succ n ih => simp [List.replicate_succ,fieldsPoly,ih,pow_succ,mul_comm]

attribute [local irreducible] wordPoly fieldPoly fieldsPoly

def rawAcceptedCount (lay : Layer) : Nat :=
  ![215015893163124468571511796493705040,
    217433284086354415880083123326127992,
    217433284086354415880083123326127992,
    265682986533614028872430357565137160] lay

def AcceptSum (lay : Layer) (total : Nat) : Prop :=
  if lay=0 then total=126 else if lay=3 then 187≤total ∧ total<195 else 188≤total ∧ total<196

instance (lay : Layer) (total : Nat) : Decidable (AcceptSum lay total) :=
  inferInstanceAs (Decidable (if lay=0 then total=126 else if lay=3 then 187≤total ∧ total<195 else 188≤total ∧ total<196))

theorem usedBits_fields (lay : Layer) : usedBits (fields lay)=encodedBits lay := by
  fin_cases lay <;> decide

def packWord (lay : Layer) (n : Fin (2^usedBits (fields lay))) : Digest :=
  BitVec.ofNat 128 n.val

theorem word_lt128 (lay : Layer) (n : Fin (2^usedBits (fields lay))) : n.val<2^128 := by
  have h : n.val<2^encodedBits lay := by simpa only [usedBits_fields] using n.isLt
  exact h.trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_of_lt (encodedBits_lt lay)))

@[simp] theorem packWord_toNat (lay : Layer) (n : Fin (2^usedBits (fields lay))) :
    (packWord lay n).toNat=n.val := by
  simp only [packWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (word_lt128 lay n)]



def q4 (y : Nat) : Nat := 1+y+y^2+y^3
def q8 (y : Nat) : Nat := 1+y+y^2+y^3+y^4+y^5+y^6+y^7

def radix : Nat := 2^136
def topPacked : Nat := q4 radix^49*q8 radix^9
def lowerPacked : Nat := q8 radix^42

theorem eval_wordPoly (ws : List Nat) (y : Nat) :
    (wordPoly ws).eval y = ∑ n : Fin (2^usedBits ws), y^wordSum ws n.val := by
  simp [wordPoly,eval_finsetSum]

theorem eval_field2 (y : Nat) : (fieldPoly 2).eval y=q4 y := by
  unfold fieldPoly
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [q4,Finset.sum_range_succ]

theorem eval_field3 (y : Nat) : (fieldPoly 3).eval y=q8 y := by
  unfold fieldPoly
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [q8,Finset.sum_range_succ]

theorem top_weighted :
    (∑ n : Fin (2^usedBits (fields 0)), radix^wordSum (fields 0) n.val)=topPacked := by
  rw [←eval_wordPoly,wordPoly_eq_fieldsPoly]
  change (fieldsPoly (List.replicate 49 2++List.replicate 9 3)).eval radix=topPacked
  rw [fieldsPoly_append,fieldsPoly_replicate,fieldsPoly_replicate]
  simp only [eval_mul,eval_pow,eval_field2,eval_field3,topPacked]

theorem lower_weighted (lay : Layer) (hl : lay≠0) :
    (∑ n : Fin (2^usedBits (fields lay)), radix^wordSum (fields lay) n.val)=lowerPacked := by
  rw [←eval_wordPoly,wordPoly_eq_fieldsPoly]
  simp only [fields,if_neg hl,fieldsPoly_replicate,eval_pow,eval_field3,lowerPacked]

theorem word_card_small (lay : Layer) :
    Fintype.card (Fin (2^usedBits (fields lay)))<radix-1 := by
  rw [Fintype.card_fin,usedBits_fields]
  fin_cases lay <;> norm_num [encodedBits,radix]

theorem interval_card {α : Type} [Fintype α] [DecidableEq α] (f : α → Nat)
    (lo hi : Nat) (h : lo≤hi) :
    (Finset.univ.filter (fun a => lo≤f a ∧ f a<hi)).card =
      (Finset.univ.filter (fun a => f a<hi)).card -
        (Finset.univ.filter (fun a => f a<lo)).card := by
  have he : (Finset.univ.filter (fun a => lo≤f a ∧ f a<hi)) =
      (Finset.univ.filter (fun a => f a<hi)) \ (Finset.univ.filter (fun a => f a<lo)) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [he,Finset.card_sdiff_of_subset]
  intro a ha
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  omega

theorem truncated_count (lay : Layer) (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun n : Fin (2^usedBits (fields lay)) =>
      wordSum (fields lay) n.val<cut).card =
      ((∑ n : Fin (2^usedBits (fields lay)),radix^wordSum (fields lay) n.val)%radix^cut)%(radix-1) := by
  symm
  exact DigestCounting.packed_card (by norm_num [radix]) hc _ _
    (by simpa only [Finset.card_univ] using word_card_small lay)

def intervalCount (packed lo hi : Nat) : Nat :=
  (packed%radix^hi)%(radix-1) - (packed%radix^lo)%(radix-1)

theorem top_exact : intervalCount topPacked 126 127=rawAcceptedCount 0 := by decide +kernel
theorem lower_first_exact : intervalCount lowerPacked 188 196=rawAcceptedCount 1 := by decide +kernel
theorem lower_last_exact : intervalCount lowerPacked 187 195=rawAcceptedCount 3 := by decide +kernel

theorem interval_words_count (lay : Layer) (lo hi : Nat) (hl : 0<lo) (hh : lo≤hi) :
    Fintype.card {n : Fin (2^usedBits (fields lay)) //
      lo≤wordSum (fields lay) n.val ∧ wordSum (fields lay) n.val<hi} =
      intervalCount (∑ n : Fin (2^usedBits (fields lay)),radix^wordSum (fields lay) n.val) lo hi := by
  classical
  rw [Fintype.card_subtype,interval_card _ lo hi hh,
    truncated_count lay hi (lt_of_lt_of_le hl hh),truncated_count lay lo hl]
  rfl

attribute [local irreducible] wordSum fields usedBits

theorem accepted_words_count (lay : Layer) :
    Fintype.card {n : Fin (2^usedBits (fields lay)) //
      AcceptSum lay (wordSum (fields lay) n.val)} = rawAcceptedCount lay := by
  classical
  fin_cases lay
  · have h := interval_words_count 0 126 127 (by decide) (by decide)
    rw [top_weighted,top_exact] at h
    have he (s : Nat) : (126 ≤ s ∧ s < 127) ↔ s = 126 := by omega
    simpa [he,AcceptSum] using h
  · have h := interval_words_count 1 188 196 (by decide) (by decide)
    rw [lower_weighted 1 (by decide),lower_first_exact] at h
    simpa [AcceptSum] using h
  · have h := interval_words_count 2 188 196 (by decide) (by decide)
    rw [lower_weighted 2 (by decide),lower_first_exact] at h
    simpa [AcceptSum,rawAcceptedCount] using h
  · have h := interval_words_count 3 187 195 (by decide) (by decide)
    rw [lower_weighted 3 (by decide),lower_last_exact] at h
    simpa [AcceptSum] using h

theorem decode_isSome_iff (lay : Layer) (value : Digest) (hl : lay≠0) :
    (decode lay value).isSome ↔ value.toNat<2^encodedBits lay ∧
      AcceptSum lay (wordSum (fields lay) value.toNat) := by
  rw [wordSum,decodeFields_fields lay value hl]
  fin_cases lay <;> dsimp only at * <;> try contradiction
  all_goals
    simp only [decode] <;> split_ifs <;>
    simp_all [AcceptSum,target] <;> omega

theorem packWord_acceptance (lay : Layer) (n : Fin (2^usedBits (fields lay))) (hl : lay≠0) :
    (decode lay (packWord lay n)).isSome ↔ AcceptSum lay (wordSum (fields lay) n.val) := by
  rw [decode_isSome_iff lay _ hl,packWord_toNat]
  have h : n.val<2^encodedBits lay := by simpa only [usedBits_fields] using n.isLt
  simp only [h,true_and]

def acceptedDigestEquiv (lay : Layer) (hl : lay≠0) :
    {value : Digest // (decode lay value).isSome} ≃
      {n : Fin (2^usedBits (fields lay)) // AcceptSum lay (wordSum (fields lay) n.val)} where
  toFun value :=
    ⟨⟨value.val.toNat,by rw [usedBits_fields];exact ((decode_isSome_iff lay value.val hl).mp value.property).1⟩,
      ((decode_isSome_iff lay value.val hl).mp value.property).2⟩
  invFun n := ⟨packWord lay n.val,(packWord_acceptance lay n.val hl).mpr n.property⟩
  left_inv value := by
    apply Subtype.ext
    apply BitVec.eq_of_toNat_eq
    exact packWord_toNat lay _
  right_inv n := by
    apply Subtype.ext
    apply Fin.ext
    exact packWord_toNat lay _

/-- Exact accepted counts for the actual radix-five top and radix-eight lower decoders. -/
def acceptedCount (lay : Layer) : Nat :=
  ![183707182173445436457863622839156476,
    217433284086354415880083123326127992,
    217433284086354415880083123326127992,
    265682986533614028872430357565137160] lay

/-- Exact accepted digest count, including the unused high-bit rejection and
checksum interval in the unchanged base decoder. -/
theorem decoder_acceptance_count (lay : Layer) :
    Fintype.card {value : Digest // (decode lay value).isSome} = acceptedCount lay := by
  classical
  by_cases hl : lay=0
  · subst lay
    simpa [acceptedCount,SigGolfResearch.NonbinaryTop.Counting.count] using
      Nonbinary.actual_decoder_count
  · rw [Fintype.card_congr (acceptedDigestEquiv lay hl),accepted_words_count]
    fin_cases lay <;> simp_all [acceptedCount,rawAcceptedCount]

open OracleComp OracleSpec ENNReal

/-- Success probability for one fresh uniform 128-bit digest. -/
theorem decoder_uniform_probability (lay : Layer) :
    Pr[fun value => (decode lay value).isSome | ($ᵗ Digest : ProbComp Digest)] =
      (acceptedCount lay : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,← Fintype.card_subtype,decoder_acceptance_count]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]

/-- The source counter-search decoder reads exactly the low 128 bits of a
uniform hash answer; the unused upper half contributes a cancelling factor. -/
theorem encoding_uniform_probability (lay : Layer) :
    Pr[fun answer => (Sampling.encodingDecode lay answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedCount lay : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample]
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128)
    (by decide) (fun value => (decode lay value).isSome)
  change (Finset.univ.filter fun answer : HashOutput =>
    (decode lay (answer.extractLsb' 0 128)).isSome).card = _ at hc
  rw [show (Finset.univ.filter fun answer : HashOutput =>
      (Sampling.encodingDecode lay answer).isSome).card =
      (Finset.univ.filter fun value : Digest => (decode lay value).isSome).card*2^128 from hc]
  rw [← Fintype.card_subtype,decoder_acceptance_count]
  simp only [Fintype.card_bitVec,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = 2^128*2^128 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

#print axioms decoder_acceptance_count
#print axioms encoding_uniform_probability
end SigGolfCandidate.T3.EncodingCounting
end
