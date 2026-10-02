import SigGolfCandidate.T3.Nonbinary.Counting
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform

namespace SigGolfResearch.NonbinaryTop.Decoder
open scoped BigOperators
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false

/-- Actual grouped-rank parsing: each full bytecode table rank must be below125;
    the final six bits encode three quaternary digits.  The base case rejects
    any high bits, so a128-bit input cannot alias a shorter canonical input. -/
def parse : (n : Nat) → Nat → Option ((Fin n → Triple5) × Triple4)
  | 0,x => if h : x<64 then some ((fun i => Fin.elim0 i),digits4 ⟨x,h⟩) else none
  | n+1,x => if h : x%128<125 then
      match parse n (x/128) with
      | none => none
      | some (ds,q) => some (Fin.cons (digits5 ⟨x%128,h⟩) ds,q)
    else none

def encodeN {n : Nat} (d : (Fin n → Triple5) × Triple4) : Nat :=
  pack (List.ofFn fun i => (rank5 (d.1 i)).val) (rank4 d.2).val

theorem encodeN_zero (d : (Fin 0 → Triple5) × Triple4) : encodeN d=(rank4 d.2).val := rfl

theorem encodeN_succ {n : Nat} (d : (Fin (n+1) → Triple5) × Triple4) :
    encodeN d=(rank5 (d.1 0)).val+128*encodeN (Fin.tail d.1,d.2) := by
  simp [encodeN,List.ofFn_succ,pack,Fin.tail]

theorem parse_encodeN {n : Nat} (d : (Fin n → Triple5) × Triple4) :
    parse n (encodeN d)=some d := by
  induction n with
  | zero =>
    rw [encodeN_zero]
    simp only [parse,dif_pos (rank4 d.2).isLt]
    change some ((fun i => Fin.elim0 i),digits4 (rank4 d.2))=some d
    rw [digits4_rank4]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hd := (rank5 (d.1 0)).isLt
    have hd128 : (rank5 (d.1 0)).val<128 := lt_trans hd (by decide)
    rw [encodeN_succ]
    simp only [parse,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd128,
      dif_pos hd,Nat.add_mul_div_left _ _ (by decide : 0<128),
      Nat.div_eq_of_lt hd128,Nat.zero_add,ih]
    change some (Fin.cons (digits5 (rank5 (d.1 0))) (Fin.tail d.1),d.2)=some d
    rw [digits5_rank5,Fin.cons_self_tail]

theorem encodeN_parse {n x : Nat} {d : (Fin n → Triple5) × Triple4}
    (h : parse n x=some d) : encodeN d=x := by
  induction n generalizing x with
  | zero =>
    simp only [parse] at h
    split at h
    · cases h
      simp [encodeN,pack,rank4_digits4]
    · contradiction
  | succ n ih =>
    simp only [parse] at h
    split at h
    · split at h
      · contradiction
      · rename_i ds q he
        cases h
        rw [encodeN_succ]
        simp only [Fin.cons_zero,Fin.tail_cons,rank5_digits5]
        rw [ih he]
        exact Nat.mod_add_div x 128
    · contradiction

def decode (d : Fin (2^128)) : Option Word :=
  (parse 17 d.val).filter fun w => decide (weight w=126)

theorem encodeN_word (w : Word) : encodeN w=encode w := rfl

attribute [local irreducible] encodeN Codec.encode Codec.pack Codec.ranks

theorem decode_some_iff (d : Fin (2^128)) (w : Word) :
    decode d=some w ↔ digest w=d ∧ weight w=126 := by
  constructor
  · intro h
    obtain ⟨hparse,hw⟩ := Option.filter_eq_some_iff.mp h
    have hp := encodeN_parse hparse
    refine ⟨?_,of_decide_eq_true hw⟩
    apply Fin.ext
    exact (encodeN_word w).symm.trans hp
  · rintro ⟨hd,hw⟩
    subst d
    apply Option.filter_eq_some_iff.mpr
    constructor
    · change parse 17 (encode w)=some w
      rw [←encodeN_word]
      exact parse_encodeN w
    · exact decide_eq_true hw

theorem decode_isSome_iff (d : Fin (2^128)) : (decode d).isSome ↔ d∈acceptedDigests := by
  classical
  simp only [Option.isSome_iff_exists,acceptedDigests,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨he,hweight⟩ := (decode_some_iff d w).mp hw
    exact ⟨w,hweight,he⟩
  · rintro ⟨w,hweight,he⟩
    exact ⟨w,(decode_some_iff d w).mpr ⟨he,hweight⟩⟩

theorem decoder_count :
    Fintype.card {d : Fin (2^128) // (decode d).isSome}=count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => (decode d).isSome)=acceptedDigests := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,decode_isSome_iff]
  rw [he,accepted_digest_card]

open OracleComp OracleSpec ENNReal

theorem decoder_uniform_probability :
    Pr[fun d => (decode d).isSome | ($ᵗ Fin (2^128) : ProbComp (Fin (2^128)))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,←Fintype.card_subtype,decoder_count]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

/-- The actual source interface is a128-bit digest; its carrier is just Fin2^128. -/
def decodeBV (d : BitVec 128) : Option Word := decode d.toFin

def acceptedBVEquiv : {d : BitVec 128 // (decodeBV d).isSome} ≃
    {d : Fin (2^128) // (decode d).isSome} where
  toFun d := ⟨d.val.toFin,d.property⟩
  invFun d := ⟨BitVec.ofFin d.val,d.property⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl

theorem decoder_bv_count :
    Fintype.card {d : BitVec 128 // (decodeBV d).isSome}=count := by
  classical
  rw [Fintype.card_congr acceptedBVEquiv,decoder_count]

theorem decoder_bv_probability :
    Pr[fun d => (decodeBV d).isSome | ($ᵗ BitVec 128 : ProbComp (BitVec 128))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,←Fintype.card_subtype,decoder_bv_count]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]

@[reducible] def encodingDecode (answer : BitVec 256) : Option Word :=
  decodeBV (answer.extractLsb' 0 128)

theorem encoding_uniform_probability :
    Pr[fun answer => (encodingDecode answer).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample]
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128)
    (by decide) (fun d => (decodeBV d).isSome)
  change (Finset.univ.filter fun answer : BitVec 256 =>
    (decodeBV (answer.extractLsb' 0 128)).isSome).card = _ at hc
  simp only [encodingDecode]
  rw [hc]
  rw [←Fintype.card_subtype,decoder_bv_count]
  simp only [Fintype.card_bitVec,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256=2^128*2^128 by rw [←pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

end SigGolfResearch.NonbinaryTop.Decoder
#print axioms SigGolfResearch.NonbinaryTop.Decoder.parse_encodeN
#print axioms SigGolfResearch.NonbinaryTop.Decoder.encodeN_parse
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decode_some_iff
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_count
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_uniform_probability

#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_bv_count
#print axioms SigGolfResearch.NonbinaryTop.Decoder.encoding_uniform_probability
