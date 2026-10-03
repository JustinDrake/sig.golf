import SigGolfCandidate.T3.Nonbinary.Counting
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.T3.Nonbinary.SourceDigits

section


namespace SigGolfResearch.NonbinaryTop.Decoder
open scoped BigOperators
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
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
end

section

namespace SigGolfResearch.NonbinaryTop.Decoder
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem parse_succ_isSome (n x : Nat) :
    (parse (n+1) x).isSome ↔ x%128<125 ∧ (parse n (x/128)).isSome := by
  by_cases h : x%128<125
  · cases hp : parse n (x/128) <;> simp [parse,h,hp]
  · simp [parse,h]
theorem parse_isSome_iff (n x : Nat) :
    (parse n x).isSome ↔ x<64*128^n ∧ ∀ j<n,x/128^j%128<125 := by
  induction n generalizing x with
  | zero =>
    by_cases h : x<64 <;> simp [parse,h]
  | succ n ih =>
    rw [parse_succ_isSome,ih]
    have hb : x/128<64*128^n ↔ x<64*128^(n+1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0<128),pow_succ,Nat.mul_assoc]
    constructor
    · rintro ⟨hzero,hbound,hrest⟩
      refine ⟨hb.mp hbound,?_⟩
      intro j hj
      cases j with
      | zero => simpa using hzero
      | succ j =>
        have hh := hrest j (by omega)
        simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh
    · rintro ⟨hbound,hrest⟩
      refine ⟨by simpa using hrest 0 (by omega),hb.mpr hbound,?_⟩
      intro j hj
      have hh := hrest (j+1) (by omega)
      simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh
theorem parse_fields {n x : Nat} {d : (Fin n → Triple5) × Triple4}
    (h : parse n x=some d) :
    (∀ j : Fin n,(rank5 (d.1 j)).val=x/128^j.val%128) ∧
      (rank4 d.2).val=x/128^n := by
  induction n generalizing x with
  | zero =>
    simp only [parse] at h
    split at h
    · cases h
      constructor
      · intro j; exact Fin.elim0 j
      · simp [rank4_digits4]
    · contradiction
  | succ n ih =>
    simp only [parse] at h
    split at h
    · split at h
      · contradiction
      · rename_i ds q hp
        cases h
        obtain ⟨hr,hq⟩ := ih hp
        constructor
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [rank5_digits5]
          · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hr j
        · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hq
    · contradiction
end SigGolfResearch.NonbinaryTop.Decoder
end

section


namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def wordDigits (w : Codec.Word) : List Nat :=
  (List.ofFn fun j => List.ofFn fun k => (w.1 j k).val).flatten ++
    List.ofFn fun k => (w.2 k).val
theorem wordDigits_sum (w : Codec.Word) : (wordDigits w).sum=Counting.weight w := by
  simp only [wordDigits,List.sum_append,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rfl
theorem coreDigit_parse5 {v : Digest} {w : Codec.Word}
    (h : Decoder.parse 17 v.toNat=some w) (j : Fin 17) (k : Fin 3) :
    coreDigit 0 v (3*j.val+k.val)=(w.1 j k).val := by
  rw [top_core_triple v j.val k.val j.isLt k.isLt]
  have hp := (Decoder.parse_fields h).1 j
  have he : (Codec.rank5 (w.1 j)).val=v.toNat/2^(7*j.val)%128 := by
    simpa only [show (128:Nat)=2^7 by decide,←pow_mul] using hp
  rw [←he]
  have hd := congrFun (Codec.digits5_rank5 (w.1 j)) k
  have hh := (Codec.rank5 (w.1 j)).isLt
  apply Fin.val_inj.mpr at hd
  fin_cases k <;> simp [Codec.digits5] at hd ⊢ <;> omega
theorem coreDigit_parse4 {v : Digest} {w : Codec.Word}
    (h : Decoder.parse 17 v.toNat=some w) (k : Fin 3) :
    coreDigit 0 v (51+k.val)=(w.2 k).val := by
  have hp := (Decoder.parse_fields h).2
  have he : (Codec.rank4 w.2).val=v.toNat/2^119 := by simpa using hp
  have hd := congrFun (Codec.digits4_rank4 w.2) k
  apply Fin.val_inj.mpr at hd
  have hh := (Codec.rank4 w.2).isLt
  have hediv : ∀ t : Nat,v.toNat/2^(119+t)=v.toNat/2^119/2^t := by
    intro t; rw [Nat.div_div_eq_div_mul,pow_add]
  simp only [coreDigit,if_pos rfl,show ¬51+k.val<51 by omega,if_false,Nat.add_sub_cancel_left,hediv,←he]
  fin_cases k <;> simp [Codec.digits4] at hd ⊢ <;> omega
theorem dataDigits_parse {v : Digest} {w : Codec.Word}
    (h : Decoder.parse 17 v.toNat=some w) : dataDigits 0 v=wordDigits w := by
  have hof : dataDigits 0 v=List.ofFn (fun i : Fin 54 => coreDigit 0 v i.val) := by
    apply List.ext_getElem
    · simp only [dataDigits,List.length_map,List.length_range,List.length_ofFn,dataCount,ite_true]
    · intro i hi hj
      simp only [dataDigits,List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [hof,List.ofFn_add (n := 51) (m := 3)]
  change (List.ofFn fun i : Fin (17*3) => coreDigit 0 v i.val) ++
      (List.ofFn fun i : Fin 3 => coreDigit 0 v (51+i.val))=wordDigits w
  rw [List.ofFn_mul]
  apply congrArg₂ List.append
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg List.ofFn
    funext k
    simpa [Nat.mul_comm] using coreDigit_parse5 h j k
  · apply congrArg List.ofFn
    funext k
    exact coreDigit_parse4 h k
theorem parse_top_isSome_iff (v : Digest) :
    (Decoder.parse 17 v.toNat).isSome ↔ v.toNat<2^125 ∧ topRanksValid v=true := by
  rw [Decoder.parse_isSome_iff]
  have hbound : 64*128^17=(2:Nat)^125 := by decide +kernel
  rw [hbound]
  simp only [topRanksValid,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  simp only [show (128:Nat)=2^7 by decide,←pow_mul]
theorem decode_top_eq_map (v : Digest) :
    T3.decode 0 v=(Decoder.decodeBV v).map wordDigits := by
  change T3.decode 0 v=((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126)).map wordDigits
  cases hp : Decoder.parse 17 v.toNat with
  | none =>
    have hn : ¬(v.toNat<2^125 ∧ topRanksValid v=true) := by
      intro hh
      have hx := (parse_top_isSome_iff v).mpr hh
      simp [hp] at hx
    by_cases hb : v.toNat ≥ 2^125
    · simp only [T3.decode,encodedBits,ite_true,if_pos hb,Option.filter_none,Option.map_none]
    · have hbits : v.toNat<2^125 := by omega
      have hg : topRanksValid v=false := Bool.eq_false_iff.mpr (fun ht => hn ⟨hbits,ht⟩)
      simp only [T3.decode,encodedBits,ite_true,if_neg hb,hg,Bool.false_and,
        Bool.false_eq_true,if_false,Option.filter_none,Option.map_none]
  | some w =>
    have hh := (parse_top_isSome_iff v).mp (by simp [hp])
    have hdata := dataDigits_parse hp
    have hbits : ¬ v.toNat ≥ 2^125 := by omega
    by_cases hsum : Counting.weight w=126
    · simp only [T3.decode,encodedBits,ite_true,if_neg hbits,hh.2,Bool.true_and,
        hdata,wordDigits_sum,show target 0=126 by rfl,hsum,decide_true,
        if_true,decide_false,Bool.false_eq_true,if_false,Option.filter_some,Option.map_some,Option.map_none]
    · simp only [T3.decode,encodedBits,ite_true,if_neg hbits,hh.2,Bool.true_and,
        hdata,wordDigits_sum,show target 0=126 by rfl,hsum,decide_true,
        if_true,decide_false,Bool.false_eq_true,if_false,Option.filter_some,Option.map_some,Option.map_none]
theorem decode_top_isSome (v : Digest) :
    (T3.decode 0 v).isSome=(Decoder.decodeBV v).isSome := by
  rw [decode_top_eq_map]
  simp only [Option.isSome_map]
theorem actual_decoder_count :
    Fintype.card {v : Digest // (T3.decode 0 v).isSome}=Counting.count := by
  classical
  simp_rw [decode_top_isSome]
  exact Decoder.decoder_bv_count
open OracleComp OracleSpec ENNReal
theorem actual_decoder_probability :
    Pr[fun v => (T3.decode 0 v).isSome | ($ᵗ Digest : ProbComp Digest)]=
      (Counting.count : ENNReal)/(2 : ENNReal)^128 := by
  simp_rw [decode_top_isSome]
  exact Decoder.decoder_bv_probability
theorem actual_encoding_probability :
    Pr[fun answer : BitVec 256 => (T3.decode 0 (answer.extractLsb' 0 128)).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      (Counting.count : ENNReal)/(2 : ENNReal)^128 := by
  simp_rw [decode_top_isSome]
  exact Decoder.encoding_uniform_probability
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.decode_top_eq_map
#print axioms SigGolfCandidate.T3.Nonbinary.actual_decoder_count
#print axioms SigGolfCandidate.T3.Nonbinary.actual_encoding_probability
end
