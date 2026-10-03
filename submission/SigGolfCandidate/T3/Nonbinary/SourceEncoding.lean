import SigGolfCandidate.T3.Nonbinary.SourceDigits
import SigGolfCandidate.T3.Nonbinary.ParseFields

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
