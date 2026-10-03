import SigGolfCandidate.T3.Gate6.ProductFibres
import SigGolfCandidate.T3.Gate6.ChildCounting

section

namespace SigGolfResearch.Gate6
open OracleComp ENNReal
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def digestRecord (output : BitVec 256) : RawRecord :=
  (((output.extractLsb' 0 31).toFin,
      fun c => (output.extractLsb' (31+25*c.val) 4).toFin),
    ((fun c j => (output.extractLsb' (31+25*c.val+4+7*j.val) 7).toFin),
      ((output.extractLsb' 206 3).toFin,(output.extractLsb' 209 47).toFin)))
theorem digestRecord_injective : Function.Injective digestRecord := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position<31
  · have hc := congrArg (fun x : RawRecord => BitVec.ofFin x.1.1) heq
    change left.extractLsb' 0 31=right.extractLsb' 0 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD position) hc
    simpa only [BitVec.getLsbD_extractLsb',hindex,decide_true,Bool.true_and,Nat.zero_add] using hb
  · by_cases hslots : position<206
    · let c : Fin 7 := ⟨(position-31)/25,by omega⟩
      let within := (position-31)%25
      have hwithin : within<25 := by dsimp [within];omega
      have hoff : 31+25*c.val+within=position := by dsimp [c,within];omega
      by_cases hbucket : within<4
      · have hc := congrArg (fun x : RawRecord => (BitVec.ofFin (x.1.2 c) : BitVec 4)) heq
        change left.extractLsb' (31+25*c.val) 4=right.extractLsb' (31+25*c.val) 4 at hc
        have hb := congrArg (fun bits : BitVec 4 => bits.getLsbD within) hc
        simpa only [BitVec.getLsbD_extractLsb',hbucket,decide_true,Bool.true_and,hoff] using hb
      · let j : Fin 3 := ⟨(within-4)/7,by omega⟩
        let bit := (within-4)%7
        have hbit : bit<7 := by dsimp [bit];omega
        have hoff' : 31+25*c.val+4+7*j.val+bit=position := by dsimp [j,bit];omega
        have hc := congrArg (fun x : RawRecord => (BitVec.ofFin (x.2.1 c j) : BitVec 7)) heq
        change left.extractLsb' (31+25*c.val+4+7*j.val) 7=
          right.extractLsb' (31+25*c.val+4+7*j.val) 7 at hc
        have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD bit) hc
        simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff'] using hb
    · by_cases hgate : position<209
      · have hc := congrArg (fun x : RawRecord => (BitVec.ofFin x.2.2.1 : BitVec 3)) heq
        change left.extractLsb' 206 3=right.extractLsb' 206 3 at hc
        have hb := congrArg (fun bits : BitVec 3 => bits.getLsbD (position-206)) hc
        have hbit : position-206<3 := by omega
        have hoff : 206+(position-206)=position := by omega
        simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff] using hb
      · have hc := congrArg (fun x : RawRecord => (BitVec.ofFin x.2.2.2 : BitVec 47)) heq
        change left.extractLsb' 209 47=right.extractLsb' 209 47 at hc
        have hb := congrArg (fun bits : BitVec 47 => bits.getLsbD (position-209)) hc
        have hbit : position-209<47 := by omega
        have hoff : 209+(position-209)=position := by omega
        simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff] using hb
theorem digestRecord_bijective : Function.Bijective digestRecord := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨digestRecord_injective,by rw [rawRecord_card,Fintype.card_bitVec]⟩
def DigestAccepted (digest : BitVec 256) : Prop := Accepted (digestRecord digest)
noncomputable instance : DecidablePred DigestAccepted := Classical.decPred _
theorem digest_event (event : RawRecord → Prop) [DecidablePred event] :
    Pr[fun d => event (digestRecord d) | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      Pr[event | ($ᵗ RawRecord : ProbComp RawRecord)] := by
  change Pr[event ∘ digestRecord | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = _
  rw [← probEvent_map]
  simp only [probEvent_eq_tsum_ite,probOutput_map_bijective_uniform_cross (BitVec 256) digestRecord digestRecord_bijective]
theorem digest_mark_conditional (mark : MarkedLabel) :
    Pr[fun d => DigestAccepted d ∧ (digestRecord d).1=mark |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] /
    Pr[DigestAccepted | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = (2^59 : ENNReal)⁻¹ := by
  change Pr[fun d => Accepted (digestRecord d) ∧ (digestRecord d).1=mark | _] /
    Pr[fun d => Accepted (digestRecord d) | _] = _
  rw [digest_event (fun r => Accepted r ∧ r.1=mark),digest_event Accepted,fresh_mark_conditional]
end SigGolfResearch.Gate6
end

section

namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local irreducible] Finset.univ Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 5000
theorem family_card_packed_generic (y cap : Nat) (hy : 3≤y) (hc : 341376^7<y-1) :
    (univ.filter (fun s : SetFamily => familyCost s≤cap)).card =
      ((((Q y 7).coeff 3)^7)%y^(cap+1))%(y-1) := by
  classical
  have h := generic_capped_card familyCost y cap hy (by rw [family_card];exact hc)
  rw [family_weight_sum] at h
  convert h using 1
theorem coefficient_power_mod (K y M H j n : Nat) (hm : 1<M) (hj : j≤K) :
    ((Q y H).coeff j)^n%M = ((piter K y M H [0,1]).getD j 0)^n%M := by
  have hp := rep_piter (K:=K) (y:=y) (M:=M) H 0 [0,1] (rep_zero K y M hm) j hj
  rw [Nat.zero_add] at hp
  rw [hp,←Nat.pow_mod]
end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.family_card_packed_generic
#print axioms SigGolfResearch.Gate6.coefficient_power_mod
end

section

namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local irreducible] Finset.univ Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 5000
theorem family_card_packed :
    (univ.filter (fun s : SetFamily => familyCost s≤87)).card =
      ((((Q (2^160) 7).coeff 3)^7)%(2^160)^(87+1))%(2^160-1) :=
  family_card_packed_generic (2^160) 87 (by norm_num) (by norm_num)
theorem dp_coefficient_packed :
    ((((Q (2^160) 7).coeff 3)^7)%(2^160)^(87+1))%(2^160-1)=packedSetCount :=
  congrArg (fun n => n%(2^160-1))
    (coefficient_power_mod 3 (2^160) ((2^160)^(87+1)) 7 3 7 (by norm_num) le_rfl)
theorem capped_family_card :
    (univ.filter (fun s : SetFamily => familyCost s≤87)).card = 1792558607887680192091036610744811520 :=
  family_card_packed.trans (dp_coefficient_packed.trans packedSetCount_value)
end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.capped_family_card
end

section

namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
noncomputable def tripleSet (v : Triple) (hv : Function.Injective v) : ChildSet :=
  ⟨slotSet v,mem_powersetCard.mpr ⟨fun x hx => by
    rw [slotSet,List.mem_toFinset,mem_valList] at hx
    obtain ⟨i,rfl⟩ := hx
    exact mem_range.mpr (v i).isLt,by
      rw [slotSet,List.toFinset_card_of_nodup ((valList_nodup v).mpr hv)]
      simp [valList]⟩⟩
abbrev Enumeration (s : ChildSet) := {v : Triple // Function.Injective v ∧ slotSet v=s.val}
noncomputable def orderedEquiv : {s : Slots // SlotsAccepted s} ≃
    (Σ f : {s : SetFamily // familyCost s≤87}, (bank : Bank) → Enumeration (f.val bank)) where
  toFun s := ⟨⟨fun b => tripleSet (s.val b) (s.property.1 b),s.property.2⟩,
    fun b => ⟨s.val b,s.property.1 b,rfl⟩⟩
  invFun x := ⟨fun b => (x.2 b).val,fun b => (x.2 b).property.1,by
    change (∑ b,octH 7 (slotSet (x.2 b).val).sort)≤87
    simp_rw [(x.2 _).property.2]
    exact x.1.property⟩
  left_inv s := by apply Subtype.ext;rfl
  right_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      funext b
      exact Subtype.ext (x.2 b).property.2
    · apply Function.hfunext rfl
      intro b b' hb
      have hb' : b=b' := eq_of_heq hb
      subst b'
      refine (Subtype.heq_iff_coe_eq (fun v => ?_)).mpr ?_
      · change (Function.Injective v ∧ slotSet v=slotSet (x.2 b).val) ↔
          (Function.Injective v ∧ slotSet v=(x.1.val b).val)
        rw [(x.2 b).property.2]
      · rfl
theorem enumeration_card (s : ChildSet) : Fintype.card (Enumeration s) = 6 := by
  rw [Fintype.card_subtype]
  exact (card_fiber 3 128 s.val s.property).trans (by decide)
theorem sigma_card_constant {α : Type} {β : α → Type} [Fintype α] [∀a,Fintype (β a)]
    (c : Nat) (hc : ∀ a,Fintype.card (β a)=c) : Fintype.card (Sigma β)=Fintype.card α*c := by
  rw [Fintype.card_sigma]
  simp only [hc,sum_const,card_univ,smul_eq_mul]
theorem enumeration_family_card (f : {s : SetFamily // familyCost s≤87}) :
    Fintype.card ((bank : Bank) → Enumeration (f.val bank))=6^7 := by
  rw [Fintype.card_pi]
  simp only [enumeration_card,prod_const,card_univ,Bank,Fintype.card_fin]
theorem ordered_accepted_card : Fintype.card {s : Slots // SlotsAccepted s} =
    6^7 * 1792558607887680192091036610744811520 := by
  have hfirst := Fintype.card_congr orderedEquiv
  have hmiddle := sigma_card_constant (β:=fun f : {s : SetFamily // familyCost s≤87} =>
    (bank : Bank) → Enumeration (f.val bank)) (6^7) enumeration_family_card
  have hlast : Fintype.card {s : SetFamily // familyCost s≤87}=1792558607887680192091036610744811520 := by
    rw [Fintype.card_subtype]
    exact capped_family_card
  exact hfirst.trans (hmiddle.trans ((congrArg (fun n => n*6^7) hlast).trans (Nat.mul_comm _ _)))
end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.ordered_accepted_card
end

section


namespace SigGolfResearch.Gate6
open OracleComp ENNReal
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
noncomputable def acceptance : ENNReal :=
  (6963897326262647489342145 : ENNReal)/19807040628566084398385987584
theorem fresh_acceptance_exact :
    Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] = acceptance := by
  rw [fresh_acceptance,payload_accepted_card,ordered_accepted_card]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (by unfold acceptance;finiteness)).mp
  norm_num [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,acceptance]
theorem fresh_mark_joint_exact (mark : MarkedLabel) :
    Pr[fun r => Accepted r ∧ r.1=mark | ($ᵗ RawRecord : ProbComp RawRecord)] =
      acceptance/2^59 := by
  rw [fresh_mark_joint,fresh_acceptance_exact]
theorem digest_acceptance_exact :
    Pr[DigestAccepted | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = acceptance :=
  (digest_event Accepted).trans fresh_acceptance_exact
theorem digest_mark_joint_exact (mark : MarkedLabel) :
    Pr[fun d => DigestAccepted d ∧ (digestRecord d).1=mark |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = acceptance/2^59 :=
  (digest_event (fun r => Accepted r ∧ r.1=mark)).trans (fresh_mark_joint_exact mark)
end SigGolfResearch.Gate6
end
