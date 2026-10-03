import SigGolfCandidate.T3.Gate6.ProductFibres
namespace SigGolfResearch.Gate6
open OracleComp ENNReal
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The actual interleaved proposed T3 layout: address bits0..30;
seven25-bit fields of bucket4 and three7-bit children; gate206..208;
unused211..255. The gate is checked without conditioning the mark. -/
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
