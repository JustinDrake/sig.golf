import Mathlib.Tactic
import SigGolfCandidate.Budget.Octopus.Tuples
import VCVio.OracleComp.Constructions.SampleableType
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
set_option maxHeartbeats 3000000

abbrev Address := Fin (2^31)
abbrev Bank := Fin 7
abbrev Bucket := Fin 16
abbrev MarkedLabel := Address × (Bank → Bucket)

theorem markedLabel_card : Fintype.card MarkedLabel = 2^59 := by
  norm_num [MarkedLabel,Address,Bank,Bucket,Fintype.card_prod,Fintype.card_fun]

abbrev Triple := Fin 3 → Fin 128
abbrev Slots := Bank → Triple
abbrev Padding := Fin 1024
abbrev Unused := Fin (2^40)
abbrev Payload := Slots × (Padding × Unused)
/-- 31 address bits, seven 4-bit buckets, twenty-one 7-bit slots,
a ten-bit gate field accepted below 135 and 40 unused bits. -/
abbrev RawRecord := MarkedLabel × Payload

def slotSet (v : Triple) : Finset Nat := (valList v).toFinset

def childAuth (v : Triple) : Nat := octH 7 (slotSet v).sort

def SlotsAccepted (slots : Slots) : Prop :=
  (∀ bank, Function.Injective (slots bank)) ∧ (∑ bank, childAuth (slots bank)) ≤ 87

def PayloadAccepted (payload : Payload) : Prop :=
  payload.2.1.val < 135 ∧ SlotsAccepted payload.1

def Accepted (raw : RawRecord) : Prop := PayloadAccepted raw.2

noncomputable instance : DecidablePred SlotsAccepted := Classical.decPred _
noncomputable instance : DecidablePred PayloadAccepted := Classical.decPred _
noncomputable instance : DecidablePred Accepted := Classical.decPred _

theorem rawRecord_card : Fintype.card RawRecord = 2^256 := by
  norm_num [RawRecord,Payload,Slots,Triple,Padding,Unused,MarkedLabel,Address,Bank,Bucket,
    Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]

theorem payload_card : Fintype.card Payload = 2^197 := by
  norm_num [Payload,Slots,Triple,Padding,Unused,Bank,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]

def witnessTriple : Triple := fun i => ⟨i.val,by omega⟩

theorem witness_injective : Function.Injective witnessTriple := by
  intro a b h
  exact Fin.ext (show a.val=b.val from congrArg (fun x : Fin 128 => x.val) h)

theorem witness_auth : childAuth witnessTriple = 6 := by
  unfold childAuth slotSet
  rw [← sortLeaves_eq ((valList_nodup _).mpr witness_injective)]
  decide

theorem accepted_witness : Accepted ((0,fun _ => 0),((fun _ => witnessTriple),(0,0))) := by
  refine ⟨by decide,fun _ => witness_injective,?_⟩
  simp only [witness_auth,sum_const,Fintype.card_fin,Bank,smul_eq_mul]
  norm_num

instance : Nonempty {r : RawRecord // Accepted r} :=
  ⟨⟨_,accepted_witness⟩⟩
instance : Nonempty {p : Payload // PayloadAccepted p} :=
  ⟨⟨_,accepted_witness⟩⟩

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.rawRecord_card
#print axioms SigGolfResearch.Gate6.accepted_witness
