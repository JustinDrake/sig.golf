import SigGolfCandidate.T3.Gate6.CountBridge
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local irreducible] Finset.univ Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 5000

theorem family_card_packed :
    (univ.filter (fun s : SetFamily => familyCost s≤93)).card =
      ((((Q (2^160) 7).coeff 3)^7)%(2^160)^(93+1))%(2^160-1) :=
  family_card_packed_generic (2^160) 93 (by norm_num) (by norm_num)

theorem dp_coefficient_packed :
    ((((Q (2^160) 7).coeff 3)^7)%(2^160)^(93+1))%(2^160-1)=packedSetCount :=
  congrArg (fun n => n%(2^160-1))
    (coefficient_power_mod 3 (2^160) ((2^160)^(93+1)) 7 3 7 (by norm_num) le_rfl)

/-- Exact count of seven unordered child triples with summed authentication cap93. -/
theorem capped_family_card :
    (univ.filter (fun s : SetFamily => familyCost s≤93)).card = 26380945558139291669735127569368350720 :=
  family_card_packed.trans (dp_coefficient_packed.trans packedSetCount_value)

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.capped_family_card
