import SigGolfCandidate.T3.Gate6.TupleFibres
import SigGolfCandidate.T3.Gate6.DigestLayout
namespace SigGolfResearch.Gate6
open OracleComp ENNReal
set_option maxHeartbeats 100000
set_option maxRecDepth 10000

noncomputable def acceptance : ENNReal :=
  (29451879398455505315211969 : ENNReal)/79228162514264337593543950336

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
