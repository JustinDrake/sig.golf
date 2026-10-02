import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck00
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck01
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck02
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck03
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck04
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck05
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck06
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck07
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck08
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck09
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck10
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck11
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck12
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck13
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck14
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck15
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck16
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCheck17

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

theorem tripleCheck_at (q : Nat) (hq : q<18) : tripleCheck q=true := by
  interval_cases q
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5, tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_9, tripleCheck_10, tripleCheck_11, tripleCheck_12, tripleCheck_13, tripleCheck_14, tripleCheck_15, tripleCheck_16, tripleCheck_17]

theorem entCheck_at (q k : Nat) (hq : q<18) (hk : k<(mx q+1)^3) : entCheck q k=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 k (List.mem_range.mpr hk)

theorem blockCheck_at (q dB dC : Nat) (hq : q<18) (hB : dB ≤ mx q) (hC : dC ≤ mx q) :
    blockCheck q dB dC=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hh : (mx q+1)*dB+dC<(mx q+1)^2 := by
    unfold mx at *
    split_ifs at * <;> omega
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  rwa [e1,e2] at hb

#print axioms tripleCheck_at
end SigGolfCandidate.T3M.Nonbinary
