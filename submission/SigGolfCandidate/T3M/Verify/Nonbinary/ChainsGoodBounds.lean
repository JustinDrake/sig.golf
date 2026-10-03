import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecks

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem baseTab_all : (baseTab.all fun x => decide (x<96160))=true := by decide +kernel

theorem base_lt (q dB dC : Nat) : base q dB dC<96160 := by
  unfold base
  rw [List.getD_eq_getElem?_getD]
  split
  · cases hn : baseTab[25*q+5*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)
  · cases hn : baseTab[425+4*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)

theorem mx_bounds (q : Nat) : 3≤ mx q ∧ mx q≤4 := by unfold mx;split <;> omega

theorem partLen_le (q d : Nat) : partLen q d≤14 := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega

namespace NCtx

theorem qX_lt (c : NCtx) (i : Nat) : c.qX i<97000 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have h2 := partLen_le (i/3) (c.dig (3*(i/3)+2))
  have hm := mx_bounds (i/3)
  unfold qX pcX pcC pcB
  omega

theorem startPc_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) : c.startPc i<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hm := mx_bounds (i/3)
  have hk := c.kOf_lt hds (i/3) (by omega)
  unfold startPc entW qB qC pcC pcB mx at *
  split_ifs at * <;> omega

theorem rungPc_lt (c : NCtx) (i m : Nat) (hm : m≤ last i) : c.rungPc i m<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hmx := mx_bounds (i/3)
  have hl := last_bounds i
  unfold rungPc qb startPc qB qC pcC pcB
  split_ifs <;> omega

theorem inline_rungPc (c : NCtx) (i : Nat) (h0 : i%3≠0) :
    c.rungPc i (c.dig i)=c.startPc i+(if c.dig i=last i then 4 else 5) := by
  simp [rungPc,h0]

theorem inline_copy_end (c : NCtx) (i : Nat) (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    c.startPc i+5=c.endPc i := by
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold startPc endPc qB qC qX pcX pcC partLen
  unfold topMax at hd
  split_ifs <;> omega

end NCtx
end SigGolfCandidate.T3M.Nonbinary
