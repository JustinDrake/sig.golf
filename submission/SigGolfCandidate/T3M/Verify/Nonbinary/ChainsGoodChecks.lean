import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_17 : tripleCheck 17=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_16 : tripleCheck 16=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_15 : tripleCheck 15=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_14 : tripleCheck 14=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_13 : tripleCheck 13=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_12 : tripleCheck 12=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_11 : tripleCheck 11=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_10 : tripleCheck 10=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_9 : tripleCheck 9=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_8 : tripleCheck 8=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_7 : tripleCheck 7=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_6 : tripleCheck 6=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_5 : tripleCheck 5=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_4 : tripleCheck 4=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_3 : tripleCheck 3=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_2 : tripleCheck 2=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_1 : tripleCheck 1=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
theorem tripleCheck_0 : tripleCheck 0=true := by decide +kernel
end SigGolfCandidate.T3M.Nonbinary
end

section


















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
end

section


namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def DigitsOk (c : NCtx) : Prop := ∀i,i<54 → c.dig i ≤ topMax i
theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<18) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  simpa only [topMax,show (3*q+k)/3=q by omega] using h
theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> omega
theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩
theorem blk_at (c : NCtx) (hd : c.DigitsOk) (i : Nat) (hi : i<54) :
    blockCheck (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))=true :=
  blockCheck_at _ _ _ (by omega) (c.dig_group_le hd _ 1 (by omega) (by decide))
    (c.dig_group_le hd _ 2 (by omega) (by decide))
theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 7=some (headJD .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)< mx q-1 := by simpa only [last,topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_neg (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he
theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hm := topMax_bounds (3*q)
  have hd' : c.dig (3*q)=mx q-1 := by simpa only [last,topMax,eq] using hd
  simp only [topMax,eq] at hm
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_pos (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he
theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 7=some (copyN .x19 (off i) (slot i) (c.endPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)=mx q := by simpa only [topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_pos hd'] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have he' : c.endPc (3*q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2)) := by simp [endPc,qB,h0,eq]
  rw [hs,he']
  exact rOK_eq he
theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3≠0) :
    partOK (i/3) i (c.dig i) (c.startPc i)=true := by
  obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
  have eq : (3*q+r)/3=q := by omega
  have hb := c.blk_at hds (3*q+r) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-,hB⟩,hC⟩,-⟩ := hb
  unfold startPc qB qC
  rw [if_neg h0,eq]
  rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
  · rw [if_pos (by omega)];exact hB
  · rw [if_neg (by omega)];exact hC
theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 8=some (headRH .x19 (off i) (c.dig i) none (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i< mx (i/3)-1 := hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (i/3)-1 := hd
  have hm : 3≤ mx (i/3) := (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 4=some (copyFH .x19 (off i) (slot i) (c.startPc i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  change c.dig i=mx (i/3) at hd
  rw [if_pos hd] at hp
  exact rOK_eq hp
theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54)
    (hm : c.dig i ≤ m) (hm2 : m ≤ last i) (hfirst : i%3≠0 → c.dig i< m) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (slot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0
  · obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
    have eq : 3*q/3=q := by omega
    have hb := c.blk_at hds (3*q) hi
    rw [eq] at hb
    unfold blockCheck at hb
    simp only [Bool.and_eq_true] at hb
    have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
    have hh := List.all_eq_true.mp hb.1.1.1.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
    have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
    simpa only [rungsOK,Nat.sub_zero,Nat.add_zero,hr,ht] using rOK_eq hh
  · have hp := c.part_at hds i hi h0
    have hd := hfirst h0
    have hn : c.dig i< mx (i/3) := by change c.dig i< topMax i;unfold last at hm2;omega
    unfold partOK at hp
    rw [if_neg (by omega),Bool.and_eq_true] at hp
    have hmmax : m< mx (i/3) := by change m<topMax i;unfold last at hm2;omega
    have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc i m=c.startPc i+5+2*(m-(c.dig i+1)) := by
      unfold rungPc
      rw [if_neg h0,if_neg (by omega)]
      omega
    have ht : (m+1=mx (i/3)) ↔ m=last i := by unfold last topMax;omega
    simpa only [hr,ht] using rOK_eq hh
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54) (h0 : i%3=0) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m+1) 2=some (tailR (if m=last i then some (slot i) else none) (c.rungPc i m+1)) := by
  have hmx := topMax_bounds i
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have hb := c.blk_at hds (3*q) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
  have hh := List.all_eq_true.mp hb.1.1.1.1 m (List.mem_range.mpr hn)
  have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
  have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
  simpa only [hr,ht] using rOK_eq hh
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
