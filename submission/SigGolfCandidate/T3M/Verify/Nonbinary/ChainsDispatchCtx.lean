import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCompose
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsFit

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

structure Encoded (v : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16=v.extractLsb' 0 64
  hi : s.getReg .x17=v.extractLsb' 63 64
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119)
  mask : s.getReg .x24=130048#64
  table : s.getReg .x15=712704#64

theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<18) :
    vrun (c.endPc (3*q+2)) 5=some (if q<16 then dispatchR (q+1) else if q=16 then tailDispatchR else retR) := by
  have hh := c.blk_at hds (3*q+2) (by omega)
  unfold blockCheck at hh
  simp only [Bool.and_eq_true] at hh
  have h := rOK_eq hh.2
  have eq : (3*q+2)/3=q := by omega
  simpa only [dispatchOK,endPc,qX,eq,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h

/-- Between the first seventeen triples, only x14 changes. -/
theorem end_dispatch (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn s0 (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,h25,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  rw [if_pos hq] at hr
  have hbound : c.endPc (3*q+2)<210432 := by
    have := c.qX_lt (3*q+2)
    simpa only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using (show c.qX (3*q+2)<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (by omega) hbound hr s v hpc
    ((hR _ (by decide)).trans he.lo) ((hR _ (by decide)).trans he.hi)
    ((hR _ (by decide)).trans he.mask) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩,by omega,fun _ => ?_,?_⟩⟩
  · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
    exact hR x hx
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [rt.get (by decide),h25]
    congr 1
  · rw [pt]
    unfold startPc
    rw [if_pos (show 3*(q+1)%3=0 by omega),show 3*(q+1)/3=q+1 by omega,c.fit_rank hf hv (q+1) (by omega)]

/-- Changing this unused initial register preserves the original witness. -/
def tailInitial (s0 t : MachineState) : MachineState := s0.setReg .x15 (t.getReg .x15)

theorem tailInitial_mem (s0 t : MachineState) (a : Word) :
    (tailInitial s0 t).getMem a=s0.getMem a := rfl

theorem tailInitial_regs (s0 t : MachineState) (r : Reg) (hr : r≠.x15) :
    (tailInitial s0 t).getReg r=s0.getReg r := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  cases r <;> simp_all [MachineState.getReg]

theorem tailInitial_15 (s0 t : MachineState) :
    (tailInitial s0 t).getReg .x15=t.getReg .x15 := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  rfl

theorem tailInitial_known (c : NCtx) {s0 t : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) :
    ∀p∈c.known,(tailInitial s0 t).getReg p.1=p.2 := by
  intro p hp
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp

theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  intro i hi k hk
  exact h0 i hi k hk

/-- The final radix-four table changes x15; the baseline rebase preserves memory exactly. -/
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn (tailInitial s0 t) 51 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,h25,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide)
  norm_num at hr
  have hbound : c.endPc 50<210432 := by
    have := c.qX_lt 50
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 50<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := tail_dispatch_step hbound hr s (v.toNat/2^119) (by omega) hpc
    ((hR _ (by decide)).trans he.tail)
  refine ⟨t,st,⟨⟨fun x hx => ?_,?_,fun j hj => ?_⟩,by omega,fun _ => ?_,?_⟩⟩
  · by_cases hx15 : x=.x15
    · subst x;rw [tailInitial_15]
    · rw [tailInitial_regs _ _ _ hx15,rt.get (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or];exact ⟨fun h => hx (by rw [h];decide),hx15⟩)]
      exact hR x hx
  · intro A hA hn
    rw [tailInitial_mem]
    exact ft.get hA (by simp) |>.trans (hF.get hA hn)
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [rt.get (by decide),h25]
  · rw [pt]
    change pcOf (entW 17 (v.toNat/2^119))=pcOf (entW 17 (c.kOf 17))
    rw [c.fit_tail hf hv]

end SigGolfCandidate.T3M.Nonbinary.NCtx
