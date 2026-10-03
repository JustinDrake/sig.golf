import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodCost

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧ s.pc=pcOf c.ret

theorem end_return (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 b : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1=p.2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (tailInitial s0 b) 53 acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.TopOut s0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 17 (by decide)
  norm_num at hr
  have hp : c.endPc 53 < 210432 := by
    have := c.qX_lt 53
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 53<210432 by omega)
  have st := piece_steps45 hr hp s hpc (by simp [retR])
  have h1 : s.getReg .x1=pcOf c.ret :=
    (hR .x1 (by decide)).trans ((tailInitial_regs _ _ _ (by decide)).trans (hk (.x1,pcOf c.ret) (by simp [known])))
  refine ⟨retR.toState s,st,⟨fun x hx hx15 => ?_,?_,hlen,?_,?_⟩⟩
  · exact (retR_keeps.reg s (by simp)).trans ((hR x hx).trans (tailInitial_regs _ _ _ hx15))
  · intro A hA hn
    exact hF A hA hn
  · intro j hj;exact hS j hj
  · rw [Result.toState_pc]
    simp only [retR,E.eval,BinOp.eval,h1]
    exact even_andNot1' _ (by have := hc.2.2.2.2.2;omega)

theorem chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]

/-- The seventeen radix-five triples, with only the sixteen intervening dispatches. -/
theorem prefix_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv s0 50 acc t → Verify.GoodQ t N C Q A (K acc)) :
    ∀ n q, n+q=17 → 0<n → ∀ acc s,c.ChainIn s0 (3*q) acc s →
      Verify.GoodQ s (N+124*n) (C+c.chainsCost (3*q) (3*n)+4*(n-1)) Q
        (A+c.chainsCost (3*q) (3*n)+4*(n-1))
        (Verify.ccM ((List.range' (3*q) (3*n)).foldlM c.chainF acc) K) := by
  intro n
  induction n with
  | zero => intro q _ h;omega
  | succ n ih =>
    intro q hn _ acc s hs
    have hd := c.fit_digits hf
    by_cases hz : n=0
    · subst n
      have hq : q=16 := by omega
      subst q
      have H := c.group_good hc hd hk h0 16 (by decide) K N C A Q hK 3 48 (by decide) (by decide) (by decide) acc s hs
      exact H.mono (by omega) (by simp) (fun h => ⟨h,by simp⟩)
    · rw [show 3*(n+1)=3+3*n by omega,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
      have H := c.group_good hc hd hk h0 q (by omega)
        (fun ends => Verify.ccM ((List.range' (3*q+3) (3*n)).foldlM c.chainF ends) K)
        (N+124*n+4) (C+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4)
        (A+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4) Q
        (fun ends t ht => by
          obtain ⟨u,st,hu⟩ := c.end_dispatch hc hd he hf hv q (by omega) ends t ht
          have H := ih (q+1) (by omega) (by omega) ends u hu
          rw [show 3*(q+1)=3*q+3 by omega] at H
          exact Verify.GoodQ.steps st H)
        3 (3*q) (le_refl _) (by omega) (by decide) acc s hs
      have ec := c.chainsCost_add (3*q) 3 (3*n)
      rw [show 3*q+3=3*(q+1) by omega] at ec
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []

/-- All 54 mixed-radix chains, seventeen dispatches and the return instruction. -/
theorem top_good_exact (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125) (hr : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N+2321) (C+c.chainsCost 0 54+69) Q (A+c.chainsCost 0 54+69)
      (Verify.ccM c.topP K) := by
  have hd := c.fit_digits hf
  unfold topP
  rw [show (54:Nat)=51+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have H := c.prefix_good hc hk h0 he hf hr
    (fun ends => Verify.ccM ((List.range' 51 3).foldlM c.chainF ends) K)
    (N+125) (C+c.chainsCost 51 3+5) (A+c.chainsCost 51 3+5) Q
    (fun ends t ht => by
      obtain ⟨u,st,hu⟩ := c.end_tail hc hd he hf hv ends t ht
      have H := c.group_good hc hd (c.tailInitial_known hk) (c.tailInitial_orig h0) 17 (by decide)
        K (N+1) (C+1) (A+1) Q
        (fun acc t ht => by
          obtain ⟨u,st,hu⟩ := c.end_return hc hd hk acc t ht
          exact Verify.GoodQ.steps st (hK acc u hu))
        3 51 (by decide) (by decide) (by decide) ends u hu
      have H := Verify.GoodQ.steps st H
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩))
    17 0 (by decide) (by decide) [] s hs
  have ec := c.chainsCost_add 0 51 3
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] at ec H ⊢
  exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

theorem top_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest} {ds : List Nat}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : decode 0 v=some ds)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N+2321) (C+1129) Q (A+1129) (Verify.ccM c.topP K) := by
  have hd := decode_facts hv
  have H := c.top_good_exact hc hk h0 he hf hd.1 hd.2.1 K N C A Q hK s hs
  have e : c.chainsCost 0 54=totalCost (coreDigit 0 v) := by
    unfold chainsCost totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi)]
  have hb := source_accepted_total hv
  rw [e] at H
  exact H.mono (le_refl _) (by omega) (fun h => ⟨h,by omega⟩)

#print axioms top_good
end SigGolfCandidate.T3M.Nonbinary.NCtx
