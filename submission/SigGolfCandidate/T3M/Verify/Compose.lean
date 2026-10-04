import SigGolfCandidate.T3.Nonbinary.SourceEncoding
import SigGolfCandidate.T3.Nonbinary.Cost
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3M.Verify.LeafSem
import SigGolfCandidate.T3M.Verify.LayerLower
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Verify.MerkleRuns
import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.Init

section


namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
theorem decode_top_credit {value : Digest} {digits : List Nat}
    (h : T3.decode 0 value = some digits) :
    ∃ w : Codec.Word, Decoder.decodeBV value = some w ∧ digits = wordDigits w ∧
      Counting.weight w = 126 ∧ 11 ≤ Cost.credit w := by
  rw [decode_top_eq_map] at h
  cases hw : Decoder.decodeBV value with
  | none => simp [hw] at h
  | some w =>
    have hd : wordDigits w = digits := by simpa only [hw,Option.map_some,Option.some.injEq] using h
    have hs := (Decoder.decode_some_iff value.toFin w).mp hw
    exact ⟨w, rfl, hd.symm, hs.2, Cost.accepted_credit_ge_eleven w hs.2⟩
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.decode_top_credit
end

section


namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def liveCredit (i d : Nat) : Nat := if d < topMax i then 1 else 0
def liveSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => liveCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum
theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d+liveCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit liveCredit
  split_ifs <;> omega
theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f+liveSum f=2205 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum+(l.map fun i => liveCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2205 := by decide +kernel
  exact hs.trans he
theorem total_cost_credit (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i)
    (hs : digitSum f=126) : totalCost f+17*4+1+creditSum f+liveSum f=1140 := by
  have h := total_balance f hd
  omega
theorem packed_credit_floor (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    54 ≤ creditSum f + liveSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      l.length ≤ (l.map fun i => digitCredit i (f i)).sum +
        (l.map fun i => liveCredit i (f i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hcredit : 1 ≤ digitCredit i (f i) + liveCredit i (f i) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
theorem range_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
theorem source_credit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : creditSum (coreDigit 0 v)=Cost.credit w := by
  unfold creditSum
  rw [range_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => digitCredit i.val (coreDigit 0 v i.val)).sum+
      (List.ofFn fun k : Fin 3 => digitCredit (51+k.val) (coreDigit 0 v (51+k.val))).sum=Cost.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold Cost.credit Cost.credit5 Cost.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse5 hp j k
    have hl : last (j.val*3+k.val)=3 := by
      unfold last topMax mx
      rw [if_pos (by have := j.isLt;have := k.isLt;omega)]
    simpa only [digitCredit,hl,Nat.mul_comm] using congrArg (fun d => if 3≤d then (1:Nat) else 0) he
  · apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse4 hp k
    have hl : last (51+k.val)=2 := by
      unfold last topMax mx
      rw [if_neg (by have := k.isLt;omega)]
    simpa only [digitCredit,hl] using congrArg (fun d => if 2≤d then (1:Nat) else 0) he
theorem source_accepted_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : 11≤creditSum (coreDigit 0 v) := by
  obtain ⟨w,hw,_,_,hc⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  rw [source_credit_parse hp]
  exact hc
theorem source_accepted_sum {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : digitSum (coreDigit 0 v)=126 := by
  obtain ⟨w,hw,_,hs,_⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  change (dataDigits 0 v).sum=126
  rw [T3.Nonbinary.dataDigits_parse hp,T3.Nonbinary.wordDigits_sum,hs]
theorem source_accepted_total {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4+1≤1086 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := packed_credit_floor (coreDigit 0 v) hd
  omega
#print axioms total_cost_credit
#print axioms source_accepted_total
end SigGolfCandidate.T3M.Nonbinary.NCtx
end

section


namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧ s.pc=pcOf c.ret ∧ s.getReg .x15 = 843776#64
theorem end_return (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 b : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1=p.2) (hb : b.getReg .x15 = 843776#64)
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
  refine ⟨retR.toState s,st,⟨fun x hx hx15 => ?_,?_,hlen,?_,?_,?_⟩⟩
  · exact (retR_keeps.reg s (by simp)).trans ((hR x hx).trans (tailInitial_regs _ _ _ hx15))
  · intro A hA hn
    exact hF A hA hn
  · intro j hj;exact hS j hj
  · rw [Result.toState_pc]
    simp only [retR,E.eval,BinOp.eval,h1]
    exact even_andNot1' _ (by have := hc.2.2.2.2.2;omega)
  · exact (retR_keeps.reg s (by simp)).trans ((hR .x15 (by decide)).trans ((tailInitial_15 _ _).trans hb))
theorem chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]
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
      obtain ⟨u,st,hu,hu15⟩ := c.end_tail hc hd he hf hv ends t ht
      have H := c.group_good hc hd (c.tailInitial_known hk) (c.tailInitial_orig h0) 17 (by decide)
        K (N+1) (C+1) (A+1) Q
        (fun acc t ht => by
          obtain ⟨u,st,hu⟩ := c.end_return hc hd hk hu15 acc t ht
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
    Verify.GoodQ s (N+2321) (C+1086) Q (A+1086) (Verify.ccM c.topP K) := by
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
end

section


namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15]
def topChainWrites (A : Nat) : Prop := (512 ≤ A ∧ A < 1488) ∨ (12104 ≤ A ∧ A < 15576)
theorem topLeafReady_of (w : WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ends : List Digest) (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hp : s.pc = pcOf (trPc 0 c + 12))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x15 = 843776#64)
    (hlen : ends.length = 54) (hend : ∀j<54, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk : KnownOK (leafK 0) s := by
    intro p hp
    simp [leafK,baseK] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals try exact h15
    all_goals rw [hr.get (by simp [topChainRegs]), he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [BC.bK, bK,layK,baseK,hw])
  have h12 : t.getReg .x12 = 256#64 := ht.glob.1 (_,_) (by simp [BC.bK, bK])
  have hg := Glob_writeHash ht.glob a 256 h12 (by decide)
  have hfr : Frame (writeHash t a) s topChainWrites :=
    (he.frame.trans hf).mono (by intro A h; simpa using h)
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h <;> omega) hk
  refine ⟨hp,hglob,?_,?_,?_,?_,hlen,hend,?_⟩
  · intro p hp
    simp [lfKeepK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs])]
    all_goals try exact he.s6
    all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [BC.bK, bK,layK,baseK,lfT3,t3In])
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.s7 0 rfl
  · trivial
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.tp 0 rfl
  · have ho := topEntry_orig w pk index c t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by norm_num [layerBase,T3.height,layerEnd] at *;omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [layerBase,T3.height] at hp
      unfold topChainWrites WIT
      omega)
end SigGolfCandidate.T3M
end

section



namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem nctx_block (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - 0x800 = chainBlock 0 i := by
  change 13768 - 1664 + 64 * (53 - i) - 2048 = 9288 + 64 * 12 + 64 * (54 - 1 - i)
  omega
theorem nctx_chain_eq (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) (hi : i < 54) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i) =
      chainP 0 (route index 0).2 (route index 0).1 i ((dataDigits 0 v).getD i 0)
        (maxDigit 0 i - (dataDigits 0 v).getD i 0) (wchainPads w 0 i).1 (wchainPads w 0 i).2 (wchainHeaderPad w 0 i) (wvalue w 0 i) := by
  have hm : NCtx.topMax i = maxDigit 0 i := by
    simp [NCtx.topMax, Nonbinary.mx, maxDigit, show (i / 3 < 17) ↔ i < 51 by omega]
  dsimp only
  rw [T3.dataDigits_getD 0 v i hi, hm]
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader NCtx.val
  rw [nctx_block]
  rfl
theorem nctx_mapM_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    let c := nctxOf w index v p
    (List.finRange 54).mapM (fun i => chainP 0 c.tree c.leaf i.val (c.dig i.val)
      (NCtx.topMax i.val - c.dig i.val) (c.pad0 i.val) (c.pad1 i.val) (c.padHeader i.val) (c.val i.val)) =
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold chainsP
  apply congrArg (fun f => (List.finRange 54).mapM f)
  funext i
  exact nctx_chain_eq w index v p i.val i.isLt
end SigGolfCandidate.T3M
end

section



namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_topP_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).topP = chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold NCtx.topP NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  rw [← List.range_eq_range', ← finRange_mapM]
  exact nctx_mapM_eq w index v p
theorem nctx_initial (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hvalid : T3.topRanksValid v = true) :
    (nctxOf w index v p).ChainIn s 0 [] s := by
  let c := nctxOf w index v p
  have hf : c.Fit v := fun i hi => rfl
  refine ⟨⟨fun r hr => rfl, Frame.refl s _, by simp⟩,rfl,?_⟩
  rw [he.pc]
  change pcOf (176744 + 256 * (v.toNat % 128)) = pcOf (c.startPc 0)
  rw [NCtx.startPc, if_pos (by decide), c.fit_rank hf hvalid 0 (by decide)]
  simp [Nonbinary.entW,Search.topRank]
theorem nctx_encoded (u s : MachineState) (v : Digest) (p : Nat) (he : TopEntry u v p s)
    (hv : v.toNat < 2 ^ 125) : NCtx.Encoded v s := by
  refine ⟨he.lo,?_,?_,he.mask,he.table⟩
  · rw [he.hi]
    exact Search.topWindow_cross v
  · rw [he.tail,Search.topWindow_tail v hv]
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 13768) {s t : MachineState}
    (hf : Frame s t (c.Wr 54)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  simpa only [NCtx.Wr, NCtx.blk, hc, topChainWrites] using hA
theorem layer_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index 0 M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index 0 ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + layerCost 0 0) (ccM (layerHead w index 0 M R) K) := by
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index 0 M s hs
  have hfuel : layerFuel 0 = 10 + 1 + 123 + 2321 + 12 := by decide
  have hcost : layerCost 0 0 = 10 + 8 + 75 + 12 + 1086 := by decide
  have hsA : stepsA (0 : Layer).val = 10 := rfl
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w 0).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    change Steps image s 12 12 u at hst
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    rw [hsA] at hst
    have hblk := BC.encoding_blocks w 0 (route index 0).2 (route index 0).1 M
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 12 + 2321 + 123) (C + 12 + 1086 + 75) Q (A + 12 + 1086 + 75)
        (ccM (match decode 0 (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) K) := by
      intro a
      cases hds : decode 0 (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure,hK0]
        obtain ⟨k,z,st,hk,hz,h5z,h10z⟩ := topTransition_reject w pk index c hc t hpre a hds
        exact GoodQ.steps' st (GoodQ.reject (Q := Q) (A := 0) hz h5z h10z) (by omega) (by omega)
          (fun hq => ⟨hq,by omega⟩)
      | some ds =>
        dsimp only
        have hcan : decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128)) := by
          rw [hds,(decode_top_sum _ _ hds).1]
          rfl
        obtain ⟨s0,st0,he⟩ := topTransition_ok w pk index c hc t hpre a hcan
        let L := nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)
        have hLok : L.ok := nctx_ok w index _ c hidx
        have hkn : KnownOK L.known s0 := nctx_known w pk index c t s0 a hidx hpre he
        have h12 : t.getReg .x12 = 256#64 := hpre.glob.1 (_, _) (by simp [BC.bK, bK])
        have hDs0 : DataOK s0 := (Glob_writeHash hpre.glob a 256 h12 (by decide)).2.2.2.2.2.congr
          (fun A _ hA => he.frame.get (by omega) (by simp))
        have hO := nctx_orig w index (a.extractLsb' 0 128) (trPc 0 c) s0
          (topEntry_orig w pk index c t s0 a hpre he) hDs0
        have hfit : L.Fit (a.extractLsb' 0 128) := fun i hi => rfl
        have hdec := NCtx.decode_facts hds
        have hIn := nctx_initial w index _ (trPc 0 c) _ s0 he hdec.2.1
        have hEnc := nctx_encoded _ s0 _ (trPc 0 c) he hdec.1
        have hG := L.top_good hLok hkn hO hEnc hfit hds (fun ends => ccM (R ends) K)
          (N+12) (C+12) (A+12) Q (fun ends z hz => by
            obtain ⟨hr,hf,hlen,hend,hpc,h15⟩ := hz
            have hregs : RegsExcept s0 z topChainRegs := by
              intro r hrn
              apply hr r
              · intro hh;exact hrn ((by decide : chainRegs ⊆ topChainRegs) hh)
              · intro hh;subst r;exact hrn (by decide)
            have hframe : Frame s0 z topChainWrites := by
              exact top_chain_frame L rfl hf
            have hready := topLeafReady_of w pk index c t s0 z a ends hpre he hpc hregs hframe h15 hlen
              (fun j hj => by have h := hend j (by omega);exact h)
            obtain ⟨u,st,hu⟩ := leafT_step w pk index c hc hidx ends z hready
            exact GoodQ.steps' st (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)) s0 hIn
        have e : chainsP w 0 (route index 0).2 (route index 0).1 ds = L.topP := by
          rw [(decode_top_sum _ _ hds).1]
          exact (nctx_topP_eq w index _ (trPc 0 c)).symm
        rw [ccM_bind,e]
        exact GoodQ.steps' st0 hG (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode 0 answer with
      | none => pure none
      | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
end SigGolfCandidate.T3M
end

section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
theorem layer_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  by_cases h0 : lay = 0
  · subst h0
    exact layer_good_top w pk index M s hs R K hK0 N C A Q hR
  · exact layer_good_low w pk index lay h0 M s hs R K hK0 N C A Q hR
end SigGolfCandidate.T3M
end

section


set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
set_option maxRecDepth 100000
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel
theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end

section




set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
abbrev selC (a : HashOutput) (c : Nat) : Selection := (selections a).getD c ⟨0, []⟩
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FCtx where
  pk : Digest
  w : WBytes
  a : HashOutput
namespace FCtx
def idx (F : FCtx) : Nat := F.a.toNat % 2 ^ 31
def sel (F : FCtx) (c : Nat) : Selection := selC F.a c
def g (F : FCtx) (s : Nat) : Nat := T3M.selLeaf (F.sel (s / 3)) (s % 3)
theorem idx_lt (F : FCtx) : F.idx < 2 ^ 31 := Nat.mod_lt _ (by decide)
end FCtx
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def layerPc : Nat := 588
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FtsOut (F : FCtx) (root : Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  root : DigAt u 0x100 root
  wit : Orig F.w (fun o => o < 64 ∨ 9288 ≤ o) u
  a2 : u.getReg .x12 = BitVec.ofNat 64 0x100
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : WBytes) (index : Nat) (r : Option Digest) : T3.M Bool :=
  match r with
  | some root => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.forest root)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb
theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]
theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]
open ClaudeWCT.WCT9 (LayerMsg)
def RestIn (w : WBytes) (pk : Digest) (index n : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  if n = 0 then match msg with
    | .forest root => CmpIn pk root s
    | .pair _ _ => False
  else LayerIn w pk index (n - 1) msg s
theorem mkEnd_top (w : WBytes) (pk : Digest) (index : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index 0).1 u root t) : CmpIn pk root t := by
  have hpc : t.pc = pcOf (38675 + 53 * mkSh 0 1 (route index 0).1) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 33 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · rw [hpc]; rfl
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg]
      congr 1
      exact (mkDst_chunk _).symm
  · change DigAt t (11336 + 48 * (mkSh 0 1 (route index 0).1 / 32 % 2)) root
    rw [mkDst_chunk]
    exact ht.root
theorem mkStop_next (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index lay ends u)
    (v : Digest) (t : MachineState) (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    RestIn w pk index lay.val (mkMessage w index lay v) t := by
  by_cases h0 : lay.val = 0
  · have hz : lay = 0 := Fin.ext h0
    subst lay
    exact mkEnd_top w pk index u v t ht
  · simpa [RestIn, h0] using mkStop_next_lower w pk index hidx lay h0 ends u hu v t ht
def lCyc : Nat → Nat
  | 0 => 8
  | n + 1 => layerCost n 0 + mkCyc n + lCyc n
def lFuel : Nat → Nat
  | 0 => 9
  | n + 1 => layerFuel n + mkFuel n + lFuel n
theorem lCyc_4 : lCyc 4 = 5700 := by decide
theorem lFuel_4 : lFuel 4 = 7999 := by decide
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQ s (lFuel n) (lCyc n) Q (lCyc n) (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ msg s hs
    cases msg with
    | forest root =>
      simp only [BC.layerLoop, ccM_pure, kFin_some]
      exact cmp_good pk root s hs Q hQ
    | pair left right => exact False.elim hs
  | succ n ih =>
    intro hn msg s hs
    have hs' : LayerIn w pk index n msg s := by simpa [RestIn] using hs
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    rw [layerLoop_succ w index n (by omega) msg]
    have hg := layer_good w pk index (Fin.ofNat 4 n) msg s (by rwa [hv])
      (fun ends => leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCyc n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCyc n) Q
          (fun v t ht => ih (by omega) _ t (by
            have h := mkStop_next w pk index hidx (Fin.ofNat 4 n) ends u hu v t ht
            rw [hv] at h
            exact h))
        simp only [ccM_bind, merkleMsg, ccM_pure, hv] at hm ⊢
        exact hm)
    rw [hv] at hg
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega) (fun q => ⟨q, by simp only [lCyc]; omega⟩)
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8050 8050 Q 5706 (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb) := by
  have hidx : a.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit h.a2
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl (.forest root) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb =
      ccM (BC.layerLoop w (a.toNat % 2 ^ 31) 4 (.forest root)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4] at hg
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
end SigGolfCandidate.T3M
end
