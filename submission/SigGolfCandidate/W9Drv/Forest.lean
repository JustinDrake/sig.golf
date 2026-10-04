import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Drv.Gate

section

namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def fPrepWords:List (BitVec 32) :=
  [0xf0290193,0x70303823,0x71603c23,0x7a003023,0x7a003423,0x70000513,0xc000593,268437011,115]
def fTailWords:List (BitVec 32):=[0x6fc0006f]
def fHeader:E:=addC (.reg .x18) (-254)
def fPrep:Result :=
  ⟨⟨(((RegFile.init.set .x3 fHeader).set .x10 (.c (BitVec.ofNat 64 1792))).set
      .x11 (.c (BitVec.ofNat 64 192))).set .x12 (.c (BitVec.ofNat 64 256)),
    [(⟨none,BitVec.ofNat 64 1960⟩,.c 0),(⟨none,BitVec.ofNat 64 1952⟩,.c 0),
      (⟨none,BitVec.ofNat 64 1816⟩,.reg .x22),(⟨none,BitVec.ofNat 64 1808⟩,fHeader)],
    []⟩,.c (pcOf 209),.ecall,8,8⟩
def fTail:Result :=
  ⟨SymState.init,.c (pcOf 657),.jump,1,1⟩
theorem fPrep_checked:rOK (symRun {} fPrepWords (pcOf 201) 9) fPrep = true:=by decide +kernel
theorem fPrep_linked:sliceChecked 201 fPrepWords = true:=by decide +kernel
theorem fTail_checked:rOK (symRun {} fTailWords (pcOf 210) 1) fTail = true:=by decide +kernel
theorem fTail_linked:sliceChecked 210 fTailWords = true:=by decide +kernel
end W9Drv
end

section


namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M HashInput pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
open W9Machine
def forestIn (index:Nat) (roots:List Digest):HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (SigGolfCandidate.T3.header 15 0 index 0 0) ++
    (roots.drop 1).flatMap (bytesLE 16)
theorem forestPk_eq' (index:Nat) (roots:List Digest) :
    ClaudeWCT.WCT9.forestPk index roots = shortHash (forestIn index roots):=rfl
theorem forestIn_length (index:Nat) (roots:List Digest) (h:roots.length = 9) :
    (forestIn index roots).length = 160:=by
  unfold forestIn
  simp only [List.length_append,bytesLE_length,List.length_flatMap]
  rw [sum_map_16,List.length_drop,h]
theorem wordsOf_forestIn (index:Nat) (roots:List Digest) :
    wordsOf (forestIn index roots) =
      [dlo (roots.getD 0 0),dhi (roots.getD 0 0),BitVec.ofNat 64 (hdr0 15 0 index 0),
        BitVec.ofNat 64 (hdr1 index 0)] ++ (roots.drop 1).flatMap (fun d => [dlo d,dhi d]):=by
  unfold forestIn
  rw [wordsOf_append _ _ (by simp only [List.length_append,bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),wordsOf_bytesLE16,wordsOf_header,
    wordsOf_flatMap16]
  rfl
theorem pad64_forestIn_length (index:Nat) (roots:List Digest) (h:roots.length = 9) :
    (pad64 (forestIn index roots)).length = 192:=by
  rw [pad64_length,forestIn_length index roots h]
theorem wordsOf_pad64_forestIn (index:Nat) (roots:List Digest) (h:roots.length = 9) :
    wordsOf (pad64 (forestIn index roots)) =
      [dlo (roots.getD 0 0),dhi (roots.getD 0 0),BitVec.ofNat 64 (hdr0 15 0 index 0),
        BitVec.ofNat 64 (hdr1 index 0)] ++ (roots.drop 1).flatMap (fun d => [dlo d,dhi d]) ++
        [0,0,0,0]:=by
  rw [wordsOf_pad64 _ (by rw [forestIn_length index roots h]),forestIn_length index roots h,
    wordsOf_forestIn]
  rfl
theorem blocks_forestIn (index:Nat) (roots:List Digest) (h:roots.length = 9) :
    (toQ (pad64 (forestIn index roots))).blocks = 3:=by
  rw [blocks_toQ (by rw [Aligned,pad64_forestIn_length index roots h]; omega),
    pad64_forestIn_length index roots h]
theorem hdr0_forest15 (idx:Nat) (hi:idx < 2 ^ 32):hdr0 15 0 idx 0 = 3841:=by
  rw [hdr0_eq 15 0 idx 0 (by decide) (by decide) hi (by decide)]; norm_num
theorem hdr1_forest15 (idx:Nat) (hi:idx < 2 ^ 32):hdr1 idx 0 = idx:=by
  unfold hdr1; rw [Nat.mod_eq_of_lt hi]; simp
theorem fPrep_mem (u:MachineState) (B:Nat) (hB:B < 2 ^ 64) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) =
      if B = 1960 then 0 else if B = 1952 then 0
      else if B = 1816 then u.getReg .x22 else if B = 1808 then fHeader.eval u
      else u.getMem (BitVec.ofNat 64 B):=by
  rw [Result.toState_getMem]
  show memEval u [(⟨none,BitVec.ofNat 64 1960⟩,.c 0),(⟨none,BitVec.ofNat 64 1952⟩,.c 0),
      (⟨none,BitVec.ofNat 64 1816⟩,.reg .x22),(⟨none,BitVec.ofNat 64 1808⟩,fHeader)]
    (BitVec.ofNat 64 B) = _
  rw [memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_nil]
  rfl
theorem fPrep_frame (u:MachineState) (B:Nat) (hB:B < 2 ^ 64)
    (h:B ≠ 1960 ∧ B ≠ 1952 ∧ B ≠ 1816 ∧ B ≠ 1808) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) = u.getMem (BitVec.ofNat 64 B):=by
  obtain ⟨h3,h4,h5,h6⟩:=h
  rw [fPrep_mem u B hB,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
theorem forest_words (u:MachineState) (idx:Nat) (roots:List Digest) (hlen:roots.length = 9)
    (hi:idx < 2 ^ 31) (h22:u.getReg .x22 = BitVec.ofNat 64 idx)
    (h18:u.getReg .x18 = BitVec.ofNat 64 4095)
    (hr:∀ i,i < 9 → DigAt u (W9Machine.forestSlot i) (roots.getD i 0))
    (hz:∀ A,A = 1968 ∨ A = 1976 → u.getMem (BitVec.ofNat 64 A) = 0) :
    (fPrep.toState u).readWords (BitVec.ofNat 64 0x700) 24 = wordsOf (pad64 (forestIn idx roots)):=by
  have hroot:∀ i,i < 9 → DigAt (fPrep.toState u) (W9Machine.forestSlot i) (roots.getD i 0):=by
    intro i hi9
    have hs:1792 ≤ W9Machine.forestSlot i ∧ W9Machine.forestSlot i ≤ 1936 ∧
        (W9Machine.forestSlot i = 1792 ∨ 1824 ≤ W9Machine.forestSlot i):=by
      unfold W9Machine.forestSlot; split <;> omega
    exact ⟨(fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1,
      (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2⟩
  rw [readWords_ofNat _ 0x700 24 (by norm_num),wordsOf_pad64_forestIn idx roots hlen,
    show List.range 24 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23] from rfl]
  match roots,hlen,hroot with
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8],_,hroot =>
    have d0:=hroot 0 (by decide)
    have d1:=hroot 1 (by decide)
    have d2:=hroot 2 (by decide)
    have d3:=hroot 3 (by decide)
    have d4:=hroot 4 (by decide)
    have d5:=hroot 5 (by decide)
    have d6:=hroot 6 (by decide)
    have d7:=hroot 7 (by decide)
    have d8:=hroot 8 (by decide)
    simp only [W9Machine.forestSlot,List.getD_cons_zero,List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6 d7 d8
    norm_num at d0 d1 d2 d3 d4 d5 d6 d7 d8
    have h16:(fPrep.toState u).getMem (BitVec.ofNat 64 1808) =
        BitVec.ofNat 64 (hdr0 15 0 idx 0):=by
      rw [fPrep_mem u _ (by norm_num),hdr0_forest15 idx (by omega)]
      change fHeader.eval u = BitVec.ofNat 64 3841
      rw [fHeader,addC_eval]
      change u.getReg .x18 + (-254:Word) = BitVec.ofNat 64 3841
      rw [h18]; rfl
    have h24:(fPrep.toState u).getMem (BitVec.ofNat 64 1816) = BitVec.ofNat 64 (hdr1 idx 0):=by
      rw [fPrep_mem u _ (by norm_num),hdr1_forest15 idx (by omega)]; exact h22
    have z0:(fPrep.toState u).getMem (BitVec.ofNat 64 1952) = 0:=by
      rw [fPrep_mem u _ (by norm_num)]; rfl
    have z1:(fPrep.toState u).getMem (BitVec.ofNat 64 1960) = 0:=by
      rw [fPrep_mem u _ (by norm_num)]; rfl
    have z2:(fPrep.toState u).getMem (BitVec.ofNat 64 1968) = 0 :=
      (fPrep_frame u _ (by decide) (by omega)).trans (hz _ (Or.inl rfl))
    have z3:(fPrep.toState u).getMem (BitVec.ofNat 64 1976) = 0 :=
      (fPrep_frame u _ (by decide) (by omega)).trans (hz _ (Or.inr rfl))
    simp only [List.map_cons,List.map_nil,Nat.reduceMul,Nat.reduceAdd,d0.1,d0.2,d1.1,d1.2,
      d2.1,d2.2,d3.1,d3.2,d4.1,d4.2,d5.1,d5.2,d6.1,d6.2,d7.1,d7.2,d8.1,d8.2,h16,h24,
      z0,z1,z2,z3,List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,List.flatMap_cons,
      List.flatMap_nil,List.cons_append,List.nil_append,List.append_nil]
theorem forest_good (pk:Digest) (w:WBytes) (a:HashOutput)
    (roots:List Digest) (u:MachineState) (N C A:Nat) (Q:Prop)
    (K:Digest → OracleComp HashSpec Obs)
    (hu:CoordPre pk w a 9 roots u)
    (hnext:∀ root t,FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K root)) :
    GoodQFor Frozen.image u (N + 10) (C + 33) Q (A + 33)
      (ccM (ClaudeWCT.WCT9.forestPk (a.toNat % 2 ^ 31) roots) K):=by
  have hi:idxOf a < 2 ^ 31:=Nat.mod_lt _ (by decide)
  have st1:=block_steps fPrep_checked fPrep_linked rfl u hu.pc
  have st1':Steps Frozen.image u 8 8 (fPrep.toState u):=st1
  set s1:=fPrep.toState u with hs1
  have hf:=block_ecall fPrep_checked fPrep_linked rfl u rfl
  have r1:∀ x,x ≠ .x3 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → s1.getReg x = u.getReg x:=by
    intro x h3 h10 h11 h12
    rw [hs1,Result.toState_getReg]
    -- Discharge clobbered-register cases before reducing the symbolic state.
    cases x <;> first | exact absurd rfl ‹_› | rfl
  have h5:s1.getReg .x5 = 0 :=
    (r1 .x5 (by decide) (by decide) (by decide) (by decide)).trans (hu.glob.1 (.x5,0) (by simp [baseK]))
  have h10:s1.getReg .x10 = BitVec.ofNat 64 0x700:=by rw [hs1,Result.toState_getReg]; rfl
  have h11:s1.getReg .x11 = BitVec.ofNat 64 (64 * (2 + 1)):=by rw [hs1,Result.toState_getReg]; rfl
  have h12:s1.getReg .x12 = BitVec.ofNat 64 0x100:=by rw [hs1,Result.toState_getReg]; rfl
  have h22:s1.getReg .x22 = BitVec.ofNat 64 (idxOf a) :=
    (r1 .x22 (by decide) (by decide) (by decide) (by decide)).trans hu.index
  have hv:hashArgumentsValid s1 = true :=
    hashArgs_of s1 0x700 192 0x100 h10 h11 h12 (by decide) (by decide) (by norm_num) (by decide)
      (by norm_num)
  have hin:hashInput s1 = toQ (pad64 (forestIn (idxOf a) roots)) :=
    hashInput_toQ s1 _ 2 0x700 (pad64_forestIn_length _ _ hu.length) h10 (by decide) (by norm_num)
      h11 (by norm_num) (forest_words u (idxOf a) roots hu.length hi hu.index
        (hu.glob.1 (.x18,4095) (by simp [baseK])) hu.roots hu.forestZero)
  have g1:Glob baseK w pk s1:=by
    have g:Glob [] w pk s1 :=
      Glob_toState hu.glob fPrep.st (fPrep.pc.eval u) (by decide) rfl
    refine ⟨?_,g.2⟩
    intro p hp
    simp only [baseK,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact (r1 .x5 (by decide) (by decide) (by decide) (by decide)).trans
        (hu.glob.1 (.x5,0) (by simp [baseK]))
    · exact (r1 .x18 (by decide) (by decide) (by decide) (by decide)).trans
        (hu.glob.1 (.x18,4095) (by simp [baseK]))
  have o1:Orig w (fun o => o < 64 ∨ 11288 ≤ o) s1 :=
    hu.layer.frame (fun j hj _ => fPrep_frame u _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
  have hpost:∀ ans:BitVec 256,GoodQFor Frozen.image (writeHash s1 ans) (N + 1) (C + 1) Q (A + 1)
      (ccM (pure (ans.extractLsb' 0 128):M Digest) K):=by
    intro ans
    rw [ccM_pure]
    have hpc:(writeHash s1 ans).pc = pcOf 210:=by
      rw [writeHash_pc]
      show pcOf 209 + 4 = pcOf 210
      exact SigGolfCandidate.T3M.pcOf_add4 209
    have st2:=block_steps fTail_checked fTail_linked rfl (writeHash s1 ans) hpc
    have st2':Steps Frozen.image (writeHash s1 ans) 1 1 (fTail.toState (writeHash s1 ans)):=st2
    set t:=fTail.toState (writeHash s1 ans) with ht
    have mt:t.mem = (writeHash s1 ans).mem:=toState_mem_nil _ _ rfl
    have et:∀ A,t.getMem A = (writeHash s1 ans).getMem A:=fun A => congrFun mt A
    have hout:FtsOut ⟨pk,w,a⟩ (ans.extractLsb' 0 128) t:=by
      refine ⟨?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_⟩
      · have g2:=Glob_writeHash g1 ans 0x100 h12 (by decide)
        have g:Glob [] w pk t:=Glob_toState g2 fTail.st
          (fTail.pc.eval (writeHash s1 ans)) (by decide) (by decide)
        refine ⟨?_,g.2⟩
        intro p hp
        rw [ht,Result.toState_getReg]
        change (RegFile.init.get p.1).eval (writeHash s1 ans) = p.2
        rw [init_getReg]
        exact g2.1 p hp
      · rw [ht,Result.toState_getReg]
        show (writeHash s1 ans).getReg .x22 = _
        rw [writeHash_getReg]; exact h22
      · obtain ⟨e0,e1⟩:=writeHash_lo s1 ans 0x100 h12 (by norm_num)
        exact ⟨(et _).trans e0,(et _).trans e1⟩
      · have o2:=Orig_writeHash o1 ans 0x100 h12 (by norm_num)
        have o3:Orig w (fun o => o < 64 ∨ 11288 ≤ o) (writeHash s1 ans) :=
          o2.mono (fun o ho => ⟨ho,Or.inr (by unfold WIT; omega)⟩)
        exact o3.frame (fun j _ _ => et _)
      · rw [ht,Result.toState_getReg]
        show (writeHash s1 ans).getReg .x6 = 1
        rw [writeHash_getReg]
        exact (r1 .x6 (by decide) (by decide) (by decide) (by decide)).trans hu.stepOne
      · rw [ht,Result.toState_getReg]
        show (writeHash s1 ans).getReg .x7 = 2
        rw [writeHash_getReg]
        exact (r1 .x7 (by decide) (by decide) (by decide) (by decide)).trans hu.stepTwo
      · rw [ht,Result.toState_getReg]
        show (writeHash s1 ans).getReg .x12 = _
        rw [writeHash_getReg]; exact h12
      · rw [ht,Result.toState_getReg]
        show (writeHash s1 ans).getReg .x28 = _
        rw [writeHash_getReg]
        have hb:u.getReg .x28 = BitVec.ofNat 64 TOPBASE:=by
          simpa [TOPBASE] using hu.headerReg
        exact (r1 .x28 (by decide) (by decide) (by decide) (by decide)).trans hb
      · intro k hk
        rw [et,writeHash_frame s1 ans 256 (TOPLOAD + 8 * k) h12
          (by unfold TOPLOAD; omega) (by norm_num) (Or.inr (by unfold TOPLOAD; omega)),hs1]
        exact (fPrep_frame u _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
          (hu.bank.top k hk)
    exact (hnext _ t hout).steps st2'
  have hq:=GoodQFor.shortHash_bind (f:=fun d:Digest => (pure d:M Digest)) (K:=K)
    hf h5 hv hin hpost
  rw [blocks_forestIn _ _ hu.length,bind_pure] at hq
  have:=hq.steps st1'
  rw [forestPk_eq']
  exact this.mono (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
end W9Drv
end
