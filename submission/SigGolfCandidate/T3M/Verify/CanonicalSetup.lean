import SigGolfCandidate.T3M.Verify.CanonicalSelect

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def ReadyC (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) : Prop :=
  SelState pk w a 7 (s.setPC (pcOf 359)) ∧ s.pc=pcOf 362

def setupConstantsC : List (Reg × Word) :=
  carryK ++ [(.x11,64),(.x29,BitVec.ofNat 64 A4_LIMIT),(.x31,0x10000),
    (.x19,BitVec.ofNat 64 (WIT+64)),(.x20,0xfef000),(.x21,0xfef400),(.x24,BitVec.ofNat 64 ETAB),
    (.x25,BitVec.ofNat 64 FOREST),(.x14,BitVec.ofNat 64 (WIT+1088))]
def setupSpecC : Spec :=
  ⟨[(.x27,.bin .add (.bin .sll (.reg .x22) (SigGolfCandidate.T3M.Verify.cw 32)) (SigGolfCandidate.T3M.Verify.cw 0xa01)),
    (.x28,.bin .add (.bin .sll (.reg .x22) (SigGolfCandidate.T3M.Verify.cw 32)) (SigGolfCandidate.T3M.Verify.cw 0x901))],
    [(⟨none,BitVec.ofNat 64 SENTINEL⟩,.c (-1#64))],banks[0]!,false,24,[],none,24⟩
theorem setup_load_checked :
    specB [] [] baseK (runAtC {} baseK [369] 362 []) setupLdSpec [] baseK [.x22]=true := by
  decide +kernel
theorem setup_new_checked :
    specB [] [] [] (runAtC {} setupLdK [banks[0]!] 369 []) setupSpecC [] setupConstantsC [.x22]=true := by
  decide +kernel

theorem canonical_setup (pk : Digest) (w : WBytes) (a : HashOutput) (t : MachineState)
    (hrdy : ReadyC pk w a t) :
    ∃ u, Steps fixture t 31 31 u ∧ BankEntry ⟨pk,w,a⟩ 0 1088 [] u := by
  obtain ⟨htc,hpc⟩ := hrdy
  have ht := htc.toSelIn
  have hk0 : KnownOK baseK t := ht.known
  have htidx : t.getReg .x22=BitVec.ofNat 64 (a.toNat%2^31) := ht.idx
  -- words 362 .. 368: the six setup constants from the embedded data
  obtain ⟨t1, h1⟩ := spec_runC setup_load_checked t hpc hk0 (by simp [setupLdSpec]) (by simp)
  have hm1 : ∀ A, t1.getMem A = t.getMem A := fun A => by rw [h1.mem]; rfl
  have r14 : t1.getReg .x14 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 40))).eval t := h1.regs (.x14, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 40))) (by simp [setupLdSpec])
  have r29 : t1.getReg .x29 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 48))).eval t := h1.regs (.x29, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 48))) (by simp [setupLdSpec])
  have r27 : t1.getReg .x27 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 56))).eval t := h1.regs (.x27, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 56))) (by simp [setupLdSpec])
  have r28 : t1.getReg .x28 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 64))).eval t := h1.regs (.x28, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 64))) (by simp [setupLdSpec])
  have r26 : t1.getReg .x26 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 72))).eval t := h1.regs (.x26, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 72))) (by simp [setupLdSpec])
  have r21 : t1.getReg .x21 = (E.ld (SigGolfCandidate.T3M.Verify.cw (DATA + 80))).eval t := h1.regs (.x21, .ld (SigGolfCandidate.T3M.Verify.cw (DATA + 80))) (by simp [setupLdSpec])
  have e14 : t1.getReg .x14 = BitVec.ofNat 64 A4_0 :=
    r14.trans (ht.data.word 5 (by omega) A4_0 (by decide) (DATA + 40) (by omega))
  have e29 : t1.getReg .x29 = BitVec.ofNat 64 A4_LIMIT :=
    r29.trans (ht.data.word 6 (by omega) A4_LIMIT (by decide) (DATA + 48) (by omega))
  have e27 : t1.getReg .x27 = BitVec.ofNat 64 0xa01 :=
    r27.trans (ht.data.word 7 (by omega) 0xa01 (by decide) (DATA + 56) (by omega))
  have e28 : t1.getReg .x28 = BitVec.ofNat 64 0x901 :=
    r28.trans (ht.data.word 8 (by omega) 0x901 (by decide) (DATA + 64) (by omega))
  have e26 : t1.getReg .x26 = BitVec.ofNat 64 tbN :=
    r26.trans (ht.data.word 9 (by omega) tbN (by decide) (DATA + 72) (by omega))
  have e21 : t1.getReg .x21 = BitVec.ofNat 64 tbL :=
    r21.trans (ht.data.word 10 (by omega) tbL (by decide) (DATA + 80) (by omega))
  have hk : KnownOK setupLdK t1 := by
    intro p hp
    simp only [setupLdK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.known p hp
    · exact h1.regs (.x2,SigGolfCandidate.T3M.Verify.cw 0x1000000) (by simp [setupLdSpec])
    · exact e14
    · exact e29
    · exact e27
    · exact e28
    · exact e26
    · exact e21
  obtain ⟨u,hu⟩ := spec_runC setup_new_checked t1 (h1.pc rfl) hk
    (by simp [setupSpecC]) (by simp)
  have hmem : ∀ A, A<2^64 → u.getMem (BitVec.ofNat 64 A)=
      if A=SENTINEL then -1#64 else t.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu.mem]; simp only [setupSpecC]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by unfold SENTINEL; omega),memEval_nil,hm1]; rfl
  have hfr : ∀ A, A<2^64 → A≠SENTINEL → u.getMem (BitVec.ofNat 64 A)=t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => by rw [hmem A hA,if_neg hn]
  have hW : WitAll w u := by
    intro j hj
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT SENTINEL; omega)]
    exact ht.wit j hj
  have hz : ∀ A, A<WIT → 0xB0≤A → (A<ETAB ∨ ETAB+24*7≤A) → A≠SENTINEL →
      u.getMem (BitVec.ofNat 64 A)=0 := by
    intro A hA h1 h2 h3
    rw [hfr A (by unfold WIT at hA; omega) h3]
    exact ht.zero A hA (Or.inr (Or.inr h1)) h2
  have hheaders : KnownOK (packedCK 0 (a.toNat%2^31)) u := by
    intro p hp
    simp only [packedCK,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · rw [hu.regs (.x27,.bin .add (.bin .sll (.reg .x22) (SigGolfCandidate.T3M.Verify.cw 32)) (SigGolfCandidate.T3M.Verify.cw 0xa01)) (by simp [setupSpecC])]
      simp only [E.eval,BinOp.eval,SigGolfCandidate.T3M.Verify.cw]
      rw [h1.keep .x22 (by simp),htidx,ofNat_shl,BitVec.ofNat_add_ofNat]
      congr 1
      unfold hdr1
      change (a.toNat%2^31)*2^32+0xa01 = 0xa01%2^32+((a.toNat%2^31)%2^32)*2^32
      have hi := Nat.mod_lt a.toNat (by decide : 0<2^31)
      omega
    · rw [hu.regs (.x28,.bin .add (.bin .sll (.reg .x22) (SigGolfCandidate.T3M.Verify.cw 32)) (SigGolfCandidate.T3M.Verify.cw 0x901)) (by simp [setupSpecC])]
      simp only [E.eval,BinOp.eval,SigGolfCandidate.T3M.Verify.cw]
      rw [h1.keep .x22 (by simp),htidx,ofNat_shl,BitVec.ofNat_add_ofNat]
      congr 1
      unfold hdr1
      change (a.toNat%2^31)*2^32+0x901 = 0x901%2^32+((a.toNat%2^31)%2^32)*2^32
      have hi := Nat.mod_lt a.toNat (by decide : 0<2^31)
      omega
  have hidx : u.getReg .x22=BitVec.ofNat 64 (a.toNat%2^31) := by
    rw [hu.keep .x22 (by simp),h1.keep .x22 (by simp)]; exact htidx
  have hentry : KnownOK (entryK ⟨pk,w,a⟩ 0) u := by
    intro p hp
    simp [entryK,bankK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu.known (.x2,0x1000000) (by simp [setupConstantsC,carryK,baseK])
    · exact hu.known (.x5,0) (by simp [setupConstantsC,carryK,baseK])
    · exact hu.known (.x8,3) (by simp [setupConstantsC,carryK,baseK])
    · exact hu.known (.x9,4) (by simp [setupConstantsC,carryK,baseK])
    · exact hu.known (.x13,5) (by simp [setupConstantsC,carryK,baseK])
    · exact hu.known (.x11,64) (by simp [setupConstantsC])
    · exact hu.known (.x19,BitVec.ofNat 64 (WIT+64)) (by simp [setupConstantsC])
    · exact hu.known (.x20,0xfef000) (by simp [setupConstantsC])
    · exact hu.known (.x21,0xfef400) (by simp [setupConstantsC])
    · exact hidx
    · exact hu.known (.x24,BitVec.ofNat 64 ETAB) (by simp [setupConstantsC])
    · exact hu.known (.x25,BitVec.ofNat 64 FOREST) (by simp [setupConstantsC])
    · exact hheaders (.x27,BitVec.ofNat 64 (hdr1 0xa01 (a.toNat%2^31))) (by simp [packedCK])
    · exact hheaders (.x28,BitVec.ofNat 64 (hdr1 0x901 (a.toNat%2^31))) (by simp [packedCK])
    · exact hu.known (.x29,BitVec.ofNat 64 A4_LIMIT) (by simp [setupConstantsC])
    · exact hu.known (.x31,0x10000) (by simp [setupConstantsC])
  have hcommon : Common ⟨pk,w,a⟩ u := by
    refine ⟨⟨by simp [KnownOK],hW.hdr,?_,?_,?_,?_⟩,?_,?_,?_⟩
    · exact ⟨(hfr 0xA0 (by omega) (by unfold SENTINEL; omega)).trans ht.pk.1,
        (hfr 0xA8 (by omega) (by unfold SENTINEL; omega)).trans ht.pk.2⟩
    · intro A hA
      simp only [pSlots,List.mem_cons,List.not_mem_nil,or_false] at hA
      rcases hA with rfl | rfl | rfl <;>
        exact hz _ (by unfold WIT; omega) (by omega) (Or.inl (by unfold ETAB; omega))
          (by unfold SENTINEL; omega)
    · change (u.getMem (BitVec.ofNat 64 CTRW)).toNat/2^32=0
      rw [hz CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega)
        (Or.inl (by unfold CTRW ETAB; omega)) (by unfold CTRW SENTINEL; omega)]
      rfl
    · exact ht.data.congr (fun A hA hEnd => hfr A (by omega) (by unfold TAB SENTINEL at *; omega))
    · intro s hs
      rw [hfr _ (by unfold ETAB; omega) (by unfold ETAB SENTINEL; omega)]
      have he := ht.etab (s/3) (s%3) (by omega) (by omega)
      rw [show ETAB+24*(s/3)+8*(s%3)=ETAB+8*s by omega] at he
      exact he
    · intro d h1 h2
      exact ⟨hz _ (by unfold frameA WIT; omega) (by unfold frameA; omega)
        (Or.inr (by unfold frameA ETAB; omega)) (by unfold frameA SENTINEL; omega),
        hz _ (by unfold frameA WIT; omega) (by unfold frameA; omega)
        (Or.inr (by unfold frameA ETAB; omega)) (by unfold frameA SENTINEL; omega)⟩
    · exact hu.tables (h1.tables htc.tables (RelOK.nil t)) (RelOK.nil t1)
  refine ⟨u,h1.steps.trans hu.steps,⟨hu.pc rfl,?_,hentry,hcommon,hW.orig _,RootsOK.nil u⟩⟩
  exact hu.known (.x14,BitVec.ofNat 64 (WIT+1088)) (by simp [setupConstantsC])

#print axioms canonical_setup
end SigGolfCandidate.T3M.CanonicalNative
