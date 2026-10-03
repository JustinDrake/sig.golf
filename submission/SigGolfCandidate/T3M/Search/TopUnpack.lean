import SigGolfCandidate.T3M.Search.TopUnpackIter
import SigGolfCandidate.T3M.Search.TopUnpackTail

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private theorem tail_digit (v : Digest) (k : Nat) (hk : k<3) :
    T3.coreDigit 0 v (51+k)=v.toNat/2^119/2^(2*k)%4 := by
  simp [T3.coreDigit,show ¬51+k<51 by omega,Nat.div_div_eq_div_mul,pow_add]

theorem topUnpack_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hv : v.toNat<2^125)
    (hvalid : T3.topRanksValid v=true) (ht : TableOK s)
    (hpc : s.pc=pcOf (b+362))
    (h6 : s.getReg .x6=v.extractLsb' 0 64)
    (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h30 : s.getReg .x30=BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 302 302 t ∧ t.pc=s.getReg .x1 &&& ~~~1#64 ∧
      (∀ j, j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (T3.coreDigit 0 v j)) ∧
      RegsExcept s t TopUnpack.Changed ∧ Frame s t TopUnpack.Writes := by
  have h6' : s.getReg .x6=BitVec.ofNat 64 v.toNat := by
    rw [h6]
    apply BitVec.eq_of_toNat_eq
    simp
  have h7' : s.getReg .x7=BitVec.ofNat 64 (v.toNat/2^64) := by
    rw [h7]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow]
  obtain ⟨a,sa,ha⟩ := TopUnpack.init_inv hK s v hpc h6' h7' h30
  obtain ⟨m,sm,hm⟩ := TopUnpack.iter hK ht v hvalid ha 17 (by decide)
  have hx : v.toNat/2^119<64 := by omega
  obtain ⟨t,st,pt,gt,rt,ft⟩ := TopUnpack.tail_spec hK m (by simpa using hm.pc)
    (v.toNat/2^119) hx (by simpa using hm.lo) (by simpa using hm.ptr)
  refine ⟨t,(sa.trans sm).trans st,?_,?_,?_,?_⟩
  · rw [pt,hm.regs.get (by decide)]
  · intro j hj
    rw [gt _ (by unfold DIGITS;omega)]
    by_cases h53 : j=53
    · subst j
      simp only [if_pos rfl]
      simpa using congrArg (BitVec.ofNat 8) (tail_digit v 2 (by decide)).symm
    · rw [if_neg (by omega)]
      by_cases h52 : j=52
      · subst j
        rw [if_pos rfl]
        simpa using congrArg (BitVec.ofNat 8) (tail_digit v 1 (by decide)).symm
      · rw [if_neg (by omega)]
        by_cases h51 : j=51
        · subst j
          rw [if_pos rfl]
          simpa using congrArg (BitVec.ofNat 8) (tail_digit v 0 (by decide)).symm
        · rw [if_neg (by omega)]
          exact hm.digits j (by omega)
  · exact (hm.regs.trans rt).mono (by decide)
  · exact (hm.frame.trans ft).mono (by simp)

#print axioms topUnpack_spec
end SigGolfCandidate.T3M.Search
