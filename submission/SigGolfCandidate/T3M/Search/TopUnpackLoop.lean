import SigGolfCandidate.T3M.Search.TopUnpackTriple

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

structure Inv (b : Nat) (s0 : MachineState) (v : Digest) (i : Nat) (t : MachineState) : Prop where
  bound : i ≤ 17
  pc : t.pc=if i<17 then pcOf (b+366) else pcOf (b+383)
  lo : t.getReg .x6=BitVec.ofNat 64 (v.toNat/2^(7*i))
  hi : t.getReg .x7=BitVec.ofNat 64 (v.toNat/2^(7*i)/2^64)
  index : t.getReg .x20=BitVec.ofNat 64 i
  ptr : t.getReg .x21=BitVec.ofNat 64 (DIGITS+3*i)
  table : t.getReg .x30=BitVec.ofNat 64 (TOP_DATA+128)
  digits : ∀ j, j<3*i → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (T3.coreDigit 0 v j)
  regs : RegsExcept s0 t Changed
  frame : Frame s0 t Writes


theorem ptr_address (X : Nat) :
    ((BitVec.ofNat 64 X &&& 127#64) <<< 2)+BitVec.ofNat 64 (TOP_DATA+128)=
      BitVec.ofNat 64 (TOP_DATA+128+4*(X%128)) := by
  rw [ofNat_and127, ofNat_shl, ofNat_add_ofNat]
  congr 1
  omega


theorem source_rank_digit (v : Digest) (i k : Nat) (hi : i<17) (hk : k<3) :
    T3.coreDigit 0 v (3*i+k)=rankDigit (topRank v i) k := by
  have h1 : (3*i+k)/3=i := by omega
  have h2 : (3*i+k)%3=k := by omega
  simp only [T3.coreDigit,if_pos rfl,show 3*i+k<51 by omega,if_true,h1,h2]
  rfl


theorem body {image : Image} {b : Nat} (hK : KernAt image b) {s0 t : MachineState}
    (ht : TableOK s0) (v : Digest) (hvalid : T3.topRanksValid v=true) (i : Nat) (hi : i<17)
    (hI : Inv b s0 v i t) :
    ∃ u, Steps image t 17 17 u ∧ Inv b s0 v (i+1) u := by
  have pc := hI.pc
  rw [if_pos hi] at pc
  obtain ⟨t1,s1,p1,a28,r1,f1⟩ := ptr_spec hK t pc
  have rankbound : topRank v i<125 := by
    have hv := (List.all_eq_true.mp hvalid) i (List.mem_range.mpr hi)
    exact of_decide_eq_true hv
  have hp1 : t1.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*topRank v i) := by
    rw [a28,hI.lo,hI.table,ptr_address]
    rfl
  have table1 : TableOK t1 := ht.frame (W:=Writes) ((hI.frame.trans f1).mono (by simp)) (by
    intro j hj
    unfold Writes DIGITS TOP_DATA
    omega)
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := triple_spec hK t1 p1 i (topRank v i) hi rankbound
    (by rw [r1.get (by decide),hI.ptr]) hp1 table1
  obtain ⟨u,s3,p3,g6,g7,g21,g20,r3,f3⟩ := update_spec hK t2 p2 i hi
    (by rw [r2.get (by decide),r1.get (by decide),hI.index])
  refine ⟨u,(s1.trans s2).trans s3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · exact p3
  · rw [g6,r2.get (by decide),r1.get (by decide),hI.lo,
      r2.get (by decide),r1.get (by decide),hI.hi,pair_shift]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.div_div_eq_div_mul,←pow_add,show 7*i+7=7*(i+1) by omega]
  · have hv := v.isLt
    have hx := Nat.div_le_self v.toNat (2^(7*i))
    have hh : v.toNat/2^(7*i)/2^64<2^64 := by omega
    rw [g7,r2.get (by decide),r1.get (by decide),hI.hi,ofNat_shr _ _ hh]
    apply congrArg (BitVec.ofNat 64)
    simp only [Nat.div_div_eq_div_mul]
    apply congrArg (fun d => v.toNat/d)
    simp only [←pow_add]
    congr 1 <;> omega
  · exact g20
  · rw [g21,r2.get (by decide),r1.get (by decide),hI.ptr,ofNat_add_ofNat]
    congr 1
  · rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),hI.table]
  · intro j hj
    have hb : DIGITS+j<2^64 := by unfold DIGITS;omega
    rw [f3.getByte hb (by simp),g2 _ hb]
    by_cases he2 : j=3*i+2
    · subst j
      rw [if_pos (by omega)]
      rw [source_rank_digit v i 2 hi (by decide)]
    · rw [if_neg (by omega)]
      by_cases he1 : j=3*i+1
      · subst j
        rw [if_pos (by omega),source_rank_digit v i 1 hi (by decide)]
      · rw [if_neg (by omega)]
        by_cases he0 : j=3*i
        · subst j
          rw [if_pos rfl]
          simpa only [Nat.add_zero] using congrArg (BitVec.ofNat 8) (source_rank_digit v i 0 hi (by decide)).symm
        · rw [if_neg (by omega),f1.getByte hb (by simp)]
          exact hI.digits j (by omega)
  · exact (hI.regs.trans ((r1.trans r2).trans r3)).mono (by decide)
  · exact (hI.frame.trans ((f1.trans f2).trans f3)).mono (by simp)

end SigGolfCandidate.T3M.Search.TopUnpack
