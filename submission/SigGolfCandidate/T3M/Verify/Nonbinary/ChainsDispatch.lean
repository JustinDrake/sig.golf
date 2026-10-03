import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 63 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*(q-9)

theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh

theorem source_field (v : Digest) (q : Nat) (hq : q<17) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 63 (7*(q-9)) (by omega),show 63+7*(q-9)=7*q by omega]

theorem dispatch_step {p q : Nat} (hq : q<17) (hp : p<210432)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16=v.extractLsb' 0 64)
    (h17 : s.getReg .x17=v.extractLsb' 63 64)
    (h24 : s.getReg .x24=130048#64) (h15 : s.getReg .x15=pcOf 176744) :
    ∃t, Steps Images.verifyImage s 4 4 t ∧ t.pc=pcOf (entW q (Search.topRank v q)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)=sourceWord v q := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb : sourceBit q<64 := by unfold sourceBit;split_ifs <;> omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x24)+
      s.getReg .x15+BitVec.ofNat 64 (32*q)) &&& ~~~1#64=pcOf (entW q (Search.topRank v q))
    rw [h24,h15,shift10_eval s _ _ hW _ hb,dispatch_target _ _ q hb hq,source_field v q hq]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]

theorem tail_dispatch_step {p : Nat} (hp : p<210432)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k) :
    ∃t, Steps Images.verifyImage s 4 4 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc (by simp [tailDispatchR]),?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,E.eval,BinOp.eval,h29]
    change ((BitVec.ofNat 64 k <<< 5)+BitVec.ofNat 64 843776) &&& ~~~1#64=pcOf (entW 17 k)
    rw [ofNat_shl,ofNat_add_ofNat,even_andNot1' _ (by omega)]
    unfold entW pcOf
    norm_num
    congr 1 <;> omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [tailDispatchR]
    rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
      RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),RegFile.init_get_eval]
  · intro A _ _
    simp [tailDispatchR,rv_simp]

#print axioms dispatch_step
#print axioms tail_dispatch_step
end SigGolfCandidate.T3M.Nonbinary
