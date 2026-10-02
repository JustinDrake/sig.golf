import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout
import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.T3M.Search.TopWindow

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem land_mask10 (n k : Nat) (hk : k≤7) :
    n &&& (1024*(2^k-1))=1024*(n/1024%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (1024 : Nat)=2^10 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 10≤j
  · simp only [h,decide_true,Bool.true_and,show j-10+10=j by omega]
    by_cases hj : j-10<k <;> simp [hj]
  · simp [h]

theorem field_shl10 (W s k : Nat) (hs : s≤10) (hk : k≤7) :
    W*2^s%2^64/1024%2^k=W/2^(10-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (1024 : Nat)=2^10 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+10<64 by omega,show s≤j+10 by omega]
    rw [show j+10-s=j+(10-s) by omega]
  · simp [hj]

def shiftWord10 (W : Word) (b : Nat) : Word := if b<10 then W<<<(10-b) else W>>>(b-10)

theorem word_mask10 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord10 W b &&& 130048#64=BitVec.ofNat 64 (1024*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 1024*x)
  unfold shiftWord10
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl10 _ _ _ (by omega) (by decide),show 10-(10-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-10)*1024=2^b by rw [show (1024 : Nat)=2^10 by rfl,←pow_add];congr 1;omega]
    rfl

theorem shift10_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift10 w b).eval s=shiftWord10 W b := by
  unfold shift10 shiftWord10
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega),Nat.mod_eq_of_lt (show 10-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega),Nat.mod_eq_of_lt (show b-10<64 by omega)]

theorem dispatch_target (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord10 W b &&& 130048#64)+pcOf 176744+BitVec.ofNat 64 (32*q)) &&& ~~~1#64 =
      pcOf (entW q (W.toNat/2^b%128)) := by
  rw [word_mask10 W b hb,ofNat_add_ofNat,ofNat_add_ofNat,
    even_andNot1' _ (by omega)]
  unfold pcOf entW
  rw [if_pos hq]
  apply congrArg (BitVec.ofNat 64)
  omega

theorem prologue_target (v : Digest) :
    (((v.extractLsb' 0 64 <<< 10) &&& 130048#64)+pcOf 176744) &&& ~~~1#64 =
      pcOf (176744+256*(v.toNat%128)) := by
  have h := dispatch_target (v.extractLsb' 0 64) 0 0 (by decide) (by decide)
  simpa [shiftWord10,entW,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    Nat.mod_mod_of_dvd _ (show 128∣2^64 by decide)] using h

end SigGolfCandidate.T3M.Nonbinary
