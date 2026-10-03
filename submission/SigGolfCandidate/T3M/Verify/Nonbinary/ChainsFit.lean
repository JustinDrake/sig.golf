import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodChecks
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatch
import SigGolfCandidate.T3.Nonbinary.SourceDigits

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def Fit (c : NCtx) (v : Digest) : Prop := ∀i,i<54 → c.dig i=coreDigit 0 v i

theorem fit_digits (c : NCtx) {v : Digest} (hf : c.Fit v) : c.DigitsOk := by
  intro i hi
  rw [hf i hi]
  have h := T3.Nonbinary.coreDigit_le 0 v i
  simpa [maxDigit,topMax,mx,show (i/3<17)↔i<51 by omega] using h

theorem fit_rank (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<17) : c.kOf q=Search.topRank v q := by
  have hr := T3.Nonbinary.top_rank_lt v hv q hq
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := T3.Nonbinary.top_core_triple v q 0 hq (by decide)
  have h1 := T3.Nonbinary.top_core_triple v q 1 hq (by decide)
  have h2 := T3.Nonbinary.top_core_triple v q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank
  omega

theorem fit_tail (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : v.toNat<2^125) :
    c.kOf 17=v.toNat/2^119 := by
  unfold kOf
  rw [hf 51 (by decide),hf 52 (by decide),hf 53 (by decide)]
  norm_num [mx,coreDigit]
  omega


theorem decode_facts {v : Digest} {ds : List Nat} (h : decode 0 v=some ds) :
    v.toNat<2^125 ∧ topRanksValid v=true ∧ (Search.topDigits v).sum=126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hgood
  · exact hgood

end SigGolfCandidate.T3M.Nonbinary.NCtx
