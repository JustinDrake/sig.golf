import SigGolfCandidate.AlternativeSwarDigits

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal



namespace SigGolfCandidate.Base4Candidate.SwarProof

abbrev maskWord2 : BitVec 64 := 3689348814741910323
abbrev maskWord4 : BitVec 64 := 1085102592571150095

def firstWord (a b : BitVec 64) : BitVec 64 :=
  ((a &&& maskWord2)+((a >>> 2) &&& maskWord2)) +
    ((b &&& maskWord2)+((b >>> 2) &&& maskWord2))

def sumWord (a b : BitVec 64) : BitVec 64 :=
  let x := firstWord a b
  ((x &&& maskWord4)+((x >>> 4) &&& maskWord4)) % 255

theorem firstWord_toNat (a b : BitVec 64) :
    (firstWord a b).toNat = first a.toNat b.toNat := by
  simp [firstWord, first, BitVec.toNat_add, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, maskWord2]

theorem sumWord_toNat (a b : BitVec 64) :
    (sumWord a b).toNat = tail (first a.toNat b.toNat) := by
  simp [sumWord, tail, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, maskWord4, firstWord_toNat]

theorem sumWord_decoder (d : BitVec 128) (hd : d.toNat < 2^124) :
    (sumWord (BitVec.ofNat 64 d.toNat) (BitVec.ofNat 64 (d.toNat/2^64))).toNat =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  have hb : d.toNat/2^64 < 2^64 := by
    have h := d.isLt
    norm_num at h ⊢
    omega
  rw [sumWord_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  exact decoder_sum d hd

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.SwarProof
open SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- Register arithmetic before instantiating the caller's masks and divisor. -/
def rawSumWord (a b m1 m2 modulus : BitVec 64) : BitVec 64 :=
  let x := ((a &&& m1)+((a >>> 2) &&& m1))+
    ((b &&& m1)+((b >>> 2) &&& m1))
  rv64_remu ((x &&& m2)+((x >>> 4) &&& m2)) modulus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem block_register_raw (s : MachineState) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x24 =
      rawSumWord (s.getReg .x16) (s.getReg .x17) (s.getReg .x18)
        (s.getReg .x19) (s.getReg .x20) := by rfl

theorem block_register (s : MachineState)
    (h18 : s.getReg .x18 = maskWord2) (h19 : s.getReg .x19 = maskWord4)
    (h20 : s.getReg .x20 = 255) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x24 =
      sumWord (s.getReg .x16) (s.getReg .x17) := by
  rw [block_register_raw,h18,h19,h20]
  unfold rawSumWord sumWord firstWord
  rw [rv64_remu, if_neg (by decide)]

set_option maxRecDepth 100000 in
theorem block_preserves_encoding (s : MachineState) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x16 = s.getReg .x16 ∧
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x17 = s.getReg .x17 := by
  exact ⟨rfl,rfl⟩

theorem block_decoder_sum (s : MachineState) (d : BitVec 128)
    (hd : d.toNat < 2^124)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 d.toNat)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 (d.toNat/2^64))
    (h18 : s.getReg .x18 = maskWord2) (h19 : s.getReg .x19 = maskWord4)
    (h20 : s.getReg .x20 = 255) :
    ((Reference.AsmChecks.digit_sum.res.toState s).getReg .x24).toNat =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  rw [block_register s h18 h19 h20,h16,h17]
  exact sumWord_decoder d hd

end SigGolfCandidate.Base4Candidate.SwarProof

namespace SigGolfCandidate.Base4Candidate.SwarProof

theorem block_cost : Reference.AsmChecks.digit_sum.res.steps = 14 ∧
    Reference.AsmChecks.digit_sum.res.cycles = 17 := by
  exact ⟨rfl,rfl⟩

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The witness-relative serialization and runtime memory address agree. -/
theorem block_serialization (lay chain : Nat) :
    blockAddress lay chain = 2048 + Reference.witnessChainOffset lay chain := by
  unfold blockAddress Reference.witnessChainOffset
  omega

theorem Fresh.mono {w : List Byte} {s : MachineState} {lay chain lay' chain' : Nat}
    (h : Fresh w lay chain s)
    (sub : ∀ a b k, FreshWord lay' chain' a b k → FreshWord lay chain a b k) :
    Fresh w lay' chain' s := fun a b k hk => h a b k (sub a b k hk)

/-- In-place chain hashing preserves all future witness words. This includes
its sixteen-byte spill into the following header. -/
theorem Fresh.hash_inplace {w : List Byte} {s : MachineState} {lay chain : Nat}
    (h : Fresh w lay chain s) (hl : lay < 4) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain+48))
    (answer : BitVec 256) : Fresh w lay (chain+1) (writeHash s answer) := by
  intro a b k hk
  have hb := block_interval lay chain hl hi
  have ha : blockAddress a b+8*k < 2^64 := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    omega
  have hout : blockAddress a b+8*k < blockAddress lay chain+48 ∨
      blockAddress lay chain+48+32 ≤ blockAddress a b+8*k := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    rcases horder with horder | ⟨rfl,horder⟩ <;> omega
  rw [SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (blockAddress lay chain+48) (blockAddress a b+8*k) hd (by omega) ha
    (hout.imp_right Or.inl)]
  exact h a b k (fresh_next hk)

/-- The final chain hash writes into the separate leaf buffer, below every
witness chain. Its full output preserves both the current and future pads. -/
theorem Fresh.hash_leaf {w : List Byte} {s : MachineState} {lay chain : Nat}
    (h : Fresh w lay chain s) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain))
    (answer : BitVec 256) : Fresh w lay chain (writeHash s answer) := by
  intro a b k hk
  have hs : Reference.ChainCode.leafSlot chain+32 < 5376 := by
    unfold Reference.ChainCode.leafSlot
    omega
  have ha : blockAddress a b+8*k < 2^64 := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    omega
  have hout : Reference.ChainCode.leafSlot chain+32 ≤ blockAddress a b+8*k := by
    unfold blockAddress
    omega
  rw [SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (Reference.ChainCode.leafSlot chain) (blockAddress a b+8*k) hd
    (by omega) ha (Or.inr (Or.inl hout))]
  exact h a b k hk

end SigGolfCandidate.Base4Candidate.VerifyProof
