import SigGolfCandidate.AlternativeSwarDigits
import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Rv.AddressAdapter

set_option maxErrors 400
set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal



namespace SigGolfCandidate.Base4Candidate.SwarProof
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- A mask whose set bits stay in the low machine word ignores higher bits,
even when it is applied after the fixed two-bit shift. -/
theorem mask_low_word (n shift mask : Nat) (hs : shift ≤ 64)
    (hm : mask < 2^(64-shift)) :
    (n%2^64/2^shift &&& mask) = (n/2^shift &&& mask) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i+shift < 64
  · simp [hi]
  · have hp : 2^(64-shift) ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hz := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp)
    simp [hi,hz]

theorem first_low_word (a b : Nat) : first (a%2^64) b = first a b := by
  have h0 := mask_low_word a 0 3689348814741910323 (by decide) (by decide)
  have h2 := mask_low_word a 2 3689348814741910323 (by decide) (by decide)
  norm_num only [Nat.reduceSub, Nat.reducePow, Nat.div_one] at h0 h2
  unfold first
  norm_num only [Nat.reducePow]
  rw [h0,h2]

theorem digit_value (d : BitVec 128) (i : Base4Candidate.Index) :
    (Base4Candidate.digits d i).val = d.toNat/4^i.val%4 := by
  simp [Base4Candidate.digits, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, pow_mul]

/-- The two high radix-four digits are zero exactly where the concrete decoder
requires four high padding bits to be clear. -/
theorem decoded_weight (d : BitVec 128) (hd : d.toNat < 2^124) :
    Base4Candidate.weight (Base4Candidate.digits d) =
      digitSum d.toNat + digitSum (d.toNat/2^64) := by
  have h62 : d.toNat/2^124 = 0 := Nat.div_eq_of_lt hd
  have h63 : d.toNat/2^126 = 0 := Nat.div_eq_of_lt (lt_trans hd (by norm_num))
  simp only [Base4Candidate.weight, digit_value, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [digitSum_expanded, digitSum_expanded]
  simp only [Nat.div_div_eq_div_mul]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reducePow,
    Nat.reduceMul, Nat.div_one] at h62 h63 ⊢
  rw [h62,h63]
  simp only [Nat.zero_mod, Nat.zero_add, Nat.add_zero]
  ac_rfl

/-- Exact natural arithmetic performed by the verifier's packed digit check.
The remaining machine proof must connect register operations to these terms. -/
theorem decoder_sum (d : BitVec 128) (hd : d.toNat < 2^124) :
    tail (first (d.toNat%2^64) (d.toNat/2^64)) =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  rw [first_low_word, sum_exact, ← decoded_weight d hd]

end SigGolfCandidate.Base4Candidate.SwarProof


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

/-- A chain's four padding words survive an in-place HASH, including when the
oracle's full 32-byte output spills into the next record's header. -/
theorem hash_inplace_pad (s : MachineState) (lay chain : Nat)
    (hl : lay < 4) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain+48))
    (answer : BitVec 256) (word : Nat) (hw : word < 4) :
    (writeHash s answer).getMem (BitVec.ofNat 64 (blockAddress lay chain+16+8*word)) =
      s.getMem (BitVec.ofNat 64 (blockAddress lay chain+16+8*word)) := by
  have hb := block_interval lay chain hl hi
  apply SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (blockAddress lay chain+48) (blockAddress lay chain+16+8*word) hd
    (by omega) (by omega)
  exact Or.inl (by omega)

/-- Exact postcondition of the chain HASH: its low 128 answer bits replace
the value, its pad is preserved, and all future chain records remain fresh. -/
theorem hash_inplace_effect (w : List Byte) (s : MachineState) (lay chain : Nat)
    (hl : lay < 4) (hi : chain < 62) (hfresh : Fresh w lay chain s)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain+48))
    (answer : BitVec 256) :
    Fresh w lay (chain+1) (writeHash s answer) ∧
    (∀ word, word < 4 →
      (writeHash s answer).getMem (BitVec.ofNat 64 (blockAddress lay chain+16+8*word)) =
        s.getMem (BitVec.ofNat 64 (blockAddress lay chain+16+8*word))) ∧
    (writeHash s answer).getMem (BitVec.ofNat 64 (blockAddress lay chain+48)) =
      answer.extractLsb' 0 64 ∧
    (writeHash s answer).getMem (BitVec.ofNat 64 (blockAddress lay chain+56)) =
      answer.extractLsb' 64 64 := by
  refine ⟨hfresh.hash_inplace hl hi hd answer,
    hash_inplace_pad s lay chain hl hi hd answer, ?_, ?_⟩
  · have hb := block_interval lay chain hl hi
    rw [SigGolfCandidate.Sign.writeHash_getMem_ofNat s answer
      (blockAddress lay chain+48) (blockAddress lay chain+48) hd (by omega) (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · have hb := block_interval lay chain hl hi
    rw [SigGolfCandidate.Sign.writeHash_getMem_ofNat s answer
      (blockAddress lay chain+48) (blockAddress lay chain+56) hd (by omega) (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- The final HASH may overwrite the following endpoint slot, which has not
been filled yet. It preserves every previously completed endpoint word. -/
theorem hash_leaf_prefix (s : MachineState) (chain : Nat) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain))
    (answer : BitVec 256) (previous word : Nat) (hp : previous < chain) (hw : word < 2) :
    (writeHash s answer).getMem
        (BitVec.ofNat 64 (Reference.ChainCode.leafSlot previous+8*word)) =
      s.getMem (BitVec.ofNat 64 (Reference.ChainCode.leafSlot previous+8*word)) := by
  apply SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (Reference.ChainCode.leafSlot chain) (Reference.ChainCode.leafSlot previous+8*word) hd
  · unfold Reference.ChainCode.leafSlot
    omega
  · unfold Reference.ChainCode.leafSlot
    omega
  · apply Or.inl
    unfold Reference.ChainCode.leafSlot
    omega

/-- Exact endpoint production by a chain's final HASH. This accounts for the
full oracle answer, rather than treating HASH as a sixteen-byte write. -/
theorem hash_leaf_value (s : MachineState) (chain : Nat) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain))
    (answer : BitVec 256) :
    (writeHash s answer).getMem (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain)) =
      answer.extractLsb' 0 64 ∧
    (writeHash s answer).getMem (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain+8)) =
      answer.extractLsb' 64 64 := by
  have hb : Reference.ChainCode.leafSlot chain+32 < 2^64 := by
    unfold Reference.ChainCode.leafSlot
    omega
  constructor
  · rw [SigGolfCandidate.Sign.writeHash_getMem_ofNat s answer
      (Reference.ChainCode.leafSlot chain) (Reference.ChainCode.leafSlot chain) hd hb (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [SigGolfCandidate.Sign.writeHash_getMem_ofNat s answer
      (Reference.ChainCode.leafSlot chain) (Reference.ChainCode.leafSlot chain+8) hd hb (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl]

end SigGolfCandidate.Base4Candidate.VerifyProof


namespace SigGolfCandidate.Base4Candidate.ChainHeadProof

open Lean Elab Tactic Meta in
/-- Check a universally quantified reflexive equality directly in the kernel.
The statement must be closed; no native evaluation or new axiom is used. -/
elab "kernel_forall_rfl" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.hasFVar || ty.hasMVar then
    throwError "kernel_forall_rfl: statement must be closed"
  let pf ← forallTelescope ty fun xs body => do
    let some (_, _, rhs) := body.eq? |
      throwError "kernel_forall_rfl: expected a quantified equality"
    mkLambdaFVars xs (← mkEqRefl rhs)
  let name ← mkAuxLemma [] ty (← mkExpectedTypeHint pf ty)
  goal.assign (mkConst name)
  replaceMainGoal []

open Lean Elab Tactic Meta in
/-- Check split closed cases sequentially. A failed case aborts this tactic,
so the official log identifies it without repeating the same expensive
kernel failure across every remaining case. All terms are kernel-checked. -/
elab "kernel_forall_rfl_all" : tactic => do
  let goals ← getGoals
  for (goal, branch) in goals.zipIdx do
    try
      withMVarContext goal do
        let ty ← instantiateMVars (← goal.getType)
        if ty.hasFVar || ty.hasMVar then
          throwError "kernel_forall_rfl_all: statement must be closed"
        let pf ← forallTelescope ty fun xs body => do
          let some (_, _, rhs) := body.eq? |
            throwError "kernel_forall_rfl_all: expected a quantified equality"
          mkLambdaFVars xs (← mkEqRefl rhs)
        let name ← mkAuxLemma [] ty (← mkExpectedTypeHint pf ty)
        goal.assign (mkConst name)
    catch failure =>
      logInfo m!"Stopped at closed kernel branch {branch + 1} of {goals.length}."
      throw failure
  setGoals []
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- Exact write set of a hashing head. Its only writes are the two header
words; the attacker-controlled padding and starting value are untouched. -/
def headWrites (chain : Nat) (digit : Fin 3) : SymMem :=
  let a0 := addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain))
  let a := norm a0
  let b := norm (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain+8)))
  if digit.val = 0 then [(b, .reg .x31), (a, a0)] else
    [(a, .bin (.st .b 4) a0 (.reg (if digit.val = 1 then .x6 else .x7))), (b, .reg .x31)]


def headObligations (chain : Nat) (digit : Fin 3) : List Oblig :=
  let address := fun k => norm (addC (.reg .x22)
    (BitVec.ofInt 64 (Reference.ChainCode.offset chain+k)))
  (if digit.val = 0 then [] else [.align8 (.reg .x22), .valid (address 4) 1]) ++
    [.valid (address 8) 8, .valid (address 0) 8]


/-- Explicit state at the first HASH. Execution lemmas decode the instruction
block; projection lemmas use this small state directly. This is a proposed
execution result, whose connection to the machine is checked by the kernel. -/
def hashingHeadResult (chain : Nat) (digit : Fin 3) (pc : Word) : Result :=
  let regs : RegFile := { RegFile.init with
    r10 := addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain))
    r12 := if digit.val = 2 then E.c (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain))
      else addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain+48)) }
  let steps := if digit.val = 0 then 4 else 5
  ⟨⟨regs, headWrites chain digit, headObligations chain digit⟩,
    .c (AddressAdapter.addPc pc steps), .ecall, steps, steps⟩

/-- The entire first block of each chain template, including the digit-three
copy case. Subsequent HASH continuations and image placement are separate. -/
def headResult (chain : Fin 62) (digit : Fin 4) (pc : Word := 65536) : Result :=
  if h : digit.val < 3 then hashingHeadResult chain.val ⟨digit.val, h⟩ pc
  else (symRun {noAlias := true} (Reference.ChainCode.code chain.val digit) pc 64).getD
    ⟨SymState.init, .c pc, .fuel, 0, 0⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_run (chain : Fin 62) (digit : Fin 4) (pc : Word := 65536) :
    symRun {noAlias := true} (Reference.ChainCode.code chain.val digit) pc 64 =
      some (headResult chain digit pc) := by
  fin_cases chain <;> fin_cases digit <;> revert pc
  kernel_forall_rfl_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_shape (chain : Fin 62) (digit : Fin 4) (pc : Word := 65536) :
    (headResult chain digit pc).stop = (if digit.val = 3 then .endOfCode else .ecall) ∧
    (headResult chain digit pc).steps = (if digit.val = 0 ∨ digit.val = 3 then 4 else 5) ∧
    (headResult chain digit pc).cycles = (headResult chain digit pc).steps := by
  fin_cases digit
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · fin_cases chain <;>
      refine ⟨?_, ?_, ?_⟩ <;> revert pc <;> kernel_forall_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Normalize the register file once per head. The individual register laws
below reuse this equality instead of independently decoding the same block. -/
theorem head_register_file (chain : Fin 62) (digit : Fin 3) (pc : Word) :
    (headResult chain ⟨digit.val, Nat.lt_trans digit.isLt (by decide)⟩ pc).st.regs =
      { RegFile.init with
        r10 := addC (.reg .x22)
          (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val))
        r12 := if digit.val = 2 then
          E.c (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)) else
          addC (.reg .x22)
            (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val + 48)) } := by
  simp only [headResult, dif_pos digit.isLt, hashingHeadResult]

/- Every hashing head computes its input pointer from the rebased witness
register and preserves the hash length, syscall selector and encoding words. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_registers (chain : Fin 62) (digit : Fin 3) (s : MachineState) (pc : Word := 65536) :
    let d : Fin 4 := ⟨digit.val, Nat.lt_trans digit.isLt (by decide)⟩
    let t := (headResult chain d pc).toState s
    t.getReg .x10 = (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val))).eval s ∧
    t.getReg .x12 = (if digit.val = 2 then
      E.c (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)) else
      addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val + 48))).eval s ∧
    t.getReg .x11 = s.getReg .x11 ∧
    t.getReg .x5 = s.getReg .x5 ∧
    t.getReg .x16 = s.getReg .x16 ∧
    t.getReg .x17 = s.getReg .x17 := by
  dsimp only
  simp only [Result.toState, SymState.toState, head_register_file] <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Placement-independent machine execution, with code placement and memory
obligations explicit so no standalone-template result is mistaken for an image proof. -/
theorem head_steps (image : Image) (chain : Fin 62) (digit : Fin 4) (pc : Word)
    (s : MachineState)
    (hcode : CodeAt image pc (Reference.ChainCode.code chain.val digit))
    (hpc : s.pc = pc) (hob : (headResult chain digit pc).obligs s) :
    Steps image s (headResult chain digit pc).steps (headResult chain digit pc).cycles
      ((headResult chain digit pc).toState s) :=
  symRun_sound (head_run chain digit pc) hcode s hpc hob

theorem head_ecall (image : Image) (chain : Fin 62) (digit : Fin 4) (pc : Word)
    (s : MachineState) (hd : digit.val < 3)
    (hcode : CodeAt image pc (Reference.ChainCode.code chain.val digit))
    (hob : (headResult chain digit pc).obligs s) :
    fetch image ((headResult chain digit pc).toState s) = some (.base .ECALL) := by
  apply symRun_ecall (head_run chain digit pc) hcode s hob
  rw [(head_shape chain digit pc).1, if_neg (by omega)]

end SigGolfCandidate.Base4Candidate.ChainHeadProof


namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- The chain address permutation changes exactly the first header word.
All seven following words, including arbitrary pads, are preserved. -/
theorem chain_query_words (lay treeHigh chain step : Nat) (rest : List Word)
    (hl : lay < 4) (ht : treeHigh < 4) (hi : chain < 62) (hs : step < 4)
    (hrest : rest.length = 7) :
    AddressFormat.queryPerm (queryOfWords 0
      (BitVec.ofNat 64 (AddressFormat.oldHeader lay treeHigh chain step) :: rest)) =
      queryOfWords 0
        (BitVec.ofNat 64 (AddressFormat.newHeader lay treeHigh chain step) :: rest) := by
  have hb : AddressFormat.oldHeader lay treeHigh chain step < 2^64 := by
    unfold AddressFormat.oldHeader
    omega
  rw [AddressFormat.queryPerm_words _ rest hrest,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  have hword : AddressFormat.wordPerm (AddressFormat.oldHeader lay treeHigh chain step) =
      AddressFormat.newHeader lay treeHigh chain step := by
    exact AddressFormat.old_header lay treeHigh chain step hl ht hi hs
  rw [hword]

/-- The physical eight-word memory block realizes the corresponding abstract
chain query. Memory framing supplies hwords, including nonzero attacker pads. -/
theorem chain_hashInput_words (t : MachineState) (lay treeHigh chain step : Nat)
    (rest : List Word) (hl : lay < 4) (ht : treeHigh < 4) (hi : chain < 62)
    (hs : step < 4) (hrest : rest.length = 7)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (blockAddress lay chain))
    (h11 : t.getReg .x11 = 64)
    (hwords : t.readWords (BitVec.ofNat 64 (blockAddress lay chain)) 8 =
      BitVec.ofNat 64 (AddressFormat.newHeader lay treeHigh chain step) :: rest) :
    hashInput t = AddressFormat.queryPerm (queryOfWords 0
      (BitVec.ofNat 64 (AddressFormat.oldHeader lay treeHigh chain step) :: rest)) := by
  have hb := block_interval lay chain hl hi
  have hsmall : blockAddress lay chain < 2^64 := by omega
  have hal : (t.getReg .x10).toNat % 8 = 0 := by
    rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
    exact block_aligned lay chain
  rw [hashInput_eq_words t 0 h11 (by decide) hal, h10, hwords,
    chain_query_words lay treeHigh chain step rest hl ht hi hs hrest]

end SigGolfCandidate.Base4Candidate.VerifyProof

namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Sign

/-- The byte-facing reference header has exactly the two words consumed by
HASH. The domain byte is two, distinct from the inherited construction. -/
def headerWords (tag lay tree pos leaf : Nat) : List Word :=
  [BitVec.ofNat 64 (2 + 256 * (tag % 256) + 65536 * (lay % 256) +
      2^24 * (tree / 2^32 % 256) + 2^32 * (pos % 2^32)),
   BitVec.ofNat 64 (tree % 2^32 + 2^32 * (leaf % 2^32))]

theorem wordsOf_header (tag lay tree pos leaf : Nat) :
    wordsOf (Reference.header tag lay tree pos leaf) =
      headerWords tag lay tree pos leaf := by
  unfold Reference.header
  rw [List.append_assoc, wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
    wordsOf_eight _ (by simp)]
  simp only [headerWords, SigGolfCandidate.Sign.leNat_append, leNat,
    SigGolfCandidate.Sign.leNat_le32, byte_toNat,
    List.length_cons, List.length_nil, length_le32]
  simp only [List.cons_append, List.nil_append, Nat.mod_mod, List.cons.injEq, and_true]
  constructor <;> congr 1 <;> ring

theorem length_wordsOf_32 (bytes : List Byte) (hb : bytes.length = 32) :
    (wordsOf bytes).length = 4 := by
  rw [← List.take_append_drop 16 bytes, wordsOf_append _ _ (by simp; omega),
    List.length_append, length_wordsOf_16 _ (by simp; omega),
    length_wordsOf_16 _ (by simp; omega)]

/-- No honest-padding assumption is used: every one of the attacker's 32 pad
bytes is retained in the abstract query. -/
theorem chain_pad64_words (lay tree leaf chain step : Nat) (pad value : List Byte)
    (hl : lay < 4) (ht : tree / 2^32 < 4) (hi : chain < 62) (hs : step < 4)
    (hp : pad.length = 32) (hv : value.length = 16) :
    pad64 (Reference.chainInputP lay tree leaf chain (step+1) pad value) =
      queryOfWords 0
        (BitVec.ofNat 64 (AddressFormat.oldHeader lay (tree / 2^32) chain step) ::
         BitVec.ofNat 64 (tree % 2^32 + 2^32 * (leaf % 2^32)) ::
         (wordsOf pad ++ wordsOf value)) := by
  have hlen : (Reference.chainInputP lay tree leaf chain (step+1) pad value).length = 64 := by
    simp [Reference.chainInputP, Reference.header, hp, hv]
  obtain ⟨hn, hpad⟩ := padTo64_eq
    (Reference.chainInputP lay tree leaf chain (step+1) pad value) 0 (by omega) (by omega)
  rw [pad64_eq_query, hn, hpad, hlen]
  simp only [Nat.mul_one, Nat.sub_self, zeros, List.replicate_zero, List.append_nil]
  unfold Reference.chainInputP
  rw [wordsOf_append _ _ (by simp [Reference.header, hp]),
    wordsOf_append _ _ (by simp [Reference.header]), wordsOf_header]
  have hpos : 256 * chain + (step+1) - 1 = 256 * chain + step := by omega
  have hposBound : 256 * chain + step < 2^32 := by omega
  have hw : 2 + 256 * (1 % 256) + 65536 * (lay % 256) +
      2^24 * (tree / 2^32 % 256) + 2^32 * ((256 * chain + (step+1) - 1) % 2^32) =
      AddressFormat.oldHeader lay (tree / 2^32) chain step := by
    rw [hpos, Nat.mod_eq_of_lt (show lay < 256 by omega),
      Nat.mod_eq_of_lt (show tree / 2^32 < 256 by omega), Nat.mod_eq_of_lt hposBound]
    unfold AddressFormat.oldHeader
    omega
  simp only [headerWords, hw, List.cons_append, List.nil_append, List.append_assoc]


/-- Byte-level chain hashing and the actual machine query agree for arbitrary
well-sized values and pads, including malicious nonzero pads. -/
theorem chain_hashInput_reference (t : MachineState) (lay tree leaf chain step : Nat)
    (pad value : List Byte) (hl : lay < 4) (ht : tree / 2^32 < 4)
    (hi : chain < 62) (hs : step < 4) (hp : pad.length = 32) (hv : value.length = 16)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (blockAddress lay chain))
    (h11 : t.getReg .x11 = 64)
    (hwords : t.readWords (BitVec.ofNat 64 (blockAddress lay chain)) 8 =
      BitVec.ofNat 64 (AddressFormat.newHeader lay (tree / 2^32) chain step) ::
      BitVec.ofNat 64 (tree % 2^32 + 2^32 * (leaf % 2^32)) ::
      (wordsOf pad ++ wordsOf value)) :
    hashInput t = AddressFormat.queryPerm
      (pad64 (Reference.chainInputP lay tree leaf chain (step+1) pad value)) := by
  rw [chain_pad64_words lay tree leaf chain step pad value hl ht hi hs hp hv]
  apply chain_hashInput_words t lay (tree / 2^32) chain step _ hl ht hi hs
    (by simp [length_wordsOf_32 pad hp, length_wordsOf_16 value hv]) h10 h11 hwords

end SigGolfCandidate.Base4Candidate.VerifyProof

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv
open Reference.VerifyImage

/-- The material before a fragment, including the gap inserted by place. -/
def placementPrefix (initial : List (BitVec 32)) (address : Nat) : List (BitVec 32) :=
  initial ++ List.replicate (address/4-initial.length) Reference.ChainCode.nop

theorem prefix_length (initial : List (BitVec 32)) (address : Nat)
    (h : initial.length ≤ address/4) : (placementPrefix initial address).length = address/4 := by
  simp only [placementPrefix, List.length_append, List.length_replicate]
  omega

def beforeBodies := place core 4096 dispatches
def beforeForest := place beforeBodies 65536 Reference.ChainCode.bodies
def beforeEntries := place beforeForest 196608 Reference.ForestCode.shapes
def beforeFolds := place beforeEntries 524288 Reference.ChainCode.entries

theorem placement_lengths : beforeBodies.length = 1152 ∧ beforeForest.length = 43077 ∧
    beforeEntries.length = 114688 ∧ beforeFolds.length = 163840 := by
  have hc := core_room
  simp only [beforeBodies, beforeForest, beforeEntries, beforeFolds, place,
    List.length_append, List.length_replicate, dispatches_length, bodies_length,
    forest_length, entries_length]
  norm_num only [Nat.reduceDiv]
  omega

/-- The shared chain bodies really occupy the declared image region. -/
theorem bodies_at : CodeAt image (BitVec.ofNat 64 (4096+65536)) Reference.ChainCode.bodies := by
  let pre := placementPrefix beforeBodies 65536
  let post := List.replicate (196608/4-beforeForest.length) Reference.ChainCode.nop ++
    Reference.ForestCode.shapes ++
    List.replicate (524288/4-beforeEntries.length) Reference.ChainCode.nop ++
    Reference.ChainCode.entries ++
    List.replicate (655360/4-beforeFolds.length) Reference.ChainCode.nop ++
    Reference.LayerFoldCode.tables
  have hp : pre.length = 16384 := prefix_length _ _ (by have := placement_lengths.1; omega)
  apply CodeAt.of_append (pre := pre) (post := post)
  · simp only [image, code, place, pre, post, placementPrefix, beforeBodies, beforeForest,
      beforeEntries, beforeFolds, List.append_assoc]
  · change 69632 = 4096 + 4 * pre.length
    omega
  · rw [hp, bodies_length]
    decide

/-- The direct-dispatch table is also present at its fixed byte offset. -/
theorem entries_at : CodeAt image (BitVec.ofNat 64 (4096+524288)) Reference.ChainCode.entries := by
  let pre := placementPrefix beforeEntries 524288
  let post := List.replicate (655360/4-beforeFolds.length) Reference.ChainCode.nop ++
    Reference.LayerFoldCode.tables
  have hp : pre.length = 131072 := prefix_length _ _
    (by have := placement_lengths.2.2.1; omega)
  apply CodeAt.of_append (pre := pre) (post := post)
  · simp only [image, code, place, pre, post, placementPrefix, beforeBodies, beforeForest,
      beforeEntries, beforeFolds, List.append_assoc]
  · change 528384 = 4096 + 4 * pre.length
    omega
  · rw [hp, entries_length]
    decide

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Sign

/-- All six header/padding words survive an intermediate chain HASH. The
full 32-byte write begins at word six, spilling only beyond this prefix. -/
theorem hash_inplace_header_pad (s : MachineState) (lay chain : Nat)
    (hl : lay < 4) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain + 48))
    (answer : BitVec 256) (word : Nat) (hw : word < 6) :
    (writeHash s answer).getMem (BitVec.ofNat 64 (blockAddress lay chain + 8*word)) =
      s.getMem (BitVec.ofNat 64 (blockAddress lay chain + 8*word)) := by
  have hb := block_interval lay chain hl hi
  apply writeHash_getMem_frame s answer (blockAddress lay chain + 48)
    (blockAddress lay chain + 8*word) hd (by omega) (by omega)
  exact Or.inl (by omega)

/-- The seven words needed by the following rung are the preserved tree/leaf
word and padding, followed by the low 128 bits of the actual oracle answer.
No assumption is made about the answer's high 128 bits or witness padding. -/
theorem hash_inplace_next_input (s : MachineState) (lay chain : Nat)
    (hl : lay < 4) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain + 48))
    (answer : BitVec 256) :
    (writeHash s answer).readWords (BitVec.ofNat 64 (blockAddress lay chain + 8)) 7 =
      s.readWords (BitVec.ofNat 64 (blockAddress lay chain + 8)) 5 ++
        wordsOf (answerBytes 16 answer) := by
  have hb := block_interval lay chain hl hi
  rw [show (7 : Nat) = 5+2 from rfl, readWords_ofNat_add,
    show blockAddress lay chain + 8 + 8*5 = blockAddress lay chain + 48 by omega,
    writeHash_readWords_val s answer _ hd (by omega)]
  congr 1
  apply readWords_congr
  intro word hw
  rw [show blockAddress lay chain + 8 + 8*word =
    blockAddress lay chain + 8*(word+1) by omega]
  exact hash_inplace_header_pad s lay chain hl hi hd answer (word+1) (by omega)

end SigGolfCandidate.Base4Candidate.VerifyProof

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- A symbolic placement lemma avoids enumerating every table instruction. -/
theorem flatMap_range_prefix {α : Type} (f : Nat → List α) (n i : Nat) (hi : i < n) :
    (List.range i).flatMap f ++ f i <+: (List.range n).flatMap f := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i = n
    · subst i
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact ⟨[], by simp⟩
    · obtain ⟨tail, ht⟩ := ih (by omega)
      refine ⟨tail ++ f n, ?_⟩
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [← ht]
      simp only [List.append_assoc]

/-- Every shared body has its declared offset, including the short final group. -/
theorem body_decomposition (group q : Nat) (hg : group < 16)
    (hq : q < if group = 15 then 4 else 64) :
    ∃ pre post, Reference.ChainCode.bodies = pre ++ Reference.ChainCode.body group q ++ post ∧
      pre.length = 1776 * group + Reference.ChainCode.caseOffset group q := by
  let f := fun g => (List.range (if g = 15 then 4 else 64)).flatMap (Reference.ChainCode.body g)
  obtain ⟨outer, ho⟩ := flatMap_range_prefix f 16 group hg
  obtain ⟨inner, hi⟩ := flatMap_range_prefix (Reference.ChainCode.body group)
    (if group = 15 then 4 else 64) q hq
  have houter : ((List.range group).flatMap f).length = group * 1776 := by
    rw [Reference.flatMap_length_constant (List.range group) f 1776]
    · simp
    · intro g hgm
      have hgm' := List.mem_range.mp hgm
      have hsmall : g < 15 := by omega
      dsimp only [f]
      rw [if_neg (by omega)]
      simpa only [List.length_flatMap, Function.comp_def, Reference.ChainCode.body_length]
        using Reference.ChainCode.group_words g hsmall
  have hinner : ((List.range q).flatMap (Reference.ChainCode.body group)).length =
      Reference.ChainCode.caseOffset group q := by
    simp only [Reference.ChainCode.caseOffset, List.length_flatMap, Function.comp_def,
      Reference.ChainCode.body_length]
  refine ⟨(List.range group).flatMap f ++ (List.range q).flatMap (Reference.ChainCode.body group),
    inner ++ outer, ?_, ?_⟩
  · change (List.range 16).flatMap f = _
    rw [← ho]
    change ((List.range group).flatMap f ++
      (List.range (if group = 15 then 4 else 64)).flatMap (Reference.ChainCode.body group)) ++ outer = _
    rw [← hi]
    simp only [List.append_assoc]
  · rw [List.length_append, houter, hinner]
    omega

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- Code placement is preserved when selecting a contiguous inner fragment. -/
theorem subfragment {image : Image} {pc : Word} {pre fragment post : List (BitVec 32)}
    (h : CodeAt image pc (pre ++ fragment ++ post)) (pc' : Word)
    (hp : pc'.toNat = pc.toNat + 4*pre.length) : CodeAt image pc' fragment := by
  obtain ⟨hb, ha, hr, tail, ht⟩ := h
  have hlength : (pre ++ fragment ++ post).length = pre.length + fragment.length + post.length := by
    simp only [List.length_append]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hi : (pc'.toNat-4096)/4 = (pc.toNat-4096)/4 + pre.length := by omega
  rw [hi, ← List.drop_drop, ← ht, List.append_assoc, List.append_assoc, List.drop_left]
  exact ⟨post ++ tail, by simp only [List.append_assoc]⟩

/-- Machine code for every shared chain case is located at the address used by
its direct-dispatch entry; this closes the table-to-body address obligation. -/
theorem body_at (group q : Nat) (hg : group < 16)
    (hq : q < if group = 15 then 4 else 64) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q))
      (Reference.ChainCode.body group q) := by
  obtain ⟨pre, post, he, hp⟩ := body_decomposition group q hg hq
  have hlen : pre.length ≤ 26693 := by
    have h := congrArg List.length he
    rw [Reference.VerifyImage.bodies_length] at h
    simp only [List.length_append] at h
    omega
  have h := bodies_at
  rw [he] at h
  apply subfragment h
  have hpc : 4096 + Reference.ChainCode.bodyPc group q < 2^64 := by
    unfold Reference.ChainCode.bodyPc
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
  change 4096 + Reference.ChainCode.bodyPc group q = 69632 + 4*pre.length
  unfold Reference.ChainCode.bodyPc
  omega

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

theorem entry_decomposition (group row : Nat) (hg : group < 16) (hr : row < 256) :
    ∃ pre post, Reference.ChainCode.entries = pre ++ Reference.ChainCode.entry group row ++ post ∧
      pre.length = 128 * row + 8 * group := by
  let f := fun r => (List.range 16).flatMap (fun g => Reference.ChainCode.entry g r)
  obtain ⟨outer, ho⟩ := flatMap_range_prefix f 256 row hr
  obtain ⟨inner, hi⟩ := flatMap_range_prefix (fun g => Reference.ChainCode.entry g row) 16 group hg
  have hrow (r : Nat) : (f r).length = 128 := by
    dsimp only [f]
    rw [Reference.flatMap_length_constant _ _ 8
      (fun g _ => Reference.ChainCode.entry_length g r)]
    rfl
  have houter : ((List.range row).flatMap f).length = row*128 := by
    rw [Reference.flatMap_length_constant _ _ 128 (fun r _ => hrow r), List.length_range]
  have hinner : ((List.range group).flatMap (fun g => Reference.ChainCode.entry g row)).length = group*8 := by
    rw [Reference.flatMap_length_constant _ _ 8
      (fun g _ => Reference.ChainCode.entry_length g row), List.length_range]
  refine ⟨(List.range row).flatMap f ++
      (List.range group).flatMap (fun g => Reference.ChainCode.entry g row),
    inner ++ outer, ?_, ?_⟩
  · change (List.range 256).flatMap f = _
    rw [← ho]
    change ((List.range row).flatMap f ++
      (List.range 16).flatMap (fun g => Reference.ChainCode.entry g row)) ++ outer = _
    rw [← hi]
    simp only [List.append_assoc]
  · rw [List.length_append, houter, hinner]
    omega

theorem entry_at (group row : Nat) (hg : group < 16) (hr : row < 256) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group row))
      (Reference.ChainCode.entry group row) := by
  obtain ⟨pre, post, he, hp⟩ := entry_decomposition group row hg hr
  have h := entries_at
  rw [he] at h
  apply subfragment h
  have hpc : 4096 + Reference.ChainCode.tablePc group row < 2^64 := by
    unfold Reference.ChainCode.tablePc
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
  change 4096 + Reference.ChainCode.tablePc group row = 528384 + 4*pre.length
  unfold Reference.ChainCode.tablePc
  omega

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/- Every hashing entry runs the same chain head before reaching its first
HASH; the following jump and row-dependent continuation are not executed yet. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem entry_head_run (group : Fin 16) (row : Nat) (pc : Word)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3) :
    symRun {noAlias := true} (Reference.ChainCode.entry group.val row) pc 64 =
      some (headResult ⟨4*group.val, by have := group.isLt; omega⟩
        (Reference.ChainCode.digitOf row 0) pc) := by
  unfold Reference.ChainCode.entry
  generalize he : Reference.ChainCode.digitOf row 0 = d at *
  fin_cases d <;> norm_num at hd
  all_goals fin_cases group <;> revert pc row
  kernel_forall_rfl_all

/-- The first HASH of a dispatched chain is reached in the real verifier
image, subject to the explicit memory obligations. -/
theorem entry_head_steps (group : Fin 16) (row : Nat) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row))
    (hob : (headResult ⟨4*group.val, by have := group.isLt; omega⟩
      (Reference.ChainCode.digitOf row 0) s.pc).obligs s) :
    let r := headResult ⟨4*group.val, by have := group.isLt; omega⟩
      (Reference.ChainCode.digitOf row 0) s.pc
    Steps Reference.VerifyImage.image s r.steps r.cycles (r.toState s) ∧
      fetch Reference.VerifyImage.image (r.toState s) = some (.base .ECALL) := by
  have hc := ImagePlacement.entry_at group.val row group.isLt hr
  rw [← hpc] at hc
  refine ⟨symRun_sound (entry_head_run group row s.pc hd) hc s rfl hob, ?_⟩
  apply symRun_ecall (entry_head_run group row s.pc hd) hc s hob
  rw [(head_shape _ _ s.pc).1, if_neg (by omega)]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_memory (chain : Fin 62) (digit : Fin 3) (pc : Word) :
    (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).st.mem =
      headWrites chain.val digit := by
  simp only [headResult, dif_pos digit.isLt, hashingHeadResult]

/-- The complete memory semantics, independent of the caller's initial bytes. -/
theorem head_memory_eval (chain : Fin 62) (digit : Fin 3) (pc : Word)
    (s : MachineState) (address : Word) :
    ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getMem address =
      memEval s (headWrites chain.val digit) address := by
  rw [Result.toState_getMem, head_memory]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_obligations_shape (chain : Fin 62) (digit : Fin 3) (pc : Word) :
    (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).st.obl =
      headObligations chain.val digit := by
  simp only [headResult, dif_pos digit.isLt, hashingHeadResult]

/-- Concrete validity conditions suffice for every symbolic side condition;
there are no hidden assumptions about initial witness contents. -/
theorem head_obligations (chain : Fin 62) (digit : Fin 3) (pc : Word) (s : MachineState)
    (h8 : (s.getReg .x22).toNat % 8 = 0)
    (haccess : ∀ k width, (k = 0 ∧ width = 8) ∨ (k = 8 ∧ width = 8) ∨
        (k = 4 ∧ width = 1) →
      accessValid ((norm (addC (.reg .x22)
        (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+k)))).eval s) width = true) :
    (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).obligs s := by
  unfold Result.obligs
  rw [head_obligations_shape]
  have h0 := haccess 0 8 (by simp)
  have h1 := haccess 8 8 (by simp)
  have h2 := haccess 4 1 (by simp)
  unfold headObligations
  split_ifs <;> simp only [List.nil_append, List.cons_append, Oblig.all, Oblig.holds, E.eval]
  · exact ⟨h1, h0⟩
  · exact ⟨h8, h2, h1, h0⟩

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/- Signed instruction offsets resolve to the declared witness block in every
layer, including the negative offsets before the centered base. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem centered_addresses (lay : Fin 4) (chain : Fin 62) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    let address := fun k => (norm (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+k)))).eval s
    address 0 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) ∧
    address 4 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+4) ∧
    address 8 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8) := by
  simp only [norm_eval, addC_eval, E.eval, h22]
  fin_cases lay <;> fin_cases chain <;> exact ⟨rfl, rfl, rfl⟩

/-- The actual centered witness base discharges all head memory obligations. -/
theorem head_obligations_numeric (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).obligs s := by
  have ha := centered_addresses lay chain s h22
  have hal := VerifyProof.block_aligned lay.val chain.val
  apply head_obligations chain digit pc s
  · rw [h22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := lay.isLt; omega)]
    omega
  · intro k width hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ha.1]
      exact VerifyProof.block_access lay.val chain.val 0 8 lay.isLt chain.isLt
        (by decide) (by simp) (by omega)
    · rw [ha.2.2]
      exact VerifyProof.block_access lay.val chain.val 8 8 lay.isLt chain.isLt
        (by decide) (by simp) (by omega)
    · rw [ha.2.1]
      exact VerifyProof.block_access lay.val chain.val 4 1 lay.isLt chain.isLt
        (by decide) (by simp) (by simp)

/-- Every hashing table entry reaches its first HASH from the declared layer
base. Code placement and all symbolic memory obligations are now discharged. -/
theorem entry_first_hash (lay : Fin 4) (group : Fin 16) (row : Nat) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    let r := headResult ⟨4*group.val, by have := group.isLt; omega⟩
      (Reference.ChainCode.digitOf row 0) s.pc
    Steps Reference.VerifyImage.image s r.steps r.cycles (r.toState s) ∧
      fetch Reference.VerifyImage.image (r.toState s) = some (.base .ECALL) := by
  apply entry_head_steps group row hr hd s hpc
  exact head_obligations_numeric lay _ ⟨_, hd⟩ s.pc s h22

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- Updating the step byte of a physical address gives precisely the permuted
chain header. Routed tree addresses fit the low tree word. -/
theorem physical_step_header (lay chain digit : Nat) (hl : lay < 4) (hi : chain < 62)
    (hd : digit < 4) :
    replaceByte (BitVec.ofNat 64 (VerifyProof.blockAddress lay chain)) 4 (BitVec.ofNat 8 digit) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay 0 chain digit) := by
  apply BitVec.eq_of_toNat_eq
  rw [SigGolfCandidate.Verify.replaceByte_toNat _ 4 (by decide)]
  simp only [BitVec.toNat_ofNat]
  unfold VerifyProof.blockAddress AddressFormat.newHeader
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.add_zero]
  omega

/-- Both header words produced by an actual hashing head. -/
theorem head_header_words (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) :
    let t := (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s
    t.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val digit.val) ∧
    t.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) = s.getReg .x31 := by
  have ha := centered_addresses lay chain s h22
  have h0 : (norm (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val)))).eval s =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) := by
    simpa only [Int.add_zero] using ha.1
  have he : (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val))).eval s =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) := by
    rw [← norm_eval]
    exact h0
  have hn : BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) ≠
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8) := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
    simp only [BitVec.toNat_ofNat] at h'
    omega
  dsimp only
  constructor <;> rw [head_memory_eval]
  · fin_cases digit <;>
      simp only [headWrites, if_neg (by decide : ¬(1 : Nat) = 0),
        if_neg (by decide : ¬(2 : Nat) = 0), if_neg (by decide : ¬(2 : Nat) = 1),
        List.nil_append, memEval, h0, ha.2.2, he,
        E.eval, h6, h7, BinOp.eval, StoreKind.merge, if_pos rfl, if_neg hn,
        if_neg (Ne.symm hn)]
    · rfl
    · exact physical_step_header _ _ 1 lay.isLt chain.isLt (by decide)
    · exact physical_step_header _ _ 2 lay.isLt chain.isLt (by decide)
  · fin_cases digit <;>
      simp only [headWrites, if_neg (by decide : ¬(1 : Nat) = 0),
        if_neg (by decide : ¬(2 : Nat) = 0), if_neg (by decide : ¬(2 : Nat) = 1),
        List.nil_append, memEval, h0, ha.2.2, he,
        E.eval, if_pos rfl, if_neg hn, if_neg (Ne.symm hn)]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

/-- Frame rule for both header stores and the optional step-byte store. -/
theorem head_frame (chain : Fin 62) (digit : Fin 3) (pc : Word) (s : MachineState)
    (address : Word)
    (h0 : address ≠ (norm (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val)))).eval s)
    (h8 : address ≠ (norm (addC (.reg .x22)
      (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+8)))).eval s) :
    ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getMem address =
      s.getMem address := by
  rw [head_memory_eval]
  unfold headWrites
  split_ifs <;> simp only [memEval, if_neg h0, if_neg h8]

/-- Every pad/value word is framed by a hashing head. -/
theorem head_data_word (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (pc : Word) (s : MachineState) (k : Nat) (hk : 2 ≤ k) (hk' : k < 8)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getMem
      (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8*k)) =
      s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8*k)) := by
  have ha := centered_addresses lay chain s h22
  have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
  apply head_frame
  · have h0 : (norm (addC (.reg .x22)
        (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val)))).eval s =
        BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) := by
      simpa only [Int.add_zero] using ha.1
    rw [h0]
    intro h
    have hh := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hh
    omega
  · rw [ha.2.2]
    intro h
    have hh := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hh
    omega

/-- The complete eight-word HASH input after a head, with the six data words
coming directly from the initial witness memory. -/
theorem head_input_read (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) :
    let t := (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s
    t.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) 8 =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val digit.val) ::
      s.getReg .x31 ::
      s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+16)) 6 := by
  let t := (headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s
  have hh := head_header_words lay chain digit pc s h22 h6 h7
  have ht : t.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+16)) 6 =
      s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+16)) 6 := by
    apply readWords_congr
    intro i hi
    have h := head_data_word lay chain digit pc s (i+2) (by omega) (by omega) h22
    rw [show VerifyProof.blockAddress lay.val chain.val+16+8*i =
      VerifyProof.blockAddress lay.val chain.val+8*(i+2) by omega]
    exact h
  change t.readWords _ 8 = _
  rw [show (8 : Nat) = 2+6 from rfl, readWords_ofNat_add, readWords_ofNat_two,
    hh.1, hh.2, ht]
  rfl

/-- The HASH reached by a chain head queries exactly the byte reference's
padded chain input, not just an abstract block with assumed header words. -/
theorem head_hash_query (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (tree leaf : Nat) (htree : tree < 2^32) (pad value : List Byte)
    (hp : pad.length = 32) (hv : value.length = 16) (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) (h11 : s.getReg .x11 = 64)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 (tree % 2^32 + 2^32*(leaf % 2^32)))
    (hdata : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+16)) 6 =
      wordsOf pad ++ wordsOf value) :
    hashInput ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s) =
      AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64
        (Reference.chainInputP lay.val tree leaf chain.val (digit.val+1) pad value)) := by
  have hr := head_registers chain digit s pc
  have ha := centered_addresses lay chain s h22
  have h10 : ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getReg .x10 =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) := by
    rw [hr.1, ← norm_eval]
    simpa only [Int.add_zero] using ha.1
  apply VerifyProof.chain_hashInput_reference _ lay.val tree leaf chain.val digit.val pad value
    lay.isLt (by rw [Nat.div_eq_of_lt htree]; decide) chain.isLt (by have := digit.isLt; omega)
    hp hv h10 (hr.2.2.1.trans h11)
  rw [head_input_read lay chain digit pc s h22 h6 h7, h31, hdata,
    Nat.div_eq_of_lt htree]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem centered_value_address (lay : Fin 4) (chain : Fin 62) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+48))).eval s =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48) := by
  simp only [addC_eval, E.eval, h22]
  fin_cases lay <;> fin_cases chain <;> rfl

/-- HASH validates the entire 32-byte destination, including its spill. -/
theorem head_hash_arguments (lay : Fin 4) (chain : Fin 62) (digit : Fin 3)
    (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val))
    (h11 : s.getReg .x11 = 64) :
    hashArgumentsValid ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s) = true := by
  have hr := head_registers chain digit s pc
  have ha := centered_addresses lay chain s h22
  have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
  have hal := VerifyProof.block_aligned lay.val chain.val
  have h10 : ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getReg .x10 =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val) := by
    rw [hr.1, ← norm_eval]
    simpa only [Int.add_zero] using ha.1
  have h12 : ((headResult chain ⟨digit.val, by have := digit.isLt; omega⟩ pc).toState s).getReg .x12 =
      BitVec.ofNat 64 (if digit.val = 2 then Reference.ChainCode.leafSlot chain.val else
        VerifyProof.blockAddress lay.val chain.val+48) := by
    rw [hr.2.1]
    split_ifs
    · rfl
    · exact centered_value_address lay chain s h22
  apply hashArgs_of h10 (hr.2.2.1.trans h11) h12
  · omega
  · decide
  · omega
  · split_ifs
    · unfold Reference.ChainCode.leafSlot
      omega
    · omega
  · split_ifs
    · unfold Reference.ChainCode.leafSlot
      have := chain.isLt
      norm_num only [MEMORY_BYTES]
      omega
    · omega
  · decide

/-- One concrete dispatched head plus its first HASH, with exact ordinary
step costs and the pinned eight-cycle one-block oracle charge. -/
theorem entry_hash_good (lay : Fin 4) (group : Fin 16) (row : Nat) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3)
    (tree leaf : Nat) (htree : tree < 2^32) (pad value : List Byte)
    (hp : pad.length = 32) (hv : value.length = 16) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) (h11 : s.getReg .x11 = 64)
    (h5 : s.getReg .x5 = 0)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 (tree % 2^32 + 2^32*(leaf % 2^32)))
    (hdata : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val (4*group.val)+16)) 6 =
      wordsOf pad ++ wordsOf value)
    (N C : Nat) (K : SigGolfCandidate.Ref.Val → OracleComp HashSpec VerifyProof.Obs)
    (hafter : ∀ answer,
      VerifyProof.Good (writeHash
        ((headResult ⟨4*group.val, by have := group.isLt; omega⟩
          (Reference.ChainCode.digitOf row 0) s.pc).toState s) answer) N C
        (K (SigGolfCandidate.Ref.answerBytes 16 answer))) :
    let r := headResult ⟨4*group.val, by have := group.isLt; omega⟩
      (Reference.ChainCode.digitOf row 0) s.pc
    VerifyProof.Good s (N+1+r.steps) (C+8+r.cycles)
      (VerifyProof.cc (Reference.h16 (Reference.chainInputP lay.val tree leaf (4*group.val)
        ((Reference.ChainCode.digitOf row 0).val+1) pad value)) K) := by
  let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
  let digit : Fin 3 := ⟨(Reference.ChainCode.digitOf row 0).val, hd⟩
  have hs := entry_first_hash lay group row hr hd s hpc h22
  have hregs := head_registers chain digit s s.pc
  have hargs := head_hash_arguments lay chain digit s.pc s h22 h11
  have hquery := head_hash_query lay chain digit tree leaf htree pad value hp hv s.pc s
    h22 h6 h7 h11 h31 hdata
  have hgood := VerifyProof.Good.hash hs.2 (hregs.2.2.2.1.trans h5) hargs hquery hafter
  have hblocks : (VerifyProof.queryFormat
      (Reference.chainInputP lay.val tree leaf chain.val (digit.val+1) pad value)).blocks = 1 := by
    unfold VerifyProof.queryFormat
    rw [AddressFormat.queryPerm_blocks, VerifyProof.chain_pad64_words _ _ _ _ _ _ _
      lay.isLt (by rw [Nat.div_eq_of_lt htree]; decide) chain.isLt (by have := digit.isLt; omega) hp hv]
    rfl
  simpa only [hblocks, Nat.mul_one] using hgood.steps hs.1

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- Remaining chain HASH blocks: step one updates the byte; step two also
redirects the full answer to the leaf-public-key buffer. -/
def rungResult (chain : Fin 62) (step : Fin 2) (pc : Word) : Result :=
  let regs : RegFile := if step.val = 1 then
      { RegFile.init with r12 := .c (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)) }
    else RegFile.init
  let mem : SymMem := [(⟨some (.reg .x10), 0⟩,
    .bin (.st .b 4) (.ld (.reg .x10)) (.reg (if step.val = 0 then .x6 else .x7)))]
  let obligations : List Oblig := [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 4⟩ 1]
  ⟨⟨regs, mem, obligations⟩, .c (AddressAdapter.addPc pc (step.val+1)),
    .ecall, step.val+1, step.val+1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rung_run (chain : Fin 62) (step : Fin 2) (pc : Word) :
    symRun {noAlias := true} (Reference.ChainCode.rung chain.val 0 (step.val+1)) pc 8 =
      some (rungResult chain step pc) := by
  fin_cases chain <;> fin_cases step <;> revert pc
  kernel_forall_rfl_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rung_shape (chain : Fin 62) (step : Fin 2) (pc : Word) :
    (rungResult chain step pc).stop = .ecall ∧
    (rungResult chain step pc).steps = step.val+1 ∧
    (rungResult chain step pc).cycles = step.val+1 := by
  exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rung_registers (chain : Fin 62) (step : Fin 2) (pc : Word) (s : MachineState) :
    let t := (rungResult chain step pc).toState s
    t.getReg .x10 = s.getReg .x10 ∧
    t.getReg .x12 = (if step.val = 1 then BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)
      else s.getReg .x12) ∧
    t.getReg .x11 = s.getReg .x11 ∧ t.getReg .x5 = s.getReg .x5 ∧
    t.getReg .x16 = s.getReg .x16 ∧ t.getReg .x17 = s.getReg .x17 := by
  fin_cases step <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constants used by subsequent chain steps and groups survive either rung. -/
theorem rung_constants (chain : Fin 62) (step : Fin 2) (pc : Word) (s : MachineState) :
    let t := (rungResult chain step pc).toState s
    t.getReg .x6 = s.getReg .x6 ∧ t.getReg .x7 = s.getReg .x7 ∧
    t.getReg .x22 = s.getReg .x22 ∧ t.getReg .x31 = s.getReg .x31 := by
  fin_cases step <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem rung_pc (chain : Fin 62) (step : Fin 2) (pc : Word) (s : MachineState) :
    ((rungResult chain step pc).toState s).pc = AddressAdapter.addPc pc (step.val+1) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rung_memory (chain : Fin 62) (step : Fin 2) (pc : Word) :
    (rungResult chain step pc).st.mem =
      [(⟨some (.reg .x10), 0⟩,
        .bin (.st .b 4) (.ld (.reg .x10)) (.reg (if step.val = 0 then .x6 else .x7)))] := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rung_obligations_shape (chain : Fin 62) (step : Fin 2) (pc : Word) :
    (rungResult chain step pc).st.obl =
      [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 4⟩ 1] := by
  rfl

/-- Remaining steps have no assumptions about the previous oracle answer. -/
theorem rung_obligations (lay : Fin 4) (chain : Fin 62) (step : Fin 2) (pc : Word)
    (s : MachineState)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) :
    (rungResult chain step pc).obligs s := by
  have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
  have ha := VerifyProof.block_aligned lay.val chain.val
  unfold Result.obligs
  rw [rung_obligations_shape]
  simp only [Oblig.all, Oblig.holds, E.eval, Addr.eval, h10, SigGolfCandidate.Sign.ofNat_add_ofNat]
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact VerifyProof.block_access lay.val chain.val 4 1 lay.isLt chain.isLt
      (by decide) (by simp) (by simp)

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- The suffix after the two shared first-chain rungs. -/
def afterFirstChain (group q : Nat) : List (BitVec 32) :=
  let rest := Reference.ChainCode.remainder group q
  rest ++ [if group = 15 then Reference.ChainCode.opI 103 0 0 1 0 else
    Reference.ChainCode.jal 0
      ((Reference.ChainCode.dispatchPc (group+1) : Int) -
        (Reference.ChainCode.bodyPc group q + 4*(5+rest.length) : Nat))]

theorem first_rung_at (group q : Nat) (hg : group < 16)
    (hq : q < if group = 15 then 4 else 64) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q))
      (Reference.ChainCode.rung (4*group) 0 1) := by
  have h := body_at group q hg hq
  change CodeAt _ _ ([] ++ Reference.ChainCode.rung (4*group) 0 1 ++
    (Reference.ChainCode.rung (4*group) 0 2 ++ afterFirstChain group q)) at h
  exact subfragment h _ (by simp)

theorem final_rung_at (group q : Nat) (hg : group < 16)
    (hq : q < if group = 15 then 4 else 64) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q) + 8)
      (Reference.ChainCode.rung (4*group) 0 2) := by
  have h := body_at group q hg hq
  have hbound := h.2.2.1
  have hlen : 2 ≤ (Reference.ChainCode.body group q).length := by
    rw [Reference.ChainCode.body_length]
    unfold Reference.ChainCode.caseWords
    omega
  change CodeAt _ _ (Reference.ChainCode.rung (4*group) 0 1 ++
    Reference.ChainCode.rung (4*group) 0 2 ++ afterFirstChain group q) at h
  apply subfragment h
  change (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q) + 8).toNat =
    (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q)).toNat + 4*2
  rw [BitVec.toNat_add]
  change (_ + 8) % 2^64 = _ + 8
  omega

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- A digit-three table entry starts with the complete four-instruction copy. -/
theorem copy_entry_at (group row : Nat) (hg : group < 16) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val = 3) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group row))
      (Reference.ChainCode.code (4*group) 3) := by
  have h := entry_at group row hg hr
  have hd' : Reference.ChainCode.digitOf row 0 = (3 : Fin 4) := Fin.ext hd
  unfold Reference.ChainCode.entry at h
  rw [hd'] at h
  have hlen : (Reference.ChainCode.code (4*group) 3).length = 4 :=
    Reference.ChainCode.code_length _ _
  simp only [Reference.ChainCode.firstLength] at h
  rw [List.take_of_length_le (by omega)] at h
  simp only [List.append_assoc] at h
  exact subfragment (pre := []) h _ (by simp)

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem copy_obligations_shape (chain : Fin 62) (pc : Word) :
    (headResult chain 3 pc).st.obl =
      [.valid (norm (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+56)))) 8,
       .valid (norm (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+48)))) 8] := by
  fin_cases chain <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem centered_second_value_address (lay : Fin 4) (chain : Fin 62) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+56))).eval s =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+56) := by
  simp only [addC_eval, E.eval, h22]
  fin_cases lay <;> fin_cases chain <;> rfl

theorem copy_obligations (lay : Fin 4) (chain : Fin 62) (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    (headResult chain 3 pc).obligs s := by
  have hal := VerifyProof.block_aligned lay.val chain.val
  unfold Result.obligs
  rw [copy_obligations_shape]
  simp only [Oblig.all, Oblig.holds, norm_eval,
    centered_value_address lay chain s h22, centered_second_value_address lay chain s h22]
  exact ⟨VerifyProof.block_access lay.val chain.val 56 8 lay.isLt chain.isLt
    (by decide) (by simp) (by omega),
    VerifyProof.block_access lay.val chain.val 48 8 lay.isLt chain.isLt
      (by decide) (by simp) (by omega)⟩

/-- The no-HASH case executes its complete value copy in four ordinary cycles
inside the actual direct-dispatch table. -/
theorem entry_copy_steps (lay : Fin 4) (group : Fin 16) (row : Nat) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val = 3) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    Steps Reference.VerifyImage.image s 4 4
      ((headResult ⟨4*group.val, by have := group.isLt; omega⟩ 3 s.pc).toState s) := by
  let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
  have hc := ImagePlacement.copy_entry_at group.val row group.isLt hr hd
  rw [← hpc] at hc
  have h := head_steps Reference.VerifyImage.image chain 3 s.pc s hc rfl
    (copy_obligations lay chain s.pc s h22)
  have hn := (head_shape chain 3 s.pc).2
  simpa only [hn.1, hn.2, if_pos (show (3 : Fin 4).val = 0 ∨ (3 : Fin 4).val = 3 from Or.inr rfl)] using h

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

/- The copy case writes exactly two endpoint words, loaded before either
store. It neither hashes nor changes any witness word. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem copy_memory (chain : Fin 62) (pc : Word) :
    (headResult chain 3 pc).st.mem =
      [(⟨none, BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val+8)⟩,
        .ld (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+56)))),
       (⟨none, BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)⟩,
        .ld (addC (.reg .x22) (BitVec.ofInt 64 (Reference.ChainCode.offset chain.val+48))))] := by
  fin_cases chain <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem copy_registers (chain : Fin 62) (pc : Word) (s : MachineState) :
    let t := (headResult chain 3 pc).toState s
    t.getReg .x5 = s.getReg .x5 ∧ t.getReg .x11 = s.getReg .x11 ∧
    t.getReg .x16 = s.getReg .x16 ∧ t.getReg .x17 = s.getReg .x17 ∧
    t.getReg .x22 = s.getReg .x22 ∧ t.getReg .x31 = s.getReg .x31 := by
  fin_cases chain <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem copy_endpoint_words (lay : Fin 4) (chain : Fin 62) (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    let t := (headResult chain 3 pc).toState s
    t.getMem (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)) =
      s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48)) ∧
    t.getMem (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val+8)) =
      s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+56)) := by
  have hn : BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val) ≠
      BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val+8) := by
    intro h
    have hh := congrArg BitVec.toNat h
    have hc := chain.isLt
    simp only [BitVec.toNat_ofNat, Reference.ChainCode.leafSlot] at hh
    omega
  dsimp only
  constructor <;> rw [Result.toState_getMem, copy_memory] <;>
    simp only [memEval, Addr.eval, if_pos rfl, if_neg hn, E.eval,
      centered_value_address lay chain s h22, centered_second_value_address lay chain s h22]

/-- Endpoint serialization agrees with the two initial chain-value words. -/
theorem copy_endpoint_read (lay : Fin 4) (chain : Fin 62) (pc : Word) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    ((headResult chain 3 pc).toState s).readWords
      (BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val)) 2 =
    s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48)) 2 := by
  have h := copy_endpoint_words lay chain pc s h22
  rw [readWords_ofNat_two, readWords_ofNat_two, h.1]
  rw [show VerifyProof.blockAddress lay.val chain.val+48+8 =
    VerifyProof.blockAddress lay.val chain.val+56 by omega, h.2]

/-- The two endpoint writes preserve every witness word, not just later
chains. The endpoint buffer and the complete witness region are disjoint. -/
theorem copy_witness_frame (chain : Fin 62) (pc : Word) (s : MachineState)
    (address : Nat) (ha : 2048 ≤ address) (hb : address < 2^64) :
    ((headResult chain 3 pc).toState s).getMem (BitVec.ofNat 64 address) =
      s.getMem (BitVec.ofNat 64 address) := by
  have h0 : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val) := by
    intro h
    have hh := congrArg BitVec.toNat h
    have hc := chain.isLt
    simp only [BitVec.toNat_ofNat, Reference.ChainCode.leafSlot] at hh
    omega
  have h8 : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain.val+8) := by
    intro h
    have hh := congrArg BitVec.toNat h
    have hc := chain.isLt
    simp only [BitVec.toNat_ofNat, Reference.ChainCode.leafSlot] at hh
    omega
  rw [Result.toState_getMem, copy_memory]
  simp only [memEval, Addr.eval, if_neg h8, if_neg h0]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.JumpProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64

/-- The exact immediate permutation used by the alternative assembler.  A
single arithmetic proof covers every table entry and shared-body return. -/
def raw (n : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (111 + 2147483648*(n/1048576) +
    2097152*(n/2%1024) + 1048576*(n/2048%2) + 4096*(n/4096%256))

set_option maxHeartbeats 2000000 in
theorem raw_value (n : Nat) (hn : n < 2097152) :
    (raw n).toNat = 111 + 2147483648*(n/1048576) +
      2097152*(n/2%1024) + 1048576*(n/2048%2) + 4096*(n/4096%256) := by
  unfold raw
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

set_option maxHeartbeats 2000000 in
theorem raw_fields (n : Nat) (hn : n < 2097152) :
    ((raw n).extractLsb' 0 7).toNat = 111 ∧
    ((raw n).extractLsb' 7 5).toNat = 0 ∧
    ((raw n).extractLsb' 31 1).toNat = n/1048576 ∧
    ((raw n).extractLsb' 12 8).toNat = n/4096%256 ∧
    ((raw n).extractLsb' 20 1).toNat = n/2048%2 ∧
    ((raw n).extractLsb' 21 10).toNat = n/2%1024 := by
  simp only [BitVec.extractLsb'_toNat, raw_value n hn, Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow, Nat.div_one]
  omega

private theorem append_value {m k : Nat} (x : BitVec m) (y : BitVec k) :
    (x ++ y).toNat = x.toNat * 2^k + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

set_option maxHeartbeats 2000000 in
theorem raw_immediate (n : Nat) (hn : n < 2097152) (he : n%2 = 0) :
    RiscvZkvm.Interpreter.immJ (raw n) = BitVec.ofNat 21 n := by
  have hf := raw_fields n hn
  apply BitVec.eq_of_toNat_eq
  simp only [RiscvZkvm.Interpreter.immJ, append_value, hf.2.2.1,
    hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, BitVec.toNat_ofNat]
  norm_num only [Nat.reducePow, Nat.zero_mod]
  omega

/-- Decoding the actual instruction word recovers x0 and the original even
21-bit immediate.  No assumption about the decoder is introduced. -/
theorem raw_decode (n : Nat) (hn : n < 2097152) (he : n%2 = 0) :
    decodeInstruction (raw n) = some (.base (.JAL .x0 (BitVec.ofNat 21 n))) := by
  have hf := raw_fields n hn
  have hr : (raw n).extractLsb' 7 5 = 0 := by
    apply BitVec.eq_of_toNat_eq
    exact hf.2.1
  simp [decodeInstruction, RiscvZkvm.Interpreter.decode, hf.1, hr,
    RiscvZkvm.Interpreter.regOfBits, raw_immediate n hn he]

/-- The signed assembler input is reduced modulo 2^21 exactly once. -/
theorem assembler_raw (imm : Int) :
    Reference.ChainCode.jal 0 imm = raw ((imm%2097152).toNat) := by
  simp only [Reference.ChainCode.jal, raw, Nat.mul_zero, Nat.add_zero]

/-- Within the architectural signed range, extending the decoded immediate
back to a machine word preserves the signed displacement. -/
theorem signed_displacement (imm : Int)
    (hlo : -1048576 ≤ imm) (hhi : imm < 1048576) :
    (BitVec.ofInt 21 imm).signExtend 64 = BitVec.ofInt 64 imm := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide),
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega),
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]

end SigGolfCandidate.Base4Candidate.JumpProof

namespace SigGolfCandidate.Base4Candidate.JumpProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- All direct jumps use the same checked encoder/decoder bridge, including
negative displacements from dispatch tables back into shared bodies. -/
theorem assembler_decode (imm : Int) (he : imm%2 = 0) :
    decodeInstruction (Reference.ChainCode.jal 0 imm) =
      some (.base (.JAL .x0 (BitVec.ofInt 21 imm))) := by
  have hn : (imm%2097152).toNat < 2097152 := by omega
  have he' : (imm%2097152).toNat%2 = 0 := by omega
  have hi : BitVec.ofNat 21 (imm%2097152).toNat = BitVec.ofInt 21 imm := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    change (imm%2097152).toNat%2097152 = (imm%2097152).toNat
    exact Nat.mod_eq_of_lt hn
  rw [assembler_raw, raw_decode _ hn he', hi]

/-- One ordinary cycle takes the actual instruction image to its signed
jump target without modifying the register file or memory. -/
theorem assembler_steps {image : Image} (s : MachineState) (imm : Int)
    (he : imm%2 = 0) (hlo : -1048576 ≤ imm) (hhi : imm < 1048576)
    (hc : CodeAt image s.pc [Reference.ChainCode.jal 0 imm]) :
    Steps image s 1 1 {s with pc := s.pc + BitVec.ofInt 64 imm} := by
  apply AddressAdapter.jump_step s s.pc _ (BitVec.ofInt 21 imm) rfl
  · rw [signed_displacement imm hlo hhi]
  · rw [hc.fetch s rfl, assembler_decode imm he]

end SigGolfCandidate.Base4Candidate.JumpProof

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

def entryPrefix (group row : Nat) : List (BitVec 32) :=
  (Reference.ChainCode.code (4*group) (Reference.ChainCode.digitOf row 0)).take
    (Reference.ChainCode.firstLength (Reference.ChainCode.digitOf row 0))

def entryJumpPc (group row : Nat) : Nat :=
  Reference.ChainCode.tablePc group row + 4*(entryPrefix group row).length

def entryTarget (group row : Nat) : Nat :=
  Reference.ChainCode.bodyPc group (if group = 15 then row/4%4 else row/4) +
    4*(if (Reference.ChainCode.digitOf row 0).val = 0 then 0
       else if (Reference.ChainCode.digitOf row 0).val = 1 then 2 else 5)

theorem entry_prefix_bound (group row : Nat) : (entryPrefix group row).length ≤ 7 := by
  have hm : Reference.ChainCode.firstLength (Reference.ChainCode.digitOf row 0) ≤ 7 := by
    generalize Reference.ChainCode.digitOf row 0 = d
    fin_cases d <;> decide
  simp only [entryPrefix, List.length_take]
  omega

/-- Both coordinates are aligned and fit the signed JAL range. The bound is
obtained from the actual concatenated body image, not from a guessed maximum. -/
theorem entry_coordinates (group row : Nat) (hg : group < 16) (hr : row < 256) :
    entryJumpPc group row < 1048576 ∧ entryTarget group row < 1048576 ∧
    entryJumpPc group row % 4 = 0 ∧ entryTarget group row % 4 = 0 := by
  have hq : (if group = 15 then row/4%4 else row/4) <
      if group = 15 then 4 else 64 := by split_ifs <;> omega
  obtain ⟨pre, post, he, hp⟩ := body_decomposition group _ hg hq
  have hl : pre.length ≤ 26693 := by
    have h := congrArg List.length he
    rw [Reference.VerifyImage.bodies_length] at h
    simp only [List.length_append] at h
    omega
  have hfirst := entry_prefix_bound group row
  have hb : Reference.ChainCode.bodyPc group
      (if group = 15 then row/4%4 else row/4) ≤ 172308 := by
    unfold Reference.ChainCode.bodyPc
    omega
  have ha : Reference.ChainCode.bodyPc group
      (if group = 15 then row/4%4 else row/4) % 4 = 0 := by
    unfold Reference.ChainCode.bodyPc
    omega
  have hoff : (if (Reference.ChainCode.digitOf row 0).val = 0 then 0
      else if (Reference.ChainCode.digitOf row 0).val = 1 then 2 else 5) ≤ 5 := by
    split_ifs <;> omega
  unfold entryJumpPc entryTarget Reference.ChainCode.tablePc
  omega

/-- The precise jump word after the entry's first-chain placementPrefix is present in
the official immutable instruction image. -/
theorem entry_jump_at (group row : Nat) (hg : group < 16) (hr : row < 256) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + entryJumpPc group row))
      [Reference.ChainCode.jal 0 ((entryTarget group row : Int) - entryJumpPc group row)] := by
  have hc := entry_at group row hg hr
  change CodeAt Reference.VerifyImage.image _
    (entryPrefix group row ++
      [Reference.ChainCode.jal 0 ((entryTarget group row : Int) - entryJumpPc group row)] ++
      List.replicate (7-(entryPrefix group row).length) Reference.ChainCode.nop) at hc
  apply subfragment hc
  have h := entry_coordinates group row hg hr
  have ht : Reference.ChainCode.tablePc group row < 1048576 := by
    unfold Reference.ChainCode.tablePc
    omega
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 4096 + entryJumpPc group row < 2^64 by omega),
    Nat.mod_eq_of_lt (show 4096 + Reference.ChainCode.tablePc group row < 2^64 by omega)]
  unfold entryJumpPc
  omega

/-- Every table-to-body transfer is a proved single-cycle step at its real
address. This theorem applies to all 4096 dispatch entries. -/
theorem entry_jump_steps (group row : Nat) (hg : group < 16) (hr : row < 256)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + entryJumpPc group row)) :
    Steps Reference.VerifyImage.image s 1 1
      {s with pc := BitVec.ofNat 64 (4096 + entryTarget group row)} := by
  have h := entry_coordinates group row hg hr
  have hc := entry_jump_at group row hg hr
  rw [← hpc] at hc
  have hs := JumpProof.assembler_steps s
    ((entryTarget group row : Int) - entryJumpPc group row)
    (by omega) (by omega) (by omega) hc
  have ht : s.pc + BitVec.ofInt 64
      ((entryTarget group row : Int) - entryJumpPc group row) =
      BitVec.ofNat 64 (4096 + entryTarget group row) := by
    rw [hpc, ← BitVec.ofInt_natCast 64 (4096 + entryJumpPc group row), ← BitVec.ofInt_add]
    have he : ((4096 + entryJumpPc group row : Nat) : Int) +
        ((entryTarget group row : Int) - entryJumpPc group row) =
        ((4096 + entryTarget group row : Nat) : Int) := by omega
    rw [he, BitVec.ofInt_natCast]
  simpa only [ht] using hs

end SigGolfCandidate.Base4Candidate.ImagePlacement

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

theorem addPc_ofNat (p n : Nat) :
    AddressAdapter.addPc (BitVec.ofNat 64 p) n = BitVec.ofNat 64 (p+4*n) := by
  induction n generalizing p with
  | zero => simp [AddressAdapter.addPc]
  | succ n ih =>
    change AddressAdapter.addPc (BitVec.ofNat 64 p + BitVec.ofNat 64 4) n = _
    rw [← BitVec.ofNat_add, ih]
    congr 1
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem head_pc (chain : Fin 62) (digit : Fin 4) (pc : Word) (s : MachineState) :
    ((headResult chain digit pc).toState s).pc =
      AddressAdapter.addPc pc (if digit.val = 0 ∨ digit.val = 3 then 4 else 5) := by
  fin_cases chain <;> fin_cases digit <;> rfl

/-- The complete no-HASH first-chain case includes its table-to-body jump.
It takes five cycles, produces the copied endpoint, and leaves the machine at
the shared remainder rather than merely at the end of an isolated template. -/
theorem entry_copy_and_jump (lay : Fin 4) (group : Fin 16) (row : Nat)
    (hr : row < 256) (hd : (Reference.ChainCode.digitOf row 0).val = 3)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (7360 + 3968*lay.val)) :
    let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
    let t := (headResult chain 3 s.pc).toState s
    Steps Reference.VerifyImage.image s 5 5
      {t with pc := BitVec.ofNat 64 (4096 + ImagePlacement.entryTarget group.val row)} := by
  dsimp only
  let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
  let t := (headResult chain 3 s.pc).toState s
  have hd' : Reference.ChainCode.digitOf row 0 = (3 : Fin 4) := Fin.ext hd
  have hl : (ImagePlacement.entryPrefix group.val row).length = 4 := by
    simp only [ImagePlacement.entryPrefix, hd', List.length_take,
      Reference.ChainCode.code_length] <;> rfl
  have ht : t.pc = BitVec.ofNat 64 (4096 + ImagePlacement.entryJumpPc group.val row) := by
    change ((headResult chain 3 s.pc).toState s).pc = _
    rw [head_pc, hpc]
    change AddressAdapter.addPc (BitVec.ofNat 64
      (4096 + Reference.ChainCode.tablePc group.val row)) 4 = _
    rw [addPc_ofNat]
    unfold ImagePlacement.entryJumpPc
    rw [hl]
    congr 1
    omega
  exact (entry_copy_steps lay group row hr hd s hpc h22).trans
    (ImagePlacement.entry_jump_steps group.val row group.isLt hr t ht)

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

/-- A shared rung runs to the actual HASH instruction, with its memory
obligations discharged from the layer/chain bounds. -/
theorem rung_steps (image : Image) (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (pc : Word) (s : MachineState)
    (hc : CodeAt image pc (Reference.ChainCode.rung chain.val 0 (step.val+1)))
    (hpc : s.pc = pc)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) :
    Steps image s (step.val+1) (step.val+1) ((rungResult chain step pc).toState s) ∧
    fetch image ((rungResult chain step pc).toState s) = some (.base .ECALL) := by
  have ho := rung_obligations lay chain step pc s h10
  have hs := symRun_sound (rung_run chain step pc) hc s hpc ho
  have he := symRun_ecall (rung_run chain step pc) hc s ho (rung_shape chain step pc).1
  exact ⟨by simpa only [(rung_shape chain step pc).2.1,
    (rung_shape chain step pc).2.2] using hs, he⟩

/-- Updating a previously initialized header erases the old step byte. -/
theorem replace_step_header (lay chain previous next : Nat) (hl : lay < 4)
    (hi : chain < 62) (hp : previous < 4) (hn : next < 4) :
    replaceByte (BitVec.ofNat 64 (AddressFormat.newHeader lay 0 chain previous)) 4
      (BitVec.ofNat 8 next) = BitVec.ofNat 64 (AddressFormat.newHeader lay 0 chain next) := by
  apply BitVec.eq_of_toNat_eq
  rw [SigGolfCandidate.Verify.replaceByte_toNat _ 4 (by decide)]
  simp only [BitVec.toNat_ofNat]
  unfold AddressFormat.newHeader
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.add_zero]
  omega

/-- The step-byte write is the only memory change before the next HASH. -/
theorem rung_frame (chain : Fin 62) (step : Fin 2) (pc : Word) (s : MachineState)
    (address : Word) (hne : address ≠ s.getReg .x10) :
    ((rungResult chain step pc).toState s).getMem address = s.getMem address := by
  rw [Result.toState_getMem, rung_memory]
  simp only [memEval, Addr.eval, E.eval, BitVec.add_zero, if_neg hne]

/-- Rungs preserve every other word of the HASH input, including arbitrary
attacker padding and the current chain value. -/
theorem rung_data_word (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (pc : Word) (s : MachineState) (k : Nat) (hk : 1 ≤ k) (hk' : k < 8)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) :
    ((rungResult chain step pc).toState s).getMem
      (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8*k)) =
      s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8*k)) := by
  apply rung_frame
  rw [h10]
  intro he
  have h := congrArg BitVec.toNat he
  have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
  simp only [BitVec.toNat_ofNat] at h
  omega

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

theorem rung_header_word (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (previous : Fin 4) (pc : Word) (s : MachineState)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val)) :
    ((rungResult chain step pc).toState s).getMem
      (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val (step.val+1)) := by
  rw [Result.toState_getMem, rung_memory]
  simp only [memEval, Addr.eval, E.eval, h10, BitVec.add_zero, if_pos rfl,
    BinOp.eval, StoreKind.merge, hheader]
  fin_cases step
  · simpa only [if_pos rfl, h6] using
      replace_step_header lay.val chain.val previous.val 1 lay.isLt chain.isLt previous.isLt (by decide)
  · simpa only [if_neg (by decide : ¬(1 : Nat) = 0), h7] using
      replace_step_header lay.val chain.val previous.val 2 lay.isLt chain.isLt previous.isLt (by decide)

theorem rung_input_read (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (previous : Fin 4) (pc : Word) (s : MachineState)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val)) :
    ((rungResult chain step pc).toState s).readWords
      (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) 8 =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val (step.val+1)) ::
        s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 7 := by
  rw [readWords_ofNat_succ, rung_header_word lay chain step previous pc s h10 h6 h7 hheader]
  congr 1
  apply readWords_congr
  intro i hi
  rw [show VerifyProof.blockAddress lay.val chain.val+8+8*i =
    VerifyProof.blockAddress lay.val chain.val+8*(i+1) by omega]
  exact rung_data_word lay chain step pc s (i+1) (by omega) (by omega) h10

/-- The shared rung's HASH input matches the byte specification for arbitrary
padding and current chain values, after replacing the previous step byte. -/
theorem rung_hash_query (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (previous : Fin 4) (tree leaf : Nat) (htree : tree < 2^32)
    (pad value : List Byte) (hp : pad.length = 32) (hv : value.length = 16)
    (pc : Word) (s : MachineState)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) (h11 : s.getReg .x11 = 64)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val))
    (hdata : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 7 =
      BitVec.ofNat 64 (tree%2^32 + 2^32*(leaf%2^32)) :: (wordsOf pad ++ wordsOf value)) :
    hashInput ((rungResult chain step pc).toState s) =
      AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64
        (Reference.chainInputP lay.val tree leaf chain.val (step.val+1+1) pad value)) := by
  have hr := rung_registers chain step pc s
  apply VerifyProof.chain_hashInput_reference _ lay.val tree leaf chain.val (step.val+1)
    pad value lay.isLt (by rw [Nat.div_eq_of_lt htree]; decide) chain.isLt
    (by have := step.isLt; omega) hp hv (hr.1.trans h10) (hr.2.2.1.trans h11)
  rw [rung_input_read lay chain step previous pc s h10 h6 h7 hheader,
    hdata, Nat.div_eq_of_lt htree]

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

/-- Both shared-rung destinations satisfy the complete 32-byte HASH write
check. The final rung redirects to the disjoint endpoint buffer. -/
theorem rung_hash_arguments (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (pc : Word) (s : MachineState)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h11 : s.getReg .x11 = 64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48)) :
    hashArgumentsValid ((rungResult chain step pc).toState s) = true := by
  have hr := rung_registers chain step pc s
  have hb := VerifyProof.block_interval lay.val chain.val lay.isLt chain.isLt
  have hal := VerifyProof.block_aligned lay.val chain.val
  have hout : ((rungResult chain step pc).toState s).getReg .x12 =
      BitVec.ofNat 64 (if step.val = 1 then Reference.ChainCode.leafSlot chain.val
        else VerifyProof.blockAddress lay.val chain.val+48) := by
    rw [hr.2.1]
    split_ifs <;> first | rfl | exact h12
  apply hashArgs_of (hr.1.trans h10) (hr.2.2.1.trans h11) hout
  · omega
  · decide
  · omega
  · split_ifs
    · unfold Reference.ChainCode.leafSlot
      omega
    · omega
  · split_ifs
    · unfold Reference.ChainCode.leafSlot
      have := chain.isLt
      norm_num only [MEMORY_BYTES]
      omega
    · omega
  · decide

/-- A concrete shared rung and its HASH refine one reference chain query.
The cycle increment is exactly nine or ten, including the entire HASH charge. -/
theorem rung_hash_good (lay : Fin 4) (chain : Fin 62) (step : Fin 2)
    (previous : Fin 4) (tree leaf : Nat) (htree : tree < 2^32)
    (pad value : List Byte) (hp : pad.length = 32) (hv : value.length = 16)
    (pc : Word) (s : MachineState)
    (hc : CodeAt Reference.VerifyImage.image pc
      (Reference.ChainCode.rung chain.val 0 (step.val+1))) (hpc : s.pc = pc)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h11 : s.getReg .x11 = 64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48))
    (h5 : s.getReg .x5 = 0) (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val))
    (hdata : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 7 =
      BitVec.ofNat 64 (tree%2^32 + 2^32*(leaf%2^32)) :: (wordsOf pad ++ wordsOf value))
    (N C : Nat) (K : SigGolfCandidate.Ref.Val → OracleComp HashSpec VerifyProof.Obs)
    (hafter : ∀ answer, VerifyProof.Good
      (writeHash ((rungResult chain step pc).toState s) answer) N C
      (K (SigGolfCandidate.Ref.answerBytes 16 answer))) :
    VerifyProof.Good s (N+1+(step.val+1)) (C+8+(step.val+1))
      (VerifyProof.cc (Reference.h16
        (Reference.chainInputP lay.val tree leaf chain.val (step.val+1+1) pad value)) K) := by
  have hs := rung_steps Reference.VerifyImage.image lay chain step pc s hc hpc h10
  have hr := rung_registers chain step pc s
  have hargs := rung_hash_arguments lay chain step pc s h10 h11 h12
  have hquery := rung_hash_query lay chain step previous tree leaf htree pad value hp hv
    pc s h10 h6 h7 h11 hheader hdata
  have hgood := VerifyProof.Good.hash hs.2 (hr.2.2.2.1.trans h5) hargs hquery hafter
  have hblocks : (VerifyProof.queryFormat
      (Reference.chainInputP lay.val tree leaf chain.val (step.val+1+1) pad value)).blocks = 1 := by
    unfold VerifyProof.queryFormat
    rw [AddressFormat.queryPerm_blocks, VerifyProof.chain_pad64_words _ _ _ _ _ _ _
      lay.isLt (by rw [Nat.div_eq_of_lt htree]; decide) chain.isLt
      (by have := step.isLt; omega) hp hv]
    rfl
  simpa only [hblocks, Nat.mul_one] using hgood.steps hs.1

/-- Postcondition connecting the first shared rung to the final rung. The
step-one header, tree/leaf word and arbitrary padding survive the actual
oracle write, while its low answer half becomes the next chain value. -/
theorem first_rung_hash_postcondition (lay : Fin 4) (chain : Fin 62)
    (previous : Fin 4) (pc : Word) (s : MachineState) (answer : BitVec 256)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48))
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val)) :
    let t := writeHash ((rungResult chain 0 pc).toState s) answer
    t.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val 1) ∧
    t.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 7 =
      s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 5 ++
        wordsOf (answerBytes 16 answer) := by
  dsimp only
  have hd : ((rungResult chain 0 pc).toState s).getReg .x12 =
      BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48) :=
    (rung_registers chain 0 pc s).2.1.trans h12
  constructor
  · have hf := VerifyProof.hash_inplace_header_pad ((rungResult chain 0 pc).toState s)
      lay.val chain.val lay.isLt chain.isLt hd answer 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at hf
    rw [hf]
    exact rung_header_word lay chain 0 previous pc s h10 h6 h7 hheader
  · rw [VerifyProof.hash_inplace_next_input ((rungResult chain 0 pc).toState s)
      lay.val chain.val lay.isLt chain.isLt hd answer]
    congr 1
    apply readWords_congr
    intro word hw
    rw [show VerifyProof.blockAddress lay.val chain.val+8+8*word =
      VerifyProof.blockAddress lay.val chain.val+8*(word+1) by omega]
    exact rung_data_word lay chain 0 pc s (word+1) (by omega) (by omega) h10

/-- Compose both shared HASH rungs against the byte-level oracle computation.
The final continuation is quantified over both full answers, so its state
includes the real spill writes as well as the resulting endpoint. -/
theorem two_rungs_good (lay : Fin 4) (chain : Fin 62) (previous : Fin 4)
    (tree leaf : Nat) (htree : tree < 2^32)
    (pad value : List Byte) (hp : pad.length = 32) (hv : value.length = 16)
    (pc : Word) (s : MachineState)
    (hc0 : CodeAt Reference.VerifyImage.image pc
      (Reference.ChainCode.rung chain.val 0 1))
    (hc1 : CodeAt Reference.VerifyImage.image (AddressAdapter.addPc pc 2)
      (Reference.ChainCode.rung chain.val 0 2))
    (hpc : s.pc = pc)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val))
    (h11 : s.getReg .x11 = 64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+48))
    (h5 : s.getReg .x5 = 0) (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2)
    (hheader : s.getMem (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val)) =
      BitVec.ofNat 64 (AddressFormat.newHeader lay.val 0 chain.val previous.val))
    (hprefix : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 5 =
      BitVec.ofNat 64 (tree%2^32 + 2^32*(leaf%2^32)) :: wordsOf pad)
    (hdata : s.readWords (BitVec.ofNat 64 (VerifyProof.blockAddress lay.val chain.val+8)) 7 =
      BitVec.ofNat 64 (tree%2^32 + 2^32*(leaf%2^32)) :: (wordsOf pad ++ wordsOf value))
    (N C : Nat) (K : SigGolfCandidate.Ref.Val → OracleComp HashSpec VerifyProof.Obs)
    (hafter : ∀ first second, VerifyProof.Good
      (writeHash ((rungResult chain 1 (AddressAdapter.addPc pc 2)).toState
        (writeHash ((rungResult chain 0 pc).toState s) first)) second) N C
      (K (answerBytes 16 second))) :
    VerifyProof.Good s (N+5) (C+19)
      (VerifyProof.cc (do
        let middle ← Reference.h16 (Reference.chainInputP lay.val tree leaf chain.val 2 pad value)
        Reference.h16 (Reference.chainInputP lay.val tree leaf chain.val 3 pad middle)) K) := by
  rw [VerifyProof.cc_bind]
  apply rung_hash_good lay chain 0 previous tree leaf htree pad value hp hv pc s
    hc0 hpc h10 h11 h12 h5 h6 h7 hheader hdata (N+3) (C+10)
  intro first
  have hr := rung_registers chain 0 pc s
  have hconst := rung_constants chain 0 pc s
  have hpost := first_rung_hash_postcondition lay chain previous pc s first
    h10 h12 h6 h7 hheader
  apply rung_hash_good lay chain 1 1 tree leaf htree pad (answerBytes 16 first)
    hp (length_answerBytes 16 first) (AddressAdapter.addPc pc 2)
    (writeHash ((rungResult chain 0 pc).toState s) first) hc1
  · rw [writeHash_pc, rung_pc]
    rfl
  · rw [writeHash_getReg]
    exact hr.1.trans h10
  · rw [writeHash_getReg]
    exact hr.2.2.1.trans h11
  · rw [writeHash_getReg]
    exact hr.2.1.trans h12
  · rw [writeHash_getReg]
    exact hr.2.2.2.1.trans h5
  · rw [writeHash_getReg]
    exact hconst.1.trans h6
  · rw [writeHash_getReg]
    exact hconst.2.1.trans h7
  · exact hpost.1
  · rw [hpost.2, hprefix]
    rfl
  · exact hafter first

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ChainHeadProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Sign

/-- A first HASH advances to the entry's jump word for every hashing digit,
including the shorter zero-step head and the one-HASH endpoint case. -/
theorem entry_after_hash_pc (group : Fin 16) (row : Nat)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3)
    (s : MachineState) (answer : BitVec 256)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row)) :
    let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
    (writeHash ((headResult chain (Reference.ChainCode.digitOf row 0) s.pc).toState s) answer).pc =
      BitVec.ofNat 64 (4096 + ImagePlacement.entryJumpPc group.val row) := by
  have hl : (ImagePlacement.entryPrefix group.val row).length =
      (if (Reference.ChainCode.digitOf row 0).val = 0 ∨
          (Reference.ChainCode.digitOf row 0).val = 3 then 4 else 5)+1 := by
    simp only [ImagePlacement.entryPrefix, List.length_take, Reference.ChainCode.code_length]
    generalize he : Reference.ChainCode.digitOf row 0 = d at *
    fin_cases d <;> first | omega | rfl
  dsimp only
  rw [writeHash_pc, head_pc, hpc, addPc_ofNat]
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]
  unfold ImagePlacement.entryJumpPc
  rw [hl]
  congr 1
  omega

/-- Every answer to the first chain HASH is followed by the certified direct
jump. The oracle answer cannot change the selected instruction address. -/
theorem entry_after_hash_jump (group : Fin 16) (row : Nat) (hr : row < 256)
    (hd : (Reference.ChainCode.digitOf row 0).val < 3)
    (s : MachineState) (answer : BitVec 256)
    (hpc : s.pc = BitVec.ofNat 64 (4096 + Reference.ChainCode.tablePc group.val row)) :
    let chain : Fin 62 := ⟨4*group.val, by have := group.isLt; omega⟩
    let t := writeHash ((headResult chain (Reference.ChainCode.digitOf row 0) s.pc).toState s) answer
    Steps Reference.VerifyImage.image t 1 1
      {t with pc := BitVec.ofNat 64 (4096 + ImagePlacement.entryTarget group.val row)} := by
  dsimp only
  apply ImagePlacement.entry_jump_steps group.val row group.isLt hr
  exact entry_after_hash_pc group row hd s answer hpc

end SigGolfCandidate.Base4Candidate.ChainHeadProof

namespace SigGolfCandidate.Base4Candidate.ImagePlacement
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

/-- Selecting an inner fragment by adding its byte offset is safe whenever
the containing CodeAt proof holds; no separate global address estimate is needed. -/
theorem subfragment_add {image : Image} {pc : Word} {pre fragment post : List (BitVec 32)}
    (h : CodeAt image pc (pre ++ fragment ++ post)) :
    CodeAt image (pc + BitVec.ofNat 64 (4*pre.length)) fragment := by
  have hb := h.2.2.1
  simp only [List.length_append] at hb
  apply subfragment h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 4*pre.length < 2^64 by omega),
    Nat.mod_eq_of_lt (show pc.toNat + 4*pre.length < 2^64 by omega)]

/-- The first remaining chain is physically present immediately after the
shared first-chain rungs, including the shortened final group. -/
theorem remainder_first_at (group q : Nat) (hg : group < 16)
    (hq : q < if group = 15 then 4 else 64) :
    CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q) + 20)
      (Reference.ChainCode.code (4*group+1) (Reference.ChainCode.digitOf q 0)) := by
  have hc := body_at group q hg hq
  let pre := [Reference.ChainCode.sb 6 10 4, Reference.ChainCode.hashInstruction,
    Reference.ChainCode.sb 7 10 4, Reference.ChainCode.addi 12 0 (Reference.ChainCode.leafSlot (4*group)),
    Reference.ChainCode.hashInstruction]
  let post := (if group = 15 then [] else
      Reference.ChainCode.code (4*group+2) (Reference.ChainCode.digitOf q 1) ++
      Reference.ChainCode.code (4*group+3) (Reference.ChainCode.digitOf q 2)) ++
    [if group = 15 then Reference.ChainCode.opI 103 0 0 1 0 else
      Reference.ChainCode.jal 0 ((Reference.ChainCode.dispatchPc (group+1) : Int) -
        (Reference.ChainCode.bodyPc group q + 4*(5+(Reference.ChainCode.remainder group q).length) : Nat))]
  have hc' : CodeAt Reference.VerifyImage.image
      (BitVec.ofNat 64 (4096 + Reference.ChainCode.bodyPc group q))
      (pre ++ Reference.ChainCode.code (4*group+1) (Reference.ChainCode.digitOf q 0) ++ post) := by
    simpa only [Reference.ChainCode.body, Reference.ChainCode.remainder, pre, post,
      List.append_assoc] using hc
  exact subfragment_add hc'

end SigGolfCandidate.Base4Candidate.ImagePlacement
