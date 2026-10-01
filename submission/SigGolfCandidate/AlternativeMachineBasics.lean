import SigGolfCandidate.AlternativeReference
import SigGolfCandidate.Transfer.Statements
import SigGolfCandidate.AlternativeIdeal

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal

/-! Simulation rules for the alternate verifier image. These rules expose every
remaining byte, HASH-argument, framing, and cycle obligation to subsequent proofs. -/
namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

abbrev image := Reference.VerifyImage.image

def queryFormat (x : List Byte) := AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64 x)

abbrev Obs := Bool × Nat

def obs (e : Execution) : Obs := (decide (e.exit = .success), e.hashCalls)

def Good (s : MachineState) (N C : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C

@[simp] theorem obs_charge (e : Execution) (c b : Nat) :
    obs (e.charge c 0 b) = obs e := by
  cases e; simp [obs, Execution.charge]

theorem obs_charge1 (e : Execution) (c b : Nat) :
    obs (e.charge c 1 b) = ((obs e).1, 1 + (obs e).2) := by
  cases e; rfl

theorem Good.mono {s : MachineState} {N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (h : Good s N C X) (hN : N ≤ N') (hC : C ≤ C') : Good s N' C' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  exact ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩⟩

theorem Good.congr {s : MachineState} {N C : Nat} {X Y : OracleComp HashSpec Obs}
    (h : Good s N C X) (hXY : X = Y) : Good s N C Y := hXY ▸ h

theorem Good.steps {s t : MachineState} {k c N C : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) : Good s (N + k) (C + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩

theorem Good.steps' {s t : MachineState} {k c N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) (hN : N + k ≤ N') (hC : C + c ≤ C') :
    Good s N' C' X := (h.steps hst).mono hN hC

/-! ## The counting continuation -/

def cc {α : Type} (oa : OracleComp HashSpec α) (K : α → OracleComp HashSpec Obs) :
    OracleComp HashSpec Obs :=
  countCalls oa >>= fun p => (fun q => (q.1, p.2 + q.2)) <$> K p.1

@[simp] theorem cc_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    cc (pure a) K = K a := by
  simp only [cc, countCalls_pure, pure_bind, Nat.zero_add]
  exact id_map' _

theorem cc_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (K : β → OracleComp HashSpec Obs) : cc (oa >>= f) K = cc oa (fun a => cc (f a) K) := by
  simp only [cc, countCalls_bind, bind_assoc, map_bind, Functor.map_map, bind_map_left]
  congr 1; funext p; congr 1; funext r
  simp only [Nat.add_assoc]

theorem cc_hash16 (x : List Byte) (K : Val → OracleComp HashSpec Obs) :
    cc (Reference.h16 x) K = (do
      let a ← (HashSpec.query (queryFormat x) : OracleComp HashSpec _)
      (fun q => (q.1, 1 + q.2)) <$> K (answerBytes 16 a)) := by
  simp only [Reference.h16, cc_bind]
  simp only [cc, Reference.hash, countCalls_query, bind_map_left, countCalls_pure, pure_bind,
    Functor.map_map, Nat.zero_add]
  rfl

/-! ## HASH and HALT -/

theorem Good.hash {s : MachineState} {N C : Nat} {x : List Byte}
    {K : Val → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, Good (writeHash s a) N C (K (answerBytes 16 a))) :
    Good s (N + 1) (C + 8 * (queryFormat x).blocks) (cc (Reference.h16 x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_hash16, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩

theorem cc_H (x : List Byte) (K : BitVec 256 → OracleComp HashSpec Obs) :
    cc (Reference.hash x) K = (do
      let a ← (HashSpec.query (queryFormat x) : OracleComp HashSpec _)
      (fun q => (q.1, 1 + q.2)) <$> K a) := by
  simp only [cc, Reference.hash, countCalls_query, bind_map_left]
  rfl

theorem Good.hashH {s : MachineState} {N C : Nat} {x : List Byte}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, Good (writeHash s a) N C (K a)) :
    Good s (N + 1) (C + 8 * (queryFormat x).blocks) (cc (Reference.hash x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_H, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩

theorem Good.halt {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (ht0 : s.getReg .x5 = 1) : Good s 1 1 (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf ht0, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf ht0]
    refine ⟨?_, le_refl _⟩
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]; decide
    · simp only [hx, if_false]; decide

end SigGolfCandidate.Base4Candidate.VerifyProof
namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def GoodQ (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F image s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ A)

theorem Good.toQ {s : MachineState} {N C : Nat} {X : OracleComp HashSpec Obs} (h : Good s N C X) :
    GoodQ s N C True C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2, fun _ => ⟨trivial, (h2 hash).2⟩⟩⟩

theorem GoodQ.toGood {s : MachineState} {N C : Nat} {Q : Prop} {A : Nat} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) : Good s N C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1⟩⟩

theorem GoodQ.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQ s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩

theorem GoodQ.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hXY : X = Y) : GoodQ s N C Q A Y := hXY ▸ h

theorem GoodQ.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : GoodQ t N C Q A X) : GoodQ s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps image s k c t) (h : GoodQ t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQ s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ

theorem GoodQ.hash {s : MachineState} {N C A : Nat} {Q : Prop} {x : List Byte}
    {K : Val → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K (answerBytes 16 a))) :
    GoodQ s (N + 1) (C + 8 * (queryFormat x).blocks) Q (A + 8 * (queryFormat x).blocks) (cc (Reference.h16 x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_hash16, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.hashH {s : MachineState} {N C A : Nat} {Q : Prop} {x : List Byte}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K a)) :
    GoodQ s (N + 1) (C + 8 * (queryFormat x).blocks) Q (A + 8 * (queryFormat x).blocks) (cc (Reference.hash x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_H, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩

/-- HALT(1): a rejecting run (any acceptance condition). -/
theorem GoodQ.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQ s 1 1 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf h5, map_pure]
    simp only [obs, h10]
    rfl
  · rw [hF', evalWith_halt hash (F - 1) hf h5]
    simp only [h10]
    refine ⟨by decide, le_refl _, fun h => ?_⟩
    exact absurd h (by decide)

end SigGolfCandidate.Base4Candidate.VerifyProof


namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref

def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)

theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega


def blockAddress (lay chain : Nat) : Nat := 5376+3968*lay+64*chain

def FreshWord (lay chain otherLay otherChain word : Nat) : Prop :=
  otherLay < 4 ∧ otherChain < 62 ∧ 2 ≤ word ∧ word < 8 ∧
    (otherLay < lay ∨ (otherLay = lay ∧ chain ≤ otherChain))

def Fresh (witness : List Byte) (lay chain : Nat) (state : MachineState) : Prop :=
  ∀ a b k, FreshWord lay chain a b k →
    state.getMem (BitVec.ofNat 64 (blockAddress a b+8*k)) =
      BitVec.ofNat 64 (leNat (slice witness (Reference.witnessChainOffset a b+8*k) 8))

theorem fresh_next {lay chain a b k : Nat} (h : FreshWord lay (chain+1) a b k) :
    FreshWord lay chain a b k := by
  unfold FreshWord at *
  omega

theorem fresh_layer {lay a b k : Nat} (hl : 1 ≤ lay)
    (h : FreshWord (lay-1) 0 a b k) : FreshWord lay 62 a b k := by
  unfold FreshWord at *
  omega

/-- A full HASH output may spill into the next header, but never into a future
chain's padding or value. Counters live in a separate witness region. -/
theorem fresh_ne_written {lay chain a b k : Nat} (hw : FreshWord lay (chain+1) a b k)
    (hi : chain < 62) (d : Nat)
    (hd : d = 0 ∨ d = 8 ∨ d = 48 ∨ d = 56 ∨ d = 64 ∨ d = 72) :
    blockAddress a b+8*k ≠ blockAddress lay chain+d := by
  unfold FreshWord at hw
  unfold blockAddress
  rcases hw with ⟨ha,hb,hk,hk',horder⟩
  rcases horder with horder | ⟨rfl,horder⟩ <;> omega

theorem fresh_own {lay chain k : Nat} (hl : lay < 4) (hi : chain < 62)
    (hk : 2 ≤ k) (hk' : k < 8) : FreshWord lay chain lay chain k :=
  ⟨hl,hi,hk,hk',Or.inr ⟨rfl,le_rfl⟩⟩

theorem block_aligned (lay chain : Nat) : blockAddress lay chain % 64 = 0 := by
  unfold blockAddress
  omega

theorem block_interval (lay chain : Nat) (hl : lay < 4) (hi : chain < 62) :
    5376 ≤ blockAddress lay chain ∧ blockAddress lay chain+96 ≤ 21280 := by
  unfold blockAddress
  omega

theorem block_access (lay chain k width : Nat) (hl : lay < 4) (hi : chain < 62)
    (hk : k < 128) (hw : width = 1 ∨ width = 8)
    (ha : (blockAddress lay chain+k) % width = 0) :
    accessValid (BitVec.ofNat 64 (blockAddress lay chain+k)) width = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold blockAddress; omega)]
  refine ⟨?_,ha⟩
  simp only [MEMORY_BYTES]
  unfold blockAddress
  omega

/-- HASH addresses used by a chain and its final leaf slot satisfy the pinned
alignment and memory-end checks, including the full 32-byte output. -/
theorem chain_hash_arguments (lay chain : Nat) (hl : lay < 4) (hi : chain < 62) :
    hashArgsB (blockAddress lay chain) 64 (blockAddress lay chain+48) = true ∧
    hashArgsB (blockAddress lay chain) 64 (Reference.ChainCode.leafSlot chain) = true := by
  simp only [hashArgsB, MEMORY_BYTES, blockAddress, Reference.ChainCode.leafSlot]
  simp [Nat.add_mod, Nat.mul_mod]
  omega

end SigGolfCandidate.Base4Candidate.VerifyProof


namespace SigGolfCandidate.Base4Candidate.SwarProof
open SigGolfCandidate.Verify (land_split)
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem split2 (n M : Nat) : n &&& (16*M+3) = 16*((n/16) &&& M)+n%4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256*M+15) = 256*((n/256) &&& M)+n%16 :=
  land_split n M 4 8 (by decide)
theorem and3 (n : Nat) : n &&& 3 = n%4 := Nat.and_two_pow_sub_one_eq_mod n 2
theorem and15 (n : Nat) : n &&& 15 = n%16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem mask2 (n : Nat) : n &&& 3689348814741910323 =
    16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 % 4) + n / 16 / 16 % 4) + n / 16 % 4) + n % 4 := by
  rw [show (3689348814741910323 : Nat) = 16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3 by norm_num]
  simp only [split2, and3]

theorem mask4 (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 % 16) + n / 256 / 256 % 16) + n / 256 % 16) + n % 16 := by
  rw [show (1085102592571150095 : Nat) = 256 * (256 * (256 * (256 * (256 * (256 * (256 * (15) + 15) + 15) + 15) + 15) + 15) + 15) + 15 by norm_num]
  simp only [split4, and15]

theorem mask4_nibbles (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 % 16) + n % 16 := by
  rw [mask4]
  simp only [Nat.div_div_eq_div_mul]

theorem hdiv16 (c R : Nat) (h : c < 16) : (c+16*R)/16 = R := by omega
theorem hmod16 (c R : Nat) (h : c < 16) : (c+16*R)%16 = c := by omega

theorem byteChecksum (P0 P1 P2 P3 P4 P5 P6 P7 : Nat) (h0 : P0 ≤ 24) (h1 : P1 ≤ 24) (h2 : P2 ≤ 24) (h3 : P3 ≤ 24) (h4 : P4 ≤ 24) (h5 : P5 ≤ 24) (h6 : P6 ≤ 24) (h7 : P7 ≤ 24) :
    ((P0) + 256 * ((P1) + 256 * ((P2) + 256 * ((P3) + 256 * ((P4) + 256 * ((P5) + 256 * ((P6) + 256 * (P7)))))))) % 255 = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 := by
  calc
    _ = (P0 + (P1 + (P2 + (P3 + (P4 + (P5 + (P6 + (P7)))))))) % 255 := by simp [Nat.add_mod,Nat.mul_mod]
    _ = _ := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

def tail (X : Nat) : Nat := (((X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095)) % 18446744073709551616) % 255

theorem lanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 : Nat) (h0 : L0 ≤ 12) (h1 : L1 ≤ 12) (h2 : L2 ≤ 12) (h3 : L3 ≤ 12) (h4 : L4 ≤ 12) (h5 : L5 ≤ 12) (h6 : L6 ≤ 12) (h7 : L7 ≤ 12) (h8 : L8 ≤ 12) (h9 : L9 ≤ 12) (h10 : L10 ≤ 12) (h11 : L11 ≤ 12) (h12 : L12 ≤ 12) (h13 : L13 ≤ 12) (h14 : L14 ≤ 12) (h15 : L15 ≤ 12)
    (X : Nat) (hX : X = (L0) + 16 * ((L1) + 16 * ((L2) + 16 * ((L3) + 16 * ((L4) + 16 * ((L5) + 16 * ((L6) + 16 * ((L7) + 16 * ((L8) + 16 * ((L9) + 16 * ((L10) + 16 * ((L11) + 16 * ((L12) + 16 * ((L13) + 16 * ((L14) + 16 * (L15)))))))))))))))) : tail X = L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 + L11 + L12 + L13 + L14 + L15 := by
  have hM : (X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095) = (L0+L1) + 256 * ((L2+L3) + 256 * ((L4+L5) + 256 * ((L6+L7) + 256 * ((L8+L9) + 256 * ((L10+L11) + 256 * ((L12+L13) + 256 * (L14+L15))))))) := by
    rw [hX, mask4_nibbles, mask4_nibbles]
    simp (disch := omega) only [hdiv16, hmod16, Nat.mod_eq_of_lt]
    omega
  have hbound : (X &&& 1085102592571150095) +
      (X/16 &&& 1085102592571150095) < 18446744073709551616 := by
    rw [hM]
    omega
  unfold tail
  rw [Nat.mod_eq_of_lt hbound, hM]
  have h := byteChecksum (L0+L1) (L2+L3) (L4+L5) (L6+L7) (L8+L9) (L10+L11) (L12+L13) (L14+L15) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

def first (a b : Nat) : Nat :=
  (((a &&& 3689348814741910323)+(a/4 &&& 3689348814741910323)) % 18446744073709551616 +
    ((b &&& 3689348814741910323)+(b/4 &&& 3689348814741910323)) % 18446744073709551616) % 18446744073709551616

/-- Bound the four masked words before expanding their individual digits.
This avoids modular elimination over all 64 digit variables. -/
theorem first_no_wrap (a b : Nat) :
    first a b = (a &&& 3689348814741910323)+(a/4 &&& 3689348814741910323)+
      ((b &&& 3689348814741910323)+(b/4 &&& 3689348814741910323)) := by
  have h0 : a &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h1 : a/4 &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h2 : b &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h3 : b/4 &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  unfold first
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

def digitSum (a : Nat) : Nat := ((List.range 32).map fun i => a/4^i%4).sum

theorem digitSum_expanded (a : Nat) : digitSum a =
    a % 4 + a / 4 % 4 + a / 16 % 4 + a / 64 % 4 + a / 256 % 4 + a / 1024 % 4 + a / 4096 % 4 + a / 16384 % 4 + a / 65536 % 4 + a / 262144 % 4 + a / 1048576 % 4 + a / 4194304 % 4 + a / 16777216 % 4 + a / 67108864 % 4 + a / 268435456 % 4 + a / 1073741824 % 4 + a / 4294967296 % 4 + a / 17179869184 % 4 + a / 68719476736 % 4 + a / 274877906944 % 4 + a / 1099511627776 % 4 + a / 4398046511104 % 4 + a / 17592186044416 % 4 + a / 70368744177664 % 4 + a / 281474976710656 % 4 + a / 1125899906842624 % 4 + a / 4503599627370496 % 4 + a / 18014398509481984 % 4 + a / 72057594037927936 % 4 + a / 288230376151711744 % 4 + a / 1152921504606846976 % 4 + a / 4611686018427387904 % 4 := by
  simp only [digitSum, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num
  omega


end SigGolfCandidate.Base4Candidate.SwarProof
