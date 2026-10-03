import SigGolfCandidate.W9Machine.WctChainTrace
import SigGolfCandidate.W9Machine.WctRelativeMem

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def TraceMem (value : ChainWord → Word) (B : Nat) (tr : ChainTrace) (s : MachineState) : Prop :=
  ∀ off, off < 1024 → s.getMem (BitVec.ofNat 64 (B + off)) = value (tr.read off)
theorem ChainTrace.read_put (tr : ChainTrace) (off x : Nat) (v : ChainWord) :
    (tr.put off v).read x = if x = off then v else tr.read x := by
  by_cases h : x = off
  · subst x; simp [ChainTrace.read, ChainTrace.put]
  · simp [ChainTrace.read, ChainTrace.put, h, show off ≠ x from Ne.symm h]
theorem head_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B off dst p chain digit : Nat) (ht : TraceMem value B tr s)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 1024 < 2 ^ 64)
    (hoff : off + 64 ≤ 1024)
    (hh : (hLoad chain digit).eval s = value (.header chain digit))
    (hr : s.getReg .x4 = value .route) :
    TraceMem value B ((tr.put (off + 16) (.header chain digit)).put (off + 24) .route)
      ((headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s) := by
  intro x hx
  rw [headRHRel_mem s .x8 B off dst p chain digit (B + x) hbase (by omega) (by omega)]
  simp only [ChainTrace.read_put]
  split_ifs <;> first | exact hr | exact hh | exact ht x hx | omega
end W9Machine
