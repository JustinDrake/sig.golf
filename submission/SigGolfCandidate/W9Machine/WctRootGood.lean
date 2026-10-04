import SigGolfCandidate.W9Machine.WctRootRuns
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.CodexCheck.Fetch

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M shortHash pad64 Digest)
open ClaudeWCT.W9.Machine.Merkle
def rootPrepared (k : Fin 9) (t : MachineState) : MachineState :=
  (coordRoot (rootPc k) k.val).toState t
theorem root_step (k : Fin 9) (j B index : Nat) (u t : MachineState) (v pad sib : Digest)
    (hj : j < 128) (hidx : index < 2 ^ 32) (h8 : B % 8 = 0)
    (hhi : B + 1024 ≤ MEMORY_BYTES) (hpost : ChildPost j B k.val index u v t)
    (hpad : DigAt u (B + padO 6) pad) (hsib : DigAt u (B + sibO 6 j) sib)
    (hpc : t.pc = pcOf (rootPc k)) (h5 : u.getReg .x5 = 0) :
    Steps Frozen.image t 1 1 (rootPrepared k t) ∧
    fetch Frozen.image (rootPrepared k t) = some (.base .ECALL) ∧
    (rootPrepared k t).getReg .x5 = 0 ∧
    hashArgumentsValid (rootPrepared k t) = true ∧
    hashInput (rootPrepared k t) = toQ (pad64 (rootIn k.val index j v pad sib)) := by
  have hob : ∀ o ∈ (coordRoot (rootPc k) k.val).st.obl, o.holds t := by
    simp [coordRoot]
  refine ⟨symRun_sound (rOK_eq (rootCode_checked k))
    (slice_at _ _ (rootCode_linked k)) t hpc ((Oblig.all_iff t _).mpr hob), ?_⟩
  refine ⟨symRun_ecall (rOK_eq (rootCode_checked k))
    (slice_at _ _ (rootCode_linked k)) t ((Oblig.all_iff t _).mpr hob) rfl, ?_⟩
  have keep (r : Reg) (hr : r ≠ .x12) : (rootPrepared k t).getReg r = t.getReg r :=
    (coordRoot_keeps (rootPc k) k.val).reg t (by simpa using hr)
  refine ⟨(keep .x5 (by decide)).trans
    ((hpost.keep .x5 (by decide) (by decide) (by decide) (by decide)).trans h5), ?_⟩
  have ha : (rootPrepared k t).getReg .x10 = BitVec.ofNat 64 B ∧
      (rootPrepared k t).getReg .x11 = BitVec.ofNat 64 64 :=
    ⟨(keep .x10 (by decide)).trans hpost.a0, (keep .x11 (by decide)).trans hpost.a1⟩
  have hd : forestSlot k.val % 8 = 0 ∧ forestSlot k.val + 32 ≤ 2 ^ 24 := by
    have := k.isLt
    unfold forestSlot
    split_ifs <;> omega
  refine ⟨hashArgs_of (rootPrepared k t) B 64 (forestSlot k.val) ha.1 ha.2
    (coordRoot_dest _ _ _) h8 (by decide) (by unfold MEMORY_BYTES at hhi; omega)
    hd.1 hd.2, ?_⟩
  exact rootInput j B k.val index u t (rootPrepared k t) v pad sib
    hj hidx h8 hhi hpost hpad hsib (coordRoot_mem _ _ t) ha.1 ha.2
theorem root_good (k : Fin 9) (j B index : Nat) (u t : MachineState) (v pad sib : Digest)
    (hj : j < 128) (hidx : index < 2 ^ 32) (h8 : B % 8 = 0)
    (hhi : B + 1024 ≤ MEMORY_BYTES) (hpost : ChildPost j B k.val index u v t)
    (hpad : DigAt u (B + padO 6) pad) (hsib : DigAt u (B + sibO 6 j) sib)
    (hpc : t.pc = pcOf (rootPc k)) (h5 : u.getReg .x5 = 0)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs)
    (h : ∀ ans : BitVec 256, GoodQFor Frozen.image (writeHash (rootPrepared k t) ans)
      N C Q A (K (ans.extractLsb' 0 128))) :
    GoodQFor Frozen.image t (N + 2) (C + 9) Q (A + 9)
      (ccM (shortHash (rootIn k.val index j v pad sib)) K) := by
  obtain ⟨hs, hf, ht0, hv, hin⟩ := root_step k j B index u t v pad sib
    hj hidx h8 hhi hpost hpad hsib hpc h5
  have hb : (toQ (pad64 (rootIn k.val index j v pad sib))).blocks = 1 := by
    unfold rootIn
    exact blocks_blk4 _ _ _ _
  have hhash := GoodQFor.shortHash_bind (f := fun d : Digest => (pure d : M Digest))
    (K := K) hf ht0 hv hin (by simpa only [ccM_pure] using h)
  simpa only [hb, Nat.mul_one, Nat.add_assoc, bind_pure] using GoodQFor.steps hs hhash
end W9Machine
