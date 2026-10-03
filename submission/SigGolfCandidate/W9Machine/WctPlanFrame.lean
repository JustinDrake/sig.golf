import SigGolfCandidate.W9Machine.WctTraceMem
import SigGolfCandidate.W9Machine.WctChainPieces
import SigGolfCandidate.W9Machine.WctPlanGood

section


namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem leafSetup_keeps : Keeps leafSetupRel [.x25, .x10, .x11] := by
  intro r hr
  simp only [leafSetupRel]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp))]
theorem leafSetup_mem (s : MachineState) (B A : Nat)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hhi : B + 1024 < 2 ^ 64) (hA : A < 2 ^ 64) :
    (leafSetupRel.toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + 904 then s.getReg .x4 else
      if A = B + 896 then (hLoad 7 1).eval s else s.getMem (BitVec.ofNat 64 A) := by
  convert headRHRel_mem s .x8 B 880 0 0 7 1 A hbase (by omega) hA using 1
  rfl
theorem leaf_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem value B tr s) (hbase : s.getReg .x8 = BitVec.ofNat 64 B)
    (hB : B + 1024 < 2 ^ 64) (hh : (hLoad 7 1).eval s = value .leafHeader)
    (hr : s.getReg .x4 = value .route) :
    TraceMem value B (tr.step .leaf) (leafSetupRel.toState s) := by
  intro x hx
  rw [leafSetup_mem s B (B + x) hbase hB (by omega)]
  simp only [ChainTrace.step, ChainTrace.read_put]
  split_ifs <;> first | omega | exact ht x hx
theorem leafSetup_regs (s : MachineState) (B : Nat) (hbase : s.getReg .x8 = BitVec.ofNat 64 B) :
    (leafSetupRel.toState s).getReg .x10 = BitVec.ofNat 64 (B + 880) ∧
    (leafSetupRel.toState s).getReg .x11 = 128 ∧
    (leafSetupRel.toState s).pc = s.getReg .x23 &&& ~~~1#64 := by
  simp only [leafSetupRel, Result.toState_getReg, Result.toState_pc,
    RegFile.get, RegFile.set, addC_eval, E.eval, BinOp.eval, hbase]
  exact ⟨ofNat_add_ofNat B 880, trivial, trivial⟩
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
def wctChainClobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
theorem chainPiece_keeps (p : ChainPiece) : Keeps p.result wctChainClobbers := by
  intro r hr
  have hsmall : ∀ ws : List Reg, (∀ x ∈ ws, x ∈ wctChainClobbers) → r ∉ ws := by
    intro ws h hmem; exact hr (h r hmem)
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      exact headRHRel_keeps _ _ _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | rung digit dst =>
      exact rungRRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | copy off dst =>
      exact copyFHRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | jump target => rfl
    | leaf => exact leafSetup_keeps r (hsmall _ (by simp [wctChainClobbers]))
theorem PlanReady.mono (ps : List ChainPiece) (s : MachineState)
    (post post' : MachineState → Prop) (h : PlanReady ps s post)
    (hp : ∀ t, post t → post' t) : PlanReady ps s post' := by
  induction ps generalizing s with
  | nil => exact hp s h
  | cons p ps ih =>
    obtain ⟨hl, hc, hpc, ho, ht⟩ := h
    refine ⟨hl, hc, hpc, ho, ?_⟩
    by_cases hh : p.isHash = true
    · rw [if_pos hh] at ht ⊢
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, fun ans => ih _ (ht.2.2.2.2 ans)⟩
    · rw [if_neg hh] at ht ⊢
      exact ih _ ht
theorem PlanReady.registers (ps : List ChainPiece) (s : MachineState)
    (post : MachineState → Prop) (h : PlanReady ps s post) :
    PlanReady ps s (fun t => post t ∧ ∀ r, r ∉ wctChainClobbers → t.getReg r = s.getReg r) := by
  induction ps generalizing s with
  | nil => exact ⟨h, fun _ _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨hl, hc, hpc, ho, ht⟩ := h
    refine ⟨hl, hc, hpc, ho, ?_⟩
    by_cases hh : p.isHash = true
    · rw [if_pos hh] at ht ⊢
      refine ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, fun ans => ?_⟩
      apply (ih _ (ht.2.2.2.2 ans)).mono
      intro t hp
      refine ⟨hp.1, fun r hr => ?_⟩
      rw [hp.2 r hr, writeHash_getReg, (chainPiece_keeps p).reg s hr]
    · rw [if_neg hh] at ht ⊢
      apply (ih _ ht).mono
      intro t hp
      exact ⟨hp.1, fun r hr => (hp.2 r hr).trans ((chainPiece_keeps p).reg s hr)⟩
end W9Machine
end
