import Lean
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Fetch
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Mem

section

namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
elab "krfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let fvars := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
    let (_, g2) ← g.revert fvars (preserveOrder := true)
    g2.withContext do
      let t ← instantiateMVars (← g2.getType)
      if t.hasMVar then throwError "krfl: goal contains metavariables"
      let pf ← forallTelescope t fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "krfl: goal is not an equation"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let name ← mkAuxLemma [] t pf
      g2.assign (mkConst name)
      replaceMainGoal []
end ClaudeWCT.W9.Machine.Expand
end

section




namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def windowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i => expLook (n + i) == ws[i]?
theorem codeAt_of_look {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (ws : List (BitVec 32)) (hn : 0x1000 + 4 * n + 4 * ws.length < 2 ^ 64)
    (h : ∀ i, i < ws.length → look (n + i) = ws[i]?) : CodeAt im (pcOf n) ws := by
  have hpc : (pcOf n).toNat = 0x1000 + 4 * n := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ws.length
  · rw [List.getElem?_take, if_pos (by simpa using hi), List.getElem?_drop]
    have := hl (n + i) (ws[i]) (by rw [h i hi]; simp [hi])
    rw [this]; simp [hi]
  · rw [List.getElem?_eq_none (by omega)]
    by_cases hd : i < (List.drop n im.code).length
    · have := h
      rw [List.getElem?_take, if_neg (by simp; omega)]
    · rw [List.getElem?_eq_none (by simp at hd ⊢; omega)]
theorem codeAt_of_window {im : Image} (hc : NewCodeAt im) {n : Nat} {ws : List (BitVec 32)}
    (hn : 0x1000 + 4 * n + 4 * ws.length < 2 ^ 64) (h : windowOK n ws = true) : CodeAt im (pcOf n) ws := by
  refine codeAt_of_look (expLook_ok hc) n ws hn (fun i hi => ?_)
  unfold windowOK at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this
theorem pcOf_add_lit (n m k : Nat) (h : (0x1000 + 4 * n + k) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64) :
    pcOf n + BitVec.ofNat 64 k = pcOf m := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [← h]
  omega
theorem pcOf_add4' (n : Nat) : pcOf n + 4#64 = pcOf (n + 1) := pcOf_add4 n
theorem pcOf_inj {n m : Nat} (hn : n < 2 ^ 61) (hm : m < 2 ^ 61) (h : pcOf n = pcOf m) : n = m := by
  have := congrArg BitVec.toNat h
  simp only [pcOf, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega
theorem micro_step {im : Image} {pc : Word} {w : BitVec 32} {i : Instruction} {m : Micro}
    (hc : CodeAt im pc [w]) (hd : decodeInstruction w = some i) (hcl : classify i = some m)
    {s t : MachineState} (hpc : s.pc = pc) (he : m.exec s = some t) :
    Steps im s 1 (instructionCycles i) t := by
  have hf : fetch im s = some i := (hc.fetch s hpc).trans hd
  have := Steps.step (image := im) hf ((classify_sound hcl s).trans he) (Steps.refl t)
  simpa using this
theorem jal_x0_step {im : Image} {n m : Nat} {w : BitVec 32} {imm : BitVec 21}
    (hc : CodeAt im (pcOf n) [w]) (hd : decodeInstruction w = some (.base (.JAL .x0 imm)))
    (hoff : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcOf n) : Steps im s 1 1 (s.setPC (pcOf m)) := by
  have h := micro_step (m := .jal .x0 (signExtend21 imm)) hc hd rfl hpc (t := s.setPC (pcOf m)) (by
    simp only [Micro.exec, MachineState.setReg, hpc, Option.some.injEq]
    have e : signExtend21 imm = BitVec.ofNat 64 (signExtend21 imm).toNat := by simp
    rw [e, pcOf_add_lit n m _ hoff])
  exact h
theorem expRun_sound {im : Image} (hc : NewCodeAt im) {cfg : Config} {stops : List Word} {fuel : Nat}
    {pc : Word} {dirs : List Dir} {r : PRes}
    (h : pathAux cfg expLook stops fuel pc dirs (σK []) [] = some r) (s : MachineState) (hpc : s.pc = pc)
    (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound h (expLook_ok hc) s hpc (by intro p hp; cases hp) hobl hbr
end ClaudeWCT.W9.Machine.Expand
end
