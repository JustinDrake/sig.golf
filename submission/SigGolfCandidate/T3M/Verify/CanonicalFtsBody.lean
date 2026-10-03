import SigGolfCandidate.T3M.Verify.CanonicalForest
import SigGolfCandidate.T3M.Verify.CanonicalBanksCost

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest forestPk)

def forestFinish (F : FCtx) (r : List Digest × Nat) : T3.M (Option Digest) := do
  if streamEnd<r.2 then return none
  pure (some (← forestPk F.idx r.1))

theorem forest_finish_good (F : FCtx) (roots : List Digest) (ptr : Nat) (s : MachineState)
    (hs : ForestCIn F roots ptr s) (R : Option Digest → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (hR : R none=pure (false,0)) (B A : Nat) (Q : Prop)
    (hK : ∀ root u, ptr≤10568 → ForestCOut F root u → GQ u B B Q A (R (some root))) :
    GQ s (B+24) (B+24) (Q ∧ ptr≤10568) (A+23)
      (CanonicalPort.Verify.ccM (forestFinish F (roots,ptr)) R) := by
  obtain ⟨hRej,hPass⟩ := forest_step_c F roots ptr s hs
  by_cases hp : 10568<ptr
  · simp only [forestFinish,show streamEnd<ptr by unfold streamEnd; omega,if_true,
      CanonicalPort.Verify.ccM_pure,hR]
    obtain ⟨u,hsteps,hh⟩ := hRej hp
    have h := CanonicalPort.Verify.GoodQ.reject (Q:=Q ∧ ptr≤10568) (A:=0) hh.1 hh.2.1 hh.2.2
    exact (CanonicalPort.Verify.GoodQ.steps hsteps h).mono (by omega) (by omega)
      (fun hq => ⟨hq,by omega⟩)
  · obtain ⟨u,hsteps,hf,h5,hargs,hin,hout⟩ := hPass (by omega)
    simp only [forestFinish,show ¬streamEnd<ptr by unfold streamEnd; omega,if_false,forestPk_eq]
    have h := CanonicalPort.Verify.GoodQ.shortHash_bind
      (N:=B) (C:=B) (A:=A) (Q:=Q ∧ ptr≤10568) (f:=fun r => pure (some r)) (K:=R)
      hf h5 hargs hin (fun ans => by
        simp only [CanonicalPort.Verify.ccM_pure]
        exact (hK _ _ (by omega) (hout ans)).mono (by omega) (by omega) (fun hq => ⟨⟨hq,by omega⟩,by omega⟩))
    rw [blocks_forestInput F.idx roots hs.hroots] at h
    exact CanonicalPort.Verify.GoodQ.steps' hsteps h (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

theorem all_bank_cycles : ∀ g : Fin 42, 14+bankCost g.val 0 5≤368 := by decide +kernel
theorem banks_all_bounds (F : FCtx) (hc : ChosenOk (T3.selections F.a)) :
    ∀ n c ptr, c+n≤7 →
      banksEndPtr F c n ptr≤ptr+1640*n ∧ banksCost F c n≤373*n := by
  intro n
  induction n with
  | zero => intro c ptr hn; simp [banksEndPtr,banksCost]
  | succ n ih =>
    intro c ptr hn
    have hg := (geometry_context F c (hc c (by omega))).1
    have hp := (bank_end_bounds (geomOf F c) ptr hg).2.1
    have hcost := all_bank_cycles ⟨geomOf F c,hg⟩
    dsimp only at hcost
    have hi := ih (c+1) (bankEndPtr (geomOf F c) 0 5 ptr) (by omega)
    simp only [banksEndPtr,banksCost]
    constructor
    · omega
    · split_ifs <;> omega

theorem banks_body_good (F : FCtx) (hc : ChosenOk (T3.selections F.a)) (s : MachineState)
    (hs : BankEntry F 0 1088 [] s)
    (R : Option Digest → OracleComp HashSpec CanonicalPort.Verify.Obs) (hR : R none=pure (false,0))
    (B A : Nat) (Q : Prop)
    (hK : ∀ root u, banksEndPtr F 0 7 1088≤10568 → ForestCOut F root u → GQ u B B Q A (R (some root))) :
    GQ s (B+2640) (B+2640) Q (A+2291)
      (CanonicalPort.Verify.ccM (ftsScheduled F) R) := by
  let ptr := banksEndPtr F 0 7 1088
  have hb := banks_all_bounds F hc 7 0 1088 (by omega)
  have h := banks_good F hc (fun r => CanonicalPort.Verify.ccM (forestFinish F r) R)
    (B+29) (A+28) (Q ∧ ptr≤10568) 7 0 1088 [] s
    (by omega) (by omega) (by simp) (by omega) (by omega) (by decide) hs
    (fun roots t ht => by
      obtain ⟨u,hsteps,hu⟩ := restore_forest F ptr roots t (by dsimp only [ptr]; omega) ht
      have hg := forest_finish_good F roots ptr u hu R hR B A Q hK
      convert CanonicalPort.Verify.GoodQ.steps hsteps hg using 1 <;> omega)
  have hm : GQ s (B+2640) (B+2640) Q (A+2291)
      (CanonicalPort.Verify.ccM (banksProgram F 0 7 1088 [])
        (fun r => CanonicalPort.Verify.ccM (forestFinish F r) R)) :=
    h.mono (by omega) (by omega) (fun hq => by
    have hcst := banks_accepted_cost F hc hq.2
    exact ⟨hq.1,by omega⟩)
  unfold ftsScheduled
  change GQ s _ _ _ _ (CanonicalPort.Verify.ccM
    (banksProgram F 0 7 1088 [] >>= forestFinish F) R)
  rw [CanonicalPort.Verify.ccM_bind]
  exact hm

#print axioms forest_finish_good
#print axioms banks_body_good
end SigGolfCandidate.T3M.CanonicalNative
