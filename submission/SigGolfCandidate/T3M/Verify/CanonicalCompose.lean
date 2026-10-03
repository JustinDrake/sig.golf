import SigGolfCandidate.T3M.Verify.CanonicalGate
import SigGolfCandidate.T3M.Verify.CanonicalFtsBody
import SigGolfCandidate.T3M.Verify.CanonicalFrames
import SigGolfCandidate.T3M.CanonicalPort.Verify.Compose

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput selections)

theorem chosen_ok_from_sel {pk w a t} (h : SelState pk w a 7 t) :
    ChosenOk (selections a) := by
  exact chosenOk_of a ((selectionsOk_iff a).mpr h.ok)

theorem after_sel_c_good (pk : Digest) (w : WBytes) (a : HashOutput) (t : MachineState)
    (ht : SelState pk w a 7 t) :
    GQ t 10735 10735 True 8249
      (CanonicalPort.Verify.ccM (afterSel pk (CanonicalAdapter.normalize (selections a) w) a)
        CanonicalPort.Verify.Kb) := by
  let F : FCtx := ⟨pk,w,a⟩
  have hc : ChosenOk (selections F.a) := chosen_ok_from_sel ht
  cases hg : T3.digestGate a with
  | false =>
    obtain ⟨u,hsteps,hh⟩ := fts_gate_reject pk w a t ht hg
    simp only [afterSel,hg,Bool.not_false,if_true,CanonicalPort.Verify.ccM_pure,CanonicalPort.Verify.Kb]
    exact CanonicalPort.Verify.GoodQ.steps' hsteps
      (CanonicalPort.Verify.GoodQ.reject (Q:=True) (A:=0) hh.1 hh.2.1 hh.2.2)
      (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
  | true =>
    obtain ⟨u,hsteps,hrdy⟩ := fts_gate_accept pk w a t ht hg
    obtain ⟨v,hsetup,hentry⟩ := canonical_setup pk w a u hrdy
    simp only [afterSel,hg,Bool.not_true,Bool.false_eq_true,if_false,CanonicalPort.Verify.ccM_bind]
    change GQ t _ _ _ _ (CanonicalPort.Verify.ccM
      (ftsP (CanonicalAdapter.normalize (selections F.a) F.w) F.idx (selections F.a))
      (fun r => CanonicalPort.Verify.ccM
        (afterFts F.pk (CanonicalAdapter.normalize (selections F.a) F.w) F.idx r)
        CanonicalPort.Verify.Kb))
    rw [normalized_fts_source F hc]
    have hb := banks_body_good F hc v hentry
      (fun r => CanonicalPort.Verify.ccM
        (afterFts F.pk (CanonicalAdapter.normalize (selections F.a) F.w) F.idx r)
        CanonicalPort.Verify.Kb)
      (by simp only [afterFts,CanonicalPort.Verify.ccM_pure,CanonicalPort.Verify.Kb])
      8061 5924 True (fun root z hp hz =>
        CanonicalPort.after_good _ _ True trivial _ root z (forest_out_normalized F hc hp hz))
    exact CanonicalPort.Verify.GoodQ.steps' (hsteps.trans hsetup) hb
      (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms after_sel_c_good
end SigGolfCandidate.T3M.CanonicalNative
