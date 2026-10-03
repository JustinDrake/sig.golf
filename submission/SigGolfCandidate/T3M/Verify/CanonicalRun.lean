import SigGolfCandidate.T3M.Verify.CanonicalVerify

set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify

theorem init_exists_c (input : Legacy.Input candidateSub.sizes .verify) :
    ∃ s, initialState candidateSub .verify input=some s := by
  unfold initialState
  simp only [candidateSub_admissible.2 .verify,if_true]
  exact ⟨_,rfl⟩

theorem verify_c_refines (m : Message) (pk : PublicKey) (w : Bytes 25240) :
    (fun r => (r.value,r.hashCalls)) <$> candidateSub.run .verify (m,pk,w)=
      (fun p => (if p.1 then some () else none,p.2)) <$>
        countCalls (mrealize 0 (CanonicalSource.verifyC m pk w)) := by
  obtain ⟨s,hs⟩ := init_exists_c (m,pk,w)
  have hg := (verify_c_good m pk w s (init_c m pk w s hs) CYCLE_LIMIT (by unfold CYCLE_LIMIT;norm_num)).1
  rw [ccM_Kb] at hg
  rw [run_eq candidateSub .verify _ s hs,candidateSub_verify,Functor.map_map]
  rw [←hg,Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT fixture s) ?_
  funext e
  simp only [toRunResult,obs]
  by_cases h : e.exit=.success
  · simp only [h,decide_true,if_true];rfl
  · simp only [h,decide_false,if_false,Bool.false_eq_true];rfl

theorem verify_c_terminates (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240) :
    (candidateSub.runWith hash .verify (m,pk,w)).finished=true ∧
      (candidateSub.runWith hash .verify (m,pk,w)).cycles<CYCLE_LIMIT := by
  obtain ⟨s,hs⟩ := init_exists_c (m,pk,w)
  have hg := (verify_c_good m pk w s (init_c m pk w s hs) CYCLE_LIMIT (by unfold CYCLE_LIMIT;norm_num)).2 hash
  rw [runWith_eq candidateSub hash .verify (m,pk,w) s hs,candidateSub_verify]
  simp only [toRunResult]
  refine ⟨?_,lt_of_le_of_lt hg.2.1 (by unfold CYCLE_LIMIT;norm_num)⟩
  simpa using hg.1

theorem verify_c_accept_cycles (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240)
    (h : (candidateSub.runWith hash .verify (m,pk,w)).value.isSome=true) :
    (candidateSub.runWith hash .verify (m,pk,w)).cycles≤8495 := by
  obtain ⟨s,hs⟩ := init_exists_c (m,pk,w)
  have hg := (verify_c_good m pk w s (init_c m pk w s hs) CYCLE_LIMIT (by unfold CYCLE_LIMIT;norm_num)).2 hash
  rw [runWith_eq candidateSub hash .verify (m,pk,w) s hs,candidateSub_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT fixture s)).exit=.success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  exact (hg.2.2 hsucc).2

#print axioms verify_c_refines
#print axioms verify_c_terminates
#print axioms verify_c_accept_cycles
end SigGolfCandidate.T3M.CanonicalNative
