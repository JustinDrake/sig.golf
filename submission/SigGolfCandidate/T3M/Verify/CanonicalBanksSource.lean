import SigGolfCandidate.T3M.Verify.CanonicalBanks
import SigGolfCandidate.T3M.Verify.CanonicalBankPointers

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify

theorem native_stream_fold (F : FCtx) (hc : ChosenOk (T3.selections F.a)) :
    ∀ n c roots, c+n ≤ 7 →
    (List.range' c n).foldlM
      (ftsStreamStep (CanonicalAdapter.normalize (T3.selections F.a) F.w) F.idx (T3.selections F.a))
      (some (roots,segPtr (schedule (T3.selections F.a)) (5*c)))=
      some <$> banksProgram F c n (segPtr (schedule (T3.selections F.a)) (5*c)) roots := by
  intro n
  induction n with
  | zero => intro c roots hn; simp [banksProgram]
  | succ n ih =>
    intro c roots hn
    have hc7 : c<7 := by omega
    rw [List.range'_succ,List.foldlM_cons]
    simp only [ftsStreamStep]
    have hb := normalized_native_bank F c hc hc7
    change ftsCoordP _ _ _ ((T3.selections F.a).getD c ⟨0,[]⟩) _ = _ at hb
    rw [hb]
    simp only [map_bind,bind_map_left,bind_assoc,pure_bind,banksProgram]
    apply bind_congr_of_forall_mem_support
    intro r hr
    have hp := bank_program_ptr F c (geomOf F c) 5 0
      (segPtr (schedule (T3.selections F.a)) (5*c)) [] 0 0 r hr
    rw [bank_end_schedule_global F hc c hc7] at hp
    rw [hp]
    exact ih (c+1) (roots++[r.1]) (by omega)

def ftsScheduled (F : FCtx) : T3.M (Option Digest) := do
  let p ← banksProgram F 0 7 streamBase []
  if streamEnd<p.2 then return none
  pure (some (← forestPk F.idx p.1))

theorem normalized_fts_source (F : FCtx) (hc : ChosenOk (T3.selections F.a)) :
    ftsP (CanonicalAdapter.normalize (T3.selections F.a) F.w) F.idx (T3.selections F.a)=
      ftsScheduled F := by
  rw [ftsP_eq]
  have hf := native_stream_fold F hc 7 0 [] (by omega)
  simp only [Nat.mul_zero,segPtr_zero,show List.range' 0 7=List.range 7 by decide] at hf
  rw [hf]
  simp only [ftsScheduled,map_bind,bind_map_left]

#print axioms normalized_fts_source
end SigGolfCandidate.T3M.CanonicalNative
