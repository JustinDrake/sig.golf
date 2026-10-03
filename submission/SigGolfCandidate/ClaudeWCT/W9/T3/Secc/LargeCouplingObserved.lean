import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeResidualRouter
import SigGolfCandidate.T3.Secc.LargeCouplingObserved

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargeResidual (State Charge Probe Cell observedRun readState probeState stoppedState
  disclosedState tickState observed_aux observed_read observed_probe_cached observed_probe_fresh observed_disclose
  observed_tick)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (table : Cell U → HashOutput)
theorem observed_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (coinReq U n >>= k) s =
      ((liftM (aux (.coin n)) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table (.coin n) k s
theorem observed_initReq {β : Type} (k : AuxData → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (initReq U >>= k) s =
      ((liftM (aux .init) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table .init k s
theorem observed_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (readReq U row ch >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) :=
  observed_read aux q labels table row ch k s
theorem observed_probeReq_cached {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (v : HashOutput)
    (h : s.rows row = some v) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      observedRun aux q labels table (k v) (readState q s row v .call) :=
  observed_probe_cached aux q labels table row test k s v h
theorem observed_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      if (test.effective s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effective s.candidates) (table row))
      else pure (none, stoppedState s) :=
  observed_probe_fresh aux q labels table row test k s h
theorem observed_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseReq U c ch >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) :=
  observed_disclose aux q labels table c ch k s
theorem observed_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (tickReq U ch >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) :=
  observed_tick aux q labels table ch k s
def discloseStates (q : Nat) (labels : WCoord → Digest) (s : State WCoord (Cell U)) (cs : List Coord) :
    State WCoord (Cell U) :=
  cs.foldl (fun s c => disclosedState q s (.inl c) (labels (.inl c)) .none) s
theorem observed_discloseAll {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseAll U cs >>= k) s =
      observedRun aux q labels table (k (cs.map fun c => (c, labels (.inl c)))) (discloseStates U q labels s cs) := by
  induction cs generalizing s k with
  | nil => simp only [discloseAll, pure_bind, List.map_nil, discloseStates, List.foldl_nil]
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [observed_discloseReq]
      simp only [pure_bind]
      rw [ih]
      rfl
end Router
end ClaudeWCT.W9.T3.Security.LargeResidual
