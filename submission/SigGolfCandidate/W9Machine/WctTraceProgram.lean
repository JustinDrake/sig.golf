import SigGolfCandidate.W9Machine.WctTraceInvariant

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M publicHash)
open SphincsSecurity (bytesLE)
def wordBytes (ws : List Word) : List UInt8 := ws.flatMap (bytesLE 8)
def pieceQuery (tr : ChainTrace) (p : ChainPiece) : List ChainWord :=
  (tr.step p.kind).queries.getD tr.queries.length []
def planQueries : List ChainPiece → ChainTrace → List (List ChainWord)
  | [], _ => []
  | p :: ps, tr =>
      if p.isHash then pieceQuery tr p :: planQueries ps (tr.step p.kind)
      else planQueries ps (tr.step p.kind)
def traceProgram (base : ChainWord → Word) : List (List ChainWord) → List (BitVec 256) →
    M (List (BitVec 256))
  | [], answers => pure answers
  | q :: qs, answers => do
      let ans ← publicHash (wordBytes (q.map (chainValue base answers)))
      traceProgram base qs (answers ++ [ans])
theorem wordBytes_length (ws : List Word) : (wordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, List.length_append, SphincsSecurity.bytesLE_length,
      List.length_cons] at *
    omega
theorem wordsOf_wordBytes (ws : List Word) : wordsOf (wordBytes ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change wordsOf (bytesLE 8 w ++ wordBytes ws) = w :: ws
    rw [wordsOf_append8 _ _ (SphincsSecurity.bytesLE_length _ _), readLE_bytesLE]
    simpa using congrArg (w :: ·) ih
theorem wordBytes_wordsOf (input : List UInt8) (n : Nat) (hn : input.length = 8 * n) :
    wordBytes (wordsOf input) = input := by
  have hl : (wordBytes (wordsOf input)).length = 8 * n := by
    rw [wordBytes_length, length_wordsOf n input hn]
  apply readLE_inj (hl.trans hn.symm)
  rw [← wordsToNat_wordsOf n _ hl, wordsOf_wordBytes, wordsToNat_wordsOf n input hn]
theorem ChainTrace.step_queries (tr : ChainTrace) (p : ChainPiece) :
    (tr.step p.kind).queries = tr.queries ++ if p.isHash then [pieceQuery tr p] else [] := by
  have qhash (t : ChainTrace) : t.hash.queries = t.queries ++
      [(List.range 8).map fun i => t.read (t.input + 8 * i)] := rfl
  cases p with
  | mk pc words kind =>
    cases kind <;> simp [pieceQuery, ChainTrace.step, ChainPiece.isHash, qhash,
      ChainTrace.put, List.getD_eq_getElem?_getD]
theorem planQueries_spec (ps : List ChainPiece) (tr : ChainTrace) :
    (ps.foldl (fun t p => t.step p.kind) tr).queries = tr.queries ++ planQueries ps tr := by
  induction ps generalizing tr with
  | nil => simp only [List.foldl_nil, planQueries, List.append_nil]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, tr.step_queries p]
    simp only [planQueries]
    split_ifs <;> simp only [List.append_nil, List.append_assoc, List.singleton_append]
end W9Machine
