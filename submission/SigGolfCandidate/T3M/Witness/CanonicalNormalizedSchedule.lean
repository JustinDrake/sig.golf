import SigGolfCandidate.T3M.Witness.CanonicalNormalizeQueries

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalSchedule
open OracleComp OracleSpec SigGolfCandidate.T3

theorem indexed_headers_reads (w v : WBytes) : ∀ (segs : List Segment) (f : Nat → Nat),
    (∀ i, i<segs.length → f (i+1)=segNext (f i) (segs.getD i default).a) →
    (∀ i, i<segs.length → (segs.getD i default).Matches (wbyte w (f i)).toNat ∧
      ReadsAt w v (f i) (segs.getD i default).a) →
    HeadersMatch w (f 0) segs ∧ SegmentReads w v (f 0) segs := by
  intro segs
  induction segs with
  | nil => intro f hn ha; trivial
  | cons p ps ih =>
    intro f hn ha
    have h0 := ha 0 (by simp)
    have hn0 := hn 0 (by simp)
    simp only [List.getD_cons_zero] at h0 hn0
    have ht := ih (fun i => f (i+1))
      (fun i hi => by have := hn (i+1) (by simp; omega); simpa using this)
      (fun i hi => by have := ha (i+1) (by simp; omega); simpa using this)
    simpa only [HeadersMatch,SegmentReads,hn0] using And.intro
      (And.intro h0.1 ht.1) (And.intro h0.2 ht.2)

theorem normalized_coord_exact (chosen : List Selection) (w : WBytes) (index c : Nat)
    (hc : ChosenOk chosen) (hc7 : c<7) :
    ftsCoordP (CanonicalAdapter.normalize chosen w) index c (chosen.getD c ⟨0,[]⟩)
      (segPtr (schedule chosen) (5*c))=
      some <$> coordProgram w index c (chosen.getD c ⟨0,[]⟩) (segPtr (schedule chosen) (5*c)) := by
  let v := CanonicalAdapter.normalize chosen w
  have hpred := indexed_headers_reads v w (coordSchedule c (chosen.getD c ⟨0,[]⟩))
    (fun i => segPtr (schedule chosen) (5*c+i)) (coord_ptrs chosen hc7) (fun i hi => by
      have hi5 : i<5 := by simpa [coordSchedule_length] using hi
      have hn : 5*c+i<(schedule chosen).length := by rw [schedule_length]; omega
      have hg := schedule_getD chosen (n:=5*c+i) (by omega)
      rw [show (5*c+i)/5=c by omega,show (5*c+i)%5=i by omega] at hg
      constructor
      · rw [← hg]; exact CanonicalAdapter.normalize_streamMatches_general chosen w hc _ hn
      · intro r hr off hoff
        rw [← hg] at hr
        apply CanonicalAdapter.fold_digest_normalize_general chosen w hc _ r off hn hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;> omega)
  simp only [Nat.add_zero] at hpred
  have hs := hc c hc7
  rw [coord_program_exact v index c _ _ hs.b hs.l2 hs.s01 hs.s12 hpred.1,
    coord_program_congr v w index c _ _ hc7 (leaf_same_normalize chosen w) hpred.2]

#print axioms normalized_coord_exact
end SigGolfCandidate.T3M.CanonicalSchedule
