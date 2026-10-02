import SigGolfCandidate.T3.Gate6.NativeCompletion
import SigGolfCandidate.T3.Gate6.SourceBridge

namespace SigGolfResearch.Gate6.Source
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Exact decoder equality, including the actual source's five-bit gate. -/
theorem actual_decoder_eq (output : HashOutput) :
    NativeSearch.decode output=SigGolfCandidate.T3.Sampling.digestDecode output := by
  unfold NativeSearch.decode SigGolfCandidate.T3.Sampling.digestDecode
  by_cases h : digestAdmissible output=true
  · simp [h,(actual_predicate_iff output).mp h]
  · have hn : ¬DigestAccepted output := fun hg => h ((actual_predicate_iff output).mpr hg)
    simp [h,hn]

/-- The proved native search is the actual current source counter search,
not an abstract replacement sampler. -/
theorem actual_search_eq (rho : Digest) (message : Message) (fuel : Nat) :
    NativeSearch.search rho message fuel=digestSearch rho message 0 fuel := by
  rw [digestSearch_public]
  unfold NativeSearch.search
  have he : NativeSearch.decode=SigGolfCandidate.T3.Sampling.digestDecode := funext actual_decoder_eq
  rw [he]

/-- The current source's whole fresh-nonce search, including exhaustion and its
actual public RO cache, satisfies the proposal cap. -/
theorem actual_uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => NativeSearch.completedScore mark result.1) ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  simpa only [actual_search_eq] using
    NativeSearch.uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark

noncomputable def actualRecordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (NativeSearch.complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (digestSearch rho message 0 fuel) cache))

theorem actual_recordLaw_eq (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    actualRecordLaw secret message fuel cache=NativeSearch.recordLaw secret message fuel cache := by
  simp only [actualRecordLaw,NativeSearch.recordLaw,actual_search_eq]

theorem actual_recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (1024/1025 : ENNReal)*((actualRecordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  rw [actual_recordLaw_eq]
  exact NativeSearch.recordLaw_scaled_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark

end SigGolfResearch.Gate6.Source
#print axioms SigGolfResearch.Gate6.Source.actual_search_eq
#print axioms SigGolfResearch.Gate6.Source.actual_uniform_nonce_completed_cap
#print axioms SigGolfResearch.Gate6.Source.actual_recordLaw_scaled_cap
