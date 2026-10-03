import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryBound

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
noncomputable def gameRest (scheme : Scheme SecretKey) (adversary : Adversary) (pk : PublicKey)
    (sk : SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified
theorem gameCore_eq (scheme : Scheme SecretKey) (adversary : Adversary) :
    gameCore scheme adversary
      = scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2 := rfl
namespace Concrete
noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : OracleComp OracleWorld Bool := do
  let top ← liftM
    (keygenTable parameter (otsSecret topLayer rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  gameRest scheme adversary ⟨top (layerHeight topLayer) 0, parameter⟩
    ⟨parameter, top (layerHeight topLayer) 0, otsSecret, ftsSecret, top⟩
attribute [local semireducible] keygen
theorem gameCore_eq_secrets (adversary : Adversary) :
    gameCore scheme adversary = (do
      let parameter ← liftM sampleParameter
      let otsSecret ← liftM sampleOtsSecrets
      let ftsSecret ← liftM sampleFtsSecrets
      gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [gameCore_eq]
  simp only [scheme, keygen, gameAfterSecrets, bind_assoc, pure_bind]
theorem mem_support_liftM_of_mem_support {α : Type} {oa : ProbComp α} {x : α}
    (hmem : x ∈ support oa) : x ∈ support (liftM oa : OracleComp OracleWorld α) := by
  rwa [← liftComp_eq_liftM, support_liftComp]
theorem simulateQ_romImpl_liftM_bind_run' {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM oa : OracleComp OracleWorld α) >>= k)).run' cache
      = oa >>= fun x => (simulateQ romImpl (k x)).run' cache := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    show simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (unifFwdImpl HashSpec) oa from QueryImpl.simulateQ_add_liftM_left _ _ oa,
    unifFwdImpl.simulateQ_run]
  simp [map_eq_bind_pure_comp, bind_assoc, StateT.run'_eq]
theorem hashQueryBound_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) {parameter : PublicParameter}
    (hparameter : parameter ∈ support sampleParameter)
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    (hots : otsSecret ∈ support sampleOtsSecrets)
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    HashQueryBound (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ q := by
  rw [hasHashQueryBound_iff, gameCore_eq_secrets] at hq
  exact hashQueryBound_of_sampling_bind _ _ ∅ q
    (hashQueryBound_of_sampling_bind _ _ ∅ q
      (hashQueryBound_of_sampling_bind _ _ ∅ q hq parameter hparameter) otsSecret hots)
    ftsSecret hfts
end Concrete
end SphincsSecurity
