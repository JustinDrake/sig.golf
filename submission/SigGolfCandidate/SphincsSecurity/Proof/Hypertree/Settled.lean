import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Honest

namespace SphincsSecurity
open OracleComp OracleSpec
def fromCache (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0
theorem agreesWithFn_fromCache (cache : QueryCache HashSpec) :
    cache.AgreesWithFn (fromCache cache) := by
  intro input answer hcached
  simp [fromCache, hcached]
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
variable {parameter} {otsSecret} {ftsSecret}
end SphincsSecurity
