import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Replay and message-digest collisions

If one signing entry has the forgery's complete admissible digest, a fully honest opening is the
returned signature unless the two distinct message-digest inputs have the same answer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem messageDigestPayload_injective (root : Digest) {leftMessage rightMessage : Message}
    {leftRandomness rightRandomness : Randomness}
    (h : messageDigestPayload root leftMessage leftRandomness
      = messageDigestPayload root rightMessage rightRandomness) :
    leftMessage = rightMessage ∧ leftRandomness = rightRandomness := by
  simp only [messageDigestPayload] at h
  obtain ⟨hrandomness, hrest⟩ := List.append_inj h (by simp [bytesLE_length]; exact (bytesLE_length 16 _).trans (bytesLE_length 16 _).symm)
  have hrandomness' := List.append_cancel_right hrandomness
  exact ⟨bytesLE_injective hrest, bytesLE_injective hrandomness'⟩

end SphincsSecurity.Concrete

/-!
# Finite witnesses for the few-time leak

A leak chooses one successful signing entry for each of the fourteen opened trees.  Keeping the
range of that choice as a finset exposes the number of distinct signatures used by the opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev SigningEntry := (request : Message) × SigningSpec.Range request

end SphincsSecurity.Concrete
