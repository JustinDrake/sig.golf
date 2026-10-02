import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsMaskCharge

/-!
# F1 ↔ F2: R3's honest charges and offline signer under `maskAt`

Stream F2's R3 (`proofs/WotsReference.lean`) consumes `keygenCharge T` / `signCharge T published request` ticks and
answers signing requests by `evalWithAnswerFn T (FullGame.authenticatedSign published request)`. For one address `a`
(source-sized for the signer) all of these are unchanged when `T` is replaced by `maskAt T a`.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)

/-- **F2 obligation**: the honest key-generation charge is unchanged by the mask (every address). -/
theorem keygenCharge_maskAt (T : Answers) (a : ChainAddr) : keygenCharge (maskAt T a) = keygenCharge T :=
  queried_length_maskAt_keygen T a

/-- **F2 obligation**: the honest charge of every signing request is unchanged by the mask (source-sized `a`). -/
theorem signCharge_maskAt (T : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (published : T3.Cache) (request : Request) :
    signCharge (maskAt T a) published request = signCharge T published request :=
  queried_length_maskAt_sign T a htree hleaf published request

/-- R3's offline signer is unchanged by the mask (charge and answer). -/
theorem offlineSign_maskAt (T : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (published : T3.Cache) (request : Request) :
    offlineSign (maskAt T a) published request = offlineSign T published request := by
  unfold offlineSign
  rw [signCharge_maskAt T a htree hleaf, eval_maskAt_sign T a htree hleaf]

/-- R3's offline adversary oracle is unchanged by the mask. -/
theorem offlineImpl_maskAt (T : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (published : T3.Cache) : offlineImpl (maskAt T a) published = offlineImpl T published := by
  unfold offlineImpl
  have h : offlineSign (maskAt T a) published = offlineSign T published :=
    funext (offlineSign_maskAt T a htree hleaf published)
  rw [h]

/-- R3's offline game (honest key generation, adversary interaction, verdict) is unchanged by the mask. -/
theorem offlineGame_maskAt (T : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (adversary : Final.AdversaryP) : offlineGame (maskAt T a) adversary = offlineGame T adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_maskAt, eval_maskAt_keygen, offlineImpl_maskAt T a htree hleaf]

/-- R3's capped reference game is unchanged by the mask. -/
theorem referenceGame_maskAt (T : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (adversary : Final.AdversaryP) (q : Nat) :
    referenceGame (maskAt T a) adversary q = referenceGame T adversary q := by
  unfold referenceGame
  rw [offlineGame_maskAt T a htree hleaf]

end SigGolfCandidate.T3.Security.Wots
