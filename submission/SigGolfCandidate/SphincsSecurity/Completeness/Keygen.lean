import SigGolfCandidate.SphincsSecurity.Completeness.Digest
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation

/-!
# What key generation leaves uncached

Key generation builds the top tree, with `P = 0`: derivation inputs and chain, leaf and node
tweaks; then it derives the masks (derivation inputs under tag `13`) and makes one MAC query (tag
`14`). The searches that follow hash under the randomizer, message and encoding tweaks, which none of
those produce, so their inputs are all still missing from the cache when signing begins. The MAC query,
on the other hand, is in the cache, with the tag key generation returned: the signer's check repeats it.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

open Concrete

/-- Key generation avoids any input that none of its hash calls can produce. -/
theorem Avoids.keygen_of (seed : MasterSeed) (target : HashInput)
    (hkey : ∀ (parameter : PublicParameter) (domain : KeygenDomain),
      keygenHashInput parameter domain seed ≠ target)
    (hchain : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex)
      (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain topLayer tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf topLayer tree leaf) payload ≠ target)
    (hnode : ∀ (parameter : PublicParameter) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node topLayer tree level nodeIdx) payload ≠ target)
    (f : QueryImpl HashSpec Id) : Avoids f target (Seeded.keygenFromSeed seed) :=
  Avoids.keygenFromSeed f target seed (fun _ _ _ _ => hchain _ _ _ _ _ _)
    (fun _ _ => hleaf _ _ _ _) (fun _ _ _ => hnode _ _ _ _ _) (fun _ => hkey _ _)

theorem keygenDomain_tag_ne (domain : KeygenDomain) (tag : Nat) (htag : tag = 4 ∨ tag = 7 ∨ tag = 12) :
    (keygenDomainFields domain).tag ≠ BitVec.ofNat 8 tag := by
  rcases htag with rfl | rfl | rfl <;> cases domain <;> simp [keygenDomainFields, tweakFields]

/-- After key generation, nothing the randomizer search, the message digest or a counter search hashes is cached. -/
theorem keygen_fresh (seed : MasterSeed)
    (r : (PublicKey × TopCache × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.keygenFromSeed seed)).run ∅))
    (message : Message) :
    (∀ s, r.2 (randInput r.1.2.2 message s) = none)
      ∧ (∀ ρ, r.2 (msgInput r.1.2.2 message ρ) = none)
      ∧ EncodingFresh r.1.2.2.parameter (fun _ => True) r.2 := by
  refine ⟨fun s => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_),
    fun ρ => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_),
    fun lay _ tree leaf first payload => cache_none_of_avoids _ ∅ r hr _ rfl
      (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_)⟩
  · intro parameter domain h
    exact (randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _) h.symm
  · intro parameter tree leaf chainIdx step payload h
    exact (randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ _ _) h.symm
  · intro parameter tree leaf payload h
    exact (randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ _ _) h.symm
  · intro parameter tree level nodeIdx payload h
    exact (randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ _ _) h.symm
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree leaf chainIdx step payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree leaf payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree level nodeIdx payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree' leaf' chainIdx step payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' leaf' payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' level nodeIdx payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _

/-- A query of one member is a query of the sequenced family. -/
theorem mem_queriedInputs_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) (i : Fin n) {input : HashInput}
    (h : input ∈ queriedInputs f (computation i)) :
    input ∈ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [Concrete.sequenceFin]
      cases i using Fin.cases with
      | zero => exact queriedInputs_mono_bind_left f _ _ h
      | succ j =>
          apply queriedInputs_mono_bind_right
          apply queriedInputs_mono_bind_left
          exact ih (fun index => computation index.succ) j h

/-- Key generation's MAC key derivations are on its replay path. -/
theorem mac_mem_queriedInputs_keygen (f : QueryImpl HashSpec Id) (seed : MasterSeed) (index : Fin 3) :
    keygenHashInput 0 (.mackey index) seed ∈ queriedInputs f (Seeded.keygenFromSeed seed) := by
  rw [Seeded.keygenFromSeed]
  apply queriedInputs_mono_bind_right
  split
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  rw [Seeded.deriveMacKey]
  apply mem_queriedInputs_sequenceFin f _ index
  rw [queriedInputs_oracleHash, List.mem_singleton]

/-- After key generation, the three derivations of the MAC key are cached, and the tag key generation
returned is the MAC of the cache's region under that key: the signer's derivations are cache hits and its
check passes. -/
theorem keygen_mac_cached (seed : MasterSeed)
    (r : (PublicKey × TopCache × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.keygenFromSeed seed)).run ∅)) :
    ∃ key : MacKey,
      (∀ index, r.2 (keygenHashInput r.1.2.2.parameter (.mackey index) r.1.2.2.seed) = some (key index)) ∧
        macTag key (regionBytes r.1.2.1.region) = r.1.2.1.tag := by
  obtain ⟨keys, cache⟩ := r
  obtain ⟨_, f, hf, heval, hqueries⟩ := exists_answerFn_replay_of_mem_support _ ∅ keys cache hr
  rw [eval_keygenFromSeed] at heval
  subst heval
  refine ⟨keygenMacKeyValue f seed, fun index => ?_, ?_⟩
  · obtain ⟨answer, hanswer⟩ :=
      Option.ne_none_iff_exists'.mp (hqueries _ (mac_mem_queriedInputs_keygen f seed index))
    -- reduce the key's projections first: comparing them unreduced unfolds the evaluations
    dsimp only
    unfold keygenMacKeyValue
    rw [hanswer, hf hanswer]
  · dsimp only

end SphincsSecurity.Completeness
