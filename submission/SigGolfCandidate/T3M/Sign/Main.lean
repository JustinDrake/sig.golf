import SigGolfCandidate.T3M.Sign.Payload
import SigGolfCandidate.T3M.Sign.Top
import SigGolfCandidate.T3M.Sign.InitState
import SigGolfCandidate.T3M.Search.DigestSearch

/-!
# Sign: the whole phase

* `digestSearchSpec`, `counterSearchSpec`, `kernels` : E's search kernels (t3m/e 31dd5ff) in the shapes of
  `Sign/Kernels` (bridge text from MACH-NOTES 2026-10-01 14:55);
* `sign_tbsim_of` : from the loaded state the machine refines Core's `sign (cacheDec cache) m` within `signC`
  cycles and ends in `PayPost` (given layer 0, `L0Spec`);
* `payPost_output` : at `HALT(0)` the signature buffer is `sigB` of Core's signature;
* `sign_refines_of`, `sign_terminates_of` : the phase statements from `L0Spec`;
* **`sign_refines`**, **`sign_terminates`** : the phase statements (`Final.SignRefines`, `Final.SignTerminates`
  shapes), unconditionally (layer 0 by `l0Spec_of` with E's `counter_search`).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Signature sign counterLimit attemptLimit)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## E's search kernels -/

theorem digestSearchSpec (sk : BitVec 256) : DigestSearchSpec sk := fun s rho m h =>
  (Search.digestSearch_spec Search.dsAt_sign Search.kernAt_sign s rho m ⟨h.pc, h.x5, h.x19, h.rho, h.msg⟩).mono
    le_rfl (fun r t ht => by rcases r with _ | _; exacts [⟨ht.pc, ht.x5, ht.x10⟩, ht])

theorem counterSearchSpec (sk : BitVec 256) : CounterSearchSpec sk := fun s lay tree leaf msg ret h =>
  (Search.counterSearch_spec Search.kernAt_sign s lay tree leaf msg ret
    ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.msg, h.c32, h.z40, h.z48,
      h.z56⟩).mono le_rfl (fun r t ht => by rcases r with _ | _; exacts [⟨ht.pc, ht.x5, ht.x10⟩, ht])

theorem kernels (sk : BitVec 256) : Kernels sk := ⟨digestSearchSpec sk, counterSearchSpec sk⟩

/-! ## The phase -/

/-- Cycle bound of the sign phase (before the final `ECALL`). -/
def signC : Nat := frontC + dsCost + midC

theorem signC_eq : signC = 3612954843 := by rfl

theorem signC_lt : signC + 1 < CYCLE_LIMIT := by
  rw [signC_eq]; norm_num [CYCLE_LIMIT]

section phase
variable {sk : SecretKey} {cache : Bytes 32768}

/-- **Sign on the machine** (given layer 0). -/
theorem sign_tbsim_of (hL0 : L0Spec sk cache) (m : Message) :
    TBSim image sk (sinit sk cache m) signC (sign (cacheDec cache) m) PayPost :=
  sign_front (digestSearchSpec sk) (fun _ h => h) (fun _ _ _ h => payloadRest_tbsim (counterSearchSpec sk) hL0 h)

/-- The signature buffer at `HALT(0)`. -/
theorem payPost_output {sig : Signature} {u : MachineState}
    (h : ∀ k < 355, DigAt u (SIG + 16 * k) ((sigDigests sig).getD k 0)) :
    readOutput submission.sizes submission.layout .sign u = sigB sig := by
  have hd : DigsAt u SIG (sigDigests sig) := fun k hk => h k (by rw [length_sigDigests] at hk; exact hk)
  have hw := hd.words
  rw [length_sigDigests] at hw
  have hl : ((sigDigests sig).flatMap (bytesLE 16)).length = 8 * 710 := by
    have : ∀ ds : List Digest, (ds.flatMap (bytesLE 16)).length = 16 * ds.length := fun ds => by
      induction ds with
      | nil => rfl
      | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
    rw [this, length_sigDigests]
  have e := readBuffer_of_words u SIG 710 ((sigDigests sig).flatMap (bytesLE 16)) (by decide) (by decide) hl hw
  show readBuffer u SIG (8 * 710) = sigB sig
  rw [e, sigB, serialize_eq]

/-- **Sign refinement** (given layer 0): value, calls and compressions of the phase are Core's
`sign (cacheDec cache) m`'s, with the output `sigB`. -/
theorem sign_refines_of (hL0 : L0Spec sk cache) (m : Message) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      (fun p => (p.1.map sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m)) :=
  Sim.run_eq submission .sign (sk, cache, m) (initialState_sign sk cache m) (sign_tbsim_of hL0 m)
    (by have := signC_lt; omega) (fun o => o.map sigB) (fun o u hu => by
      rcases o with _ | sig
      · exact ⟨fetch_545 u hu.pc, hu.x5, by rw [if_neg (by rw [hu.x10]; decide)]; rfl⟩
      · obtain ⟨hh, hd⟩ := hu
        exact ⟨fetch_542 u hh.pc, hh.x5, by rw [if_pos hh.x10, payPost_output hd]; rfl⟩)

/-- **Sign termination** (given layer 0): under every fixed oracle, finished within `signC + 1 < 2^32`
cycles. -/
theorem sign_terminates_of (hL0 : L0Spec sk cache) (hash : Hash) (m : Message) :
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT := by
  obtain ⟨h1, h2⟩ := Sim.runWith submission .sign (sk, cache, m) (initialState_sign sk cache m)
    (sign_tbsim_of hL0 m) signC_lt (fun o u hu => by
      rcases o with _ | sig
      · exact ⟨fetch_545 u hu.pc, hu.x5⟩
      · exact ⟨fetch_542 u hu.1.pc, hu.1.x5⟩) hash
  exact ⟨h1, by have := signC_lt; omega⟩

end phase

/-- **Sign refinement.** For every secret key, every cache (also a tampered one, rejected after the one MAC
query) and every message: value, calls and compressions of the sign phase are those of Core's
`sign (cacheDec cache) m`, with the output `sigB`. -/
theorem sign_refines (sk : SecretKey) (cache : Bytes 32768) (m : Message) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      (fun p => (p.1.map sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m)) :=
  sign_refines_of (l0Spec_of (counterSearchSpec sk)) m

/-- **Sign termination.** Under every fixed oracle and for every input: finished, within
`signC + 1 = 3,612,954,844 < 2^32` cycles. -/
theorem sign_terminates (hash : Hash) (sk : SecretKey) (cache : Bytes 32768) (m : Message) :
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT :=
  sign_terminates_of (l0Spec_of (counterSearchSpec sk)) hash m

end SigGolfCandidate.T3M.Sign
