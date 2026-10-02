import SigGolfCandidate.T3.Secc.LargeContactCertFold
import SigGolfCandidate.T3.Secc.SeccSufRoute

/-!
# LR-34 (certificate coupling, deterministic link): a contact-free clean win carries the router's certificate

**`cert_of_clean`**: on the shared law, a clean win without large-route contact satisfies `CertR`: on its (unique)
tagged split the verdict accepts, the monitor never contacts and stays within the budget, and the router fold has
CC's certificate (alive; reuse, or the forgery's digest output is a birth, admissible, with every opened position
opened by an exposure).

Route: LR-5 (`noContact_caseC`'s argument: case (C), `¬SignedDigest`); the forgery's digest row is never a trial row
(`caseC_fresh_not_signer`, trial rows are signer queries) and is answered `N` everywhere, so its first occurrence
is a birth (`birthInv_*`); every opened position's honest leaf input is a verifier query (`verifyP_leaf_queried`),
clear for the final knowledge (`monitorRun_clear`), so its secret is disclosed by a signing step, whose digest
output is exposed unless the reuse flag is set (`covered_fold`); the exposures are at most the signing steps, i.e.
the log length (`taggedRecord_log`), at most `2^32 < proposalLength`.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactCert : DecidableEq T3.Cache := Classical.decEq _

/-! ## Coordinates of disclosures -/

theorem treeChild_inl {lay : Layer} {tree : Fin (2 ^ 31)} {level c : Nat} {x : Coord}
    (h : treeChild lay tree level c = some x) : ∃ n, x = .inl n := by
  unfold treeChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩

theorem ftsChild_inl {index : Fin (2 ^ 31)} {coord : Fin 7} {level c : Nat} {x : Coord}
    (h : ftsChild index coord level c = some x) : ∃ n, x = .inl n := by
  unfold ftsChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩

theorem not_inr_keygenDisclosed (s : CanonGraph.SecretIndex) : (.inr s : Coord) ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨_, _, _, _, hc⟩ := h
  obtain ⟨n, hn⟩ := treeChild_inl hc
  cases hn

/-- A disclosed FTS secret of a signature with digest output `N` is an opened position of `N`. -/
theorem secret_mem_signItems (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) (p : CanonGraph.FtsLeafPos)
    (h : (.inr (.inr p) : Coord) ∈ signItemsWith digitsOf N) : BPair.ofLeafPos p ∈ BPair.openedPositions N := by
  unfold signItemsWith at h
  rcases List.mem_append.mp h with h | h
  · unfold ftsItems at h
    rw [List.mem_flatMap] at h
    obtain ⟨coord, hcoord, h⟩ := h
    rw [List.mem_range] at hcoord
    rcases List.mem_append.mp h with h | h
    · unfold ftsOpened at h
      rw [List.mem_filterMap] at h
      obtain ⟨leaf, hleaf, hl⟩ := h
      rw [List.mem_map] at hleaf
      obtain ⟨s, hs, rfl⟩ := hleaf
      split_ifs at hl with h2048
      have hp := Sum.inr.inj (Sum.inr.inj (Option.some.inj hl))
      subst hp
      unfold BPair.openedPositions
      rw [List.mem_flatMap]
      refine ⟨⟨coord, hcoord⟩, List.mem_finRange _, ?_⟩
      rw [List.mem_map]
      refine ⟨s, hs, ?_⟩
      unfold BPair.ofLeafPos BPair.leafIndex BPair.outputIndex
      simp only [Prod.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · exact Fin.ext (Nat.mod_eq_of_lt hcoord).symm
      · exact Fin.ext (Nat.mod_eq_of_lt h2048)
    · exfalso
      unfold ftsProof at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := ftsChild_inl hc
        cases hn
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := ftsChild_inl hc
        cases hn
  · exfalso
    unfold layerItems at h
    rw [List.mem_flatMap] at h
    obtain ⟨lay, -, h⟩ := h
    rcases List.mem_append.mp h with h | h
    · unfold layerChains at h
      split_ifs at h
      · rw [List.mem_map] at h
        obtain ⟨i, -, hi⟩ := h
        unfold chainItem at hi
        split_ifs at hi <;> cases hi
      · cases h
    · unfold layerPath at h
      split_ifs at h
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := treeChild_inl hc
        cases hn
      · cases h

/-- The monitor's disclosures come from signing steps. -/
theorem disclosed_steps_mem (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)
    (steps : List TaggedStep) (mon : Monitor) (d : Coord)
    (hd : d ∈ (steps.foldl (Monitor.step U A q published) mon).disclosed) :
    d ∈ mon.disclosed ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧
      d ∈ signDisclosed A published request := by
  induction steps generalizing mon with
  | nil => exact Or.inl hd
  | cons s rest ih =>
      rw [List.foldl_cons] at hd
      rcases ih _ hd with h | ⟨r, o, e, hm, hr⟩
      · cases s with
        | world e =>
            change d ∈ (mon.event U A q e).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request out evs =>
            change d ∈ (mon.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, out, evs, List.mem_cons_self, h⟩
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hr⟩

/-! ## The honest leaf input of an FTS position -/

theorem posOf_probeInput (f : BPair.FtsCoord) (s : Digest) :
    Extract.posOf (BPair.probeInput f s) = some (CanonGraph.Node.ftsLeaf (BPair.toLeafPos f)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  rw [BPair.hdrBlock_probeInput]
  rfl

theorem slotValue_probeInput (f : BPair.FtsCoord) (s : Digest) : slotValue (BPair.probeInput f s) 2 = s := by
  rw [BPair.probeInput_eq]
  exact (slotValue_block4 0 _ s 0).2.1

/-! ## Trial rows are signer queries -/

theorem search_queried (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start k, start ≤ k → k < start + fuel →
      (∀ c', start ≤ c' → c' < k →
        digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) →
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) : T3.Spec.Domain) ∈
        queried A (digestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start k h1 h2; omega
  | succ fuel ih =>
      intro start k h1 h2 hrej
      rw [BPB.digestSearch_succ, queried_bind, BPB.queried_digest]
      by_cases hk : k = start
      · subst hk
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) k (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2')

theorem search_result (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start,
      (∀ c N, evalWithAnswerFn A (digestSearch rho m start fuel) = some (c, N) →
        ∃ k, start ≤ k ∧ k < start + fuel ∧ c = BitVec.ofNat 32 k ∧ ∀ c', start ≤ c' → c' < k →
          digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) ∧
      (evalWithAnswerFn A (digestSearch rho m start fuel) = none → ∀ c', start ≤ c' → c' < start + fuel →
          digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      refine ⟨fun c N h => ?_, fun _ c' h1 h2 => by omega⟩
      simp [digestSearch] at h
  | succ fuel ih =>
      intro start
      rw [BPB.digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hadm : digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure]
        refine ⟨fun c N h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨start, le_rfl, by omega, h.1.symm, fun c' h1 h2 => by omega⟩
      · rw [if_neg hadm]
        have hrej : digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = false := by
          simpa using hadm
        obtain ⟨ih1, ih2⟩ := ih (start + 1)
        refine ⟨fun c N h => ?_, fun h c' h1 h2 => ?_⟩
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih1 c N h
          refine ⟨k, by omega, by omega, hk3, fun c' h1 h2 => ?_⟩
          by_cases hc : c' = start
          · subst hc; exact hrej
          · exact hk4 c' (by omega) h2
        · by_cases hc : c' = start
          · subst hc; exact hrej
          · exact ih2 h c' (by omega) (by omega)

/-- **Trial rows of a published signing are queries of the signer.** -/
theorem trialRows_queried (A : Answers) (published : T3.Cache) (request : Security.Request)
    (hc : request.cache = published) (X : HashInput)
    (hX : X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message)) :
    (.inl (.inr X) : T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published request) := by
  set rho := honestNonce A request.message with hrho
  have hsd : LargeResidual.signDigest A request.message =
      evalWithAnswerFn A (digestSearch rho request.message 0 attemptLimit) := rfl
  have hq : (.inl (.inr X) : T3.Spec.Domain) ∈ queried A (digestSearch rho request.message 0 attemptLimit) := by
    obtain ⟨r1, r2⟩ := search_result A rho request.message attemptLimit 0
    cases hfound : LargeResidual.signDigest A request.message with
    | none =>
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        exact search_queried A rho request.message attemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => r2 (hsd ▸ hfound) c' (Nat.zero_le _) (by omega))
    | some found =>
        obtain ⟨c, N⟩ := found
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        obtain ⟨k0, -, hk0, hck, hrej⟩ := r1 c N (hsd ▸ hfound)
        have hlim : attemptLimit = 2 ^ 20 := rfl
        have hct : c.toNat = k0 := by
          rw [hck, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        exact search_queried A rho request.message attemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => hrej c' (Nat.zero_le _) (by omega))
  unfold FullGame.authenticatedSign
  rw [queried_bind, BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc, signPayload_factor, queried_bind, BPB.queried_privateNonce]
  apply List.mem_append_right
  rw [queried_bind]
  exact List.mem_append_left _ hq

theorem seen_events_self (U : Finset HashInput) (events : List FirstHit.QueryEvent) (st : RouterState)
    (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) (he : (⟨b, .inl (.inr X), y⟩ : FirstHit.QueryEvent) ∈ events) :
    X ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => cases he
  | cons e rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact seen_events_mono' U rest _ X (seen_event_self U st b X y)
      · exact ih _ he

end SigGolfCandidate.T3.Security.LargeCoupling
