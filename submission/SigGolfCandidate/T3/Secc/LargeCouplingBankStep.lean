import SigGolfCandidate.T3.Secc.LargeCouplingBankQuery

/-!
# LR-34 (bank, one query): `bank_routeQuery`

For a lazy world state and a router state in the bank invariant, within the budget, one routed adversary/verifier
query is a supermartingale step of `psi q st + slackT q ws` (stops pay their `slackT`).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Step
variable {U : Finset HashInput}

/-- The invariant after a query of `X` whose request changed only the row of `X` (kept cached when it is a seen,
non-trial digest row). -/
theorem BankInv.after' {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hrows : ∀ row : Cell U, row.1 ≠ X → ws'.rows row = ws.rows row)
    (hX : ∀ hX : X ∈ U, IsDigestRow X → X ∉ st.trials → ∃ y, st.cache X = some y ∧ ws'.rows ⟨X, hX⟩ = some y)
    (hcalls : ws'.counters.calls = ws.counters.calls + 1) (hmass : ws'.counters.mass ≤ ws'.counters.calls)
    (hcand : ∀ m : Message, ws'.candidates (.inr m) = ws.candidates (.inr m)) : BankInv U ws' (st.after X) := by
  refine ⟨by rw [hcalls, h.calls]; rfl, hmass, (h.births).trans (Nat.le_succ _),
    fun m hm => by rw [hcand m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    have hne : X' ≠ X := fun he => hs (by rw [he]; exact List.mem_cons_self)
    rw [hrows ⟨X', hX'⟩ hne]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    by_cases hne : X' = X
    · subst hne
      exact hX hX' hd ht
    · rw [hrows ⟨X', hX'⟩ hne]
      have hs' : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs with he | hm
        · exact absurd he hne
        · exact hm
      exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)

theorem slackT_eq_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s'.counters.mass = s.counters.mass) : slackT q s' = slackT q s := by
  unfold slackT; rw [h]

theorem slackT_le_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s.counters.mass ≤ s'.counters.mass) : slackT q s' ≤ slackT q s := by
  unfold slackT
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.sub_le_sub_left h q

/-- One unit of mass pays a birth. -/
theorem birth_pay (m q : Nat) (hm : m < q) (p : ENNReal) :
    p + (CaseC.theta + 1 / 1024) / 2 ^ 128 + ((q - (m + 1) : Nat) : ENNReal) / 2 ^ 128 ≤
      p + ((q - m : Nat) : ENNReal) / 2 ^ 128 := by
  rw [add_assoc]
  apply add_le_add le_rfl
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  have hq : q - m = (q - (m + 1)) + 1 := by omega
  rw [hq, Nat.cast_add, Nat.cast_one, add_comm ((q - (m + 1) : Nat) : ENNReal)]
  exact add_le_add CaseC.theta_add_sixteenth_le_one le_rfl

theorem inlTest_guess (c : Coord) (v : Digest) (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨some (.inl c, v), hit⟩ :=
  ⟨fun g hg => ⟨c, by cases hg; rfl⟩, hh⟩

theorem inlTest_none (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨none, hit⟩ :=
  ⟨fun g hg => absurd hg (by simp), hh⟩

theorem hit_label_inl (c : Coord) : ∀ p, (Hit.label (Sum.inl c) : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' :=
  fun p hp => ⟨c, by cases hp; rfl⟩

theorem hit_target (t : Digest) : ∀ p, (Hit.target t : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' :=
  fun p hp => by cases hp

variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)

/-- **One routed query is a supermartingale step of the bank.** -/
theorem bank_routeQuery (a : AuxData) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (X : HashInput)
    (hinv : BankInv U ws st) (hlt : st.calls < q)
    (g : Option (LargeResidual.HashOutput × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal)
    (hstop : ∀ ws', g (none, ws') ≤ slackT q ws')
    (hcont : ∀ y st' ws', BankInv U ws' st' → st'.calls ≤ q → g (some (y, st'), ws') ≤ psi q st' + slackT q ws') :
    expectedValue (lazyRun aux q (routeQuery U a st X) ws) g ≤ psi q st + slackT q ws := by
  -- the outcome bound of a non-digest query
  have hnd : ¬(X ∈ U ∧ IsDigestRow X) →
      OutcomeLe U X ws (fun r : Option LargeResidual.HashOutput × _ => g (r.1.map fun y => (y, st.after X), r.2))
        (psi q st + slackT q ws) := by
    intro hX
    refine ⟨fun y s' hs => ?_, fun s' hs => ?_⟩
    · have hinv' := hinv.after X hX hs
      refine (hcont y (st.after X) s' hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
      rw [psi_after, slackT_eq_of_mass q hs.2.2.1]
    · exact (hstop s').trans ((le_of_eq (slackT_eq_of_mass q hs)).trans le_add_self)
  unfold routeQuery
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hndX : ¬(X ∈ U ∧ IsDigestRow X) := fun h => not_parsed_of_digest h.2 hp
      split
      · rename_i cs hfu
        rw [ev_lazy_map]
        exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_guess _ _ _ (hit_label_inl _)) ws _ _ ((hnd hndX).map U _)
      · rename_i hfu
        apply ev_discloseAll_le
        intro pairs s1 hd
        split
        · rw [lazy_discloseReq]
          apply ev_bind_le
          intro v
          rw [lazy_pure, expectedValue_pure]
          apply ((hnd hndX).of_disc U hd).1
          refine ⟨fun row hr => rfl, rfl, rfl, fun m => ?_⟩
          simp only [discloseTableValue]
          rw [Function.update_of_ne (by simp)]
        · rw [ev_lazy_map]
          exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_none _ (hit_label_inl _))
            s1 _ _ (((hnd hndX).of_disc U hd).map U _)
    · rw [dif_neg hp]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hndX : ¬(X ∈ U ∧ IsDigestRow X) := by
          intro h
          obtain ⟨L, m, ctr, hXe⟩ := he
          rw [hXe] at h
          exact encRow_not_digest L m ctr h.2
        split
        · rw [lazy_discloseReq]
          apply ev_bind_le
          intro msg
          have hd := discFrame_disclose U q ws (msgCoord (Classical.choose he)) msg
          split
          · rw [lazy_tickReq, lazy_pure, expectedValue_pure]
            apply ((hnd hndX).of_disc U hd).1
            exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩
          · rw [ev_lazy_map]
            exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_none _ (hit_target _))
              _ _ _ (((hnd hndX).of_disc U hd).map U _)
        · rw [ev_lazy_map]
          exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_guess _ _ _ (hit_target _)) ws _ _ ((hnd hndX).map U _)
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd, ev_lazy_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), lazy_readReq]
          simp only [lazy_pure, expectedValue_bind, expectedValue_pure, Option.map_some]
          have hcalls : ws.counters.calls + 1 ≤ q := by rw [hinv.calls]; omega
          have hmass_lt : ws.counters.mass < q := by have := hinv.mass; omega
          by_cases hfr : st.Fresh X
          · -- a birth
            have hnone : ws.rows ⟨X, hX⟩ = none := hinv.fresh X hX hd hfr.1 hfr.2
            have hc0 : st.cache X = none := hinv.cache_none hfr.1
            have hlen : st.births.length < q := by have := hinv.births; omega
            rw [reply, hnone]
            dsimp only
            simp only [if_pos hfr]
            have hpt : ∀ y : LargeResidual.HashOutput,
                g (some (y, st.born X y), readState q ws ⟨X, hX⟩ y .mass) ≤
                  psi q (st.born X y) + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
              intro y
              refine (hcont y _ _ (hinv.born q X hX hd hfr.1 y) (by
                change st.calls + 1 ≤ q; omega)).trans (le_of_eq ?_)
              congr 1
              unfold slackT
              simp only [readState, Counters.charge, if_pos hcalls]
            calc
              _ ≤ expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
                  (fun y => psi q (st.born X y) + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128) :=
                expectedValue_mono _ hpt
              _ ≤ psi q st + (CaseC.theta + 1 / 1024) / 2 ^ 128 + ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
                rw [expectedValue_add]
                exact add_le_add (psi_birth_le q st X hc0 hlen) (expectedValue_le_of_le _ fun _ => le_rfl)
              _ ≤ _ := birth_pay _ q hmass_lt _
          · simp only [if_neg hfr]
            by_cases ht : X ∈ st.trials
            · -- a trial row: any answer, the bank unchanged
              apply expectedValue_le_of_le
              intro y
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ ht' => absurd ht ht') rfl ?_ (fun _ => rfl)
                · simp only [readState]
                  rw [Function.update_of_ne (fun he' => hr (by rw [he']))]
                · simp only [readState, Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont y _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass q (by
                  simp only [readState, Counters.charge, if_pos hcalls]; omega))
            · -- a seen row: its cached answer
              have hs : X ∈ st.seen := by
                by_contra hs'
                exact hfr ⟨hs', ht⟩
              obtain ⟨v, hv1, hv2⟩ := hinv.seenRows X hX hd hs ht
              rw [reply, hv2]
              dsimp only
              rw [expectedValue_pure]
              have hupd : Function.update ws.rows ⟨X, hX⟩ (some v) = ws.rows := by
                rw [← hv2, Function.update_eq_self]
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ v .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ _ => ⟨v, hv1, ?_⟩) rfl ?_ (fun _ => rfl)
                · simp only [readState, hupd]
                · simp only [readState, hupd]; exact hv2
                · simp only [readState, Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont v _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass q (by
                  simp only [readState, Counters.charge, if_pos hcalls]; omega))
        · rw [if_neg hd, ev_lazy_map]
          exact ev_readReq_call_le U aux q ⟨X, hX⟩ ws _ _ ((hnd fun h => hd h.2).map U _)
  · rw [dif_neg hX, lazy_tickReq, lazy_pure, expectedValue_pure]
    apply (hnd fun h => hX h.1).1
    exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩

end Step

end SigGolfCandidate.T3.Security.LargeCoupling
