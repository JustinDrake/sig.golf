import SigGolfCandidate.T3.Secc.LargeCouplingBankSign

/-!
# LR-34 (bank, the run): the bank potential is a supermartingale of the lazy router

`bankPay q r` — the bank potential of a finished router run plus the remaining mass allowance `slackT`.
**`bank_router`**: `E[bankPay | lazy router] ≤ psi q initial + q/2^128` (program induction over the routed
interaction and the routed verdict with `bank_routeQuery` and `bank_routeSign`; key disclosures and coins keep the
bank and its invariant).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingBankRun : DecidableEq T3.Cache := Classical.decEq _

/-- The bank's payoff of a router outcome: the potential of a finished run, plus the remaining allowance. -/
noncomputable def bankPay {U : Finset HashInput} (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi q st
    | _ => 0) + slackT q r.2

section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)

/-- **The routed interaction** keeps the bank a supermartingale (any continuation). -/
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi q st + slackT q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi q st + slackT q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws

/-- **The routed verdict** keeps the bank a supermartingale. -/
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi q st + slackT q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi q st + slackT q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls

theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [RouterState.initial]),
    fun p hp => absurd hp (by simp [RouterState.initial]), fun X hX => absurd hX (by simp [RouterState.initial])⟩

/-- **The bank in the lazy router**: `E[bankPay] ≤ psi q initial + q/2^128`. -/
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay q) ≤
      psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) = (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction (auxLaw initLaw) q hUpub a _ _ _ (bankPay q) ?_ ?_ ?_ RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict (auxLaw initLaw) q a _ (bankPay q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]

end Run

end SigGolfCandidate.T3.Security.LargeCoupling
