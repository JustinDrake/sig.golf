import SigGolfCandidate.ClaudeWCT.Bank.Kernel
import SigGolfCandidate.T3.Secc.CaseCBankMain

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open CaseC (theta IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankGame : DecidableEq T3.Cache := Classical.decEq _
abbrev Requests' (Sig : Type) := Request →ₒ Option Sig
abbrev Interaction' (Sig : Type) := SphincsSecurity.OracleWorld + Requests' Sig
structure Ghost (Sig : Type) where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  dead : Bool
  log : QueryLog (Requests' Sig)
def Ghost.empty {Sig : Type} : Ghost Sig := ⟨[], [], false, false, []⟩
abbrev BankState (Sig : Type) := Ghost Sig × QueryRecorded.State
noncomputable def ghostWorld {Sig : Type} (budget : Nat) :
    (input : SphincsSecurity.OracleWorld.Domain) → Ghost Sig → QueryRecorded.State →
      SphincsSecurity.OracleWorld.Range input → Ghost Sig
  | .inl _, g, _, _ => g
  | .inr x, g, before, answer =>
      if Birth budget x before then { g with targets := g.targets ++ [show HashOutput from answer] } else g
noncomputable def birthCharge {Sig : Type} (budget : Nat) : (Interaction' Sig).Domain → BankState Sig → ENNReal
  | .inl (.inr x), st => if Birth budget x st.2 then (theta + 1 / 64) / 2 ^ 128 else 0
  | _, _ => 0
noncomputable def birthWeight {Sig : Type} (budget : Nat) : (Interaction' Sig).Domain → QueryRecorded.State → ENNReal
  | .inl (.inr x), s => if Birth budget x s then 1 else 0
  | _, _ => 0
theorem birthCharge_eq {Sig : Type} (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    birthCharge budget input st = (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2 := by
  rcases input with (n | x) | request
  · simp [birthCharge, birthWeight]
  · simp only [birthCharge, birthWeight]
    split_ifs <;> simp
  · simp [birthCharge, birthWeight]
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
noncomputable def ghostSign (published : T3.Cache) (request : Request) (g : Ghost Sig) (before : QueryRecorded.State)
    (record : (Option Sig × Option HashOutput) × LazyPrivate.State) : Ghost Sig :=
  if FreshSigning published request before then
    if S.horizon ≤ g.exposures.length then
      { g with dead := true, log := g.log ++ [⟨request, record.1.1⟩] }
    else
      { g with exposures := g.exposures ++ record.1.2.toList,
               reused := g.reused || decide (S.Reuse (lazyOf before).2 (CaseC.nonceOf record.2 request.message)
                 request.message),
               log := g.log ++ [⟨request, record.1.1⟩] }
  else { g with log := g.log ++ [⟨request, record.1.1⟩] }
noncomputable def source (published : T3.Cache) : QueryImpl (Interaction' Sig) M
  | .inl input => forwardWorld input
  | .inr request => Prod.fst <$> S.authenticatedRecord pay published request
noncomputable def bankImpl (published : T3.Cache) (budget : Nat) :
    QueryImpl (Interaction' Sig) (StateT (BankState Sig) PMF)
  | .inl input => StateT.mk fun st =>
      (liftM (QueryRecorded.run (forwardWorld input) st.2) : PMF _).map fun r =>
        (r.1, (ghostWorld budget input st.1 st.2 r.1, r.2))
  | .inr request => StateT.mk fun st =>
      (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2) : PMF _).map fun r =>
        (r.1.1, (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2))
noncomputable def recordedImpl (published : T3.Cache) : QueryImpl (Interaction' Sig) (StateT QueryRecorded.State PMF) :=
  fun input => StateT.mk fun s => (liftM (QueryRecorded.run (S.source pay published input) s) : PMF _)
theorem bank_query_project (published : T3.Cache) (budget : Nat) (input : (Interaction' Sig).Domain)
    (st : BankState Sig) :
    Prod.map id Prod.snd <$> (S.bankImpl pay published budget input).run st =
      (liftM (QueryRecorded.run (S.source pay published input) st.2) : PMF _) := by
  cases input with
  | inl input =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change PMF.map id _ = _
      rw [PMF.map_id]
      rfl
  | inr request =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change _ = (liftM (QueryRecorded.run (Prod.fst <$> S.authenticatedRecord pay published request) st.2) : PMF _)
      rw [QueryRecorded.run_map, liftM_map, ← PMF.monad_map_eq_map]
      rfl
theorem bank_project {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    Prod.map id Prod.snd <$> (simulateQ (S.bankImpl pay published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (S.source pay published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure, liftM_pure, map_pure]
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [simulateQ_bind, simulateQ_spec_query, QueryRecorded.run_bind, liftM_bind]
      rw [← S.bank_query_project pay published budget input st, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2
noncomputable def bankValue (g : Ghost Sig) : ENNReal :=
  (g.targets.map fun N => S.forecast (S.horizon - g.exposures.length) g.exposures N).sum
noncomputable def excessTerm (budget count : Nat) (g : Ghost Sig) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * S.excessForecast (S.horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + S.reusePotential lazy
  else S.bankValue g + S.reusePotential lazy + S.excessTerm budget count g
noncomputable def potential (budget : Nat) (st : BankState Sig) : ENNReal :=
  S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
theorem livePotential_count_anti (budget : Nat) {count count' : Nat} (h : count ≤ count') (g : Ghost Sig)
    (lazy : LazyPrivate.State) : S.livePotential budget count' g lazy ≤ S.livePotential budget count g lazy := by
  unfold livePotential
  by_cases hd : g.dead = true
  · simp [hd]
  by_cases hb : budget < count'
  · simp [hd, hb]
  have hb0 : ¬budget < count := by omega
  have hd' : g.dead = false := by simpa using hd
  simp only [hd', hb, hb0, Bool.false_eq_true, false_or, if_false]
  by_cases hr : g.reused = true
  · simp only [hr, if_true, le_refl]
  · simp only [hr]
    apply add_le_add le_rfl
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast Nat.sub_le_sub_left h budget
theorem bankValue_birth (g : Ghost Sig) (a : HashOutput) :
    S.bankValue { g with targets := g.targets ++ [a] } =
      S.bankValue g + S.forecast (S.horizon - g.exposures.length) g.exposures a := by
  simp [bankValue, List.map_append, List.sum_append]
theorem livePotential_alive (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = false) :
    S.livePotential budget count g lazy = S.bankValue g + S.reusePotential lazy + S.excessTerm budget count g := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reused (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = true) :
    S.livePotential budget count g lazy = 1 + S.reusePotential lazy := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reuse_mono (budget count : Nat) (g : Ghost Sig) {lazy lazy' : LazyPrivate.State}
    (h : S.reusePotential lazy' ≤ S.reusePotential lazy) :
    S.livePotential budget count g lazy' ≤ S.livePotential budget count g lazy := by
  unfold livePotential
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h
  · exact add_le_add (add_le_add le_rfl h) le_rfl
theorem excessTerm_succ (budget count : Nat) (g : Ghost Sig) (hc : count < budget) :
    S.excessTerm budget count g = S.excessTerm budget (count + 1) g +
      S.excessForecast (S.horizon - g.exposures.length) g.exposures / 2 ^ 128 := by
  unfold excessTerm
  have hn : budget - count = (budget - (count + 1)) + 1 := by omega
  rw [hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]
theorem livePotential_log (budget count : Nat) (g : Ghost Sig) (l : QueryLog (Requests' Sig))
    (lazy : LazyPrivate.State) :
    S.livePotential budget count { g with log := l } lazy = S.livePotential budget count g lazy := rfl
theorem world_unfold (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (f : BankState Sig → ENNReal) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => f r.2) =
      expectedValue (QueryRecorded.run (forwardWorld input) st.2)
        (fun r => f (ghostWorld budget input st.1 st.2 r.1, r.2)) := by
  change expectedValue (PMF.map _ (liftM _)) _ = _
  rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st (S.potential budget)]
  cases input with
  | inl n =>
      have hb : birthCharge (Sig := Sig) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change S.livePotential budget (countOf r.2) st.1 (lazyOf r.2) ≤
        S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact S.livePotential_count_anti budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change S.livePotential budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact S.livePotential_count_anti budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = (theta + 1 / 64) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : S.potential budget st = 1 + S.reusePotential lz :=
                S.livePotential_reused budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_reused budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + (1 / 64) / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : S.potential budget st = S.bankValue g + S.reusePotential lz + S.excessTerm budget c g :=
                S.livePotential_alive budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (theta + S.excessForecast R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact S.average_forecast_le R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      S.excessTerm budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_alive budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    S.excessTerm budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (theta + S.excessForecast R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + (1 / 64) / 2 ^ 128) + S.excessTerm budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    (S.excessTerm budget (c + 1) g + S.excessForecast R g.exposures / 2 ^ 128) +
                    (theta + 1 / 64) / 2 ^ 128 := by
                  rw [ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← S.excessTerm_succ budget c g hlt]
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ S.livePotential budget (c + 1) g lz :=
                  S.livePotential_reuse_mono budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ S.livePotential budget c g lz := S.livePotential_count_anti budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [livePotential, hover]
noncomputable def signWeight (budget count : Nat) (g : Ghost Sig) (A : HashOutput) : ENNReal :=
  S.bankValue { g with exposures := g.exposures ++ [A] } +
    S.excessTerm budget count { g with exposures := g.exposures ++ [A] }
theorem freshPrice_signWeight (budget count : Nat) (g : Ghost Sig) (hlen : g.exposures.length < S.horizon) :
    S.freshPrice (S.signWeight budget count g) = S.bankValue g + S.excessTerm budget count g := by
  rw [← S.expected_accepted]
  have hR' : ∀ A : HashOutput, S.horizon - (g.exposures ++ [A]).length = S.horizon - g.exposures.length - 1 := by
    intro A
    simp only [List.length_append, List.length_singleton]
    omega
  have hRR : S.horizon - g.exposures.length - 1 + 1 = S.horizon - g.exposures.length := by omega
  unfold signWeight bankValue excessTerm
  rw [expectedValue_add]
  simp only [hR']
  rw [CaseC.expectedValue_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    rw [S.forecast_step, hRR]
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => ((budget - count : Nat) : ENNReal) *
        S.excessForecast (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => ((budget - count : Nat) : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ *
          S.excessForecast (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, S.excessForecast_step, hRR]
    ring
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => S.potential budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.potential budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change S.livePotential budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact S.livePotential_count_anti budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ S.potential budget st := ?_
  change _ ≤ S.livePotential budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [ghostSign, hfresh, if_false, livePotential_log]
    apply S.livePotential_reuse_mono
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [S.livePotential_reused budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      S.livePotential_reused budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + S.excessTerm budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' (S.signWeight budget c g)
  have hpoint : ∀ r, S.livePotential budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [S.livePotential_reused budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [S.livePotential_alive budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold bankValue; rw [htar r, hexp r]
      have het : S.excessTerm budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.excessTerm budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain (S.signWeight budget c g) P'
        (le_of_eq (S.freshPrice_signWeight budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = S.livePotential budget c g lz := by
      rw [S.livePotential_alive budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget input st := by
  cases input with
  | inl input => exact S.world_step pay published budget input st
  | inr request => exact (S.sign_step pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => S.potential budget r.2) ≤
      S.potential budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (birthCharge budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            S.potential budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              (birthCharge budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => S.potential budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                (birthCharge budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ (S.potential budget st + birthCharge budget input st) + _ :=
          add_le_add (S.potential_step pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget) program (g, s) =
      (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact birthCharge_eq budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
theorem potential_initial_le (budget : Nat) (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.potential budget ((Ghost.empty : Ghost Sig), generated.2) ≤
      (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he := S.excessForecast_initial
      simpa [Ghost.empty] using he
noncomputable def bankExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    PMF (Bool × BankState Sig) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ (S.bankImpl pay generated.1.2 budget) (rest generated.1.1 generated.1.2)).run (Ghost.empty, generated.2)
noncomputable def recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) :
    PMF (Bool × QueryRecorded.State) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (liftM (QueryRecorded.run (simulateQ (S.source pay generated.1.2) (rest generated.1.1 generated.1.2))
    generated.2) : PMF _)
theorem bank_experiment_project (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    (fun r : Bool × BankState Sig => (r.1, r.2.2)) <$> S.bankExperiment pay rest budget =
      S.recordedExperiment pay rest := by
  unfold bankExperiment recordedExperiment
  rw [map_bind]
  apply bind_congr
  intro generated
  exact S.bank_project pay generated.1.2 budget (rest generated.1.1 generated.1.2) (Ghost.empty, generated.2)
noncomputable def expectedBirths (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
    BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2) (birthWeight budget)
      (rest generated.1.1 generated.1.2) generated.2)
theorem bank_potential_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * S.excessRate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.potential_initial_le budget generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem potential_win (budget : Nat) (st : BankState Sig) (halive : st.1.dead = false)
    (hcount : countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, S.admissible N = true ∧ S.covered st.1.exposures N) :
    1 ≤ S.potential budget st := by
  have hnot : ¬budget < countOf st.2 := by omega
  unfold potential
  by_cases hr : st.1.reused = true
  · rw [S.livePotential_reused budget _ st.1 _ halive hnot hr]
    exact le_add_right le_rfl
  · have hr' : st.1.reused = false := by simpa using hr
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    rw [S.livePotential_alive budget _ st.1 _ halive hnot hr']
    calc
      (1 : ENNReal) ≤ S.score st.1.exposures N := S.one_le_score _ N hadm hcov
      _ ≤ S.forecast (S.horizon - st.1.exposures.length) st.1.exposures N := S.score_le_forecast _ _ _
      _ ≤ S.bankValue st.1 := List.le_sum_of_mem (List.mem_map_of_mem hN)
      _ ≤ _ := le_self_add.trans le_self_add
theorem bank_event_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le pay hNotDigest hAvoids rest budget)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
end FtsBankSpec
end ClaudeWCT.Bank
