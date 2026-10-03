import SigGolfCandidate.T3.Secc.CaseCBankReuse
import SigGolfCandidate.T3.Secc.CaseCExcess

/-!
# Stream CC: the bank potential and its one-step bound

`potential budget st` (zero once the ghost is dead or the budget is exceeded; `1 + reuse` once a reuse happened):

    Σ_{N ∈ targets} forecast (horizon − |X|) X N  +  reusePotential  +  (budget − count) · excessForecast(…)/2^128.

`potential_step`: for every interaction query, `E[potential after] ≤ potential before + birthCharge`, where a
birth (fresh in-budget digest query) costs `(theta + 1/1024)/2^128` and everything else costs nothing.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankStep : DecidableEq T3.Cache := Classical.decEq _

/-! ## Transfers between the recorded and the lazy run -/

theorem lazy_of_recorded {α : Type} (program : M α) (s : QueryRecorded.State) :
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
      LazyPrivate.run program (lazyOf s) := by
  calc
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
        Prod.map id Prod.snd <$> (Prod.map id MonitoredPrivate.State.source <$>
          (Prod.map id QueryRecorded.State.base <$> QueryRecorded.run program s)) := by
      simp only [Functor.map_map]
      rfl
    _ = LazyPrivate.run program (lazyOf s) := by
      rw [QueryRecorded.run_erasure, MonitoredPrivate.run_erasure, CountedPrivate.run_erasure]
      rfl

theorem expected_recorded {α : Type} (program : M α) (s : QueryRecorded.State)
    (f : α × LazyPrivate.State → ENNReal) :
    expectedValue (QueryRecorded.run program s) (fun r => f (r.1, lazyOf r.2)) =
      expectedValue (LazyPrivate.run program (lazyOf s)) f := by
  rw [← lazy_of_recorded, expectedValue_map]

theorem recorded_lazy_support {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) :
    (r.1, lazyOf r.2) ∈ support (LazyPrivate.run program (lazyOf s)) := by
  rw [← lazy_of_recorded, support_map]
  exact ⟨r, hr, rfl⟩

theorem recorded_count_le {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) : countOf s ≤ countOf r.2 :=
  CreationGame.recorded_count_monotone program s r hr

/-! ## The potential -/

/-- Forecasts of all targets. -/
noncomputable def bankValue (g : Ghost) : ENNReal :=
  (g.targets.map fun N => forecast (horizon - g.exposures.length) g.exposures N).sum

/-- The remaining-budget excess term (the creation charge above `theta`, paid in advance). -/
noncomputable def excessTerm (budget count : Nat) (g : Ghost) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * excessForecast (horizon - g.exposures.length) g.exposures / 2 ^ 128

/-- The live potential, evaluated at a given count and lazy state. -/
noncomputable def livePotential (budget count : Nat) (g : Ghost) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + reusePotential lazy
  else bankValue g + reusePotential lazy + excessTerm budget count g

/-- **The bank potential.** -/
noncomputable def potential (budget : Nat) (st : BankState) : ENNReal :=
  livePotential budget (countOf st.2) st.1 (lazyOf st.2)

/-- The birth charge of a query. -/
noncomputable def birthCharge (budget : Nat) : LazyPrivate.Interaction.Domain → BankState → ENNReal
  | .inl (.inr x), st => if Birth budget x st.2 then (theta + 1 / 1024) / 2 ^ 128 else 0
  | _, _ => 0

theorem livePotential_count_anti (budget : Nat) {count count' : Nat} (h : count ≤ count') (g : Ghost)
    (lazy : LazyPrivate.State) : livePotential budget count' g lazy ≤ livePotential budget count g lazy := by
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
  · simp only [hr, if_false]
    apply add_le_add le_rfl
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast Nat.sub_le_sub_left h budget

theorem expectedValue_liftM {α : Type} (X : ProbComp α) (g : α → ENNReal) :
    expectedValue (liftM X : PMF α) g = expectedValue X g := by
  unfold expectedValue
  rfl

theorem expectedValue_pmf_map {α β : Type} (X : PMF α) (f : α → β) (g : β → ENNReal) :
    expectedValue (X.map f) g = expectedValue X (fun x => g (f x)) := by
  rw [← PMF.monad_map_eq_map, expectedValue_map]

/-! ## World queries in the lazy tables -/

theorem lazy_world_coin (n : Nat) (lazy : LazyPrivate.State)
    (r : SphincsSecurity.OracleWorld.Range (.inl n) × LazyPrivate.State)
    (hr : r ∈ support (LazyPrivate.run (forwardWorld (.inl n)) lazy)) : r.2 = lazy := by
  change r ∈ support (LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) lazy) at hr
  rw [LazyPrivate.run_query] at hr
  simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  change step ∈ support ((fun answer => (answer, lazy.2)) <$>
    ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
  rw [support_map] at hstep
  obtain ⟨_, _, rfl⟩ := hstep
  rfl

theorem lazy_world_cached (x : HashInput) (lazy : LazyPrivate.State) (a0 : HashOutput) (hx : lazy.2 x = some a0) :
    LazyPrivate.run (forwardWorld (.inr x)) lazy = pure (a0, lazy) := by
  change LazyPrivate.run (Sampling.publicHandler x) lazy = _
  rw [LazyPrivate.run_publicQuery, randomOracle.run_eq, hx]
  simp

theorem lazy_world_fresh (x : HashInput) (lazy : LazyPrivate.State) (hx : lazy.2 x = none)
    (f : HashOutput × LazyPrivate.State → ENNReal) :
    expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lazy) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => f (a, (lazy.1, lazy.2.cacheQuery x a))) := by
  change expectedValue (LazyPrivate.run (Sampling.publicHandler x) lazy) f = _
  rw [LazyPrivate.run_publicQuery, expectedValue_bind]
  simp only [expectedValue_pure]
  exact Sampling.expectedValue_fresh x lazy.2 hx (fun result => f (result.1, (lazy.1, result.2)))

theorem digestRowOf_isDigest {x : HashInput} {m : Message} (h : DigestRowOf x m) : IsDigestInput x := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨p.1, m, BitVec.ofNat 32 p.2.val, rfl⟩

theorem reusePotential_public_nondigest (s : LazyPrivate.State) (x : HashInput) (a : HashOutput)
    (hx : s.2 x = none) (hnd : ¬IsDigestInput x) :
    reusePotential (s.1, s.2.cacheQuery x a) ≤ reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m
  split_ifs with h
  · have h1 := reuseMass_cacheQuery_le s.2 x a hx m
    rw [if_neg (fun hr => hnd (digestRowOf_isDigest hr)), ENNReal.zero_div, add_zero] at h1
    exact h1
  · exact le_rfl


theorem bankValue_birth (g : Ghost) (a : HashOutput) :
    bankValue { g with targets := g.targets ++ [a] } =
      bankValue g + forecast (horizon - g.exposures.length) g.exposures a := by
  simp [bankValue, List.map_append, List.sum_append]

theorem livePotential_alive (budget count : Nat) (g : Ghost) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = false) :
    livePotential budget count g lazy = bankValue g + reusePotential lazy + excessTerm budget count g := by
  simp [livePotential, hd, hb, hr]

theorem livePotential_reused (budget count : Nat) (g : Ghost) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = true) :
    livePotential budget count g lazy = 1 + reusePotential lazy := by
  simp [livePotential, hd, hb, hr]

theorem livePotential_reuse_mono (budget count : Nat) (g : Ghost) {lazy lazy' : LazyPrivate.State}
    (h : reusePotential lazy' ≤ reusePotential lazy) :
    livePotential budget count g lazy' ≤ livePotential budget count g lazy := by
  unfold livePotential
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h
  · exact add_le_add (add_le_add le_rfl h) le_rfl

theorem excessTerm_succ (budget count : Nat) (g : Ghost) (hc : count < budget) :
    excessTerm budget count g = excessTerm budget (count + 1) g +
      excessForecast (horizon - g.exposures.length) g.exposures / 2 ^ 128 := by
  unfold excessTerm
  have hn : budget - count = (budget - (count + 1)) + 1 := by omega
  rw [hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]

/-- **One world query.** -/
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState) :
    expectedValue ((bankImpl published budget (.inl input)).run st) (fun r => potential budget r.2) ≤
      potential budget st + birthCharge budget (.inl input) st := by
  have hunfold : expectedValue ((bankImpl published budget (.inl input)).run st) (fun r => potential budget r.2) =
      expectedValue (QueryRecorded.run (forwardWorld input) st.2)
        (fun r => potential budget (ghostWorld budget input st.1 st.2 r.1, r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [expectedValue_pmf_map, expectedValue_liftM]
  rw [hunfold]
  cases input with
  | inl n =>
      have hb : birthCharge budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (recorded_lazy_support _ _ r hr)
      have hc := recorded_count_le _ _ r hr
      change livePotential budget (countOf r.2) st.1 (lazyOf r.2) ≤ livePotential budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact livePotential_count_anti budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change livePotential budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          expected_recorded _ _
            (fun r => livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : birthCharge budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact livePotential_count_anti budget (Nat.le_succ _) g _
      | none =>
          rw [lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : birthCharge budget (.inl (.inr x)) st = (theta + 1 / 1024) / 2 ^ 128 := by
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
            · -- after a reuse only the reuse potential remains
              have hpt : potential budget st = 1 + reusePotential lz :=
                livePotential_reused budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + reusePotential lz + admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [livePotential_reused budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr, add_assoc]
                  exact add_le_add le_rfl (reusePotential_public_le lz x a hx)
                _ = 1 + reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + reusePotential lz + (1 / 1024) / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right expected_admInd_tight _)
                _ ≤ _ := by
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : potential budget st = bankValue g + reusePotential lz + excessTerm budget c g :=
                livePotential_alive budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => forecast R g.exposures a) ≤
                  (theta + excessForecast R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact average_forecast_le R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    bankValue g + forecast R g.exposures a + (reusePotential lz + admInd a / 2 ^ 128) +
                      excessTerm budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [livePotential_alive budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr', bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (reusePotential_public_le lz x a hx)) le_rfl
                _ = bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => forecast R g.exposures a) +
                    (reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd / 2 ^ 128) +
                    excessTerm budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ bankValue g + (theta + excessForecast R g.exposures) / 2 ^ 128 +
                    (reusePotential lz + (1 / 1024) / 2 ^ 128) + excessTerm budget (c + 1) g := by
                  gcongr
                  exact expected_admInd_tight
                _ = bankValue g + reusePotential lz +
                    (excessTerm budget (c + 1) g + excessForecast R g.exposures / 2 ^ 128) +
                    (theta + 1 / 1024) / 2 ^ 128 := by
                  rw [ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← excessTerm_succ budget c g hlt]
          · have hcb : birthCharge budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ livePotential budget (c + 1) g lz :=
                  livePotential_reuse_mono budget (c + 1) g (reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ livePotential budget c g lz := livePotential_count_anti budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [livePotential, hover]

/-! ## Signing requests: support facts -/

theorem sign_other_nonce (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    result.2.1 (.inr (.inl m')) = lz.1 (.inr (.inl m')) :=
  NonceFreshness.run_preserves m' _
    (MonitoredPrivate.authenticatedRecord_avoids m' published request (Or.inr (Ne.symm hm'))) lz result hr

theorem sign_other_reuseMass (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    reuseMass result.2.2 m' = reuseMass lz.2 m' := by
  have hext := SourceReplay.run_extends _ lz result hr
  unfold reuseMass
  congr 1
  apply tsum_congr
  intro p
  unfold admissibleEntry
  cases hc : lz.2 (Sampling.digestTrial p.1 m' p.2.val) with
  | some a =>
      rw [hext.2 hc]
  | none =>
      have hn : result.2.2 (Sampling.digestTrial p.1 m' p.2.val) = none := by
        by_contra hne
        have hrow := signer_new_rows published request lz result hr _ hc hne
          (digestRowOf_isDigest ⟨p, rfl⟩)
        exact hm' (digestRowOf_unique ⟨p, rfl⟩ hrow)
      rw [hn]

theorem sign_published_nonce (published : T3.Cache) (m : Message) (lz : LazyPrivate.State)
    (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) lz)) :
    result.2.1 (.inr (.inl m)) ≠ none := by
  rw [FullGame.authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, _, hr⟩ := hr
  simp only [if_true] at hr
  rw [payloadRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨nonce, hnonce, hr⟩ := hr
  have hext := SourceReplay.run_extends _ nonce.2 result hr
  unfold privateNonce at hnonce
  rw [LazyPrivate.run_bind, mem_support_bind_iff] at hnonce
  obtain ⟨hashed, hhashed, hn⟩ := hnonce
  rw [LazyPrivate.run_pure, mem_support_pure_iff] at hn
  have hc := SourceReplay.hash_query_caches (.inr (.inr (.inl m))) trivial mac.2 hashed hhashed
  have hc' : nonce.2.1 (.inr (.inl m)) = some hashed.1 := by rw [hn]; exact hc
  rw [hext.1 hc']
  simp

theorem sign_unpublished (published : T3.Cache) (request : Request) (hc : request.cache ≠ published)
    (lz : LazyPrivate.State) (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) lz)) :
    result.2.1 (.inr (.inl request.message)) = lz.1 (.inr (.inl request.message)) ∧ result.2.2 = lz.2 := by
  rw [FullGame.authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, hmac, hr⟩ := hr
  simp only [hc, if_false, LazyPrivate.run_pure, mem_support_pure_iff] at hr
  subst hr
  exact LazyPrivate.privateMac_preserves_nonce request.cache.region request.message lz mac hmac

/-! ## Signing requests: the step -/

/-- `ghostSign` read through the lazy tables of the record. -/
noncomputable def ghostSignL (published : T3.Cache) (request : Request) (g : Ghost) (before : QueryRecorded.State)
    (record : (Option Signature × Option HashOutput) × LazyPrivate.State) : Ghost :=
  if FreshSigning published request before then
    if horizon ≤ g.exposures.length then
      { g with dead := true, log := g.log ++ [⟨request, record.1.1⟩] }
    else
      { g with exposures := g.exposures ++ record.1.2.toList,
               reused := g.reused || decide (Reuse (lazyOf before).2 (nonceOf record.2 request.message)
                 request.message),
               log := g.log ++ [⟨request, record.1.1⟩] }
  else { g with log := g.log ++ [⟨request, record.1.1⟩] }

theorem ghostSign_eq (published : T3.Cache) (request : Request) (g : Ghost) (before : QueryRecorded.State)
    (record : (Option Signature × Option HashOutput) × QueryRecorded.State) :
    ghostSign published request g before record = ghostSignL published request g before (record.1, lazyOf record.2) :=
  rfl

theorem livePotential_log (budget count : Nat) (g : Ghost) (l : QueryLog Requests) (lazy : LazyPrivate.State) :
    livePotential budget count { g with log := l } lazy = livePotential budget count g lazy := rfl

/-- The selection weight of a fresh signing: the bank and excess terms after appending the selection. -/
noncomputable def signWeight (budget count : Nat) (g : Ghost) (A : HashOutput) : ENNReal :=
  bankValue { g with exposures := g.exposures ++ [A] } + excessTerm budget count { g with exposures := g.exposures ++ [A] }

theorem expectedValue_list_sum {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]

theorem freshPrice_signWeight (budget count : Nat) (g : Ghost) (hlen : g.exposures.length < horizon) :
    Sampling.WeightedSelection.freshPrice (signWeight budget count g) = bankValue g + excessTerm budget count g := by
  rw [← expected_accepted]
  have hR : horizon - (g.exposures ++ [default]).length + 1 = horizon - g.exposures.length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hR' : ∀ A : HashOutput, horizon - (g.exposures ++ [A]).length = horizon - g.exposures.length - 1 := by
    intro A
    simp only [List.length_append, List.length_singleton]
    omega
  have hRR : horizon - g.exposures.length - 1 + 1 = horizon - g.exposures.length := by omega
  unfold signWeight bankValue excessTerm
  rw [expectedValue_add]
  simp only [hR']
  rw [expectedValue_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    rw [forecast_step, hRR]
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => ((budget - count : Nat) : ENNReal) *
        excessForecast (horizon - g.exposures.length - 1) (g.exposures ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => ((budget - count : Nat) : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ *
          excessForecast (horizon - g.exposures.length - 1) (g.exposures ++ [A]) by
      funext A; ring]
    rw [pmf_expectedValue_left_mul, excessForecast_step, hRR]
    ring

/-- **One signing request**: the potential is a supermartingale step (no charge). -/
theorem sign_step (published : T3.Cache) (budget : Nat) (request : Request) (st : BankState) :
    expectedValue ((bankImpl published budget (.inr request)).run st) (fun r => potential budget r.2) ≤
      potential budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((bankImpl published budget (.inr request)).run st) (fun r => potential budget r.2) =
      expectedValue (QueryRecorded.run (FullGame.authenticatedRecord published request) st.2)
        (fun r => potential budget (ghostSign published request st.1 st.2 r, r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [expectedValue_pmf_map, expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (FullGame.authenticatedRecord published request) st.2)
        (fun r => livePotential budget c (ghostSignL published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change livePotential budget (countOf r.2) (ghostSign published request st.1 st.2 r) (lazyOf r.2) ≤ _
      rw [ghostSign_eq]
      exact livePotential_count_anti budget (recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published request) lz)
        (fun r => livePotential budget c (ghostSignL published request g st.2 r) r.2) :=
      expected_recorded _ _ (fun r => livePotential budget c (ghostSignL published request g st.2 r) r.2)
    _ ≤ potential budget st := ?_
  change _ ≤ livePotential budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  · -- not a fresh published signing: only the log grows, the reuse potential does not increase
    apply expectedValue_le_of_support
    intro r hr
    simp only [ghostSignL, hfresh, if_false, livePotential_log]
    apply livePotential_reuse_mono
    apply reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached
      intro hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := sign_unpublished published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => sign_other_nonce published request lz r hr m' hm'
    · exact fun m' hm' => sign_other_reuseMass published request lz r hr m' hm'
  by_cases hhor : horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSignL, hfresh, hhor, livePotential]
  have hlen : g.exposures.length < horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSignL, hfresh, hhor, livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSignL, hfresh, hhor, livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz),
      reusePotential r.2 + reuseMass lz.2 m ≤ reusePotential lz := fun r hr =>
    reusePotential_sign_le lz r.2 m hnonce (sign_published_nonce cache m lz r hr)
      (fun m' hm' => sign_other_nonce cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => sign_other_reuseMass cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (ghostSignL cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [ghostSignL, hfr, hhor, hd']
  have hreu : ∀ r, (ghostSignL cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (Reuse (lazyOf st.2).2 (nonceOf r.2 m) m)) := by
    intro r; simp [ghostSignL, hfr, hhor]
  have hexp : ∀ r, (ghostSignL cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [ghostSignL, hfr, hhor]
  have htar : ∀ r, (ghostSignL cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [ghostSignL, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [livePotential_reused budget c (ghostSignL cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      livePotential_reused budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P := bankValue g + excessTerm budget c g with hP
  let Fmain : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if Reuse lz.2 (nonceOf r.2 m) m then 1 else r.1.2.elim P (signWeight budget c g)
  have hpoint : ∀ r, livePotential budget c (ghostSignL cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + reusePotential r.2 := by
    intro r
    by_cases hre : Reuse lz.2 (nonceOf r.2 m) m
    · have hru : (ghostSignL cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [livePotential_reused budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (ghostSignL cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [livePotential_alive budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : bankValue (ghostSignL cache ⟨m, cache⟩ g st.2 r) =
          bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold bankValue; rw [htar r, hexp r]
      have het : excessTerm budget c (ghostSignL cache ⟨m, cache⟩ g st.2 r) =
          excessTerm budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
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
    _ ≤ expectedValue (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz)
          (fun r => reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P + reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz)
          (fun r => reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply fresh_signing_kernel cache m lz hnonce Fmain (signWeight budget c g) P
        (le_of_eq (freshPrice_signWeight budget c g hlen))
      intro r _
      exact le_rfl
    _ = P + (expectedValue (LazyPrivate.run (FullGame.authenticatedRecord cache ⟨m, cache⟩) lz)
          (fun r => reusePotential r.2 + reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P + reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = livePotential budget c g lz := by
      rw [livePotential_alive budget c g lz hd' hb hr', hP]
      ring

end SigGolfCandidate.T3.Security.CaseC
