import SigGolfCandidate.T3.Secc.CaseCNearSearch
import SigGolfCandidate.T3.Secc.CaseCNearPay

/-!
# Stream CC: the bank invariant of the ghost lazy world, and the payoff it dominates

* `Replays rows rho m found`: from every rows cache extending `rows`, SEC's lazy digest search of `(rho, m)` returns
  `found` and adds nothing (`replays_of_search`: true right after a search, `Replays.mono`);
* `InvM`: every world exposure is a fresh exposure, the fresh list is not longer than the world's, and every signed
  message's search replays to a fresh exposure;
* `ΦI q`: the memory near potential on invariant states, `⊤` elsewhere;
* `payoff_le_ΦI`: CC's `nearPayoff` on the projected state is at most `ΦI`;
* `ΦI_initial ≤ q·(103 + 1/16)/2^128`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Search replay -/

/-- Cache extension. -/
def Extends (rows rows' : Sampling.RCache) : Prop := ∀ x a, rows x = some a → rows' x = some a

theorem Extends.refl (rows : Sampling.RCache) : Extends rows rows := fun _ _ h => h

theorem Extends.trans {r1 r2 r3 : Sampling.RCache} (h1 : Extends r1 r2) (h2 : Extends r2 r3) : Extends r1 r3 :=
  fun x a h => h2 x a (h1 x a h)

theorem search_replays_gen {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      Extends cache r.2 ∧ ∀ cache', Extends r.2 cache' → ∀ r' ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache'),
          r' = (r.1, cache') := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨Extends.refl _, fun cache' _ r' hr' => ?_⟩
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr'
      change r' ∈ support (Sampling.roRun secret (pure none) cache') at hr'
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
      exact hr'
  | succ fuel ih =>
      intro counter cache r hr
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      -- the first query: its answer is cached in `first.2`
      have hfirst' : Extends cache first.2 ∧ first.2 (inputs counter) = some first.1 := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            subst hfirst
            exact ⟨Extends.refl _, hc⟩
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            subst hfa
            refine ⟨fun x b hx => ?_, QueryCache.cacheQuery_self _ _ _⟩
            have hne : x ≠ inputs counter := fun he => by rw [he, hc] at hx; cases hx
            exact (QueryCache.cacheQuery_of_ne cache a hne).trans hx
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          obtain ⟨h1, h2⟩ := ih (counter + 1) first.2 r hr
          refine ⟨hfirst'.1.trans h1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ (h1 _ _ hfirst'.2)
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          exact h2 cache' hc' r' hr'
      | some value =>
          rw [hd] at hr
          simp only at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨hfirst'.1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ hfirst'.2
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
          exact hr'

/-- **The search replays.** -/
def Replays (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' → ∀ r' ∈ support (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) cache'),
    r' = (found, cache')

theorem Replays.mono {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : Replays rows rho m found) (hext : Extends rows rows') : Replays rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)

theorem replays_of_search (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (digestSearch rho m 0 attemptLimit) rows)) :
    Extends rows r.2 ∧ Replays r.2 rho m r.1 := by
  rw [Sampling.digestSearch_public] at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) Sampling.digestDecode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  rw [Sampling.digestSearch_public] at hr'
  exact h2 cache' hc r' hr'

/-! ## The invariant and the potential -/

/-- **The bank invariant** of a ghost memory. -/
def InvM (M : BPair.LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, Replays M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh

theorem invM_empty : InvM (BPair.LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [BPair.LazyMem.empty] at hv, by simp [BPair.LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [BPair.LazyMem.empty] at h

/-- The memory near potential of a ghost memory. -/
noncomputable def ghostPot (q : Nat) (M : BPair.LazyMem × NearGhost) : ENNReal :=
  nearMemPotential q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces

/-- **The bank potential of a ghost state**: `⊤` off the invariant. -/
noncomputable def ΦI (q : Nat) (s : GState) : ENNReal := if InvM s.memory then ghostPot q s.memory else ⊤

theorem ΦI_initial (q : Nat) : ΦI q initG ≤ (q : ENNReal) * (103 + 1 / 16) / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial q

theorem nearCoveredBy_mono {X Y : List HashOutput} (h : ∀ v ∈ X, v ∈ Y) {N : HashOutput} (hN : NearCoveredBy X N) :
    NearCoveredBy Y N := by
  obtain ⟨f, hf, hcov⟩ := hN
  exact ⟨f, hf, fun g hg hne => by
    obtain ⟨out, hout, ho⟩ := hcov g hg hne
    exact ⟨out, h out hout, ho⟩⟩

/-- **The payoff is dominated by the bank potential.** -/
theorem payoff_le_ΦI (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × GState) :
    nearPayoff q (r.1, projS r.2) ≤ ΦI q r.2 := by
  unfold ΦI
  split_ifs with hinv
  · unfold nearPayoff
    split_ifs with hp
    · obtain ⟨hb, hl, N, hN, hadm, hcov⟩ := hp
      exact mem_win q _ _ _ _ _ hb (hinv.2.1.trans hl) (Or.inr ⟨N, hN, hadm, nearCoveredBy_mono hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top

end SigGolfCandidate.T3.Security.CaseC
