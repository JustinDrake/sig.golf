import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearCore
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyDefs

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le DigestRowOf
  digestRowOf_unique tsum_indicator_le_of_subsingleton)
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then nearSpec.reuseMass rows m else 0
theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : reuseC (rows.cacheQuery x a) nonces ≤ reuseC rows nonces + nearSpec.admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then nearSpec.reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then nearSpec.reuseMass rows m else 0) +
          (if DigestRowOf x m then nearSpec.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' (Function.update nonces m (some v)) + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then nearSpec.reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' nonces = reuseC rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]
theorem search_cache_frame {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      ∀ y, (∀ k, y ≠ inputs k) → r.2 y = cache y := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr y _
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | succ fuel ih =>
      intro counter cache r hr y hy
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfc : first.2 y = cache y := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            rw [hfirst]
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            rw [hfa]
            exact QueryCache.cacheQuery_of_ne cache a (hy counter)
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          exact (ih (counter + 1) first.2 r hr y hy).trans hfc
      | some value =>
          rw [hd] at hr
          change r ∈ support (Sampling.roRun secret (pure _) first.2) at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hfc
theorem digestSearch_cache_frame (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) nearSpec.decode _ fuel 0 cache r hr
theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m :=
    ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → nearSpec.reuseMass r.2 m' = nearSpec.reuseMass cache m' := by
  intro m' hm
  unfold ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [digestSearch_cache_frame secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else nearPotential ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128)
theorem mem_birth (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (x : HashInput) (hx : rows x = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun a : HashOutput => nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : births.length < q
  · obtain ⟨s, hs⟩ : ∃ s, q - births.length = s + 1 := ⟨q - births.length - 1, by omega⟩
    have hb : nearMemPotential q births exposures reused rows nonces =
        nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + ((s + 1 : Nat) : ENNReal) *
          ((1 / 16) / 2 ^ 128) := by
      unfold nearMemPotential
      rw [if_neg (by omega), hs]
    have ha : ∀ a : HashOutput, nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces =
        nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
          targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces } +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
      intro a
      unfold nearMemPotential
      have hl : (births ++ [a]).length = births.length + 1 := by simp
      rw [if_neg (by omega), show q - (births ++ [a]).length = s by omega]
    simp_rw [ha]
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
            nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
              targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces }) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := expectedValue_add_const_le _ _ _
      _ ≤ (nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + (1 / 16) / 2 ^ 128) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
        apply add_le_add _ le_rfl
        exact near_birth ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ s rfl _
          (fun a => reuseC_birth_le rows nonces x a hx)
      _ = _ := by
        push_cast
        ring
  · apply expectedValue_le_of_le
    intro a
    unfold nearMemPotential
    rw [if_pos (by simp; omega)]
    exact bot_le
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
        nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · apply expectedValue_le_of_le
    intro v
    apply expectedValue_le_of_le
    intro r
    unfold nearMemPotential
    rw [if_pos hq]
    exact bot_le
  push Not at hq
  set C0 := reuseC rows (Function.update nonces m (some 0)) with hC0
  have hupd : ∀ v : Digest, reuseC rows (Function.update nonces m (some v)) = C0 := by
    intro v
    unfold reuseC
    apply tsum_congr
    intro m'
    by_cases he : m' = m
    · subst he; simp
    · simp only [Function.update_of_ne he]
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      reuseC r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [reuseC_signed_eq rows r.2 _ m (by simp) (digestSearch_reuseMass secret v m fuel rows r hr), hupd]
  have hC : C0 + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
    rw [← hupd 0]
    exact reuseC_sign_le rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128) with hextra
  have hbefore : nearMemPotential q births exposures reused rows nonces = nearPotential b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)) =
        nearPotential ⟨births, exposures ++ (r.1.map Prod.snd).toList,
          reused || decide (nearSpec.Reuse rows v m), C0, q - births.length⟩ + extra := by
    intro v r hr
    unfold nearMemPotential
    rw [if_neg (by omega), hafter v r hr]
  have hreuse : ∀ (o : Option HashOutput), nearPotential ⟨births, exposures ++ o.toList, true, C0,
      q - births.length⟩ ≤ nearPotential { b with reused := true, reuse := C0 } := by
    intro o
    have hl : exposures.length ≤ (exposures ++ o.toList).length := by simp
    unfold nearPotential
    rw [hb]
    simp only [if_true]
    by_cases h2 : horizon < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : horizon < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add (near_sign b rows m C0 hC secret fuel hfuel) le_rfl
theorem mem_sign_repeat (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows rows' : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m ≠ none)
    (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    nearMemPotential q births exposures reused rows' nonces = nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [reuseC_signed_eq rows rows' nonces m hm hrows]
theorem mem_initial (q : Nat) :
    nearMemPotential q [] [] false ∅ (fun _ => none) ≤ (q : ENNReal) * 404 / 2 ^ 128 := by
  unfold nearMemPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
  have hC : reuseC ∅ (fun _ => none) = 0 := by
    unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
    simp
  have hn := near_initial q
  rw [show (⟨[], [], false, reuseC ∅ (fun _ => none), q⟩ : BankCore) = ⟨[], [], false, 0, q⟩ by rw [hC]]
  calc
    _ ≤ (q : ENNReal) * (6463 / 16) / 2 ^ 128 + (q : ENNReal) * ((1 / 16) / 2 ^ 128) := add_le_add hn le_rfl
    _ = (q : ENNReal) * ((6463 / 16) + 1 / 16) / 2 ^ 128 := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [ClaudeWCT.Numerics.WCTPrice.near_bound_add_charge]
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q) (hlen : exposures.length ≤ horizon)
    (h : reused = true ∨ ∃ N ∈ births, WCT9.admissible N = true ∧ Guess.NearCoveredBy exposures N) :
    1 ≤ nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact (near_win ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add
end ClaudeWCT.W9.T3.Security.CaseC
end

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Generic
variable {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
def SuperProg {β : Type} (W : OracleComp WPair.WSpecL β) : Prop :=
  ∀ s, expectedValue (SecretGuessObservation.runWith impl W s) (fun r => Φ r.2) ≤ Φ s
theorem runWith_bind' {β γ : Type} (W : OracleComp WPair.WSpecL β) (K : β → OracleComp WPair.WSpecL γ)
    (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (W >>= K) s =
      SecretGuessObservation.runWith impl W s >>= fun r => SecretGuessObservation.runWith impl (K r.1) r.2 := by
  simp only [SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]
theorem runWith_pure' {β : Type} (b : β) (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (pure b) s = pure (b, s) := by
  simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure]
theorem superProg_pure {β : Type} (b : β) : SuperProg impl Φ (pure b : OracleComp WPair.WSpecL β) := by
  intro s
  rw [runWith_pure', expectedValue_pure]
theorem superProg_bind {β γ : Type} {W : OracleComp WPair.WSpecL β} {K : β → OracleComp WPair.WSpecL γ}
    (hW : SuperProg impl Φ W) (hK : ∀ b, SuperProg impl Φ (K b)) : SuperProg impl Φ (W >>= K) := by
  intro s
  rw [runWith_bind', expectedValue_bind]
  exact (expectedValue_mono _ fun (r : β × SecretGuessObservation.State Guess.GCoord Digest Mem) =>
    hK r.1 r.2).trans (hW s)
end Generic
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
noncomputable local instance instDecidableEqCache_w9caseCNearWorld : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem interactionL_pure (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    WPair.interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (x : HashInput) (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (WPair.signL hU ω published request >>= fun signature => WPair.interactionL hU ω published (next signature) >>=
        fun rest => pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : CanonTable.Omega U) {β : Type} (value : β) :
    WPair.programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : CanonTable.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.programL hU ω (next coin)) := rfl
theorem programL_public (ω : CanonTable.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : CanonTable.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr c)) >>= next) =
      WPair.programL hU ω (next 0) := rfl
theorem interactionL_super (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ request, SuperProg impl Φ (WPair.signL hU ω published request)) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) : SuperProg impl Φ (WPair.interactionL hU ω published oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      rw [interactionL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [interactionL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [interactionL_request]
        exact superProg_bind impl Φ (hsign request) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
theorem programL_super (ω : CanonTable.Omega U)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x)) {β : Type}
    (program : M β) : SuperProg impl Φ (WPair.programL hU ω program) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [programL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [programL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [programL_private]
        exact ih (0 : HashOutput)
theorem worldGameCore_super (ω : CanonTable.Omega U) (adversary : AdversaryP)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ published request, SuperProg impl Φ (WPair.signL hU ω published request)) :
    SuperProg impl Φ (WPair.worldGameCore hU ω adversary) := by
  unfold WPair.worldGameCore
  exact superProg_bind impl Φ (interactionL_super hU impl Φ ω _ hcoin hhash (hsign _) _) fun _ =>
    superProg_bind impl Φ (programL_super hU impl Φ ω hcoin hhash _) fun _ => superProg_pure impl Φ _
end World
theorem expectedValue_liftM_pmf {α : Type} (p : PMF α) (g : α → ENNReal) :
    expectedValue (liftM p : SPMF α) g = expectedValue p g := by
  unfold expectedValue
  simp [SPMF.probOutput_eq_apply, PMF.probOutput_eq_apply]
theorem expectedValue_uniformOfFintype {α : Type} [Fintype α] [Nonempty α] (g : α → ENNReal) :
    expectedValue (PMF.uniformOfFintype α) g = BPORS.finiteAverage g := by
  unfold expectedValue BPORS.finiteAverage
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure NearGhost where
  reused : Bool
  lastFresh : Bool
  fresh : List HashOutput
def NearGhost.empty : NearGhost := ⟨false, false, []⟩
noncomputable def ghostStep (mem : LazyMem) : (i : AuxL) → AuxSpecL.Range i → NearGhost → NearGhost
  | .nonce m, v, g =>
      { g with lastFresh := decide (mem.nonces m = none),
               reused := g.reused || (decide (mem.nonces m = none) && decide (nearSpec.Reuse mem.rows v m)) }
  | .expose o, _, g => if g.lastFresh then { g with fresh := g.fresh ++ o.toList } else g
  | _, _, g => g
def projS (s : SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)) : WPair.WStateL :=
  ⟨s.allowed, s.retired, s.guesses, s.probes, s.memory.1⟩
noncomputable def envG (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest (LazyMem × NearGhost) where
  auxiliary st i := (fun r => (r.1, (r.2, ghostStep st.memory.1 i r.1 st.memory.2))) <$> env.auxiliary (projS st) i
  trial mem c v hit := (env.trial mem.1 c v hit, mem.2)
  disclosure mem c v := (env.disclosure mem.1 c v, mem.2)
abbrev GState := SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)
def initG : GState := SecretGuessObservation.initialState (LazyMem.empty, NearGhost.empty)
theorem projS_initG : projS initG = WPair.initL := rfl
section Project
variable (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat)
theorem liftM_map_pmf {α β : Type} (f : α → β) (p : PMF α) :
    (liftM (f <$> p) : SPMF β) = f <$> (liftM p : SPMF α) :=
  evalSPMF_map p f
theorem step_project (q : WPair.WSpecL.Domain) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> (SecretGuessObservation.forcedImpl (envG env) slot q).run s =
      (SecretGuessObservation.forcedImpl env slot q).run (projS s) := by
  rcases q with i | (⟨c, v⟩ | c)
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    change (fun r => (r.1, projS r.2)) <$> ((fun result => (result.1, { s with memory := result.2 })) <$>
      (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> env.auxiliary (projS s) i) :
        SPMF _)) =
      (fun result => (result.1, { projS s with memory := result.2 })) <$> (liftM (env.auxiliary (projS s) i) : SPMF _)
    rw [liftM_map_pmf, Functor.map_map, Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk]
    rw [Functor.map_map]
    have h1 : SecretGuessObservation.forcedTrial slot s c v =
        SecretGuessObservation.forcedTrial slot (projS s) c v := by
      have hA : (projS s).allowed = s.allowed := rfl
      have hP : (projS s).probes = s.probes := rfl
      have hR : (projS s).retired = s.retired := rfl
      unfold SecretGuessObservation.forcedTrial SecretGuessObservation.EligibleAt
      rw [hA, hP, hR]
    rw [h1]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    rw [Functor.map_map]
    rfl
theorem run_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState) :
    (fun r => (r.1, projS r.2)) <$>
        SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s =
      SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure b =>
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      rw [SecretGuessObservation.runWith_query_bind, SecretGuessObservation.runWith_query_bind, map_bind]
      simp_rw [ih]
      rw [← step_project env slot q s, bind_map_left]
theorem expectedValue_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState)
    (payoff : β × WPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s)) payoff =
      expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s)
        (fun r => payoff (r.1, projS r.2)) := by
  rw [← run_project env slot W s, expectedValue_map]
end Project
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev implG (slot : Nat) := SecretGuessObservation.forcedImpl (envG WPair.envL) slot
theorem ev_aux_bind {β : Type} (slot : Nat) (i : AuxL) (k : AuxSpecL.Range i → OracleComp WPair.WSpecL β)
    (s : GState) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i)) >>= k) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k r.1)
          { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) }) G) := by
  rw [SecretGuessObservation.runWith_query_bind, expectedValue_bind]
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
  change expectedValue ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) _ = _
  rw [expectedValue_map, expectedValue_liftM_pmf, expectedValue_map]
theorem searchL_succ (rho : Digest) (m : Message) (c fuel : Nat) :
    WPair.searchL rho m c (fuel + 1) =
      (liftM (WPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m c)))) >>= fun output =>
        if WCT9.admissible output = true then pure (some (BitVec.ofNat 32 c, output))
        else WPair.searchL rho m (c + 1) fuel) := rfl
theorem ev_uniform_eq (g : HashOutput → ENNReal) :
    expectedValue (PMF.uniformOfFintype HashOutput) g = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem nearSpec_decode_some {a : HashOutput} (h : WCT9.admissible a = true) : nearSpec.decode a = some a := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_admissible, h]
theorem nearSpec_decode_none {a : HashOutput} (h : ¬WCT9.admissible a = true) : nearSpec.decode a = none := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_admissible, h]
theorem search_law (slot : Nat) (rho : Digest) (m : Message)
    (F : Option (BitVec 32 × HashOutput) → Sampling.RCache → ENNReal) :
    ∀ fuel c (s : GState),
      expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s)
          (fun r => F r.1 r.2.memory.1.rows) =
        expectedValue (Sampling.roRun 0 (nearSpec.search rho m c fuel) s.memory.1.rows) (fun r => F r.1 r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s
      change expectedValue (SecretGuessObservation.runWith (implG slot) (pure none) s) _ =
        expectedValue (Sampling.roRun 0 (pure none) s.memory.1.rows) _
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
        expectedValue_pure]
  | succ fuel ih =>
      intro c s
      rw [searchL_succ, ev_aux_bind]
      unfold ClaudeWCT.Bank.FtsBankSpec.search
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind,
        randomOracle.run_eq]
      change expectedValue (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
        (PMF.uniformOfFintype HashOutput)) _ = _
      cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
      | some a =>
          simp only [BPair.rowStep, hx]
          rw [expectedValue_pure, expectedValue_pure]
          dsimp only
          by_cases had : WCT9.admissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
      | none =>
          have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
          simp only [BPair.rowStep, hx, hdi, if_true]
          rw [expectedValue_map, expectedValue_bind, ev_uniform_eq]
          apply congrArg
          funext a
          rw [expectedValue_pure]
          dsimp only
          by_cases had : WCT9.admissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
def RowsFrame (s s' : GState) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.2 = s.memory.2 ∧ s'.memory.1.nonces = s.memory.1.nonces ∧ s'.memory.1.births = s.memory.1.births ∧
    s'.memory.1.exposures = s.memory.1.exposures
theorem RowsFrame.refl (s : GState) : RowsFrame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem RowsFrame.trans {s s' s'' : GState} (h : RowsFrame s s') (h' : RowsFrame s' s'') : RowsFrame s s'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2⟩
theorem runWith_bind_nonzero {β γ : Type} (slot : Nat) (W : OracleComp WPair.WSpecL β)
    (K : β → OracleComp WPair.WSpecL γ) (s : GState) (r : γ × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith (implG slot) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith (implG slot) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runWith_pure_nonzero {β : Type} (slot : Nat) (b : β) (s : GState) (r : β × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem aux_nonzero (slot : Nat) (i : AuxL) (s : GState) (r : AuxSpecL.Range i × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, WPair.envL.auxiliary (projS s) i res ≠ 0 ∧
      r = (res.1, { s with memory := (res.2, ghostStep s.memory.1 i res.1 s.memory.2) }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) r ≠ 0 at hr
  rw [liftM_map_pmf, Functor.map_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  refine ⟨res, ?_, hr⟩
  simpa [SPMF.liftM_apply] using hres
theorem search_frame (slot : Nat) (rho : Digest) (m : Message) :
    ∀ fuel c (s : GState) r, SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s r ≠ 0 →
      RowsFrame s r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr
      rw [runWith_pure_nonzero slot none s r hr]
      exact RowsFrame.refl s
  | succ fuel ih =>
      intro c s r hr
      rw [searchL_succ] at hr
      obtain ⟨mid, hmid, hr⟩ := runWith_bind_nonzero slot _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hf : RowsFrame s { s with memory := (res.2, ghostStep s.memory.1 (.trial (Sampling.digestTrial rho m c))
          res.1 s.memory.2) } := by
        have hres' : res ∈ (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
            (PMF.uniformOfFintype HashOutput)).support := (PMF.mem_support_iff _ _).mpr hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold BPair.rowStep at hres'
        cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨rfl, rfl, rfl⟩
        | none =>
            simp only [hx] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            exact ⟨rfl, rfl, rfl⟩
      dsimp only at hr
      split_ifs at hr
      · rw [runWith_pure_nonzero slot _ _ r hr]
        exact hf
      · exact hf.trans (ih (c + 1) _ r hr)
end ClaudeWCT.W9.T3.Security.CaseC
end
