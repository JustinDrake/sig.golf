import SigGolfCandidate.T3.Secc.CaseCNearCore
import SigGolfCandidate.T3.Secc.CaseCBankReuse

/-!
# Stream CC: the near potential read off a lazy-world memory (rows cache, nonces, births, exposures, reuse flag)

For the forced lazy world of B-PAIR §8 the bank state is a function of the world memory: the targets are the fresh
adversary/verifier digest births, the exposures the signer's accepted selections of fresh signings, the reuse mass
`reuseC rows nonces = Σ_{m, nonce of m undrawn} reuseMass rows m`, and the remaining births `q − |births|`:

    nearMemPotential q births exposures reused rows nonces
      = 0                                                        if q < |births|
      = nearPotential ⟨births, exposures, reused, reuseC rows nonces, q − |births|⟩ + (q − |births|)·(1/16)/2^128

(the second term prepays the reuse charge of the remaining births). Step lemmas over pure laws:

* `mem_birth`: a fresh digest row read by the adversary/verifier (uniform answer, cached, appended to the births);
* `mem_sign_fresh`: a fresh signing — uniform nonce, the reuse flag decided on the rows cache, SEC's lazy digest
  search on the rows cache, the selection exposed;
* `mem_sign_repeat`: a repeated signing (nonce cached; only trial rows of the signed message added; no exposure);
* `mem_initial` / `mem_win`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The reuse mass of a memory -/

/-- Cached admissible digest rows of messages whose nonce is not drawn yet. -/
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then reuseMass rows m else 0

theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : reuseC (rows.cacheQuery x a) nonces ≤ reuseC rows nonces + admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then reuseMass rows m else 0) +
          (if DigestRowOf x m then admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)

/-- Drawing the nonce of `m` removes the reuse mass of `m`; rows of other messages unchanged keep theirs. -/
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → reuseMass rows' m' = reuseMass rows m') :
    reuseC rows' (Function.update nonces m (some v)) + reuseMass rows m ≤ reuseC rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]

/-- Rows of a signed message only: the reuse mass is unchanged when the nonce of `m` is already drawn. -/
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → reuseMass rows' m' = reuseMass rows m') :
    reuseC rows' nonces = reuseC rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]

/-! ## The digest search only adds trial rows of its own message -/

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
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  rw [Sampling.digestSearch_public] at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) Sampling.digestDecode _ fuel 0 cache r hr

theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m := ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)

/-- **The search keeps the reuse mass of every other message.** -/
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → reuseMass r.2 m' = reuseMass cache m' := by
  intro m' hm
  unfold reuseMass admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [digestSearch_cache_frame secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]

/-! ## The memory potential -/

/-- **The near potential of a lazy-world memory** (budget `q` of births). -/
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else nearPotential ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128)

/-- **Birth step**: a fresh digest row (uniform answer, cached, appended to the births). -/
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

/-- **Fresh-signing step**: uniform nonce `v` of an unsigned message `m`; the flag records `Reuse rows v m`; SEC's
lazy digest search on the rows cache; its selection is exposed. -/
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (digestSearch v m 0 fuel) rows) (fun r =>
        nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · have h0 : ∀ X r n, nearMemPotential q births X r rows n = 0 := by
      intro X r n
      unfold nearMemPotential
      rw [if_pos hq]
    apply expectedValue_le_of_le
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
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (digestSearch v m 0 fuel) rows) →
      reuseC r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [reuseC_signed_eq rows r.2 _ m (by simp) (digestSearch_reuseMass secret v m fuel rows r hr), hupd]
  have hC : C0 + reuseMass rows m ≤ reuseC rows nonces := by
    rw [← hupd 0]
    exact reuseC_sign_le rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128) with hextra
  have hbefore : nearMemPotential q births exposures reused rows nonces = nearPotential b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (digestSearch v m 0 fuel) rows) →
      nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList) (reused || decide (Reuse rows v m)) r.2
          (Function.update nonces m (some v)) =
        nearPotential ⟨births, exposures ++ (r.1.map Prod.snd).toList, reused || decide (Reuse rows v m), C0,
          q - births.length⟩ + extra := by
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
    by_cases h2 : BPORS.Numeric.proposalLength < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : BPORS.Numeric.proposalLength < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (digestSearch v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (digestSearch v m 0 fuel) rows) (fun r =>
            (if Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (digestSearch v m 0 fuel) rows) (fun r =>
            (if Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (digestSearch v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add (near_sign b rows m C0 hC secret fuel hfuel) le_rfl

/-- **Repeated-signing step**: the nonce of `m` is drawn; the search only adds trial rows of `m`; no exposure. -/
theorem mem_sign_repeat (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows rows' : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m ≠ none)
    (hrows : ∀ m', m' ≠ m → reuseMass rows' m' = reuseMass rows m') :
    nearMemPotential q births exposures reused rows' nonces = nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [reuseC_signed_eq rows rows' nonces m hm hrows]

/-- **Initial memory potential**: `≤ (203 + 1/16)·q/2^128`. -/
theorem mem_initial (q : Nat) :
    nearMemPotential q [] [] false ∅ (fun _ => none) ≤ (q : ENNReal) * (203 + 1 / 16) / 2 ^ 128 := by
  unfold nearMemPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
  have hC : reuseC ∅ (fun _ => none) = 0 := by
    unfold reuseC reuseMass admissibleEntry
    simp
  have hn := near_initial q
  rw [show (⟨[], [], false, reuseC ∅ (fun _ => none), q⟩ : BankCore) = ⟨[], [], false, 0, q⟩ by rw [hC]]
  calc
    _ ≤ (q : ENNReal) * 203 / 2 ^ 128 + (q : ENNReal) * ((1 / 16) / 2 ^ 128) := add_le_add hn le_rfl
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

/-- **Win**: an alive memory with a reuse or a near-covered admissible birth holds a full unit. -/
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q)
    (hlen : exposures.length ≤ BPORS.Numeric.proposalLength)
    (h : reused = true ∨ ∃ N ∈ births, admissible (selections N) = true ∧ digestGate N=true ∧ NearCoveredBy exposures N) :
    1 ≤ nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact (near_win ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add


end SigGolfCandidate.T3.Security.CaseC
