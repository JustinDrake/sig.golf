import SigGolfCandidate.Budget.Search

/-!
# Paired digest search

A pair shares one randomizer query and short-circuits after its first successful digest.
The entire randomizer answer is cached.  We condition on that entire answer and charge any
collision of either half with the old digest cache, or with the other half, as a bad pair.
Thus no independence claim is made about a half after the randomizer has been cached.
-/

namespace SigGolfCandidate.Budget
attribute [local irreducible] SigGolfCandidate.Ref.AddressFormat.queryPerm
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist

noncomputable def epsP : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 21 / 2 ^ 128

def pairLo (u : BitVec 256) : Val := (answerBytes 32 u).take 16
def pairHi (u : BitVec 256) : Val := (answerBytes 32 u).drop 16

@[simp] theorem pairLo_eq (u : BitVec 256) : pairLo u = answerBytes 16 u := by
  simp only [pairLo, answerBytes, ← List.map_take, List.take_range]
  rfl

@[simp] theorem pairLo_length (u : BitVec 256) : (pairLo u).length = 16 := by simp
@[simp] theorem pairHi_length (u : BitVec 256) : (pairHi u).length = 16 := by simp [pairHi]

theorem pairHi_nat (u : BitVec 256) : leNat (pairHi u) = u.toNat / 2 ^ 128 := by
  have ha : leNat (answerBytes 32 u) = u.toNat := by
    rw [answerBytes_eq 32 u (by decide), leNat_leBytes]
    have hu := u.isLt
    norm_num at hu ⊢
    omega
  rw [← List.take_append_drop 16 (answerBytes 32 u), leNat_append] at ha
  change leNat (pairLo u) + 256 ^ (pairLo u).length * leNat (pairHi u) = u.toNat at ha
  rw [pairLo_length, pairLo_eq, leNat_answerBytes16] at ha
  norm_num at ha
  omega

theorem prf2_pair_bind_eq {β : Type} (x : List Byte)
    (f : Val × Val → OracleComp HashSpec β) :
    prf2 x >>= f = qry (addrFmt x) >>= fun u => f (pairLo u, pairHi u) := by
  simp only [prf2, Ref.H, bind_assoc, pure_bind, pairLo, pairHi]

private theorem count_div_eq_le (A r : Nat) (hA : 0 < A) :
    (∑ k ∈ Finset.range (A * A), if k / A = r then 1 else 0) ≤ A := by
  rw [sum_range_mul]
  have he : ∀ b ∈ Finset.range A, ∀ a ∈ Finset.range A, (a + A * b) / A = b := by
    intro b hb a ha
    rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt (Finset.mem_range.mp ha), Nat.zero_add]
  calc (∑ b ∈ Finset.range A, ∑ a ∈ Finset.range A,
      if (a + A * b) / A = r then 1 else 0)
      = ∑ b ∈ Finset.range A, if b = r then A else 0 := by
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.sum_congr rfl fun a ha => by rw [he b hb a ha]]
        by_cases h : b = r <;> simp [h]
    _ ≤ A := by
      rw [Finset.sum_ite_eq' (Finset.range A) r (fun _ => A)]
      split <;> simp

private theorem count_halves_eq_le (A : Nat) (hA : 0 < A) :
    (∑ k ∈ Finset.range (A * A), if k % A = k / A then 1 else 0) ≤ A := by
  rw [sum_range_mul]
  calc (∑ b ∈ Finset.range A, ∑ a ∈ Finset.range A,
      if (a + A * b) % A = (a + A * b) / A then 1 else 0)
      ≤ ∑ _b ∈ Finset.range A, 1 := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [Finset.sum_congr rfl fun a ha => by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
            Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt (Finset.mem_range.mp ha), Nat.zero_add]]
        rw [Finset.sum_ite_eq' (Finset.range A) b (fun _ => 1)]
        split <;> simp
    _ = A := by simp

private theorem probEvent_pairHi_mem_le (R : Finset Val) :
    Pr[fun u : BitVec 256 => pairHi u ∈ R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
      (R.card : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniformSample]
  have hsub : (Finset.univ.filter fun u : BitVec 256 => pairHi u ∈ R) ⊆
      R.biUnion fun r => Finset.univ.filter fun u : BitVec 256 => u.toNat / 2 ^ 128 = leNat r := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, hu, (pairHi_nat u).symm⟩
  have hone : ∀ r : Nat,
      (Finset.univ.filter fun u : BitVec 256 => u.toNat / 2 ^ 128 = r).card ≤ 2 ^ 128 := by
    intro r
    rw [card_bitVec_filter 256 (fun k => k / 2 ^ 128 = r), card_filter_range,
      show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
    exact count_div_eq_le _ _ (by positivity)
  have hcard : (Finset.univ.filter fun u : BitVec 256 => pairHi u ∈ R).card ≤ R.card * 2 ^ 128 :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
      calc ∑ r ∈ R, (Finset.univ.filter fun u : BitVec 256 => u.toNat / 2 ^ 128 = leNat r).card
          ≤ ∑ _r ∈ R, 2 ^ 128 := Finset.sum_le_sum fun r _ => hone _
        _ = R.card * 2 ^ 128 := by simp))
  have hc : (Fintype.card (BitVec 256) : ℝ≥0∞) = 2 ^ 128 * 2 ^ 128 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  rw [hc]
  calc _ ≤ ((R.card * 2 ^ 128 : Nat) : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128) := by gcongr
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

private theorem probEvent_pair_halves_eq_le :
    Pr[fun u : BitVec 256 => pairHi u = pairLo u |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ (1 : ℝ≥0∞) / 2 ^ 128 := by
  have hmono : Pr[fun u : BitVec 256 => pairHi u = pairLo u |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
      Pr[fun u : BitVec 256 => u.toNat % 2 ^ 128 = u.toNat / 2 ^ 128 |
        ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
    refine _root_.probEvent_mono fun u _ hu => ?_
    have h := congrArg leNat hu
    simpa only [pairHi_nat, pairLo_eq, leNat_answerBytes16] using h.symm
  refine hmono.trans ?_
  rw [probEvent_uniform_toNat (fun k => k % 2 ^ 128 = k / 2 ^ 128)]
  have hc : ((Finset.range (2 ^ 256)).filter fun k => k % 2 ^ 128 = k / 2 ^ 128).card ≤ 2 ^ 128 := by
    rw [card_filter_range, show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
    exact count_halves_eq_le _ (by positivity)
  calc _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) / 2 ^ 256 := by gcongr
    _ = (1 : ℝ≥0∞) / 2 ^ 128 := by
      rw [Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
      simpa using ENNReal.mul_div_mul_right (1 : ℝ≥0∞) (2 ^ 128) (by simp : (2 : ℝ≥0∞) ^ 128 ≠ 0)
        (by simp : (2 : ℝ≥0∞) ^ 128 ≠ ⊤)

def PairBad (R : Finset Val) (u : BitVec 256) : Prop :=
  pairLo u ∈ R ∨ pairHi u ∈ R ∨ pairHi u = pairLo u

instance (R : Finset Val) : DecidablePred (PairBad R) := fun u => by unfold PairBad; infer_instance

/-- The bound includes both old-cache collisions and the equality of the two halves. -/
theorem probEvent_pairBad_le (R : Finset Val) (hcard : R.card < 2 ^ 21) :
    Pr[PairBad R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ 2 * epsP := by
  have h0 := probEvent_answerBytes_mem_le R
  have h1 := probEvent_pairHi_mem_le R
  have he := probEvent_pair_halves_eq_le
  have ho := probEvent_or_le ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u => pairLo u ∈ R) (fun u => pairHi u ∈ R ∨ pairHi u = pairLo u)
  have hi := probEvent_or_le ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u => pairHi u ∈ R) (fun u => pairHi u = pairLo u)
  change Pr[PairBad R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ _ at ho
  simp only [pairLo_eq] at ho
  refine ho.trans ((add_le_add h0 (hi.trans (add_le_add h1 he))).trans ?_)
  calc (R.card : ℝ≥0∞) / 2 ^ 128 + ((R.card : ℝ≥0∞) / 2 ^ 128 + 1 / 2 ^ 128)
      = ((2 * R.card + 1 : Nat) : ℝ≥0∞) / 2 ^ 128 := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        simp only [div_eq_mul_inv]
        ring
    _ ≤ ((2 * 2 ^ 21 : Nat) : ℝ≥0∞) / 2 ^ 128 := by
      gcongr
      omega
    _ = 2 * epsP := by
      simp only [epsP, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
      ring

/-- Query-domain and worst-path bound: at most three compressions per pair. -/
theorem spec_searchDigestPairs (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a, Spec PD (fun _ => True) (3 * fuel) (searchDigestPairs S m a fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a; exact Spec.pure _ _ trivial
  | succ n ih =>
    intro a
    unfold searchDigestPairs
    rw [prf2_pair_bind_eq]
    obtain ⟨h1, h2⟩ := rnd_ok S m hS hm a
    refine Spec.qry_bind h1 (k := 2 + 3 * n) (fun u => ?_) (by omega)
    dsimp only
    rw [digest_bind_eq]
    obtain ⟨h3, h4⟩ := dig_ok (pairLo u) m (pairLo_length u) hm
    refine Spec.qry_bind h3 (k := 1 + 3 * n) (fun v => ?_) (by omega)
    split
    · exact Spec.pure _ _ trivial
    · rw [digest_bind_eq]
      obtain ⟨h5, h6⟩ := dig_ok (pairHi u) m (pairHi_length u) hm
      refine Spec.qry_bind h5 (k := 3 * n) (fun w => ?_) (by omega)
      split
      · exact Spec.pure _ _ trivial
      · exact ih (a + 1)

/-- Fresh future randomizer queries; only members of `R` may have cached digests. -/
def PairFresh (S m : List Byte) (a : Nat) (R : Finset Val) (cache : RCache) : Prop :=
  (∀ a', a ≤ a' → a' < 2 ^ 32 → cache (addrFmt (rndInput S m a')) = none) ∧
  (∀ rho, rho.length = 16 → rho ∉ R → cache (addrFmt (digestInput rho m)) = none)

private theorem PairFresh.enlarge {S m : List Byte} {a : Nat} {R R' : Finset Val}
    {cache : RCache} (h : PairFresh S m a R cache) (hR : R ⊆ R') :
    PairFresh S m a R' cache :=
  ⟨h.1, fun rho hl hn => h.2 rho hl (fun hr => hn (hR hr))⟩

private theorem PairFresh.randomizer {S m : List Byte} {a : Nat} {R : Finset Val}
    {cache : RCache} (h : PairFresh S m a R cache) (ha : a < 2 ^ 32) (u : BitVec 256) :
    PairFresh S m (a + 1) R (cache.cacheQuery (addrFmt (rndInput S m a)) u) := by
  constructor
  · intro a' ha' ha'b
    rw [QueryCache.cacheQuery_of_ne]
    · exact h.1 a' (by omega) ha'b
    · intro heq
      have := rnd_inj S m ha'b ha heq
      omega
  · intro rho hl hn
    rw [QueryCache.cacheQuery_of_ne _ _ (fun heq => rnd_ne_dig S m rho m a heq.symm)]
    exact h.2 rho hl hn

private theorem PairFresh.digest {S m : List Byte} {a : Nat} {R : Finset Val}
    {cache : RCache} (h : PairFresh S m a R cache) (hm : m.length = 32)
    (rho : Val) (hrho : rho.length = 16) (u : BitVec 256) :
    PairFresh S m a (insert rho R) (cache.cacheQuery (addrFmt (digestInput rho m)) u) := by
  constructor
  · intro a' ha' ha'b
    rw [QueryCache.cacheQuery_of_ne _ _ (rnd_ne_dig S m rho m a')]
    exact h.1 a' ha' ha'b
  · intro rho' hl hn
    rw [Finset.mem_insert, not_or] at hn
    rw [QueryCache.cacheQuery_of_ne _ _ (fun heq => hn.1 (dig_inj m hm hl hrho heq))]
    exact h.2 rho' hl hn.2

private theorem PairFresh.digest_support {S m : List Byte} {a : Nat} {R : Finset Val}
    {cache : RCache} (h : PairFresh S m a R cache) (hm : m.length = 32)
    (rho : Val) (hrho : rho.length = 16) (y : BitVec 256 × RCache)
    (hy : y ∈ support ((randomOracle (addrFmt (digestInput rho m))).run cache)) :
    PairFresh S m a (insert rho R) y.2 := by
  rcases mem_support_ro _ _ y hy with ⟨_, heq⟩ | ⟨_, heq⟩
  · rw [heq]
    exact h.enlarge (Finset.subset_insert _ _)
  · rw [heq]
    exact h.digest hm rho hrho y.1

/-- A cache-uniform exponential-moment bound.  The conservative collision term charges a
whole bad pair, giving `2 * epsP` instead of expanding `(rhoD + epsP)^2`.
No numerical value of `rhoD` is assumed. -/
theorem V_searchDigestPairs (z b : ℝ≥0∞) (hz : 1 ≤ z) (hb : 1 ≤ b)
    (hstep : z ^ 2 * (1 - rhoD) + z ^ 3 * rhoD * (1 - rhoD) +
      z ^ 3 * (rhoD ^ 2 + 2 * epsP) * b ≤ b)
    (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a (cache : RCache) (R : Finset Val), a + fuel ≤ 2 ^ 20 → R.card ≤ 2 * a →
      (∀ a', a ≤ a' → a' < 2 ^ 32 → cache (addrFmt (rndInput S m a')) = none) →
      (∀ rho, rho.length = 16 → rho ∉ R → cache (addrFmt (digestInput rho m)) = none) →
      V z (searchDigestPairs S m a fuel) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro a cache R _ _ _ _; simp [searchDigestPairs, hb]
  | succ n ih =>
    intro a cache R hbound hcard hrnd hdig
    have hf : PairFresh S m a R cache := ⟨hrnd, hdig⟩
    have hz1 : ∀ q : Query, q.blocks ≤ 1 → z ^ q.blocks ≤ z := fun q hq =>
      (pow_le_pow_right₀ hz hq).trans_eq (pow_one z)
    have hzb : 1 ≤ z * b := (show (1 : ℝ≥0∞) = 1 * 1 by simp).trans_le (mul_le_mul' hz hb)
    unfold searchDigestPairs
    rw [prf2_pair_bind_eq, V_query,
      expectedValue_ro_fresh _ _ (hrnd a le_rfl (by omega))]
    obtain ⟨_, hbr⟩ := rnd_ok S m hS hm a
    have hcont : ∀ u : BitVec 256,
        V z (digest (pairLo u) m >>= fun N0 =>
          if admissible N0 = true then pure (some (pairLo u, N0)) else
            digest (pairHi u) m >>= fun N1 =>
              if admissible N1 = true then pure (some (pairHi u, N1))
              else searchDigestPairs S m (a + 1) n)
          (cache.cacheQuery (addrFmt (rndInput S m a)) u) ≤
        if PairBad R u then z ^ 2 * b
        else z * (rhoD * (z * (rhoD * b + (1 - rhoD))) + (1 - rhoD)) := by
      intro u
      let R1 := insert (pairLo u) R
      let R2 := insert (pairHi u) R1
      have hc1 := hf.randomizer (by omega) u
      have hcard2 : R2.card ≤ 2 * (a + 1) := by
        have h1 := Finset.card_insert_le (pairLo u) R
        have h2 := Finset.card_insert_le (pairHi u) R1
        dsimp only [R1, R2] at *
        omega
      have hrec : ∀ c2, PairFresh S m (a + 1) R2 c2 →
          V z (searchDigestPairs S m (a + 1) n) c2 ≤ b := by
        intro c2 hc2
        exact ih (a + 1) c2 R2 (by omega) hcard2 hc2.1 hc2.2
      obtain ⟨_, hbl⟩ := dig_ok (pairLo u) m (pairLo_length u) hm
      obtain ⟨_, hbh⟩ := dig_ok (pairHi u) m (pairHi_length u) hm
      have hsecond : ∀ c2, PairFresh S m (a + 1) R1 c2 →
          V z (digest (pairHi u) m >>= fun N1 =>
            if admissible N1 = true then pure (some (pairHi u, N1))
            else searchDigestPairs S m (a + 1) n) c2 ≤ z * b := by
        intro c2 hc2
        rw [digest_bind_eq, V_query]
        refine mul_le_mul' (hz1 _ hbh) (expectedValue_le_of_support fun y hy => ?_)
        split
        · simpa using hb
        · exact hrec y.2 (hc2.digest_support hm _ (pairHi_length u) y hy)
      have hsecond_good (hhi : pairHi u ∉ R1) : ∀ c2, PairFresh S m (a + 1) R1 c2 →
          V z (digest (pairHi u) m >>= fun N1 =>
            if admissible N1 = true then pure (some (pairHi u, N1))
            else searchDigestPairs S m (a + 1) n) c2 ≤ z * (rhoD * b + (1 - rhoD)) := by
        intro c2 hc2
        rw [digest_bind_eq, V_query,
          expectedValue_ro_fresh _ _ (hc2.2 _ (pairHi_length u) hhi)]
        refine (mul_le_mul' (hz1 _ hbh) (ev_ite_le
          (fun v : BitVec 256 => ¬ admissible v.toNat = true) b 1 _ fun v => ?_)).trans ?_
        · by_cases hv : admissible v.toNat = true
          · simp [hv]
          · simp only [hv]
            exact hrec _ (hc2.digest hm _ (pairHi_length u) v)
        · rw [probEvent_not_uniform (fun v : BitVec 256 => ¬ admissible v.toNat = true), mul_one]
          exact le_rfl
      rw [digest_bind_eq, V_query]
      by_cases hbad : PairBad R u
      · rw [if_pos hbad]
        calc
          _ ≤ z * (z * b) := by
            refine mul_le_mul' (hz1 _ hbl) (expectedValue_le_of_support fun y hy => ?_)
            split
            · simpa using hzb
            · exact hsecond y.2 (hc1.digest_support hm _ (pairLo_length u) y hy)
          _ = z ^ 2 * b := by ring
      · rw [if_neg hbad]
        have hlo : pairLo u ∉ R := fun h => hbad (Or.inl h)
        have hhi : pairHi u ∉ R1 := by
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hbad (Or.inr (Or.inr h))
          · exact hbad (Or.inr (Or.inl h))
        rw [expectedValue_ro_fresh _ _ (hc1.2 _ (pairLo_length u) hlo)]
        refine (mul_le_mul' (hz1 _ hbl) (ev_ite_le
          (fun v : BitVec 256 => ¬ admissible v.toNat = true)
          (z * (rhoD * b + (1 - rhoD))) 1 _ fun v => ?_)).trans ?_
        · by_cases hv : admissible v.toNat = true
          · simp [hv]
          · simp only [hv]
            exact hsecond_good hhi _ (hc1.digest hm _ (pairLo_length u) v)
        · rw [probEvent_not_uniform (fun v : BitVec 256 => ¬ admissible v.toNat = true), mul_one]
          exact le_rfl
    refine (mul_le_mul' (hz1 _ hbr) (ev_ite_le (PairBad R) _ _ _ hcont)).trans ?_
    have hcoll := probEvent_pairBad_le R (by omega)
    calc z * (Pr[PairBad R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * (z ^ 2 * b) +
          Pr[fun u => ¬ PairBad R u | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] *
            (z * (rhoD * (z * (rhoD * b + (1 - rhoD))) + (1 - rhoD))))
        ≤ z * ((2 * epsP) * (z ^ 2 * b) +
          1 * (z * (rhoD * (z * (rhoD * b + (1 - rhoD))) + (1 - rhoD)))) := by
          gcongr
          exact probEvent_le_one
      _ = z ^ 2 * (1 - rhoD) + z ^ 3 * rhoD * (1 - rhoD) +
          z ^ 3 * (rhoD ^ 2 + 2 * epsP) * b := by ring
      _ ≤ b := hstep

end SigGolfCandidate.Budget
