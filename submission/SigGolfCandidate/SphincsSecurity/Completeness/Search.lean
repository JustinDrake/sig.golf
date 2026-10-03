import SigGolfCandidate.SphincsSecurity.Scheme

open OracleComp OracleSpec ENNReal
set_option maxRecDepth 10000
namespace SphincsSecurity.Completeness
variable {β γ : Type}
def searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) : Nat → Nat → OracleComp HashSpec (Option γ)
  | 0, _ => pure none
  | n + 1, t => do
      let answer ← Concrete.oracleHash (inputs t)
      match decode answer with
      | some value => some <$> success t value
      | none => searchLoop inputs decode success n (t + 1)
noncomputable def failMass (decode : HashOutput → Option β) : ℝ≥0∞ :=
  ((Finset.univ.filter fun u => decode u = none).card : ℝ≥0∞) / (Fintype.card HashOutput : ℝ≥0∞)
theorem failMass_eq_probEvent (decode : HashOutput → Option β) :
    failMass decode = Pr[fun u => decode u = none | ($ᵗ HashOutput : ProbComp HashOutput)] :=
  (probEvent_uniformSample HashOutput _).symm
theorem fresh_run (input : HashInput) (cache : QueryCache HashSpec) (hfresh : cache input = none)
    {δ : Type} (next : HashOutput × QueryCache HashSpec → ProbComp δ) (p : δ → Prop) :
    Pr[p | (randomOracle (spec := HashSpec) input).run cache >>= next]
      = ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹
          * Pr[p | next (u, cache.cacheQuery input u)] := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind]
  rw [show (uniformSampleImpl (spec := HashSpec) input) = ($ᵗ HashOutput : ProbComp HashOutput)
    from rfl, probEvent_bind_eq_tsum]
  exact tsum_congr fun u => by rw [probOutput_uniformSample]
theorem probEvent_searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) (bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s') :
    ∀ (n t : Nat), t + n ≤ bound → ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr[fun r => r.1 = none |
          (simulateQ randomOracle (searchLoop inputs decode success n t)).run cache]
        ≤ failMass decode ^ n := by
  intro n
  induction n with
  | zero => intro t _ cache _; simp [searchLoop]
  | succ n ih =>
      intro t hbound cache hfresh
      rw [searchLoop]
      simp only [Concrete.oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind]
      rw [fresh_run (inputs t) cache (hfresh t (Nat.le_refl t) (by omega))]
      have hterm : ∀ u : HashOutput,
          Pr[fun r => r.1 = none | (simulateQ randomOracle
              (match decode u with
                | some value => some <$> success t value
                | none => searchLoop inputs decode success n (t + 1))).run
              (cache.cacheQuery (inputs t) u)]
            ≤ (if decode u = none then failMass decode ^ n else 0) := by
        intro u
        cases hu : decode u with
        | some value =>
            simp only [reduceCtorEq, if_false, simulateQ_map, StateT.run_map, probEvent_map]
            simp
        | none =>
            simp only [if_true]
            refine ih (t + 1) (by omega) _ (fun s hs hsb => ?_)
            have hne : inputs s ≠ inputs t := fun hcon => by
              have hst := hinj s t hsb (by omega) hcon
              omega
            exact (QueryCache.cacheQuery_of_ne cache u hne).trans
              (hfresh s (Nat.le_of_succ_le hs) hsb)
      refine le_trans (ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hterm u) _)) ?_
      rw [tsum_fintype, Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero]),
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        pow_succ', failMass, div_eq_mul_inv, ← mul_assoc]
theorem probEvent_bind_le {α δ : Type} (x : OracleComp HashSpec α) (k : α → OracleComp HashSpec δ)
    (p : δ × QueryCache HashSpec → Prop) (cache : QueryCache HashSpec) (b : ℝ≥0∞)
    (hk : ∀ r ∈ support ((simulateQ randomOracle x).run cache),
      Pr[p | (simulateQ randomOracle (k r.1)).run r.2] ≤ b) :
    Pr[p | (simulateQ randomOracle (x >>= k)).run cache] ≤ b := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc ∑' r : α × QueryCache HashSpec,
        Pr[= r | (simulateQ randomOracle x).run cache]
          * Pr[p | (simulateQ randomOracle (k r.1)).run r.2]
      ≤ ∑' r : α × QueryCache HashSpec, Pr[= r | (simulateQ randomOracle x).run cache] * b := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · exact mul_le_mul_right (hk r hr) _
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ b := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem probEvent_bind_le_add {α δ : Type} (x : OracleComp HashSpec α)
    (k : α → OracleComp HashSpec δ) (p : α × QueryCache HashSpec → Prop)
    (q : δ × QueryCache HashSpec → Prop) (cache : QueryCache HashSpec) (b : ℝ≥0∞)
    (hk : ∀ r ∈ support ((simulateQ randomOracle x).run cache), ¬ p r →
      Pr[q | (simulateQ randomOracle (k r.1)).run r.2] ≤ b) :
    Pr[q | (simulateQ randomOracle (x >>= k)).run cache]
      ≤ Pr[p | (simulateQ randomOracle x).run cache] + b := by
  classical
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite (mx := (simulateQ randomOracle x).run cache) (p := p)]
  calc ∑' r : α × QueryCache HashSpec,
        Pr[= r | (simulateQ randomOracle x).run cache]
          * Pr[q | (simulateQ randomOracle (k r.1)).run r.2]
      ≤ ∑' r : α × QueryCache HashSpec,
          ((if p r then Pr[= r | (simulateQ randomOracle x).run cache] else 0)
            + Pr[= r | (simulateQ randomOracle x).run cache] * b) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · by_cases hp : p r
          · simp only [hp, if_true]
            have hone : Pr[q | (simulateQ randomOracle (k r.1)).run r.2] ≤ 1 := probEvent_le_one
            exact le_add_right (mul_le_of_le_one_right' hone)
          · simp only [hp, if_false, zero_add]
            exact mul_le_mul_right (hk r hr hp) _
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ (∑' r : α × QueryCache HashSpec,
          if p r then Pr[= r | (simulateQ randomOracle x).run cache] else 0) + b := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        have hmass : ∑' r : α × QueryCache HashSpec,
            Pr[= r | (simulateQ randomOracle x).run cache] ≤ 1 := tsum_probOutput_le_one
        exact add_le_add le_rfl (mul_le_of_le_one_left' hmass)
theorem bytesLE_inj {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) : x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb
theorem counter_bytes_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : (bytesLE 4 (BitVec.ofNat counterBits c) : HashInput)
        = bytesLE 4 (BitVec.ofNat counterBits c')) : c = c' := by
  have hv := congrArg BitVec.toNat (bytesLE_inj h)
  simp only [BitVec.toNat_ofNat, counterBits] at hv
  rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hv
open Concrete in
theorem encodingSearch_eq_searchLoop (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) :
    ∀ (n t : Nat),
      (encodingSearch parameter lay tree leaf message n t
        : OracleComp HashSpec (Option (Counter × Encoding)))
        = searchLoop
            (fun c => tweakableHashInput parameter (.encoding lay tree leaf)
              (bytesLE 16 message ++ bytesLE 4 (BitVec.ofNat counterBits c)))
            (fun out => TargetSum.decodeDigest (truncateHash out))
            (fun c encoding => pure (BitVec.ofNat counterBits c, encoding))
            n t := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
      intro t
      rw [encodingSearch, searchLoop]
      simp only [encode, tweakableHash, oracleHash, bind_assoc, pure_bind, ih]
      refine bind_congr fun answer => ?_
      cases TargetSum.decodeDigest (truncateHash answer) <;> rfl
end SphincsSecurity.Completeness
