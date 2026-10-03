import SigGolfCandidate.T3.Secc.LargeCouplingBankLazy
import SigGolfCandidate.T3.Secc.SeccSufRoute

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
noncomputable def reuseC (st : RouterState) : ENNReal :=
  ∑' m : Message, if (st.memo.lookup m).isSome then 0 else CaseC.reuseMass st.cache m
noncomputable def bankOf (q : Nat) (st : RouterState) : CaseC.BankCore :=
  ⟨(st.births.map Prod.snd).reverse, st.exposures, st.reused, reuseC st, q - st.births.length⟩
noncomputable def psi (q : Nat) (st : RouterState) : ENNReal := CaseC.corePotential (bankOf q st)
noncomputable def slackT {U : Finset HashInput} (q : Nat) (ws : LargeResidual.State WCoord (Cell U)) : ENNReal :=
  ((q - ws.counters.mass : Nat) : ENNReal) / 2 ^ 128
structure BankInv (U : Finset HashInput) (ws : LargeResidual.State WCoord (Cell U)) (st : RouterState) : Prop where
  calls : ws.counters.calls = st.calls
  mass : ws.counters.mass ≤ ws.counters.calls
  births : st.births.length ≤ st.calls
  nonce : ∀ m, st.memo.lookup m = none → ws.candidates (.inr m) = Finset.univ
  fresh : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∉ st.seen → X ∉ st.trials → ws.rows ⟨X, hX⟩ = none
  seenRows : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∈ st.seen → X ∉ st.trials →
    ∃ y, st.cache X = some y ∧ ws.rows ⟨X, hX⟩ = some y
  bornSeen : ∀ p ∈ st.births, p.1 ∈ st.seen
  trials : ∀ X ∈ st.trials, ∃ rho m c, X = pad64 (digestInput rho m c) ∧ (st.memo.lookup m).isSome
def _root_.SigGolfCandidate.T3.Security.LargeResidual.RouterState.born (st : RouterState) (X : HashInput) (y : LargeResidual.HashOutput) : RouterState :=
  { st.after X with births := (X, y) :: st.births }
theorem _root_.SigGolfCandidate.T3.Security.LargeResidual.RouterState.next_eq (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : LargeResidual.HashOutput) :
    st.next U X y = if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then st.born X y else st.after X := rfl
theorem bankOf_after (q : Nat) (st : RouterState) (X : HashInput) : bankOf q (st.after X) = bankOf q st := rfl
theorem psi_after (q : Nat) (st : RouterState) (X : HashInput) : psi q (st.after X) = psi q st := rfl
theorem cache_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput) :
    (st.born X y).cache Z =
      if Z = X then some y else st.cache Z := by
  simp only [RouterState.born, RouterState.cache, List.lookup_cons]
  by_cases h : Z = X
  · subst h; simp
  · have hb : (Z == X) = false := by simpa using h
    rw [hb, if_neg h]
theorem digestTrial_inj {rho rho' : Digest} {m m' : Message} {c c' : Fin (2 ^ 32)}
    (h : Sampling.digestTrial rho m c.val = Sampling.digestTrial rho' m' c'.val) : m = m' ∧ rho = rho' ∧ c = c' := by
  have h' : pad64 (digestInput rho m (BitVec.ofNat 32 c.val)) = pad64 (digestInput rho' m' (BitVec.ofNat 32 c'.val)) := h
  obtain ⟨h1, h2, h3⟩ := BPB.digestInput_injective h'
  refine ⟨h3, h1, Fin.ext ?_⟩
  have := congrArg BitVec.toNat h2
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt] using this
theorem tsum_trial_indicator_le (X : HashInput) (a : ENNReal) :
    (∑' m : Message, ∑' p : Digest × Fin (2 ^ 32),
      if Sampling.digestTrial p.1 m p.2.val = X then a else 0) ≤ a := by
  by_cases hex : ∃ (m : Message) (p : Digest × Fin (2 ^ 32)), Sampling.digestTrial p.1 m p.2.val = X
  · obtain ⟨m0, p0, h0⟩ := hex
    have hinner : ∀ m, (∑' p : Digest × Fin (2 ^ 32), if Sampling.digestTrial p.1 m p.2.val = X then a else 0) =
        if m = m0 then a else 0 := by
      intro m
      by_cases hm : m = m0
      · subst hm
        rw [if_pos rfl, tsum_eq_single p0]
        · rw [if_pos h0]
        · intro p hp
          rw [if_neg]
          intro hp'
          obtain ⟨-, h1, h2⟩ := digestTrial_inj (hp'.trans h0.symm)
          exact hp (Prod.ext h1 h2)
      · rw [if_neg hm]
        apply ENNReal.tsum_eq_zero.mpr
        intro p
        rw [if_neg]
        intro hp'
        exact hm (digestTrial_inj (hp'.trans h0.symm)).1
    simp_rw [hinner]
    rw [tsum_ite_eq]
  · push Not at hex
    simp only [hex, if_false, tsum_zero]
    exact zero_le
theorem admissibleEntry_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput)
    (hX : st.cache X = none) :
    CaseC.admissibleEntry (st.born X y).cache Z ≤
      CaseC.admissibleEntry st.cache Z + if Z = X then CaseC.admInd y else 0 := by
  unfold CaseC.admissibleEntry
  simp only [cache_birth]
  by_cases h : Z = X
  · subst h
    simp only [if_true, hX, Option.elim_none, Option.elim_some, zero_add, CaseC.admInd]
    exact le_rfl
  · simp only [h, if_false, add_zero]
    exact le_rfl
theorem reuseC_birth (st : RouterState) (X : HashInput) (y : LargeResidual.HashOutput) (hX : st.cache X = none) :
    reuseC (st.born X y) ≤ reuseC st + CaseC.admInd y / 2 ^ 128 := by
  unfold reuseC CaseC.reuseMass
  have hmemo : (st.born X y).memo = st.memo := rfl
  rw [hmemo]
  calc
    _ ≤ ∑' m : Message, ((if (st.memo.lookup m).isSome then 0 else
          (∑' p : Digest × Fin (2 ^ 32), CaseC.admissibleEntry st.cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128) +
          (∑' p : Digest × Fin (2 ^ 32), if Sampling.digestTrial p.1 m p.2.val = X then CaseC.admInd y else 0) /
            2 ^ 128) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs
      · exact zero_le
      · rw [← ENNReal.add_div, ← ENNReal.tsum_add]
        apply ENNReal.div_le_div_right
        apply ENNReal.tsum_le_tsum
        intro p
        exact admissibleEntry_birth st X _ y hX
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := by
      apply add_le_add le_rfl
      simp only [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul' (tsum_trial_indicator_le X _) le_rfl
theorem reuseC_signed (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (hm : st.memo.lookup m = none) :
    reuseC (st.signed rho m found) + CaseC.reuseMass st.cache m = reuseC st := by
  obtain ⟨-, -, -, hb, -, hmemo⟩ := RouterState.signed_fields st rho m found
  have hcache : (st.signed rho m found).cache = st.cache := by
    funext X; simp only [RouterState.cache, hb]
  unfold reuseC
  rw [hmemo, hcache, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' => if (st.memo.lookup m').isSome then 0 else
    CaseC.reuseMass st.cache m')]
  simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro m'
  by_cases h : m' = m
  · subst h
    simp [List.lookup_cons]
  · have hb' : (m' == m) = false := by simpa using h
    simp only [List.lookup_cons, hb', if_neg h]
theorem expectedValue_uniform_reply (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]
theorem psi_birth_le (q : Nat) (st : RouterState) (X : HashInput) (hX : st.cache X = none)
    (hlen : st.births.length < q) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
        (fun y => psi q (st.born X y)) ≤
      psi q st + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  rw [expectedValue_uniform_reply]
  have hs : (bankOf q st).slack = (q - (st.births.length + 1)) + 1 := by
    change q - st.births.length = _
    omega
  have h := CaseC.core_birth (bankOf q st) _ hs
    (fun y => reuseC (st.born X y))
    (fun y => reuseC_birth st X y hX)
  refine le_trans (le_of_eq ?_) h
  apply tsum_congr
  intro y
  have hb : bankOf q (st.born X y) = { bankOf q st with
      targets := (bankOf q st).targets ++ [(y : HashOutput)]
      slack := q - (st.births.length + 1)
      reuse := reuseC (st.born X y) } := by
    simp only [bankOf, RouterState.born, List.map_cons, List.reverse_cons, List.length_cons]
    rfl
  congr 1
  exact congrArg CaseC.corePotential hb
theorem psi_cert (q : Nat) (st : RouterState) (h : CertGhost st) : 1 ≤ psi q st := by
  apply CaseC.core_win
  · exact not_lt.mpr h.1
  · rcases h.2 with h | ⟨p, hp, hadm, hcov⟩
    · exact Or.inl h
    · refine Or.inr ⟨p.2, ?_, hadm, hcov⟩
      change p.2 ∈ (st.births.map Prod.snd).reverse
      rw [List.mem_reverse]
      exact List.mem_map_of_mem hp
theorem psi_initial (q : Nat) : psi q RouterState.initial ≤ (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h0 : reuseC RouterState.initial = 0 := by
    unfold reuseC
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    have hc : ∀ Z, RouterState.initial.cache Z = none := fun _ => rfl
    have hm : RouterState.initial.memo.lookup m = none := rfl
    simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false]
    simp only [CaseC.reuseMass, CaseC.admissibleEntry, hc, Option.elim_none, tsum_zero, ENNReal.zero_div]
  unfold psi bankOf
  rw [h0]
  exact CaseC.core_initial q
end SigGolfCandidate.T3.Security.LargeCoupling
