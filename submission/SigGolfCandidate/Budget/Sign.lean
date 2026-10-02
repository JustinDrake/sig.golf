import SigGolfCandidate.Budget.PairedSearch

/-!
# Budget: the expectation bound for `signRef` (PORS+FP: MAC check, cached top tree)

From any random-oracle cache without tweak types `4`, `7`, `12` (e.g. after keygen, which only
queries types `0..3`, `13`, `14`), and for **every** cache argument, the expectation of
`z ^ (compressions of signRef sk cache m)` is at most

  `z ^ 3 * (bD * (z ^ 40959 * (counterProduct bC 5 * z ^ (73244 + 217))))`,

where `bD` bounds the digest search and `bC i` the counter search in layer `i` (`V_signRef`). The
deterministic part (paired PRF secrets, 5 layers (11,6,6,6,5), targets 185/186) is MAC keys 3 + PORS tree
40959 + layers 1..4 73244 + top layer 217 = 115258 blocks (top layer: 21 paired secret queries,
`targetSum = 185` chain steps, 11 masks).
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist Finset

/-- Compressions of the trees of layers `1 .. n`. -/
def layerCost (n : Nat) : Nat := ∑ l ∈ Finset.range n, treeCost (height (l + 1))

theorem layerCost_succ (n : Nat) : layerCost (n + 1) = layerCost n + treeCost (height (n + 1)) := by
  simp [layerCost, Finset.sum_range_succ]

theorem layerCost_4 : layerCost 4 = 73244 := by decide

/-- Before the layers `n-1 .. 0`: every cached counter query is of a layer `≥ n`. -/
def InvL (n : Nat) (q : Query) : Prop := qbyte q 1 = 4 → n ≤ qbyte q 2

/-- Sign's starting cache: no counter, randomizer or digest queries. -/
def Inv0 (q : Query) : Prop := qbyte q 1 ≠ 4 ∧ qbyte q 1 ≠ 7 ∧ qbyte q 1 ≠ 12

/-! ## The top layer -/

theorem sum_getD (x : List Nat) : ∑ i ∈ range x.length, x.getD i 0 = x.sum := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    omega

theorem spec_chainTo (lay tau e i x : Nat) (v : Val) (hv : v.length ≤ 16) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) x (chainTo lay tau e i x v) := by
  unfold chainTo
  refine Spec.foldlM_range'_le (P := fun _ => True) 1 x _ (fun _ (w : Val) => w.length ≤ 16)
    (fun _ => 1) v hv (fun i' _ w hw => ?_) (fun _ h => h) (by simp)
  exact spec_hash16_bind (chainInput lay tau e i (1 + i') w) trivial
    (blocksFmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl

theorem sum_pairs (f : Nat → Nat) (n : Nat) :
    ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) = ∑ i ∈ range (2 * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_assoc]

theorem spec_topPath (S cache : List Byte) (hS : S.length = 32) (e : Nat) :
    Spec (fun _ => True) (fun _ => True) 11 (topPath S cache e) := by
  unfold topPath
  rw [topH_eq]
  refine Spec.foldlM_range_le (P := fun _ => True) 11 _ (fun _ (_ : List Val) => True)
    (fun _ => 1) [] trivial (fun l _ acc _ => ?_) (fun _ _ => trivial) (by simp)
  exact spec_hash16_bind _ trivial (mask_ok S hS l _).2 (fun _ _ => Spec.pure _ 0 trivial) le_rfl

/-- Compressions of the top layer after its counter search. -/
def topCost : Nat := 21 + 185 + 11

theorem V_signTop (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC 0 * bC + (1 - rhoC 0)) ≤ bC) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) (M : Val) (c : RCache) (hM : M.length ≤ 32) (hinv : CacheInv (InvL 1) c) :
    V z (signTop S cache idx M) c ≤ bC * z ^ topCost := by
  unfold signTop
  rcases hr : route idx 0 with ⟨e, tau⟩
  dsimp only
  have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 → c (addrFmt (encInput 0 tau e M c')) = none := by
    intro c' _ _
    cases hq : c (addrFmt (encInput 0 tau e M c')) with
    | none => rfl
    | some u =>
      exfalso
      have h := hinv _ u hq (by rw [qbyte_tag_enc])
      rw [qbyte_lay_enc] at h; omega
  refine (V_bind_le z _ _ c (z ^ topCost) fun x hx => ?_).trans
    (mul_le_mul' (V_searchCounter 0 z bC hz hbC hstepC tau e M hM cMax 0 c (by simp [cMax])
      hfresh) le_rfl)
  have hx' := (spec_searchCounter 0 tau e M hM (by omega) cMax 0).support
    (I := fun _ => True) (fun _ _ => trivial) c (fun _ _ _ => trivial) x hx
  obtain ⟨o, c1⟩ := x
  rcases o with _ | ⟨cnt, xs⟩
  · simpa using one_le_pow₀ hz
  · dsimp only
    obtain ⟨hlen, hsum⟩ := hx'.1 cnt xs rfl
    refine Spec.V_le (P := fun _ => True) (Post := fun _ => True) ?_ hz c1
    refine Spec.bind' (l := 11) (Spec.foldlM_range (P := fun _ => True) (nChains / 2) _
      (fun _ (_ : List Val) => True) (fun k => 1 + (xs.getD (2 * k) 0 + xs.getD (2 * k + 1) 0))
      [] trivial (fun k _ acc _ => ?_)) (fun vals _ => ?_) ?_
    · obtain ⟨h1, h2⟩ := prf_ok S hS 0 tau e k
      refine spec_prf2 _ trivial h2 (l := xs.getD (2 * k) 0 + xs.getD (2 * k + 1) 0)
        (fun sp hs0 hs1 => ?_) le_rfl
      obtain ⟨s0, s1⟩ := sp
      dsimp only at hs0 hs1 ⊢
      refine (spec_chainTo 0 tau e (2 * k) _ s0 hs0).bind' (fun v0 _ => ?_) le_rfl
      exact (spec_chainTo 0 tau e (2 * k + 1) _ s1 hs1).bind' (l := 0)
        (fun _ _ => Spec.pure _ 0 trivial) (by omega)
    · exact (spec_topPath S cache hS e).bind' (l := 0) (fun _ _ => Spec.pure _ 0 trivial) le_rfl
    · have h42 : 2 * (nChains / 2) = xs.length := by rw [hlen]; rfl
      rw [Finset.sum_add_distrib, sum_pairs (fun i => xs.getD i 0), h42, sum_getD, hsum]
      simp [topCost, targetFor, targetSum, nChains]

/-- Product of the separate counter-search envelopes. -/
noncomputable def counterProduct (b : Nat → ℝ≥0∞) (n : Nat) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, b i

@[simp] theorem counterProduct_zero (b : Nat → ℝ≥0∞) : counterProduct b 0 = 1 := by
  simp [counterProduct]

theorem counterProduct_succ (b : Nat → ℝ≥0∞) (n : Nat) :
    counterProduct b (n + 1) = counterProduct b n * b n := by
  exact Finset.prod_range_succ b n

theorem one_le_counterProduct {b : Nat → ℝ≥0∞} (hb : ∀ i, 1 ≤ b i) (n : Nat) :
    1 ≤ counterProduct b n := by
  exact Finset.one_le_prod (fun i _ => hb i)

theorem V_signLayers (z : ℝ≥0∞) (bC : Nat → ℝ≥0∞) (hz : 1 ≤ z) (hbC : ∀ i, 1 ≤ bC i)
    (hstepC : ∀ i, z * (rhoC i * bC i + (1 - rhoC i)) ≤ bC i) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) :
    ∀ lay (M : Val) (c : RCache), lay ≤ 4 → M.length ≤ 32 → CacheInv (InvL (lay + 1)) c →
      V z (signLayers S cache idx lay M) c ≤ counterProduct bC (lay + 1) * z ^ (layerCost lay + topCost) := by
  intro lay
  induction lay with
  | zero =>
    intro M c _ hM hinv
    simp only [signLayers, layerCost, Finset.range_zero, Finset.sum_empty, Nat.zero_add, counterProduct_succ, counterProduct_zero, one_mul]
    exact V_signTop z (bC 0) hz (hbC 0) (hstepC 0) S cache hS idx M c hM hinv
  | succ lay ih =>
    intro M cache' hlay hM hinv
    have hpos : 0 < height (lay + 1) := by
      have h4 : lay < 4 := by omega
      interval_cases lay <;> decide
    unfold signLayers
    rcases hr : route idx (lay + 1) with ⟨e, tau⟩
    dsimp only
    have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 →
        cache' (addrFmt (encInput (lay + 1) tau e M c')) = none := by
      intro c' _ _
      cases hq : cache' (addrFmt (encInput (lay + 1) tau e M c')) with
      | none => rfl
      | some u =>
        exfalso
        have h := hinv _ u hq (by rw [qbyte_tag_enc])
        rw [qbyte_lay_enc] at h; omega
    refine (V_bind_le z _ _ cache' (counterProduct bC (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) fun x hx => ?_).trans ?_
    · have hx' := (spec_searchCounter (lay + 1) tau e M hM (by omega) cMax 0).support
        (I := InvL (lay + 1)) (fun q hq h => by rw [hq.2]) cache'
        (hinv.mono fun q h h4 => by have := h h4; omega) x hx
      obtain ⟨o, c1⟩ := x
      have hbig : 1 ≤ counterProduct bC (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)) := one_le_mul (one_le_counterProduct hbC _) (one_le_pow₀ hz)
      rcases o with _ | ⟨cnt, xs⟩
      · simpa using hbig
      · dsimp only
        refine (V_bind_le z _ _ c1 (counterProduct bC (lay + 1) * z ^ (layerCost lay + topCost))
          fun y hy => ?_).trans ?_
        · have hy' := (spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs hpos).support
            (I := InvL (lay + 1)) (fun q hq h => by unfold PT at hq; omega) c1 hx'.2 y hy
          obtain ⟨⟨root, vals, path⟩, c2⟩ := y
          dsimp only
          refine (V_bind_le z _ _ c2 1 fun w _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := w
            rcases r with _ | rest <;> simp
          · rw [mul_one]; exact ih root c2 (by omega) hy'.1 hy'.2
        · rw [pow_add z (treeCost (height (lay + 1))) (layerCost lay + topCost)]
          calc V z (buildTree S (lay + 1) tau (height (lay + 1)) e xs) c1 *
                (counterProduct bC (lay + 1) * z ^ (layerCost lay + topCost))
              ≤ z ^ treeCost (height (lay + 1)) * (counterProduct bC (lay + 1) * z ^ (layerCost lay + topCost)) :=
                mul_le_mul' ((spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs hpos).V_le hz c1)
                  le_rfl
            _ = counterProduct bC (lay + 1) * (z ^ treeCost (height (lay + 1)) *
                  z ^ (layerCost lay + topCost)) := by ring
    · rw [layerCost_succ]
      calc V z (searchCounter (lay + 1) tau e M 0 cMax) cache' * (counterProduct bC (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)))
          ≤ bC (lay + 1) * (counterProduct bC (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) :=
            mul_le_mul' (V_searchCounter (lay + 1) z (bC (lay + 1)) hz (hbC (lay + 1)) (hstepC (lay + 1)) tau e M hM cMax 0 cache'
              (by simp [cMax]) hfresh) le_rfl
        _ = counterProduct bC (lay + 1 + 1) * z ^ (layerCost lay + treeCost (height (lay + 1)) + topCost) := by
            rw [show layerCost lay + treeCost (height (lay + 1)) + topCost =
              treeCost (height (lay + 1)) + (layerCost lay + topCost) by omega, counterProduct_succ bC (lay + 1)]
            ring

theorem spec_H {P : Query → Prop} (x : List Byte) (k : Nat) (hP : P (addrFmt x))
    (hk : (addrFmt x).blocks ≤ k) : Spec P (fun _ => True) k (Ref.H x) := by
  rw [← bind_pure (Ref.H x)]
  exact Spec.qry_bind hP (fun u => Spec.pure _ 0 trivial) (by omega)

/-- The signing bound without the MAC check. -/
noncomputable abbrev signBound (z bD : ℝ≥0∞) (bC : Nat → ℝ≥0∞) : ℝ≥0∞ :=
  bD * (z ^ 40959 * (counterProduct bC 5 * z ^ (73244 + 217)))

set_option maxRecDepth 100000 in
/-- The expectation bound for the part of `signList` after the MAC check, from `Inv0`. -/
theorem V_signBody (z bD : ℝ≥0∞) (bC : Nat → ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : ∀ i, 1 ≤ bC i)
    (hstepD : z ^ 2 * (1 - rhoD) + z ^ 3 * rhoD * (1 - rhoD) +
      z ^ 3 * (rhoD ^ 2 + 2 * epsP) * bD ≤ bD)
    (hstepC : ∀ i, z * (rhoC i * bC i + (1 - rhoC i)) ≤ bC i)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (do
      match ← searchDigestPairs S m 0 aMax with
      | none => pure none
      | some (rho, N) =>
        let (levels, secrets) ← buildPorsTree S (idxOf N)
        let M := (levels.getD porsH []).getD 0 []
        let fts := porsOpening (sortLeaves (leavesOf N)) levels secrets
        match ← signLayers S cache (idxOf N) (nLayers - 1) (P ++ M) with
        | none => pure none
        | some lays => pure (some (serialize rho fts lays))) c ≤ signBound z bD bC := by
  have hbig : 1 ≤ z ^ 40959 * (counterProduct bC 5 * z ^ (73244 + 217)) :=
    one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_counterProduct hbC _) (one_le_pow₀ hz))
  refine (V_bind_le z _ _ c _ fun x hx => ?_).trans (mul_le_mul' ?_ le_rfl)
  · have hx' := (spec_searchDigestPairs S m hS hm aMax 0).support
      (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PD at hq; omega) c
      (hinv.mono fun q h => h.1) x hx
    obtain ⟨o, c1⟩ := x
    rcases o with _ | ⟨rho, N⟩
    · simpa using hbig
    · dsimp only
      refine (V_bind_le z _ _ c1 (counterProduct bC 5 * z ^ (73244 + 217)) fun y hy => ?_).trans ?_
      · have hy' := (spec_buildPorsTree S hS (idxOf N)).support (I := fun q => qbyte q 1 ≠ 4)
          (fun q hq => by unfold PP at hq; omega) c1 hx'.2 y hy
        obtain ⟨⟨levels, secrets⟩, c2⟩ := y
        dsimp only
        refine (V_bind_le z _ _ c2 1 fun r _ => ?_).trans ?_
        · obtain ⟨r, _⟩ := r
          rcases r with _ | lays <;> simp
        · rw [mul_one, ← layerCost_4, show (217 : Nat) = topCost from rfl]
          refine V_signLayers z bC hz hbC hstepC S cache hS (idxOf N) (nLayers - 1) _ c2
            (by decide) (by
              have hlen : ((levels.getD porsH []).getD 0 []).length ≤ 16 := hy'.1
              simp only [List.length_append, P, zeros, List.length_replicate]
              omega) ?_
          exact hy'.2.mono fun q h h4 => absurd h4 h
      · refine mul_le_mul' ?_ le_rfl
        rw [← porsCost_eq]
        exact (spec_buildPorsTree S hS (idxOf N)).V_le hz c1
  · refine V_searchDigestPairs z bD hz hbD hstepD S m hS hm aMax 0 c ∅ (by simp [aMax]) (by simp)
      (fun a' _ _ => ?_) (fun rho _ _ => ?_)
    · cases hq : c (addrFmt (rndInput S m a')) with
      | none => rfl
      | some u =>
        exfalso
        have h7 : qbyte (addrFmt (rndInput S m a')) 1 = 7 := by
          rw [qbyte_fmt _ _ (by decide)]
          simp [rndInput, byte_toNat]
        exact (hinv _ u hq).2.1 h7
    · cases hq : c (addrFmt (digestInput rho m)) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.2; unfold digestInput at this; rw [qbyte_tag] at this
        exact this rfl

/-- The expectation bound for `signList` (MAC check first), for every cache argument. -/
theorem V_signList (z bD : ℝ≥0∞) (bC : Nat → ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : ∀ i, 1 ≤ bC i)
    (hstepD : z ^ 2 * (1 - rhoD) + z ^ 3 * rhoD * (1 - rhoD) +
      z ^ 3 * (rhoD ^ 2 + 2 * epsP) * bD ≤ bD)
    (hstepC : ∀ i, z * (rhoC i * bC i + (1 - rhoC i)) ≤ bC i)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (signList S cache m) c ≤ z ^ 3 * signBound z bD bC := by
  unfold signList
  have hs := fun i => spec_H (P := fun q => qbyte q 1 = 14) (macKeyInput S i) 1 (macKey_ok S hS i).1
    (macKey_ok S hS i).2
  have hI : ∀ q, qbyte q 1 = 14 → Inv0 q := fun q hq => by unfold Inv0; omega
  refine (V_bind_le z _ _ c (z ^ 2 * signBound z bD bC) fun x0 hx0 => ?_).trans
    ((mul_le_mul' ((hs 0).V_le hz c) le_rfl).trans (le_of_eq (by ring)))
  have h0 := (hs 0).support (I := Inv0) hI c hinv x0 hx0
  refine (V_bind_le z _ _ x0.2 (z ^ 1 * signBound z bD bC) fun x1 hx1 => ?_).trans
    ((mul_le_mul' ((hs 1).V_le hz x0.2) le_rfl).trans (le_of_eq (by ring)))
  have h1 := (hs 1).support (I := Inv0) hI x0.2 h0.2 x1 hx1
  refine (V_bind_le z _ _ x1.2 (signBound z bD bC) fun x2 hx2 => ?_).trans
    (mul_le_mul' ((hs 2).V_le hz x1.2) le_rfl)
  have h2 := (hs 2).support (I := Inv0) hI x1.2 h1.2 x2 hx2
  dsimp only
  split
  · exact V_signBody z bD bC hz hbD hbC hstepD hstepC S cache m hS hm x2.2 h2.2
  · simp only [V_pure]
    exact one_le_mul hbD (one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_counterProduct hbC _)
      (one_le_pow₀ hz)))

theorem V_signRef (z bD : ℝ≥0∞) (bC : Nat → ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : ∀ i, 1 ≤ bC i)
    (hstepD : z ^ 2 * (1 - rhoD) + z ^ 3 * rhoD * (1 - rhoD) +
      z ^ 3 * (rhoD ^ 2 + 2 * epsP) * bD ≤ bD)
    (hstepC : ∀ i, z * (rhoC i * bC i + (1 - rhoC i)) ≤ bC i)
    (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache) (hinv : CacheInv Inv0 c) :
    V z (signRef sk cache m) c ≤ z ^ 3 * signBound z bD bC := by
  unfold signRef
  refine (V_bind_le z _ _ c 1 fun _ _ => by simp).trans ?_
  rw [mul_one]
  exact V_signList z bD bC hz hbD hbC hstepD hstepC _ _ _ (length_toList sk) (length_toList m)
    c hinv

end SigGolfCandidate.Budget
