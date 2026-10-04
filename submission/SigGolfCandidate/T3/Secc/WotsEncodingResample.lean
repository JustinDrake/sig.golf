import SigGolfCandidate.T3.Secc.WotsEncodingCongr
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Enc
theorem uniform_resample {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
  let _ : DecidableEq K := Classical.decEq K
  apply PMF.ext
  intro ω₀
  obtain ⟨k₀, hk₀⟩ : ∃ k, k = d ω₀ := ⟨_, rfl⟩
  let σ : Ω × X k₀ → Ω × X k₀ := fun p =>
    if h : d p.1 = k₀ then (ov k₀ p.1 p.2, rd k₀ p.1) else p
  have hov : ∀ ω (h : d ω = k₀) (x : X k₀), d (ov k₀ ω x) = k₀ := by
    intro ω h x
    subst h
    exact h3 ω x
  have hσ : Function.Involutive σ := by
    rintro ⟨ω, x⟩
    by_cases h : d ω = k₀
    · have h' := hov ω h x
      simp only [σ, dif_pos h, dif_pos h']
      subst h
      rw [h2 ω x, h1 ω x]
    · simp only [σ, dif_neg h]
  have hinner : ∀ ω, (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
      if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
      else 0 := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h]
      have hgen : ∀ k (hk : d ω = k), (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
          (PMF.uniformOfFintype (X k)).map (ov k ω) ω₀ := by
        rintro k rfl; rfl
      rw [hgen k₀ h, PMF.map_apply]
      apply tsum_congr
      intro x
      simp only [σ, dif_pos h]
      by_cases he : ω₀ = ov k₀ ω x
      · rw [if_pos he, if_pos he.symm, mul_one]
      · rw [if_neg he, if_neg (fun h' => he h'.symm), mul_zero]
    · rw [if_neg h, PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      rw [if_neg]
      intro he
      apply h
      rw [hk₀, he, h3 ω x]
  rw [PMF.bind_apply]
  simp only [hinner]
  have hconst : ∀ (ω : Ω) (x : X k₀), PMF.uniformOfFintype Ω ω * PMF.uniformOfFintype (X k₀) x =
      PMF.uniformOfFintype (Ω × X k₀) (ω, x) := by
    intro ω x
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    rw [ENNReal.mul_inv (by simp) (by simp)]
  have hfiber : ∀ ω, PMF.uniformOfFintype Ω ω *
      (if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
        else 0) =
      ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω, x) * (if (σ (ω, x)).1 = ω₀ then 1 else 0) := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      rw [← mul_assoc, hconst]
    · rw [if_neg h, mul_zero]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have : (σ (ω, x)).1 = ω := by simp only [σ, dif_neg h]
      rw [this, if_neg (fun he => h (by rw [he, hk₀])), mul_zero]
  simp only [hfiber]
  rw [← ENNReal.tsum_prod (f := fun ω x => PMF.uniformOfFintype (Ω × X k₀) (ω, x) *
    (if (σ (ω, x)).1 = ω₀ then 1 else 0))]
  have hc : ∀ p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p = PMF.uniformOfFintype (Ω × X k₀) (σ p) := by
    intro p
    simp only [PMF.uniformOfFintype_apply]
  calc (∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (p.1, p.2) * (if (σ (p.1, p.2)).1 = ω₀ then 1 else 0))
      = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (σ p) * (if (σ p).1 = ω₀ then 1 else 0) := by
        apply tsum_congr
        intro p
        rw [← hc p]
    _ = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0) :=
        (hσ.toPerm σ).tsum_eq (fun p => PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0))
    _ = ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω₀, x) := by
        rw [ENNReal.tsum_prod']
        rw [tsum_eq_single ω₀]
        · simp only [if_true, mul_one]
        · intro ω hω
          apply ENNReal.tsum_eq_zero.mpr
          intro x
          rw [if_neg hω, mul_zero]
    _ = PMF.uniformOfFintype Ω ω₀ := by
        simp only [← hconst, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
theorem tsum_bind_mul {α β : Type} (μ : PMF α) (g : α → PMF β) (F : β → ENNReal) :
    ∑' b, (μ.bind g) b * F b = ∑' a, μ a * ∑' b, g a b * F b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [mul_assoc]
theorem tsum_map_mul {α β : Type} (μ : PMF α) (f : α → β) (F : β → ENNReal) :
    ∑' b, (μ.map f) b * F b = ∑' a, μ a * F (f a) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a)]
  · rw [if_pos rfl]
  · intro b hb
    rw [if_neg hb, zero_mul]
theorem uniform_resample_tsum {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) (F : Ω → ENNReal) :
    ∑' ω, PMF.uniformOfFintype Ω ω * F ω =
      ∑' ω, PMF.uniformOfFintype Ω ω * ∑' x, PMF.uniformOfFintype (X (d ω)) x * F (ov (d ω) ω x) := by
  conv_lhs => rw [← uniform_resample d ov rd h1 h2 h3]
  rw [tsum_bind_mul]
  refine tsum_congr fun ω => ?_
  rw [tsum_map_mul]
abbrev EncIndex := CanonGraph.LeafPos × (Digest × BitVec 96 × Digest) × BitVec 32
def encInput (e : EncIndex) : HashInput := encodingRow (leafOf e.1) e.2.1 e.2.2
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 := by
  simp [encInput, encodingRow, encodingInput, pad64, bytesLE_length]
theorem encInput_injective : Function.Injective encInput := by
  rintro ⟨L, m, c⟩ ⟨L', m', c'⟩ he
  have he' := Sampling.pad64_inj_of_length (by simp only [encodingInput, List.length_append, bytesLE_length]) he
  have ht : L.tree.val < 2 ^ 40 := lt_of_lt_of_le L.tree.isLt (by norm_num)
  have ht' : L'.tree.val < 2 ^ 40 := lt_of_lt_of_le L'.tree.isLt (by norm_num)
  have hl : L.leaf.val < 2 ^ 32 := lt_of_lt_of_le L.leaf.isLt (by norm_num)
  have hl' : L'.leaf.val < 2 ^ 32 := lt_of_lt_of_le L'.leaf.isLt (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5⟩ := QuerySpace.encodingInput_injective ht ht' hl hl' he'
  obtain ⟨lay, tree, leaf⟩ := L
  obtain ⟨lay', tree', leaf'⟩ := L'
  simp only [leafOf] at h1 h2 h3
  subst h1 h4 h5
  have : tree = tree' := Fin.ext h2
  have : leaf = leaf' := Fin.ext h3
  subst tree leaf
  rfl
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
theorem encInput_encHeader (e : EncIndex) : EncHeader (encInput e) := by
  refine ⟨e.1.lay.val, e.1.tree.val, 0, e.1.leaf.val, ?_⟩
  unfold encInput encodingRow encodingInput leafOf
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  simp [Extract.hdrBlock, List.append_assoc, bytesLE_length]
theorem reached_encInput {T : Answers} {L : CanonGraph.LeafPos} {input : HashInput}
    (h : Reached T (leafOf L) input) : ∃ c : BitVec 32, input = encInput (L, leafMsg T (leafOf L), c) := by
  obtain ⟨c, -, rfl, -⟩ := h
  exact ⟨_, rfl⟩
def Free (T : Answers) (e : EncIndex) : Prop := ¬ Reached T (leafOf e.1) (encInput e)
def freeSet (T : Answers) : Set EncIndex := {e | Free T e}
theorem reached_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (L : CanonGraph.LeafPos)
    (input : HashInput) : Reached T' (leafOf L) input ↔ Reached T (leafOf L) input := by
  have hm : leafMsg T' (leafOf L) = leafMsg T (leafOf L) := leafMsg_congr_nonEnc (nonEnc_of_honest h) _
  have hrow : ∀ c, c < counterLimit → (∀ c' < c, decode (leafOf L).lay (low (T (.inl (.inr
      (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c')))))) = none) →
      T' (.inl (.inr (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c)))) =
        T (.inl (.inr (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c)))) := by
    intro c hc hprev
    exact h _ (Or.inr ⟨L, c, hc, rfl, hprev⟩)
  unfold Reached
  rw [hm]
  constructor
  · rintro ⟨c, hc, rfl, hprev⟩
    refine ⟨c, hc, rfl, fun c' hc' => ?_⟩
    by_contra hvalid
    have hex : ∃ c'', c'' < c ∧ decode (leafOf L).lay (low (T (.inl (.inr
        (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'')))))) ≠ none := ⟨c', hc', hvalid⟩
    classical
    let c₀ := Nat.find hex
    have hc₀ : c₀ < c ∧ _ := Nat.find_spec hex
    have hmin : ∀ c'' < c₀, decode (leafOf L).lay (low (T (.inl (.inr
        (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'')))))) = none := by
      intro c'' hc''
      have := Nat.find_min hex hc''
      push Not at this
      exact this (lt_trans hc'' hc₀.1)
    have hagree := hrow c₀ (lt_trans hc₀.1 hc) hmin
    apply hc₀.2
    rw [← hagree]
    exact hprev c₀ hc₀.1
  · rintro ⟨c, hc, rfl, hprev⟩
    refine ⟨c, hc, rfl, fun c' hc' => ?_⟩
    have hprev' : ∀ c'' < c', decode (leafOf L).lay (low (T (.inl (.inr
        (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c'')))))) = none :=
      fun c'' hc'' => hprev c'' (lt_trans hc'' hc')
    rw [hrow c' (lt_trans hc' hc) hprev']
    exact hprev c' hc'
theorem free_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) : freeSet T' = freeSet T := by
  ext e
  simp only [freeSet, Set.mem_ofPred_eq, Free]
  rw [reached_congr h]
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
theorem ov_at (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput)
    (e : k) : ov k pub y ⟨encInput e.val, hU (encInput_short e.val)⟩ = y e := by
  unfold ov
  have h : ∃ e', e' ∈ k ∧ encInput e' = encInput e.val := ⟨e.val, e.property, rfl⟩
  rw [dif_pos h]
  have he : Classical.choose h = e.val := encInput_injective (Classical.choose_spec h).2
  congr 1
  exact Subtype.ext he
theorem ov_other (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) (u : U)
    (hu : ∀ e, e ∈ k → encInput e ≠ u.val) : ov k pub y u = pub u := by
  unfold ov
  rw [dif_neg]
  rintro ⟨e, he, heq⟩
  exact hu e he heq
theorem rd_ov (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) :
    rd hU k (ov k pub y) = y := by
  funext e
  exact ov_at hU k pub y e
theorem ov_ov_rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput)
    (y : k → HashOutput) : ov k (ov k pub y) (rd hU k pub) = pub := by
  funext u
  unfold ov
  split_ifs with h
  · unfold rd
    congr 1
    exact Subtype.ext ((Classical.choose_spec h).2)
  · rfl
end Overwrite
section Tables
variable (U : Finset HashInput)
theorem eagerAnswers_public_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput) (u : U) :
    eagerAnswers U privateTable pub (.inl (.inr u.val)) = pub u := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub u.val = pub u
  rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U pub u.val u.property (by simp)]
theorem eagerAnswers_public_not_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (input : HashInput) (h : input ∉ U) : eagerAnswers U privateTable pub (.inl (.inr input)) = (0 : HashOutput) := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub input = 0
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  simp [h]
  rfl
theorem honest_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    ∀ q, HonestQ (eagerAnswers U privateTable pub) q →
      eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) q =
        eagerAnswers U privateTable pub q := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
        eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
      apply ov_other
      intro e he heq
      rcases hq with hnon | ⟨L, hr⟩
      · have h' : encInput e = input := heq
        exact hnon (h' ▸ encInput_encHeader e)
      · obtain ⟨c, hc⟩ := reached_encInput hr
        have hee := encInput_injective ((show encInput e = input from heq).trans hc)
        apply he
        rw [hee, ← hc]
        exact hr
    · rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · simp only [eagerAnswers]
theorem free_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    freeSet (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) =
      freeSet (eagerAnswers U privateTable pub) :=
  free_congr (honest_ov U privateTable pub y)
theorem public_resample (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput))
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
          F (ov (freeSet (eagerAnswers U privateTable pub)) pub y) :=
  @uniform_resample_tsum (U → HashOutput) (Set EncIndex) _ _ (fun k : Set EncIndex => k → HashOutput) iX _
    (fun pub => freeSet (eagerAnswers U privateTable pub)) (fun k pub y => ov k pub y) (fun k pub => rd hU k pub)
    (fun pub y => rd_ov hU _ pub y) (fun pub y => ov_ov_rd hU _ pub y) (fun pub y => free_ov U privateTable pub y) F
end Tables
end Enc
end SigGolfCandidate.T3.Security.Wots
