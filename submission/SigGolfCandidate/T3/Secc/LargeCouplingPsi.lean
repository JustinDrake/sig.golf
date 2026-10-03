import SigGolfCandidate.T3.Secc.LargeCouplingSwap

/-!
# LR-34 (law, 2/3): the eager table of the router's data

`tablePsi U hU hE vals nv τ a` is the eager answers table built from the router's data: secrets `vals ∘ inr`, labels
`joinLabels (vals ∘ inl) a.high` programmed on the canonical cells, nonce low halves `nv`, the other private halves
from `a.priv`, the honest-message encoding rows of route leaves from `a.rows` on their first-success prefix and from
`τ` beyond it (`residualPsi`), every other row from `τ`.

**`coherent_psi`**: it is coherent with the data (`Coherent U (tablePsi …) vals nv τ a`).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Private part -/

theorem nonce_not_secret (m : Message) :
    (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) ∉ Set.range secretCoordinate := by
  rintro ⟨s, hs⟩
  have hp := congrArg Prod.fst hs
  cases s <;> cases hp

/-- The nonce low half of a message, as an other private half. -/
def nonceHalf (m : Message) : OtherHalf := ⟨((.inr (.inl m) : Coordinate), 0), nonce_not_secret m⟩

theorem nonceHalf_injective : Function.Injective nonceHalf := by
  intro m m' h
  have h1 := congrArg (fun x : OtherHalf => x.val.1) h
  simp only [nonceHalf] at h1
  exact Sum.inl.inj (Sum.inr.inj h1)

/-- The other private halves with the nonce low halves overwritten. -/
noncomputable def nonceOver (o : OtherHalves) (nvv : Message → Digest) : OtherHalves :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite nonceHalf nonceHalf_injective nvv o

/-- The private table of the router's data. -/
noncomputable def privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) : FullGame.FullTable :=
  privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)

theorem privateEquiv_snd (t : FullGame.FullTable) (h : OtherHalf) : (privateEquiv t).2 h = ChainGraph.halves t h.val := by
  change (splitEquiv (ChainGraph.halves t)).2 h = _
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow]
  rfl

theorem halves_privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable)
    (h : ChainGraph.HalfCoordinate) (hs : h ∉ Set.range secretCoordinate) :
    ChainGraph.halves (privPsi s nvv priv) h =
      if hn : ∃ m, h = ((.inr (.inl m) : Coordinate), 0) then nvv (Classical.choose hn)
      else ChainGraph.halves priv h := by
  have h1 := privateEquiv_snd (privPsi s nvv priv) ⟨h, hs⟩
  unfold privPsi at h1
  rw [Equiv.apply_symm_apply] at h1
  change (nonceOver (privateEquiv priv).2 nvv) ⟨h, hs⟩ = _ at h1
  change ChainGraph.halves (privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)) (⟨h, hs⟩ : OtherHalf).val = _
  rw [← h1]
  split_ifs with hn
  · have hm := Classical.choose_spec hn
    have heq : (⟨h, hs⟩ : OtherHalf) = nonceHalf (Classical.choose hn) := Subtype.ext hm
    rw [heq]
    exact SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed _ _ _ _ _
  · rw [nonceOver, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ (by
      rintro ⟨m, hm⟩
      exact hn ⟨m, (congrArg Subtype.val hm).symm⟩), privateEquiv_snd]

theorem privPsi_other (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (c : Coordinate)
    (hc : ∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) (hn : ∀ m : Message, c ≠ .inr (.inl m)) :
    privPsi s nvv priv c = priv c := by
  have hh : ∀ i : Fin 2, ChainGraph.halves (privPsi s nvv priv) (c, i) = ChainGraph.halves priv (c, i) := by
    intro i
    rw [halves_privPsi s nvv priv (c, i) (hc i), dif_neg]
    rintro ⟨m, hm⟩
    exact hn m (congrArg Prod.fst hm)
  have h0 := hh 0
  have h1 := hh 1
  simp only [ChainGraph.halves] at h0 h1
  simp only [Fin.isValue, Fin.val_zero, if_true, Fin.val_one, one_ne_zero, if_false] at h0 h1
  rw [← ChainGraph.joinOutput_parts (privPsi s nvv priv c), ← ChainGraph.joinOutput_parts (priv c), h0, h1]

theorem privPsi_nonce (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (m : Message) :
    (privPsi s nvv priv (.inr (.inl m))).extractLsb' 0 128 = nvv m := by
  have h := halves_privPsi s nvv priv _ (nonce_not_secret m)
  rw [dif_pos ⟨m, rfl⟩] at h
  have hm : Classical.choose (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) =
      ((.inr (.inl m') : Coordinate), 0)) = m := by
    have := Classical.choose_spec (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) :
      ChainGraph.HalfCoordinate) = ((.inr (.inl m') : Coordinate), 0))
    have h1 := congrArg Prod.fst this
    exact (Sum.inl.inj (Sum.inr.inj h1)).symm
  rw [hm] at h
  simpa [ChainGraph.halves] using h

theorem privateSecrets_privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) :
    privateSecrets (privPsi s nvv priv) = s := privateSecrets_symm _ _

/-! ## Public part -/

/-- The first-success prefix of the honest-message rows of a route leaf (all counters if no success). -/
def rowPrefix (f : EncLeaf × Fin (2 ^ 22) → HashOutput) (x : EncLeaf × Fin (2 ^ 22)) : Prop :=
  ∀ r, SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => f (x.1, c)) = some r → x.2 ≤ r.1

theorem select_congr_prefix (L : EncLeaf) (f g : Fin (2 ^ 22) → HashOutput)
    (h : ∀ c, (∀ r, SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f = some r → c ≤ r.1) → f c = g c) :
    SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) g =
      SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f := by
  cases hs : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f with
  | none =>
      have hfg : f = g := funext fun c => h c (fun r hr => by rw [hs] at hr; cases hr)
      rw [← hfg, hs]
  | some r =>
      obtain ⟨i, v⟩ := r
      have hsome := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ f i v).mp hs
      apply (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g i v).mpr
      have hle : ∀ c, c ≤ i → f c = g c := fun c hc => h c (fun r hr => by
        rw [hs] at hr; cases hr; exact hc)
      refine ⟨by rw [← hle i le_rfl]; exact hsome.1, fun j hj => ?_⟩
      rw [← hle j (le_of_lt hj)]
      exact hsome.2 j hj

theorem rowPrefix_determined : PrefixDetermined rowPrefix := by
  intro f g hfg x
  unfold rowPrefix
  have hsel : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => g (x.1, c)) =
      SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => f (x.1, c)) :=
    select_congr_prefix x.1 _ _ (fun c hc => hfg (x.1, c) hc)
  rw [hsel]

section Public
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)

/-- The residual public table of the router's data: `τ` with the honest-message encoding rows of route leaves
taken from the presampled rows on their first-success prefix. -/
noncomputable def residualPsi (labels : Labels) (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (τ : U → HashOutput) :
    U → HashOutput :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite (encCell U hE labels) (encCell_injective U hE labels)
    (mix rowPrefix (Function.uncurry rows) (fun x => τ (encCell U hE labels x))) τ

/-- **The eager table of the router's data.** -/
noncomputable def tablePsi (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput) (a : AuxData) :
    Answers :=
  Wots.eagerAnswers U (privPsi (fun s => vals (.inr s)) nv a.priv)
    (programmed U hU (fun s => vals (.inr s)) (routerLabels vals a) (residualPsi U hE (routerLabels vals a) a.rows τ))

theorem eagerAnswers_eq (priv : FullGame.FullTable) (pub : U → HashOutput) :
    Wots.eagerAnswers U priv pub = CanonGraph.eagerAnswers priv U pub := by
  funext q
  rcases q with (n | x) | c <;> rfl

theorem encCell_val (labels : Labels) (L : EncLeaf) (c : Fin (2 ^ 22)) :
    (encCell U hE labels (L, c)).val = Wots.encodingRow L.toWots (msgLabel labels L) (BitVec.ofNat 32 c.val) := rfl

theorem msgLabel_router (vals : Coord → Digest) (a : AuxData) (L : EncLeaf) :
    msgLabel (routerLabels vals a) L = vals (msgCoord L) := by
  unfold msgLabel msgCoord
  by_cases hl : L.1.lay.val < 3
  · rw [dif_pos hl, dif_pos hl, treeLabel_root]
    exact joinLabels_low _ _ _
  · rw [dif_neg hl, dif_neg hl]
    exact joinLabels_low _ _ _

theorem sel_psi (a : AuxData) (labels : Labels) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOf U hE labels (residualPsi U hE labels a.rows τ) L = a.sel L := by
  unfold selectionsOf AuxData.sel
  apply select_congr_prefix
  intro c hc
  unfold residualPsi
  rw [SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
  unfold mix
  rw [if_pos (show rowPrefix (Function.uncurry a.rows) (L, c) from hc)]
  rfl

theorem rowPrefix_iff (a : AuxData) (L : EncLeaf) (c : Fin (2 ^ 22)) :
    rowPrefix (Function.uncurry a.rows) (L, c) ↔ PrefixRow a L (BitVec.ofNat 32 c.val) := by
  have hc : (BitVec.ofNat 32 c.val).toNat = c.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
  unfold rowPrefix PrefixRow
  rw [hc]
  constructor
  · intro h
    exact ⟨c.isLt, fun r hr => h r hr⟩
  · intro h r hr
    exact h.2 r hr

end Public

section Coherence
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)

/-- **The router's data is coherent with its eager table.** -/
theorem coherent_psi (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput) (a : AuxData) :
    Coherent U (tablePsi U hU hE vals nv τ a) vals nv τ a := by
  set s : Secrets := fun x => vals (.inr x) with hs
  set labels := routerLabels vals a with hlabels
  set res := residualPsi U hE labels a.rows τ with hres
  set o := nonceOver (privateEquiv a.priv).2 nv with ho
  have hT : tablePsi U hU hE vals nv τ a = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) U
      (programmed U hU s labels res) := by
    unfold tablePsi
    rw [eagerAnswers_eq]
    rfl
  have hsec : secretsOf (tablePsi U hU hE vals nv τ a) = s := by
    rw [hT, secretsOf_eager, privateSecrets_symm]
  have hpubX : ∀ (X : HashInput) (hX : X ∈ U), tablePsi U hU hE vals nv τ a (.inl (.inr X)) =
      programmed U hU s labels res ⟨X, hX⟩ := by
    intro X hX
    rw [hT]
    exact eagerAnswers_mem _ U _ ⟨X, hX⟩
  refine ⟨?_, hsec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    exact eager_programmed_agrees U hU s o labels res
  · -- residual rows
    intro X hX hcell hpre
    rw [hpubX X hX, programmed_other U hU s labels res ⟨X, hX⟩ (fun N => by
      have := hcell N
      rw [hsec] at this
      exact this)]
    by_cases hr : (⟨X, hX⟩ : U) ∈ Set.range (encCell U hE labels)
    · obtain ⟨x, hx⟩ := hr
      rw [hres, residualPsi, ← hx, SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
      unfold mix
      rw [if_neg]
      intro hpx
      apply hpre
      obtain ⟨L, c⟩ := x
      refine ⟨L, BitVec.ofNat 32 c.val, ?_, (rowPrefix_iff a L c).mp hpx⟩
      have hv := congrArg Subtype.val hx
      rw [encCell_val, msgLabel_router] at hv
      exact hv.symm
    · rw [hres, residualPsi, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ hr]
  · -- presampled prefix rows
    intro L ctr hp
    have hc : BitVec.ofNat 32 (⟨ctr.toNat, hp.1⟩ : Fin (2 ^ 22)).val = ctr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hp.1; omega)
    have hX : Wots.encodingRow L.toWots (vals (msgCoord L)) ctr = (encCell U hE labels (L, ⟨ctr.toNat, hp.1⟩)).val := by
      rw [encCell_val, msgLabel_router, hc]
    rw [hX, hpubX _ (encCell U hE labels (L, ⟨ctr.toNat, hp.1⟩)).property]
    rw [programmed_other U hU s labels res _ (fun N => encodingQuery_ne_cell _ s N labels)]
    rw [hres, residualPsi, show (⟨(encCell U hE labels (L, ⟨ctr.toNat, hp.1⟩)).val,
      (encCell U hE labels (L, ⟨ctr.toNat, hp.1⟩)).property⟩ : U) = encCell U hE labels (L, ⟨ctr.toNat, hp.1⟩) from rfl,
      SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
    unfold mix
    rw [if_pos ((rowPrefix_iff a L _).mpr (by rw [hc]; exact hp))]
    unfold prefixValue
    rw [dif_pos hp.1]
    rfl
  · -- the honest searches are the presampled selections
    intro L
    have hpub : ∀ x : U, tablePsi U hU hE vals nv τ a (.inl (.inr x.val)) =
        programmed U hU (secretsOf (tablePsi U hU hE vals nv τ a)) labels res x := by
      intro x
      rw [hsec]
      exact hpubX x.val x.property
    rw [referenceSearch_eq U hU hE _ labels res hpub L, sel_psi]
  · -- other private coordinates
    intro c hc hn
    change privPsi s nv a.priv c = a.priv c
    exact privPsi_other s nv a.priv c hc hn
  · -- outside the universe
    intro X hX
    change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ X = 0
    unfold SphincsSecurity.Concrete.finiteHashAnswer
    rw [dif_neg hX]
    rfl
  · -- nonces
    intro m
    exact privPsi_nonce s nv a.priv m

end Coherence

end SigGolfCandidate.T3.Security.LargeCoupling
