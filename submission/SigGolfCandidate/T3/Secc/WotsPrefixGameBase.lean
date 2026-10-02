import SigGolfCandidate.T3.Secc.WotsMaskRef
import SigGolfCandidate.T3.Secc.WotsMaskRest
import SigGolfCandidate.T3.Secc.WotsExtractChain
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint

/-!
# Stream C (base): the hidden part of one chain inside R3's eager tables

R3 (`Wots.referenceExperiment`, stream F2) samples a uniform private table and a uniform public table over
`referenceInputs adversary`. For one chain address `a`, the part the generic `PartialChainEndpoint` model treats as
hidden is: the low halves of `a`'s canonical prefix rows (`chainRow a step value`, `step < depth a`, every value)
and `a`'s seed half of the private coordinate `seedTweak a`. Its size depends on `depth a`, which is a function
of the rest (F1's `depth_congr`).

* `PrefixGame.uniform_resample` (abstract): overwriting a self-determined part of a uniform sample with a fresh
  uniform value keeps the uniform law (the part's size may depend on the rest).
* `PrefixGame.ov` / `PrefixGame.rd`: overwrite / read `a`'s hidden part of a pair of tables; `rd_ov`, `ov_ov_rd`,
  `restDepth_ov`, and the table values after an overwrite (`restTable_ov_*`).
* `PrefixGame.frontierValue_ov`: after an overwrite with `(tables, secret)`, `a`'s frontier value is the generic
  `PartialChainEndpoint.evaluate tables secret`.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable

noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction

namespace PrefixGame

/-! ## Resampling a self-determined part of a uniform sample -/

/-- **Resampling a self-determined part of a uniform table.** `ov k ω x` overwrites the `k`-part of `ω` with `x`,
`rd k ω` reads it back. If the part to overwrite (`k = d ω`) is determined by the rest (`d` is invariant under
overwriting its own part, `h3`), overwriting it with a fresh uniform value keeps the uniform law. -/
theorem uniform_resample {Ω : Type} [Fintype Ω] [Nonempty Ω] {X : ℕ → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → ℕ) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
  apply PMF.ext
  intro ω₀
  obtain ⟨k₀, hk₀⟩ : ∃ k, k = d ω₀ := ⟨_, rfl⟩
  -- the involution on `Ω × X k₀`
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
  -- the inner term vanishes off the fiber `d ω = k₀`
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
  -- rewrite the sum over the fiber as a sum over `Ω × X k₀`
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
  -- the uniform weight is constant, so the involution can be undone
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

end PrefixGame

/-! ## R3's tables -/

/-- R3's eager tables (the rest of every address): the private table and the public table over
`referenceInputs adversary`. -/
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)

noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance

instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩

/-- The law of the rest: R3's own uniform tables. -/
noncomputable def restLaw (adversary : AdversaryP) : PMF (RefTables adversary) := PMF.uniformOfFintype _

/-- The eager answers table of a pair of tables (as R3's `eagerAnswers`). -/
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2

/-- The depth of `a` read off the rest (irreducible: its value is a 2^22-step counter search). -/
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a

theorem restDepth_eq {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) :
    restDepth a R = depth (restTable R) a := by
  unfold restDepth; rfl

namespace PrefixGame

variable {adversary : AdversaryP}

/-- The high half of a hash output. -/
def high (output : HashOutput) : Digest := output.extractLsb' 128 128

/-- `a`'s seed half of a seed-coordinate output (`leafSeed`'s choice of half). -/
def seedHalf (a : ChainAddr) (output : HashOutput) : Digest :=
  if a.chain % 2 = 0 then output.extractLsb' 0 128 else output.extractLsb' 128 128

/-- Replace `a`'s seed half of a seed-coordinate output, keeping the sibling half. -/
noncomputable def setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) : HashOutput :=
  if a.chain % 2 = 0 then ChainGraph.joinOutput seed (output.extractLsb' 128 128)
  else ChainGraph.joinOutput (output.extractLsb' 0 128) seed

theorem seedHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    seedHalf a (setSeed a output seed) = seed := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_low]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_high]

theorem setSeed_seedHalf (a : ChainAddr) (output : HashOutput) : setSeed a output (seedHalf a output) = output := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_parts]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_parts]

theorem setSeed_setSeed (a : ChainAddr) (output : HashOutput) (seed seed' : Digest) :
    setSeed a (setSeed a output seed) seed' = setSeed a output seed' := by
  unfold setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]

theorem siblingHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    siblingHalf a (setSeed a output seed) = siblingHalf a output := by
  unfold siblingHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]

/-- The prefix-row index (`step < d`) and value of a canonical row of `a`. -/
noncomputable def rowOf (a : ChainAddr) (d : Nat) (input : HashInput) : Option (Fin d × Digest) :=
  if h : ∃ p : Fin d × Digest, input = chainRow a p.1 p.2 then some (Classical.choose h) else none

theorem rowOf_some {a : ChainAddr} {d : Nat} {input : HashInput} {p : Fin d × Digest}
    (h : rowOf a d input = some p) : input = chainRow a p.1 p.2 := by
  unfold rowOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem rowOf_none {a : ChainAddr} {d : Nat} {input : HashInput} (h : rowOf a d input = none) (p : Fin d × Digest) :
    input ≠ chainRow a p.1 p.2 := by
  intro he
  unfold rowOf at h
  rw [dif_pos ⟨p, he⟩] at h
  cases h

theorem rowOf_chainRow (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (i : Fin d) (v : Digest) :
    rowOf a d (chainRow a i v) = some (i, v) := by
  cases h : rowOf a d (chainRow a i v) with
  | none => exact absurd rfl (rowOf_none h (i, v))
  | some p =>
      have he := rowOf_some h
      obtain ⟨hs, hv⟩ := chainRow_inj (by omega) (by have := p.1.isLt; omega) he
      rw [show p = (i, v) from Prod.ext (Fin.ext hs.symm) hv.symm]

theorem rowOf_none_iff (a : ChainAddr) {d : Nat} (input : HashInput) :
    rowOf a d input = none ↔ ¬∃ step value, step < d ∧ input = chainRow a step value := by
  constructor
  · rintro h ⟨step, value, hs, rfl⟩
    exact rowOf_none h (⟨step, hs⟩, value) rfl
  · intro h
    cases hp : rowOf a d input with
    | none => rfl
    | some p => exact absurd ⟨p.1.val, p.2, p.1.isLt, rowOf_some hp⟩ h

/-- A canonical row is a short input, hence in R3's public universe. -/
theorem chainRow_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRow_eq]
  have h : (chainInput a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [chainInput, zero16, SphincsSecurity.bytesLE_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega


/-- Public answers of a pair of tables inside the universe. -/
theorem restTable_mem (R : RefTables adversary) (input : HashInput) (h : input ∈ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl

/-- Public answers outside the universe are `0`. -/
theorem restTable_nonmem (R : RefTables adversary) (input : HashInput) (h : input ∉ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl

theorem restTable_private (R : RefTables adversary) (coordinate : Coordinate) :
    restTable R (.inr coordinate) = R.1 coordinate := rfl

theorem restTable_coin (R : RefTables adversary) (n : Nat) :
    restTable R (.inl (.inl n)) = (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) := rfl

/-! ## Overwriting `a`'s hidden part -/

/-- The hidden part of `a` at depth `d`: the low halves of the prefix rows, and `a`'s seed half. -/
abbrev Hidden (d : Nat) := (Fin d → Digest → Digest) × Digest

/-- Overwrite the low halves of `a`'s prefix rows (steps `< d`) of a public table. -/
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match rowOf a d x.val with
  | some p => ChainGraph.joinOutput (tables p.1 p.2) (high (pub x))
  | none => pub x

/-- Overwrite `a`'s seed half of a private table. -/
noncomputable def ovPriv (a : ChainAddr) (priv : FullGame.FullTable) (seed : Digest) : FullGame.FullTable :=
  Function.update priv (.inl (seedTweak a)) (setSeed a (priv (.inl (seedTweak a))) seed)

/-- Overwrite `a`'s hidden part (depth `d`) of a pair of tables. -/
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (ovPriv a R.1 x.2, ovPub a d R.2 x.1)

/-- Read `a`'s hidden part (depth `d`) of a pair of tables. -/
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => low (R.2 ⟨chainRow a i v, chainRow_mem a i v⟩), seedHalf a (R.1 (.inl (seedTweak a))))

theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRow a i v, chainRow_mem a i v⟩ =
      ChainGraph.joinOutput (tables i v) (high (pub ⟨chainRow a i v, chainRow_mem a i v⟩)) := by
  unfold ovPub
  rw [rowOf_chainRow a hd i v]

theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (x : referenceInputs adversary) (h : rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]

theorem rd_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    rd a d (ov a d R x) = x := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  simp only
  refine Prod.ext ?_ ?_
  · funext i v
    simp only
    rw [ovPub_row a hd, low, ChainGraph.joinOutput_low]
  · simp only [ovPriv, Function.update_self]
    exact seedHalf_setSeed a _ seed

theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ov a d (ov a d R x) (rd a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext ?_ ?_
  · simp only [ovPriv, Function.update_self, Function.update_idem, setSeed_setSeed, setSeed_seedHalf,
      Function.update_eq_self]
  · funext y
    unfold ovPub
    cases hp : rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRow a p.1 p.2, chainRow_mem a p.1 p.2⟩ := Subtype.ext (rowOf_some hp)
        subst hy
        simp only [high, low, ChainGraph.joinOutput_high, ChainGraph.joinOutput_parts]

/-- An overwrite changes no query that the mask of `a` leaves untouched. -/
theorem restTable_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : Untouched a query) : restTable (ov a d R x) query = restTable R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ referenceInputs adversary
    · rw [restTable_mem _ _ h, restTable_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : rowOf a d input with
      | none => rfl
      | some p => exact absurd (rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [restTable_nonmem _ _ h, restTable_nonmem _ _ h]
  · rw [restTable_private, restTable_private]
    unfold ov ovPriv
    simp only
    rw [Function.update_of_ne]
    intro he
    exact hq (Sum.inl.inj he)
  · rw [restTable_private, restTable_private]
    unfold ov ovPriv
    simp only
    rw [Function.update_of_ne]
    intro he
    cases he

theorem restTable_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    restTable (ov a d R x) (.inl (.inr (chainRow a i v))) =
      ChainGraph.joinOutput (x.1 i v) (high (restTable R (.inl (.inr (chainRow a i v))))) := by
  rw [restTable_mem _ _ (chainRow_mem a i v), restTable_mem _ _ (chainRow_mem a i v)]
  exact ovPub_row a hd R.2 x.1 i v

theorem restTable_ov_nonprefix (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (input : HashInput) (h : rowOf a d input = none) :
    restTable (ov a d R x) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [restTable_mem _ _ hm, restTable_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [restTable_nonmem _ _ hm, restTable_nonmem _ _ hm]

theorem restTable_ov_seed (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    restTable (ov a d R x) (.inr (.inl (seedTweak a))) = setSeed a (restTable R (.inr (.inl (seedTweak a)))) x.2 := by
  rw [restTable_private, restTable_private]
  unfold ov ovPriv
  simp only [Function.update_self]

theorem restTable_ov_private (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (coordinate : Coordinate) (hc : coordinate ≠ .inl (seedTweak a)) :
    restTable (ov a d R x) (.inr coordinate) = restTable R (.inr coordinate) := by
  rw [restTable_private, restTable_private]
  unfold ov ovPriv
  simp only
  rw [Function.update_of_ne hc]

/-- **The depth of `a` is unchanged by overwriting `a`'s hidden part** (F1's `depth_congr`). -/
theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) (b : ChainAddr)
    (hb : b = a) : depth (restTable (ov a d R x)) b = depth (restTable R) b := by
  subst hb
  exact depth_congr b _ _ (restTable_ov_untouched b hd R x)

theorem restDepth_le (a : ChainAddr) (R : RefTables adversary) : restDepth a R ≤ 7 := by
  rw [restDepth_eq]; exact depth_le_seven _ a

theorem restDepth_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x) = restDepth a R := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  calc restDepth a (ov a (restDepth a R) R x) = depth (restTable (ov a (restDepth a R) R x)) a := restDepth_eq _ _
    _ = depth (restTable R) a := depth_ov a hd R x a rfl
    _ = restDepth a R := (restDepth_eq a R).symm

/-! ## The frontier value after an overwrite -/

theorem leafSeed_ov (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    leafSeed (restTable (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = x.2 := by
  rw [leafSeed_eq]
  have hs : header 0 a.key.lay.val a.key.tree (a.chain / 2) a.key.leaf = seedTweak a := rfl
  rw [hs, restTable_ov_seed]
  have := seedHalf_setSeed a (restTable R (.inr (.inl (seedTweak a)))) x.2
  unfold seedHalf at this
  exact this

/-- The chain of `a` under an overwrite evaluates the overwritten tables (steps below `d`). -/
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [chain, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact Correctness.eval_chain_add _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chain_one]
      have hrow : chainInput a.key.lay a.key.tree a.key.leaf a.chain s v = chainRow a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, restTable_ov_prefix a hd R x, ChainGraph.joinOutput_low, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- **`a`'s frontier value after an overwrite with `(tables, secret)` is `evaluate tables secret`.** -/
theorem frontierValue_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    frontierValue (restTable (ov a (restDepth a R) R x)) a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 x.2 := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold frontierValue honestChainValue
  rw [hdepth, leafSeed_ov]
  rw [eval_chain_ov a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))

end PrefixGame

end SigGolfCandidate.T3.Security.Wots
