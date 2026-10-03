import SigGolfCandidate.T3.Secc.WotsEvents

/-!
# F1 (base): the per-address mask `maskAt` and the generic congruence `Mask.Respects`

`maskAt answers a` is `answers` except on the hidden part of chain `a` (BP-A §4 F1): `a`'s canonical prefix rows
(`chainRow a step value`, `step < depth answers a`) answer `0` below the last prefix step and
`joinOutput (frontierValue answers a) 0` at it, and `a`'s seed half of the private coordinate `seedTweak a` is
zeroed when `depth answers a ≥ 1` (the sibling chain's half is kept). Everything else is unchanged.

This module: the definitions, the table-independent set `Mask.Untouched a` of queries the mask never changes, the
generic "tables agreeing on `S` evaluate a program identically" congruence `Mask.Respects S` with its closure
lemmas, header arithmetic (`Mask.header_fields`, `Mask.LeafAlias`), and the elementary facts on the reference word
(`depth ≤ 7`, `1 ≤ depth → chain < chainCount`).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ## Definitions -/

/-- The private coordinate of `a`'s seed: `privatePair 0` of the chain pair `a.chain / 2`. Its output holds the
seeds of chains `2·(a.chain/2)` (low half) and `2·(a.chain/2)+1` (high half). -/
def seedTweak (a : ChainAddr) : BitVec 128 := header 0 a.key.lay.val a.key.tree (a.chain / 2) a.key.leaf

/-- The half of a seed-coordinate output that is not `a`'s seed (the sibling chain's seed). -/
def siblingHalf (a : ChainAddr) (output : HashOutput) : Digest :=
  if a.chain % 2 = 0 then output.extractLsb' 128 128 else output.extractLsb' 0 128

/-- The prefix row index of an input at address `a`, if it is a canonical prefix row of `a`. -/
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRow a step value then some (Classical.choose h) else none

/-- `maskAt answers a`: `answers` except that `a`'s canonical prefix rows forget the hidden chain
(answer `0` below the last prefix step, the frontier value at it) and `a`'s seed half is zeroed when
`depth ≥ 1`. It depends on the hidden part of `a` only through `frontierValue answers a`
(`maskAt_congr`), and honest keygen/signing evaluate identically under it (`eval_maskAt_keygen`,
`eval_maskAt_sign`). -/
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr (.inl tweak) =>
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (let output := answers (.inr (.inl tweak))
         if a.chain % 2 = 0 then ChainGraph.joinOutput 0 (output.extractLsb' 128 128)
         else ChainGraph.joinOutput (output.extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak))
  | .inr (.inr other) => answers (.inr (.inr other))

namespace Mask

/-! ## The generic congruence -/

/-- `program` reads the oracle only on queries in `S`: tables agreeing on `S` evaluate it identically and issue
exactly the same queries (`SourceReplay.queried`, the logging trace; its length is the honest charge). -/
def Respects (S : Spec.Domain → Prop) {α : Type} (program : M α) : Prop :=
  ∀ T T' : Answers, (∀ q, S q → T q = T' q) →
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program

section Respects
variable {S : Spec.Domain → Prop}

theorem Respects.eval_eq {α : Type} {program : M α} (h : Respects S program) {T T' : Answers}
    (hT : ∀ q, S q → T q = T' q) : evalWithAnswerFn T program = evalWithAnswerFn T' program := (h T T' hT).1

theorem Respects.queried_eq {α : Type} {program : M α} (h : Respects S program) {T T' : Answers}
    (hT : ∀ q, S q → T q = T' q) : SourceReplay.queried T program = SourceReplay.queried T' program := (h T T' hT).2

theorem Respects.pure' {α : Type} (x : α) : Respects S (pure x : M α) := fun _ _ _ => ⟨rfl, rfl⟩

theorem Respects.bind {α β : Type} {p : M α} {f : α → M β} (hp : Respects S p) (hf : ∀ x, Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']

theorem Respects.map {α β : Type} {p : M α} (f : α → β) (hp : Respects S p) : Respects S (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact Respects.bind hp fun _ => Respects.pure' _

theorem Respects.publicHash (input : HashInput) (h : S (.inl (.inr (pad64 input)))) :
    Respects S (T3.publicHash input) := fun _ _ hT => ⟨hT _ h, rfl⟩

theorem Respects.shortHash (input : HashInput) (h : S (.inl (.inr (pad64 input)))) :
    Respects S (T3.shortHash input) := by
  unfold T3.shortHash
  exact Respects.bind (Respects.publicHash input h) fun _ => Respects.pure' _

theorem Respects.privateHash (c : Coordinate) (h : S (.inr c)) : Respects S (T3.privateHash c) :=
  fun _ _ hT => ⟨hT _ h, rfl⟩

theorem Respects.privatePair (tag lay tree position index : Nat)
    (h : S (.inr (.inl (header tag lay tree position index)))) :
    Respects S (T3.privatePair tag lay tree position index) := by
  unfold T3.privatePair
  exact Respects.bind (Respects.privateHash _ h) fun _ => Respects.pure' _

theorem Respects.foldlM {β γ : Type} (l : List β) (f : γ → β → M γ) (hf : ∀ x ∈ l, ∀ s, Respects S (f s x)) :
    ∀ init, Respects S (l.foldlM f init) := by
  induction l with
  | nil => intro init; exact Respects.pure' init
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons]
      exact Respects.bind (hf x List.mem_cons_self init)
        fun s => ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s) s

theorem Respects.mapM {α β : Type} (l : List α) (f : α → M β) (hf : ∀ x ∈ l, Respects S (f x)) :
    Respects S (l.mapM f) := by
  induction l with
  | nil => exact Respects.pure' _
  | cons x xs ih =>
      rw [List.mapM_cons]
      exact Respects.bind (hf x List.mem_cons_self) fun _ =>
        Respects.bind (ih fun y hy => hf y (List.mem_cons_of_mem x hy)) fun _ => Respects.pure' _

end Respects

/-- Bind congruence along the actual intermediate value of `T`. -/
theorem eval_bind_of {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : evalWithAnswerFn T' p = evalWithAnswerFn T p)
    (hf : evalWithAnswerFn T' (f (evalWithAnswerFn T p)) = evalWithAnswerFn T (f (evalWithAnswerFn T p))) :
    evalWithAnswerFn T' (p >>= f) = evalWithAnswerFn T (p >>= f) := by
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hp, hf]

/-! ## Header arithmetic -/

/-- A header keeps only `tag mod 2^8`, `lay mod 2^8`, `tree mod 2^40`, `position mod 2^32`, `index mod 2^32`. -/
theorem header_normal (t l tr p ix : Nat) :
    header t l tr p ix = header (t % 256) (l % 256) (tr % 2 ^ 40) (p % 2 ^ 32) (ix % 2 ^ 32) := by
  have htag : packedNodeTag (t % 256) ↔ packedNodeTag t := by simp only [packedNodeTag, Nat.mod_mod]
  have htlo : tr % 1099511627776 % 4294967296 = tr % 4294967296 := by omega
  have hthi : tr % 1099511627776 / 4294967296 % 256 = tr / 4294967296 % 256 := by omega
  by_cases h : packedNodeTag t
  · have h' := htag.mpr h
    simp only [header, if_pos h, if_pos h', Nat.mod_mod, Nat.reducePow, htlo, hthi, nodeWord_normal, nodeWord_normal']
  · have h' : ¬packedNodeTag (t % 256) := fun e => h (htag.mp e)
    simp only [header, if_neg h, if_neg h', Nat.mod_mod, Nat.reducePow, htlo, hthi]

theorem header_fields {t l tr p ix t' l' tr' p' ix' : Nat}
    (h : header t l tr p ix = header t' l' tr' p' ix') :
    t % 256 = t' % 256 ∧ l % 256 = l' % 256 ∧ tr % 2 ^ 40 = tr' % 2 ^ 40 ∧ p % 2 ^ 32 = p' % 2 ^ 32 ∧
      ix % 2 ^ 32 = ix' % 2 ^ 32 := by
  rw [header_normal t l tr p ix, header_normal t' l' tr' p' ix'] at h
  exact header_injective (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h

theorem header_congr {t l tr p ix l' tr' ix' : Nat} (hl : l % 256 = l' % 256) (htr : tr % 2 ^ 40 = tr' % 2 ^ 40)
    (hix : ix % 2 ^ 32 = ix' % 2 ^ 32) : header t l tr p ix = header t l' tr' p ix' := by
  rw [header_normal t l tr p ix, header_normal t l' tr' p ix', hl, htr, hix]

theorem header_ne_of_tag {t l tr p ix t' l' tr' p' ix' : Nat} (h : t % 256 ≠ t' % 256) :
    header t l tr p ix ≠ header t' l' tr' p' ix' := fun he => h (header_fields he).1

/-- `(lay, tree, leaf)` carries exactly the headers of the leaf `L` (headers keep `tree mod 2^40`, `leaf mod 2^32`). -/
def LeafAlias (lay : Layer) (tree leaf : Nat) (L : LeafAddr) : Prop :=
  lay = L.lay ∧ tree % 2 ^ 40 = L.tree % 2 ^ 40 ∧ leaf % 2 ^ 32 = L.leaf % 2 ^ 32

theorem LeafAlias.refl (L : LeafAddr) : LeafAlias L.lay L.tree L.leaf L := ⟨rfl, rfl, rfl⟩

theorem LeafAlias.header_eq {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L)
    (t p : Nat) : header t lay.val tree p leaf = header t L.lay.val L.tree p L.leaf := by
  obtain ⟨hl, ht, hi⟩ := h
  subst hl
  exact header_congr rfl ht hi

theorem LeafAlias.eq_of_lt {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L)
    (ht : tree < 2 ^ 40) (hl : leaf < 2 ^ 32) (ht' : L.tree < 2 ^ 40) (hl' : L.leaf < 2 ^ 32) :
    (⟨lay, tree, leaf⟩ : LeafAddr) = L := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h2
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at h3
  cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem chainInput_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    chainInput lay tree leaf i = chainInput L.lay L.tree L.leaf i := by
  funext step value
  unfold chainInput
  rw [h.header_eq]

theorem chain_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    chain lay tree leaf i = chain L.lay L.tree L.leaf i := by
  funext start count value
  unfold chain
  rw [chainInput_alias h i]

theorem leafSeed_eq (T : Answers) (lay : Layer) (tree leaf i : Nat) : leafSeed T lay tree leaf i =
    if i % 2 = 0 then (T (.inr (.inl (header 0 lay.val tree (i / 2) leaf)))).extractLsb' 0 128
    else (T (.inr (.inl (header 0 lay.val tree (i / 2) leaf)))).extractLsb' 128 128 := rfl

theorem leafSeed_alias (T : Answers) {lay : Layer} {tree leaf : Nat} {L : LeafAddr}
    (h : LeafAlias lay tree leaf L) (i : Nat) :
    leafSeed T lay tree leaf i = leafSeed T L.lay L.tree L.leaf i := by
  rw [leafSeed_eq, leafSeed_eq, h.header_eq]

/-! ## Canonical rows -/

theorem pad64_chainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (chainInput lay tree leaf i step value) = chainInput lay tree leaf i step value := by
  rw [chainInput_eq_zero, pad64_chainInputP]

theorem chainRow_eq (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value = chainInput a.key.lay a.key.tree a.key.leaf a.chain step value := rfl

/-- Two canonical rows of one address with steps below 256 are equal only for equal step and value. -/
theorem chainRow_inj {a : ChainAddr} {s s' : Nat} {v v' : Digest} (hs : s < 256) (hs' : s' < 256)
    (h : chainRow a s v = chainRow a s' v') : s = s' ∧ v = v' := by
  rw [chainRow_eq, chainRow_eq, chainInput_eq_zero, chainInput_eq_zero] at h
  obtain ⟨-, hh, -, hv⟩ := chainInputP_fields h
  have hp := (header_fields hh).2.2.2.1
  simp only [Nat.reducePow] at hp
  exact ⟨by omega, hv⟩

/-- A Core chain query equal to a canonical row of `a` is a row of an alias of `a` at the same step. -/
theorem chainInput_eq_chainRow {lay : Layer} {tree leaf i s s' : Nat} {v v' : Digest} {a : ChainAddr}
    (hi : i < 2 ^ 24) (hc : a.chain < 2 ^ 24) (hs : s < 256) (hs' : s' < 256)
    (h : chainInput lay tree leaf i s v = chainRow a s' v') :
    LeafAlias lay tree leaf a.key ∧ i = a.chain ∧ s = s' ∧ v = v' := by
  rw [chainRow_eq, chainInput_eq_zero, chainInput_eq_zero] at h
  obtain ⟨-, hh, -, hv⟩ := chainInputP_fields h
  obtain ⟨-, hl, ht, hp, hx⟩ := header_fields hh
  have hl' : lay = a.key.lay := by
    apply Fin.ext
    rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
      Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
    exact hl
  simp only [Nat.reducePow] at hp hi hc
  have hp1 : s + 256 * i < 4294967296 := by omega
  have hp2 : s' + 256 * a.chain < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2] at hp
  exact ⟨⟨hl', ht, hx⟩, by omega, by omega, hv⟩

/-- A seed coordinate equal to `a`'s belongs to an alias of `a`'s leaf, at `a`'s chain pair. -/
theorem seedTweak_alias {lay : Layer} {tree leaf i : Nat} {a : ChainAddr} (hi : i < 2 ^ 24) (hc : a.chain < 2 ^ 24)
    (h : header 0 lay.val tree (i / 2) leaf = seedTweak a) : LeafAlias lay tree leaf a.key ∧ i / 2 = a.chain / 2 := by
  unfold seedTweak at h
  obtain ⟨-, hl, ht, hp, hx⟩ := header_fields h
  have hl' : lay = a.key.lay := by
    apply Fin.ext
    rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
      Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
    exact hl
  simp only [Nat.reducePow] at hp hi hc
  have hp1 : i / 2 < 4294967296 := by omega
  have hp2 : a.chain / 2 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2] at hp
  exact ⟨⟨hl', ht, hx⟩, hp⟩

/-! ## The reference word -/

theorem dummyDigits_spec (lay : Layer) :
    (dummyDigits lay).length = chainCount lay ∧ Cost.ValidDigits lay (dummyDigits lay) := by
  fin_cases lay <;> exact ⟨by decide, by unfold Cost.ValidDigits; decide⟩

theorem referenceDigits_spec (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay ∧ Cost.ValidDigits L.lay (referenceDigits answers L) := by
  unfold referenceDigits
  cases h : referenceSearch answers L with
  | none => exact dummyDigits_spec L.lay
  | some found =>
      obtain ⟨counter, digits⟩ := found
      have hd := (Correctness.counterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L)
        counterLimit 0 counter digits (by decide) h).2.2
      exact ⟨(decode_length_sum hd).1, Cost.validDigits_decode hd⟩

/-- The reference word is the honest signer's word when the honest search succeeds. -/
theorem referenceDigits_of_search {answers : Answers} {L : LeafAddr} {counter : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (counter, digits)) : referenceDigits answers L = digits := by
  unfold referenceDigits
  rw [h]
  rfl

theorem depth_le_width (answers : Answers) (a : ChainAddr) (hc : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain :=
  (referenceDigits_spec answers a.key).2 a.chain hc

theorem width_le (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> decide

theorem chain_lt_of_depth (answers : Answers) (a : ChainAddr) (hd : 1 ≤ depth answers a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := (referenceDigits_spec answers a.key).1
  have h0 : depth answers a = 0 := List.getD_eq_default _ _ (by omega)
  omega

theorem depth_le_seven (answers : Answers) (a : ChainAddr) : depth answers a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers a
  · exact (depth_le_width answers a (chain_lt_of_depth answers a hd)).trans (width_le _ _)
  · omega

theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := chainCount_bound lay

/-! ## Basic behaviour of the mask -/

/-- The queries `maskAt answers a` never changes, for every table. -/
def Untouched (a : ChainAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ step value, step < 256 → input ≠ chainRow a step value
  | .inr (.inl tweak) => tweak ≠ seedTweak a
  | _ => True

theorem prefixStep_spec {answers : Answers} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers a input = some step) :
    step < depth answers a ∧ ∃ value, input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h

theorem prefixStep_chainRow (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers a (chainRow a s v) = if s < depth answers a then some s else none := by
  have h7 := depth_le_seven answers a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers a ∧ chainRow a s v = chainRow a step value)
    exact congrArg some (chainRow_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers a (chainRow a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRow_inj hs (by omega) heq).1
        omega

theorem prefixStep_untouched {answers : Answers} {a : ChainAddr} {input : HashInput}
    (h : Untouched a (.inl (.inr input))) : prefixStep answers a input = none := by
  cases hp : prefixStep answers a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers a; omega))

theorem maskAt_public (answers : Answers) (a : ChainAddr) (input : HashInput) :
    maskAt answers a (.inl (.inr input)) = match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl

theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) =
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (if a.chain % 2 = 0 then ChainGraph.joinOutput 0 ((answers (.inr (.inl tweak))).extractLsb' 128 128)
         else ChainGraph.joinOutput ((answers (.inr (.inl tweak))).extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak)) := rfl

theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : Untouched a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rw [maskAt_tweak, if_neg (fun h' => h h'.1)]
  · rfl

/-- On a prefix row the mask answers `0`, or `joinOutput frontier 0` at the last prefix step. -/
theorem maskAt_prefix (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers a) :
    maskAt answers a (.inl (.inr (chainRow a s v))) =
      if s + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0 else 0 := by
  have h7 := depth_le_seven answers a
  rw [maskAt_public, prefixStep_chainRow answers a v (by omega), if_pos hs]
  rfl

/-- Rows of `a` at or above the frontier are unchanged. -/
theorem maskAt_row_ge (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers a ≤ s)
    (hs' : s < 256) : maskAt answers a (.inl (.inr (chainRow a s v))) = answers (.inl (.inr (chainRow a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers a v hs', if_neg (by omega)]

/-- Without a prefix (`depth = 0`) the mask is the identity. -/
theorem maskAt_of_depth_zero (answers : Answers) (a : ChainAddr) (hd : depth answers a = 0) :
    maskAt answers a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rw [maskAt_tweak, if_neg (by omega)]
  · rfl

/-- Untouched-query programs evaluate identically under the mask. -/
theorem eval_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (Untouched a) program) :
    evalWithAnswerFn (maskAt answers a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).1

/-- Untouched-query programs issue the same queries under the mask. -/
theorem queried_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (Untouched a) program) :
    SourceReplay.queried (maskAt answers a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).2

/-! ## Untouched honest queries (tags other than 1 / 0) -/

theorem untouched_of_hdr (a : ChainAddr) (input : HashInput) (h : BitVec 128)
    (hblock : Extract.hdrBlock input = bytesLE 16 h) (htag : ∀ l tr p ix, h ≠ header 1 l tr p ix) :
    Untouched a (.inl (.inr input)) := by
  intro step value _ heq
  have hb : Extract.hdrBlock (chainRow a step value) =
      bytesLE 16 (header 1 a.key.lay.val a.key.tree (step + 256 * a.chain) a.key.leaf) := by
    rw [chainRow_eq, ← pad64_chainInput, chainInput_eq_zero, Extract.hdrBlock_chainInputP]
  rw [heq, hb] at hblock
  exact htag _ _ _ _ (bytesLE_injective hblock).symm

theorem tag_ne_one {t : Nat} (ht : t % 256 ≠ 1) (l tr p ix : Nat) :
    ∀ l' tr' p' ix', header t l tr p ix ≠ header 1 l' tr' p' ix' := fun _ _ _ _ =>
  header_ne_of_tag (by simpa using ht)

theorem untouched_block4 (a : ChainAddr) (x y z : Digest) {t : Nat} (ht : t % 256 ≠ 1) (l tr p ix : Nat) :
    Untouched a (.inl (.inr (block4 x (header t l tr p ix) y z))) :=
  untouched_of_hdr a _ _ (Extract.hdrBlock_block4 x _ y z) (tag_ne_one ht l tr p ix)

theorem untouched_prefixed (a : ChainAddr) (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 1)
    (l tr p ix : Nat) :
    Untouched a (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply untouched_of_hdr a _ _ _ (tag_ne_one ht l tr p ix)
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]

theorem untouched_privatePair (a : ChainAddr) {t : Nat} (ht : t % 256 ≠ 0) (l tr p ix : Nat) :
    Untouched a (.inr (.inl (header t l tr p ix))) := by
  change header t l tr p ix ≠ seedTweak a
  exact header_ne_of_tag (by simpa using ht)

section Programs
variable (a : ChainAddr)

theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_shortHash]
  apply Respects.shortHash
  rw [pad64_nodeInputP]
  exact untouched_block4 a left 0 right ht lay tree 0 heap

theorem respects_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (buildLevel tag lay tree h level nodes) :=
  Respects.mapM _ _ fun _ _ => respects_nodeHash a _ _ _ _ _ _ ht

theorem respects_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact Respects.foldlM _ _ (fun level _ levels =>
    Respects.bind (respects_buildLevel a tag lay tree h level _ ht) fun _ => Respects.pure' _) _

theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (Untouched a) (leafHash lay tree leaf ends) := by
  unfold leafHash
  exact Respects.shortHash _ (untouched_prefixed a _ _ (by decide) _ _ _ _)

theorem respects_forestPk (index : Nat) (roots : List Digest) :
    Respects (Untouched a) (forestPk index roots) := by
  unfold forestPk
  exact Respects.shortHash _ (untouched_prefixed a _ _ (by decide) _ _ _ _)

theorem respects_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
    Respects (Untouched a) (ftsLeaf index coord leaf secret) := by
  rw [ftsLeaf_eq_shortHash]
  apply Respects.shortHash
  rw [pad64_ftsLeafInputP]
  exact untouched_block4 a 0 secret 0 (by decide) coord index 0 leaf

theorem respects_mask (level index : Nat) : Respects (Untouched a) (mask level index) := by
  unfold mask pairedMask
  exact Respects.bind (Respects.privatePair _ _ _ _ _ (untouched_privatePair a (by decide) _ _ _ _))
    fun _ => Respects.pure' _

theorem respects_privateMac (region : Region) : Respects (Untouched a) (privateMac region) := by
  unfold privateMac privateMacKey
  exact Respects.bind (Respects.bind
    (Respects.privateHash _ (untouched_privatePair a (by decide) 0 0 0 0)) fun _ =>
    Respects.bind (Respects.privateHash _ (untouched_privatePair a (by decide) 0 0 0 1)) fun _ =>
      Respects.pure' _) fun _ => Respects.pure' _

theorem respects_privateNonce (message : Message) : Respects (Untouched a) (privateNonce message) := by
  unfold privateNonce
  exact Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _

theorem respects_ftsRows (index coord : Nat) : Respects (Untouched a) (Correctness.ftsRows index coord) := by
  unfold Correctness.ftsRows
  refine Respects.foldlM _ _ (fun pair _ state => ?_) _
  refine Respects.bind (Respects.privatePair _ _ _ _ _ (untouched_privatePair a (by decide) _ _ _ _)) ?_
  rintro ⟨left, right⟩
  exact Respects.bind (respects_ftsLeaf a _ _ _ _) fun _ =>
    Respects.bind (respects_ftsLeaf a _ _ _ _) fun _ => Respects.pure' _

theorem respects_buildFts (index coord : Nat) : Respects (Untouched a) (buildFts index coord) := by
  rw [Correctness.buildFts_eq]
  exact Respects.bind (respects_ftsRows a index coord) fun rows =>
    Respects.bind (respects_buildLevels a 10 coord index 11 rows.1 (by decide)) fun _ => Respects.pure' _

theorem respects_signForest (index : Nat) (chosen : List Selection) :
    Respects (Untouched a) (Correctness.signForest index chosen) := by
  unfold Correctness.signForest
  refine Respects.foldlM _ _ (fun coord _ state => ?_) _
  refine Respects.bind (respects_buildFts a index coord) ?_
  rintro ⟨levels, secrets⟩
  exact Respects.pure' _

theorem respects_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter, Respects (Untouched a) (counterSearch lay tree leaf message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [counterSearch]
      refine Respects.bind (Respects.shortHash _ ?_) fun answer => ?_
      · unfold encodingInput
        exact untouched_prefixed a _ _ (by decide) _ _ _ _
      · split
        · exact ih _
        · exact Respects.pure' _

theorem respects_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects (Untouched a) (digest rho message counter) := by
  unfold digest
  apply Respects.publicHash
  unfold digestInput
  exact untouched_prefixed a _ _ (by decide) _ _ _ _

theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (Untouched a) (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [digestSearch]
      refine Respects.bind (respects_digest a _ _ _) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _

end Programs

end Mask

end SigGolfCandidate.T3.Security.Wots
