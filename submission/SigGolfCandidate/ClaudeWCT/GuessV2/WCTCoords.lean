import Mathlib
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.T3.BPORS

section

namespace ClaudeWCT.Guess
section Slots
variable {κ τ : Type}
def Covered (Exp : κ → (τ → ℕ) → Prop) (u : κ → τ → ℕ) (k : κ) (t : τ) : Prop :=
  ∃ d, Exp k d ∧ u k t ≤ d t
theorem no_exposure_of_uncovered_zero {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {k : κ} {t : τ}
    (h : ¬Covered Exp u k t) (hu : u k t = 0) : ∀ d, ¬Exp k d := by
  intro d hd
  exact h ⟨d, hd, by rw [hu]; exact Nat.zero_le _⟩
theorem uncovered_of_no_exposure {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {k : κ}
    (h : ∀ d, ¬Exp k d) (t : τ) : ¬Covered Exp u k t := by
  rintro ⟨d, hd, -⟩
  exact h d hd
theorem two_probed [Fintype τ] [DecidableEq τ] (v : τ → ℕ) {s w : ℕ} (hsum : ∑ t, v t = s) (hle : ∀ t, v t ≤ w)
    (hws : w < s) : ∃ t t', t ≠ t' ∧ 1 ≤ v t ∧ 1 ≤ v t' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht⟩ : ∃ t, 1 ≤ v t := by
    by_contra h0
    push Not at h0
    have : ∑ t, v t = 0 := Finset.sum_eq_zero fun t _ => by have := h0 t; omega
    omega
  have hz : ∀ t' ∈ (Finset.univ : Finset τ), t' ≠ t → v t' = 0 := by
    intro t' _ hne
    have := hcon t t' (Ne.symm hne) ht
    omega
  have hs := Finset.sum_eq_single_of_mem t (Finset.mem_univ t) hz
  have := hle t
  omega
theorem three_way [Fintype τ] [DecidableEq κ] [DecidableEq τ] (Exp : κ → (τ → ℕ) → Prop) (u : κ → τ → ℕ) {s w : ℕ}
    (hsum : ∀ k, ∑ t, u k t = s) (hle : ∀ k t, u k t ≤ w) (hws : w < s) :
    (∀ k t, Covered Exp u k t) ∨
      (∃ k t, ¬Covered Exp u k t ∧ 1 ≤ u k t ∧ ∀ k' t', (k', t') ≠ (k, t) → Covered Exp u k' t') ∨
      (∃ k t k' t', (k, t) ≠ (k', t') ∧ ¬Covered Exp u k t ∧ 1 ≤ u k t ∧
        ¬Covered Exp u k' t' ∧ 1 ≤ u k' t') := by
  have hpair_of_unexposed : ∀ k, (∀ d, ¬Exp k d) →
      ∃ k t k' t', (k, t) ≠ (k', t') ∧ ¬Covered Exp u k t ∧ 1 ≤ u k t ∧
        ¬Covered Exp u k' t' ∧ 1 ≤ u k' t' := by
    intro k hk
    obtain ⟨t, t', hne, h1, h2⟩ := two_probed (u k) (hsum k) (hle k) hws
    refine ⟨k, t, k, t', fun h => hne (Prod.ext_iff.mp h).2, uncovered_of_no_exposure hk t, h1,
      uncovered_of_no_exposure hk t', h2⟩
  by_cases hall : ∀ k t, Covered Exp u k t
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨k0, t0, h0⟩ := hall
  rcases Nat.eq_zero_or_pos (u k0 t0) with hz0 | hp0
  · exact Or.inr (hpair_of_unexposed k0 (no_exposure_of_uncovered_zero h0 hz0))
  by_cases hrest : ∀ k' t', (k', t') ≠ (k0, t0) → Covered Exp u k' t'
  · exact Or.inl ⟨k0, t0, h0, hp0, hrest⟩
  right
  push Not at hrest
  obtain ⟨k1, t1, hne, h1⟩ := hrest
  rcases Nat.eq_zero_or_pos (u k1 t1) with hz1 | hp1
  · exact hpair_of_unexposed k1 (no_exposure_of_uncovered_zero h1 hz1)
  · exact ⟨k0, t0, k1, t1, Ne.symm hne, h0, hp0, h1, hp1⟩
theorem near_exposed {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {s w : ℕ} [Fintype τ] [DecidableEq τ]
    (hsum : ∀ k, ∑ t, u k t = s) (hle : ∀ k t, u k t ≤ w) (hws : w < s) {k : κ} {t : τ}
    (hrest : ∀ k' t', (k', t') ≠ (k, t) → Covered Exp u k' t') : ∃ d, Exp k d := by
  obtain ⟨t1, t2, hne, -, -⟩ := two_probed (u k) (hsum k) (hle k) hws
  by_cases h1 : t1 = t
  · subst h1
    obtain ⟨d, hd, -⟩ := hrest k t2 (fun h => hne (Prod.ext_iff.mp h).2.symm)
    exact ⟨d, hd⟩
  · obtain ⟨d, hd, -⟩ := hrest k t1 (fun h => h1 (Prod.ext_iff.mp h).2)
    exact ⟨d, hd⟩
end Slots
end ClaudeWCT.Guess
end

section




namespace ClaudeWCT.Guess
open OracleComp OracleSpec
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev ChainAddr := Fin (2 ^ 31) × Fin 9 × Fin 128 × Fin 7
abbrev GCoord := ChainAddr × Fin 3
def chainOf (N : HashOutput) (k : Fin 9) (t : Fin 7) : ChainAddr :=
  (⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩, k, child N k, t)
theorem chainOf_injective (N : HashOutput) {k k' : Fin 9} {t t' : Fin 7}
    (h : chainOf N k t = chainOf N k' t') : k = k' ∧ t = t' := by
  simp only [chainOf, Prod.mk.injEq] at h
  exact ⟨h.2.1, h.2.2.2⟩
def deficit (N : HashOutput) (k : Fin 9) (t : Fin 7) : Nat := digit (rank N k) t
theorem deficit_le (N : HashOutput) (k : Fin 9) (t : Fin 7) : deficit N k t ≤ 3 := digit_le_three _ _
theorem deficit_sum (N : HashOutput) (k : Fin 9) : ∑ t, deficit N k t = 6 := step_count _
def probeInput (a : ChainAddr) (p : Fin 3) (c : Digest) : HashInput :=
  WCT9.chainInput a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val c
theorem probeInput_length (a : ChainAddr) (p : Fin 3) (c : Digest) : (probeInput a p c).length = 64 := by
  simp [probeInput, WCT9.chainInput, zero16, bytesLE_length]
theorem pad64_wctChainInput (index coord selected i step : Nat) (value : Digest) :
    pad64 (WCT9.chainInput index coord selected i step value) = WCT9.chainInput index coord selected i step value := by
  simp [pad64, WCT9.chainInput, zero16, bytesLE_length]
theorem pad64_probeInput (a : ChainAddr) (p : Fin 3) (c : Digest) : pad64 (probeInput a p c) = probeInput a p c :=
  pad64_wctChainInput _ _ _ _ _ _
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
theorem chainInput_split (index coord selected i step : Nat) (value : Digest) :
    WCT9.chainInput index coord selected i step value =
      zero16 ++ (bytesLE 16 (wctHeader 5 coord index (step + 256 * i) selected) ++
        (zero16 ++ bytesLE 16 value)) := by
  simp [WCT9.chainInput, List.append_assoc]
theorem hdrBlock_wctChainInput (index coord selected i step : Nat) (value : Digest) :
    hdrBlock (WCT9.chainInput index coord selected i step value) =
      bytesLE 16 (wctHeader 5 coord index (step + 256 * i) selected) := by
  rw [chainInput_split, hdrBlock, List.drop_left' (by simp [zero16])]
  exact List.take_left' (bytesLE_length _ _)
theorem wctHeader_toNat' (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
def tagByte (h : BitVec 128) : Nat := h.toNat / 2 ^ 8 % 256
theorem tagByte_wctHeader (tag lay tree position index : Nat) :
    tagByte (wctHeader tag lay tree position index) = tag % 256 := by
  unfold tagByte
  rw [wctHeader_toNat']
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem tagByte_header (tag lay tree position index : Nat) :
    tagByte (header tag lay tree position index) = tag % 256 := by
  unfold tagByte header
  rw [BitVec.toNat_ofNat]
  have key : ∀ R : Nat, (1 + tag % 256 * 2 ^ 8 + R * 2 ^ 16) % 2 ^ 128 / 2 ^ 8 % 256 = tag % 256 := by
    intro R
    have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
    omega
  have e : ∀ x : Nat, x % 2 ^ 16 = 0 →
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 + x =
        1 + tag % 256 * 2 ^ 8 + (lay % 256 + (tree / 2 ^ 32 % 256) * 2 ^ 8 + x / 2 ^ 16) * 2 ^ 16 := by
    intro x hx
    omega
  split_ifs
  · rw [e _ (by omega)]
    exact key _
  · rw [e _ (by omega)]
    exact key _
theorem chainHeader_inj' {a a' : ChainAddr} {p p' : Fin 3}
    (h : wctHeader 5 a.2.1.val a.1.val (p.val + 256 * a.2.2.2.val) a.2.2.1.val =
      wctHeader 5 a'.2.1.val a'.1.val (p'.val + 256 * a'.2.2.2.val) a'.2.2.1.val) : a = a' ∧ p = p' := by
  have hn := congrArg BitVec.toNat h
  rw [wctHeader_toNat', wctHeader_toNat'] at hn
  obtain ⟨⟨i, hi⟩, ⟨k, hk⟩, ⟨j, hj⟩, ⟨t, ht⟩⟩ := a
  obtain ⟨⟨i', hi'⟩, ⟨k', hk'⟩, ⟨j', hj'⟩, ⟨t', ht'⟩⟩ := a'
  obtain ⟨p, hp⟩ := p
  obtain ⟨p', hp'⟩ := p'
  simp only at hn
  have e1 : i / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by omega)
  have e2 : i' / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by omega)
  rw [e1, e2, Nat.mod_eq_of_lt (show k < 256 by omega), Nat.mod_eq_of_lt (show k' < 256 by omega),
    Nat.mod_eq_of_lt (show p + 256 * t < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show p' + 256 * t' < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show i' < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show j' < 2 ^ 32 by omega)] at hn
  have : i = i' ∧ k = k' ∧ j = j' ∧ t = t' ∧ p = p' := by omega
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
  exact ⟨rfl, rfl⟩
theorem probeInput_injective {a a' : ChainAddr} {p p' : Fin 3} {c c' : Digest}
    (h : probeInput a p c = probeInput a' p' c') : a = a' ∧ p = p' ∧ c = c' := by
  unfold probeInput at h
  rw [chainInput_split, chainInput_split] at h
  have h1 := List.append_cancel_left h
  obtain ⟨hh, hv⟩ := List.append_inj h1 (by simp only [bytesLE_length])
  have hv' := List.append_cancel_left hv
  obtain ⟨ha, hp⟩ := chainHeader_inj' (bytesLE_injective hh)
  exact ⟨ha, hp, bytesLE_injective hv'⟩
noncomputable def decodeProbe (x : HashInput) : Option (GCoord × Digest) :=
  haveI := Classical.propDecidable (∃ q : GCoord × Digest, x = probeInput q.1.1 q.1.2 q.2)
  if h : ∃ q : GCoord × Digest, x = probeInput q.1.1 q.1.2 q.2 then some (Classical.choose h) else none
theorem decodeProbe_probeInput (a : ChainAddr) (p : Fin 3) (c : Digest) :
    decodeProbe (probeInput a p c) = some ((a, p), c) := by
  have h : ∃ q : GCoord × Digest, probeInput a p c = probeInput q.1.1 q.1.2 q.2 := ⟨((a, p), c), rfl⟩
  rw [decodeProbe, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := probeInput_injective (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext (Prod.ext h1 h2) h3)
theorem eq_of_decodeProbe {x : HashInput} {q : GCoord × Digest} (h : decodeProbe x = some q) :
    x = probeInput q.1.1 q.1.2 q.2 := by
  unfold decodeProbe at h
  split at h
  · rename_i hx
    cases h
    exact Classical.choose_spec hx
  · cases h
theorem decodeProbe_eq_none {x : HashInput} :
    decodeProbe x = none ↔ ∀ a p c, x ≠ probeInput a p c := by
  constructor
  · intro h a p c hx
    rw [hx, decodeProbe_probeInput] at h
    cases h
  · intro h
    rw [decodeProbe, dif_neg]
    rintro ⟨q, hq⟩
    exact h q.1.1 q.1.2 q.2 hq
theorem decodeProbe_of_hdrBlock {x : HashInput} {h : BitVec 128} (hx : hdrBlock x = bytesLE 16 h)
    (ht : tagByte h ≠ 5) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro a p c he
  rw [he, probeInput, hdrBlock_wctChainInput] at hx
  have := bytesLE_injective hx
  apply ht
  rw [← this, tagByte_wctHeader]
def seedOf (A : Correctness.Answers) (a : ChainAddr) : Digest :=
  let pair := evalWithAnswerFn A (privatePair 8 a.2.1.val a.1.val 0 (4 * a.2.2.1.val + a.2.2.2.val / 2))
  if a.2.2.2.val % 2 = 0 then pair.1 else pair.2
def chainValue (A : Correctness.Answers) (a : ChainAddr) (p : Nat) : Digest :=
  evalWithAnswerFn A (WCT9.chain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 0 p (seedOf A a))
def honestProbe (A : Correctness.Answers) (c : GCoord) : HashInput := probeInput c.1 c.2 (chainValue A c.1 c.2.val)
def ChainCovered (X : List HashOutput) (a : ChainAddr) (p : Nat) : Prop :=
  ∃ out ∈ X, out.toNat % 2 ^ 31 = a.1.val ∧ child out a.2.1 = a.2.2.1 ∧ 3 - digit (rank out a.2.1) a.2.2.2 ≤ p
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) : Prop :=
  ∃ out ∈ X, out.toNat % 2 ^ 31 = N.toNat % 2 ^ 31 ∧ child out k = child N k ∧
    deficit N k t ≤ digit (rank out k) t
theorem ChainCovered.mono_pos {X : List HashOutput} {a : ChainAddr} {p p' : Nat} (h : p ≤ p')
    (hc : ChainCovered X a p) : ChainCovered X a p' := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, hout, h1, h2, h3.trans h⟩
theorem ChainCovered.mono_log {X Y : List HashOutput} {a : ChainAddr} {p : Nat} (h : ∀ x ∈ X, x ∈ Y)
    (hc : ChainCovered X a p) : ChainCovered Y a p := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, h out hout, h1, h2, h3⟩
theorem slotCovered_iff_chainCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    SlotCovered X N k t ↔ ChainCovered X (chainOf N k t) (3 - deficit N k t) := by
  have hu := deficit_le N k t
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨out, hout, h1, h2, by simp only [chainOf]; omega⟩
  · rintro ⟨out, hout, h1, h2, h3⟩
    have hd := digit_le_three (rank out k) t
    exact ⟨out, hout, h1, h2, by simp only [chainOf] at h3; omega⟩
theorem slotCovered_iff_covered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    SlotCovered X N k t ↔
      Covered (fun k d => ∃ out ∈ X, out.toNat % 2 ^ 31 = N.toNat % 2 ^ 31 ∧ child out k = child N k ∧
        d = fun t => digit (rank out k) t) (deficit N) k t := by
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨_, ⟨out, hout, h1, h2, rfl⟩, h3⟩
  · rintro ⟨d, ⟨out, hout, h1, h2, rfl⟩, h3⟩
    exact ⟨out, hout, h1, h2, h3⟩
theorem caseC_slots (X : List HashOutput) (N : HashOutput) :
    (∀ k t, SlotCovered X N k t) ∨
      (∃ k t, 1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (3 - deficit N k t) ∧
        ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t') ∨
      (∃ k t k' t', (k, t) ≠ (k', t') ∧
        1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (3 - deficit N k t) ∧
        1 ≤ deficit N k' t' ∧ ¬ChainCovered X (chainOf N k' t') (3 - deficit N k' t')) := by
  have h := three_way (fun k d => ∃ out ∈ X, out.toNat % 2 ^ 31 = N.toNat % 2 ^ 31 ∧
      child out k = child N k ∧ d = fun t => digit (rank out k) t) (deficit N) (s := 6) (w := 3)
    (deficit_sum N) (deficit_le N) (by decide)
  simp only [← slotCovered_iff_covered, slotCovered_iff_chainCovered] at h
  rcases h with h | ⟨k, t, h1, h2, h3⟩ | ⟨k, t, k', t', hne, h1, h2, h3, h4⟩
  · exact Or.inl fun k t => (slotCovered_iff_chainCovered X N k t).mpr (h k t)
  · exact Or.inr (Or.inl ⟨k, t, h2, h1, fun k' t' hne => (slotCovered_iff_chainCovered X N k' t').mpr (h3 k' t' hne)⟩)
  · exact Or.inr (Or.inr ⟨k, t, k', t', hne, h2, h1, h4, h3⟩)
theorem chainOf_ne {N : HashOutput} {k k' : Fin 9} {t t' : Fin 7} (h : (k, t) ≠ (k', t')) :
    chainOf N k t ≠ chainOf N k' t' := by
  intro he
  obtain ⟨rfl, rfl⟩ := chainOf_injective N he
  exact h rfl
theorem queried_shortHash (A : Correctness.Answers) (input : HashInput) :
    Security.SourceReplay.queried A (shortHash input) = [.inl (.inr (pad64 input))] := by
  unfold shortHash publicHash
  rw [Security.SourceReplay.queried_bind]
  have h : Security.SourceReplay.queried A (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      [.inl (.inr (pad64 input))] := by
    rw [show (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      (liftM (Spec.query (.inl (.inr (pad64 input)))) >>= pure) from (bind_pure _).symm,
      Security.SourceReplay.queried_query_bind]
    rfl
  rw [h]
  rfl
theorem queried_chain_first (A : Correctness.Answers) (index coord selected i start count : Nat) (value : Digest)
    (hc : 1 ≤ count) :
    (.inl (.inr (WCT9.chainInput index coord selected i start value)) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.chain index coord selected i start count value) := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n + 1 := ⟨count - 1, by omega⟩
  unfold WCT9.chain
  rw [List.range'_succ, List.foldlM_cons, Security.SourceReplay.queried_bind, queried_shortHash, pad64_wctChainInput]
  exact List.mem_append_left _ (List.mem_singleton_self _)
theorem queried_mapM_mem {α β : Type} (A : Correctness.Answers) (f : α → M β) (l : List α) (x : α) (hx : x ∈ l)
    (q : Spec.Domain) (hq : q ∈ Security.SourceReplay.queried A (f x)) : q ∈ Security.SourceReplay.queried A (l.mapM f) := by
  induction l with
  | nil => cases hx
  | cons y rest ih =>
      rw [List.mapM_cons, Security.SourceReplay.queried_bind]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_left _ hq
      · apply List.mem_append_right
        rw [Security.SourceReplay.queried_bind]
        exact List.mem_append_left _ (ih hx)
theorem recoverCoordinate_probe (A : Correctness.Answers) (sig : WCT9.Signature) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) (t : Fin 7) (hu : 1 ≤ digit (rank output coord) t) :
    (.inl (.inr (WCT9.chainInput index coord.val (child output coord).val t.val (3 - digit (rank output coord) t)
        ((sig.openings coord).values t))) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.recoverCoordinate sig index output coord) := by
  unfold WCT9.recoverCoordinate
  rw [Security.SourceReplay.queried_bind]
  apply List.mem_append_left
  exact queried_mapM_mem A _ (List.finRange 7) t (List.mem_finRange t) _
    (queried_chain_first A _ _ _ _ _ _ _ hu)
end ClaudeWCT.Guess
end
