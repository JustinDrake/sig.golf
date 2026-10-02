import SigGolfCandidate.T3.Secc.WotsClasses
import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.T3.Secc.WotsRestart
import SigGolfCandidate.T3.Secc.WotsEncodingE1
import SigGolfCandidate.T3.Secc.WotsStructuralFinal

/-!
# Stream A: the union of the five primitive bounds on R3 (`reference_primitive_le`)

`WotsPrimitiveSrc` (W) splits deterministically into six events (`primitive_cases`): encoding match, structural hit,
two-edge, two contacts, marker-first-then-contact, contact-first-then-marker (`markerContact_split`: the entry completing
a marker is an encoding row, the one completing a contact a chain row, never both). Their R3 bounds:

| event | bound (×E[count]) | source |
|---|---|---|
| `EncodingMatchAt` at a source leaf | `n⁻¹·E[E]` | E1 `reference_encodingMatch_le` (proved) |
| `StructuralHitSrc` | `n⁻¹·E[O]` | S `reference_structural_src_le` (proved) |
| `TwoEdgeAt` | `twoEdgeRate·E[P]/(1−x)` | C `reference_twoEdge_le` (proved) |
| two `ContactAt` | `(4x/n)·E[P]/(1−x)²` | C, **HYP** `TwoContactsBound` |
| marker first | `2x/(1−x)·Pr[MarkerAt a]` per chain, summed: `2x/(1−x)·(3306/n)·E[E]` | C `reference_markerFirst_at_le` (proved) + E, **HYP** `MarkerSumBound` |
| contact first | `57x·E[#contacts] ≤ 57x·(2/n)·E[P]/(1−x)` | **HYP** `ContactFirstBound` (E or C) + C `reference_contacts_cost_le` (proved) |

Summed (`reference_primitive_le`): `c_P/n·E[P] + c_E/n·E[E] + n⁻¹·E[O]` with
`c_P = (3/2+4x+2x²)/(1−x) + 4x/(1−x)² + 2·57·x/(1−x)` and `c_E = 1 + 2·3306·x/(1−x)` (BP-A §1.2 exactly).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame

namespace SmallP

/-- Marker strictly first at `a`, then a contact (E-INTERFACE §4 `MarkerFirst`; C's `ContactAfterStop`). -/
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a

/-- Contact strictly first at `a`, then a marker (E-INTERFACE §4 `ContactFirst`). -/
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a

theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]

/-- **The order split of a marker contact** (E-INTERFACE §4, deterministic). -/
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, answer, digits, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, answer, digits, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, answer, digits, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact SmallA.chainRow_ne_encodingRow _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩

/-- The deterministic six-way split of a source-sized primitive event. -/
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))

/-- Six-way union bound on a `PMF`. -/
theorem probEvent_le_six {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] + Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p] := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  exact probEvent_or_le _ _ _

/-- The chain address of a finite chain index (E's indexing of `markerCount`). -/
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩

theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainOf p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩

end SmallP

open SmallP

/-! ## Pending hypotheses (streams C and E) -/

/-- **HYP** (C-INTERFACE §4 `reference_twoContacts_le`, stream C). -/
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2

/-- **HYP** (C-INTERFACE §5 contact-first branch, stream E or C): a fresh encoding row decoding into one of the ≤ 57
unit neighbours lowered at an already-contacted chain. -/
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    57 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount

/-- **HYP** (E-INTERFACE §3 `reference_marker_sum_le`, stream E). -/
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount

/-! ## Rates and the union -/

/-- Prefix-class rate (×1/n, BP-A §1.2): `(3/2+4x+2x²)/(1−x) + 4x/(1−x)² + 2·57·x/(1−x)`. -/
noncomputable def prefixCoeff (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
      (1 - (q : ENNReal) / 2 ^ 128) +
    4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
    2 * 57 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)

/-- Encoding-class rate (×1/n, BP-A §1.2): `1 + 2·3306·x/(1−x)`. -/
noncomputable def encodingCoeff (q : Nat) : ENNReal :=
  1 + 2 * 3306 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)

/-- The marker-first branch, summed over source chains. -/
theorem reference_markerFirst_sum_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : MarkerSumBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ MarkerFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  -- per chain index
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
          referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] := by
    intro p
    by_cases hs : WotsExtract.SourceChain (chainOf p)
    · simp only [hs, true_and]
      have hC := reference_markerFirst_at_le adversary q hq (chainOf p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (chainOf p)) s.answers s.trace
        (chainOf p) | referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (chainOf p) | referenceExperiment adversary q]
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ MarkerFirst s.answers s.trace a | referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
          referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainOf ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
              referenceExperiment adversary q] := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact hMS

/-- The contact-first branch through C's expected contact count. -/
theorem reference_contactFirst_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hCF : ContactFirstBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      57 * ((q : ENNReal) / 2 ^ 128) *
        ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) :=
  hCF.trans (by gcongr; exact reference_contacts_cost_le adversary q hq)

/-- **The primitive union on R3**: `Pr_R3[WotsPrimitiveSrc] ≤ c_P/n·E[P] + c_E/n·E[E] + n⁻¹·E[O]`. -/
theorem reference_primitive_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hTC : TwoContactsBound adversary q) (hCF : ContactFirstBound adversary q) (hMS : MarkerSumBound adversary q) :
    Pr[fun s => WotsExtract.WotsPrimitiveSrc s.answers s.trace | referenceExperiment adversary q] ≤
      prefixCoeff q / 2 ^ 128 * refExpect adversary q prefixClassCount +
        encodingCoeff q / 2 ^ 128 * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount := by
  refine (probEvent_le_six _ _ _ _ _ _ _ _ fun s h => primitive_cases s.answers s.trace h).trans ?_
  have h1 := reference_encodingMatch_le adversary q
  have h2 := reference_structural_src_le adversary q
  have h3 := reference_twoEdge_le adversary q hq
  have h5 := reference_markerFirst_sum_le adversary q hq hMS
  have h6 := reference_contactFirst_cost_le adversary q hq hCF
  calc _ ≤ (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount +
        twoEdgeRate q * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128) +
        (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
          (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
        57 * ((q : ENNReal) / 2 ^ 128) *
          ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) := by
        gcongr
        · exact h1
        · exact h2
        · exact h3
        · exact hTC
    _ = _ := by
        unfold prefixCoeff encodingCoeff twoEdgeRate
        simp only [div_eq_mul_inv]
        ring

end SigGolfCandidate.T3.Security.Wots
