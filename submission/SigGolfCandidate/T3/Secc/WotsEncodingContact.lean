import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.T3.Secc.WotsTransportCount

/-!
# Stream E: the contact-first branch of `MarkerAt ∧ ContactAt` (`reference_contactFirst_le`)

`Pr_R3[∃ a, SourceChain a ∧ ContactFirst a] ≤ 57 · (q/2^128) · E_R3[contactCount]` (A's `ContactFirstBound`), where
`ContactFirst T τ a := ∃ k, ContactAt T (τ.take k) a ∧ ¬MarkerAt T (τ.take k) a ∧ MarkerAt T τ a`.

In E's lazy world (one pair of tables, free encoding rows fresh), contacts are a deterministic function of the
history (chain rows are not free), so a *new* contact-first event needs a fresh free encoding row that is the first
marker of an already-contacted chain: probability ≤ 57 · 2^-128 per contacted chain (`markEntry_cell_le`). History
potential (pinned `QueryPause.traced_spmf_history_potential_le`) with charge `57 · #contacts(history)` per cell
query; the total charge is ≤ `57 · |trace| · #contacts(trace)`, and `|trace| ≤ q` on R3's support
(F2's `reference_trace_length`).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame

namespace Enc

/-! ## The event and its congruence -/

/-- Contact strictly first at `a` (A's `SmallP.ContactFirst`, inlined). -/
def ContactFirstAt (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a

/-- Contact-first at some source chain (finite index). -/
def CFK (T : Answers) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactFirstAt T trace (chainAt p)

theorem frontierValue_congr_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q)
    (p : CanonGraph.LeafPos × Fin 58) : frontierValue T' (chainAt p) = frontierValue T (chainAt p) := by
  have hd : depth T' (chainAt p) = depth T (chainAt p) := by
    unfold depth chainAt
    rw [referenceDigits_congr_honest h]
  unfold frontierValue honestChainValue
  rw [hd, leafSeed_congr_nonEnc (nonEnc_of_honest h)]
  exact (Enc.respects_chain _ _ _ _ _ _ _).eval_eq (nonEnc_of_honest h)

theorem contactAt_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry)
    (p : CanonGraph.LeafPos × Fin 58) : ContactAt T' trace (chainAt p) ↔ ContactAt T trace (chainAt p) := by
  have hd : depth T' (chainAt p) = depth T (chainAt p) := by
    unfold depth chainAt
    rw [referenceDigits_congr_honest h]
  unfold ContactAt
  rw [hd, frontierValue_congr_honest h p]

theorem cfk_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry) :
    CFK T' trace ↔ CFK T trace := by
  unfold CFK ContactFirstAt
  simp only [contactAt_congr h, markerAt_congr h]

/-! ## Contacts of a trace -/

/-- Contacted source chains of a trace (finite index). -/
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card

theorem contacts_mono (T : Answers) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T trace ≤ contacts T trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, WotsExtract.contactAt_mono hp.2 hsub⟩

theorem contacts_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry) :
    contacts T' trace = contacts T trace := by
  unfold contacts
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff := contactAt_congr h trace p
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, hiff.mp h1.2⟩ h2
  · exact absurd ⟨h2.1, hiff.mpr h2.2⟩ h1
  · rfl

/-- The cost of a tail after a history: `57 · #contacts(history)` per cell query. -/
noncomputable def costL (T : Answers) (F : Set EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) + costL T F (hist ++ [e]) rest

theorem costL_le (T : Answers) (F : Set EncIndex) :
    ∀ (trace hist : List Entry), costL T F hist trace ≤ 57 * trace.length * contacts T (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T hist ≤ contacts T (hist ++ e :: rest) :=
        contacts_mono T (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) ≤ 57 * contacts T hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith

/-! ## A new contact-first event needs the first marker of a contacted chain -/

theorem cfk_new {T : Answers} {h : List Entry} {e : Entry} (hold : ¬ CFK T h) (hnew : CFK T (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h (chainAt p) ∧
      MarkEntry T (chainAt p) e ∧ ¬ MarkerAt T h (chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T h (chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, WotsExtract.contactAt_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm

/-! ## The history potential in the lazy world -/

/-- Charge of one query after a history: `57 · #contacts` per cell query. -/
noncomputable def cfCharge (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell encInput F x then 57 * contacts T h.toList else 0
  | _ => 0

theorem costL_step (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T F h input + costL T F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]

theorem cfk_nil (T : Answers) : ¬ CFK T [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T _ _).mp hm
  simp at hmem

theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp

section Step
variable [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]

theorem cf_step (T : Answers) (F : Set EncIndex)
    (hother : ∀ x, ¬ Lazy.IsCell encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent encInput F h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl encInput F T input).run allowed] *
        (if CFK T (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T F h input : ENNReal) := by
  classical
  by_cases hold : CFK T h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell encInput F x
    · rw [Lazy.lazyImpl_cell encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
      set e₀ := Lazy.cellOf encInput F x hx with he₀
      have hx₀ : encInput e₀.val = x := Lazy.cellOf_input encInput F x hx
      by_cases hq : ∃ ans₀, (encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h.toList (chainAt p)
        calc _ = Pr[fun ans => CFK T (h.toList ++ [(x, ans)]) | cell (Finset.univ : Finset HashOutput)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T (chainAt p) (x, ans) | cell (Finset.univ : Finset HashOutput)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T (chainAt p) (x, ans) | cell (Finset.univ : Finset HashOutput)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 57 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p _ => ?_
              rw [Lazy.probEvent_cell_univ]
              exact markEntry_cell_le T x (chainAt p)
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((57 * contacts T h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le

/-- **The contact-first potential in the lazy world.** -/
theorem lazy_cf_le {α : Type} (T : Answers) (F : Set EncIndex)
    (hother : ∀ x, ¬ Lazy.IsCell encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        (fun _ => Finset.univ)] * (if CFK T z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run (fun _ => Finset.univ)] *
          (costL T F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl encInput F T)
    (fun h st => Lazy.Consistent encInput F h st)
    (fun h st hc input result hr => Lazy.consistent_step encInput F encInput_injective T h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty encInput F)))
    (fun h _ => if CFK T h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costL T F h.toList tail.toList) (cfCharge T F)
    (fun h => by simp [costL]) (fun h input answer tail => costL_step T F h input answer tail)
    (fun h st hc input => cf_step T F hother h st hc input)
    C 1 (fun _ => Finset.univ) (Lazy.consistent_one encInput F)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T), zero_add] at key
  simpa using key

end Step

/-! ## Per table and over R3 -/

/-- The contact-first indicator of a sample. -/
noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers s.trace then 1 else 0

/-- The contact-first charge of a sample: `57 · |trace| · #contacts`. -/
noncomputable def cfCost (s : RefSample) : ENNReal := ((57 * s.trace.length * contacts s.answers s.trace : Nat) : ENNReal)

theorem free_cf_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (adversary : AdversaryP) (q : Nat) (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput)
          (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          cfCost (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) := by
  rw [free_transfer adversary q iX U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) tr then (1 : ENNReal) else 0)
      (fun y r => by
        unfold cfInd mkSample
        simp only [cfk_congr (honest_ov U privateTable pub y)]),
    free_transfer adversary q iX U hU privateTable pub cfCost
      (fun tr => ((57 * tr.length * contacts (eagerAnswers U privateTable pub) tr : Nat) : ENNReal))
      (fun y r => by
        unfold cfCost mkSample
        simp only [contacts_congr (honest_ov U privateTable pub y)])]
  refine (lazy_cf_le (eagerAnswers U privateTable pub) (freeSet (eagerAnswers U privateTable pub))
    (fun x hx p => markEntry_other U privateTable pub x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costL_le (eagerAnswers U privateTable pub) (freeSet (eagerAnswers U privateTable pub)) z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this

theorem reference_cfInd_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * cfCost s := by
  let _ : ∀ k : Set EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_free_le adversary q (fun k => Pi.instFintype) cfInd cfCost _
    (fun privateTable pub => free_cf_le adversary q (fun k => Pi.instFintype) (referenceInputs adversary)
      (publicUniverse_sub adversary) privateTable pub)

theorem chainAt_injective : Function.Injective chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [chainAt, leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl

theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainAt p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩

/-- Our contact count is C's `contactCount`. -/
theorem contacts_eq_contactCount (s : RefSample) : contacts s.answers s.trace = contactCount s := by
  unfold contacts contactCount
  apply Finset.card_bij (fun p _ => chainAt p)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Finset.mem_filter, mem_sourceChains]
    exact hp
  · intro p _ p' _ h
    exact chainAt_injective h
  · intro a ha
    rw [Finset.mem_filter, mem_sourceChains] at ha
    obtain ⟨p, rfl⟩ := exists_chainAt ha.1
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha

theorem cfCost_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * cfCost s ≤
      ((57 * q : Nat) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    rw [contacts_eq_contactCount]
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlen)

end Enc

open Enc in
/-- **The contact-first branch (`reference_contactFirst_le`, A's `ContactFirstBound`)**: a first marker after a
contact, at some source chain, has probability at most `57 · q/2^128 · E[#contacted source chains]`. -/
theorem reference_contactFirst_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧
        ∃ k, ContactAt s.answers (s.trace.take k) a ∧ ¬MarkerAt s.answers (s.trace.take k) a ∧
          MarkerAt s.answers s.trace a | referenceExperiment adversary q] ≤
      57 * ((q : ENNReal) / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
  calc _ ≤ ∑' s, referenceExperiment adversary q s * cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := exists_chainAt ha
          rw [cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * cfCost s := reference_cfInd_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((57 * q : Nat) : ENNReal) *
          ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (cfCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

end SigGolfCandidate.T3.Security.Wots
