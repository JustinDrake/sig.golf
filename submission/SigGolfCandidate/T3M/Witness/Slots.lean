import SigGolfCandidate.T3M.Witness.Stream
import SigGolfCandidate.T3.Proofs

/-! # Proof slots of the honest stream (stream W)

The siblings of the schedule's folds are exactly Core's proof positions: every fold sibling is in `slotPositions`
(an empty frontier node or one of the four outer siblings), distinct folds of a coordinate have distinct siblings,
so `foldSlot` is injective on the schedule's folds and `streamPlan` inverts it. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The frontier -/

theorem hasLeaf_up {leaves : List Nat} {j n : Nat} (h : hasLeaf leaves j n = true) (d : Nat) :
    hasLeaf leaves (j + d) (n / 2 ^ d) = true := by
  obtain ⟨leaf, hm, he⟩ := (hasLeaf_iff _ _ _).mp h
  exact (hasLeaf_iff _ _ _).mpr ⟨leaf, hm, by rw [pow_add, ← Nat.div_div_eq_div_mul, he]⟩

theorem frontier_inside {leaves : List Nat} : ∀ L N p, p ∈ T3.frontier leaves L N →
    p.1 ≤ L ∧ p.2 / 2 ^ (L - p.1) = N := by
  intro L
  induction L with
  | zero =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp; subst hp; simp
  | succ L ih =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · rcases List.mem_append.mp hp with h | h
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
      · simp only [List.mem_singleton] at hp; subst hp; simp

theorem frontier_nodup {leaves : List Nat} : ∀ L N, (T3.frontier leaves L N).Nodup := by
  intro L
  induction L with
  | zero => intro N; simp only [T3.frontier]; split <;> simp
  | succ L ih =>
      intro N
      simp only [T3.frontier]
      split
      · refine List.nodup_append.mpr ⟨ih _, ih _, ?_⟩
        intro a ha b hb hab
        subst hab
        have h1 := (frontier_inside _ _ _ ha).2
        have h2 := (frontier_inside _ _ _ hb).2
        omega
      · simp

theorem frontier_mem {leaves : List Nat} : ∀ L N k s, k ≤ L → s / 2 ^ (L - k) = N →
    hasLeaf leaves k s = false → (k = L ∨ hasLeaf leaves (k + 1) (s / 2) = true) →
    (k, s) ∈ T3.frontier leaves L N := by
  intro L
  induction L with
  | zero =>
      intro N k s hk hN he _
      obtain rfl : k = 0 := by omega
      simp only [Nat.sub_zero, pow_zero, Nat.div_one] at hN; subst hN
      simp [T3.frontier, he]
  | succ L ih =>
      intro N k s hk hN he hp
      by_cases hkL : k = L + 1
      · subst hkL
        simp only [Nat.sub_self, pow_zero, Nat.div_one] at hN; subst hN
        simp [T3.frontier, he]
      · have hp' : hasLeaf leaves (k + 1) (s / 2) = true := by rcases hp with h | h; omega; exact h
        have hup := hasLeaf_up hp' (L - k)
        have hsN : s / 2 / 2 ^ (L - k) = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ', show L - k + 1 = L + 1 - k by omega, hN]
        rw [show k + 1 + (L - k) = L + 1 by omega, hsN] at hup
        simp only [T3.frontier, hup, ite_true]
        have hdiv : s / 2 ^ (L - k) / 2 = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show L - k + 1 = L + 1 - k by omega, hN]
        rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ (L - k)) with h2 | h2
        · exact List.mem_append_left _ (ih (2 * N) k s (by omega) (by omega) he (Or.inr hp'))
        · exact List.mem_append_right _ (ih (2 * N + 1) k s (by omega) (by omega) he (Or.inr hp'))

/-- `slotPositions` has no duplicates. -/
theorem slotPositions_nodup (sel : Selection) : (slotPositions sel).Nodup := by
  unfold slotPositions
  refine List.nodup_append.mpr ⟨frontier_nodup _ _, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.singleton_append, List.cons_append]
    simp
  · intro a ha b hb hab
    subst hab
    have h1 := frontier_inside _ _ _ ha
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp only at h1
    rcases j with _ | j
    · simp only [Nat.add_zero, Nat.sub_self, pow_zero, Nat.div_one] at h1
      exact xor_one_ne _ h1.2
    · omega

/-! ## The folds of one coordinate -/

/-- A fold's sibling is the sibling of `g`'s level-`k` ancestor: equal siblings mean the same level and, for
different leaves, an LCA at or below that level. -/
theorem sib_eq_imp {g g' k k' : Nat} (h : (k, g / 2 ^ k ^^^ 1) = (k', g' / 2 ^ k' ^^^ 1)) :
    k = k' ∧ (g = g' ∨ (g ≠ g' ∧ lcaLevel g g' ≤ k)) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  refine ⟨rfl, ?_⟩
  by_cases hg : g = g'
  · exact Or.inl hg
  · refine Or.inr ⟨hg, (div_eq_iff_lca hg k).mp ?_⟩
    have := congrArg (· ^^^ 1) h
    simpa only [xor_one_xor_one] using this

/-- Hypotheses on a selection the machine accepts: three strictly increasing local leaves below 128, bucket below 7. -/
structure SelOk (sel : Selection) : Prop where
  len : sel.leaves.length = 3
  b : sel.bucket < 16
  l2 : sel.leaves.getD 2 0 < 128
  s01 : sel.leaves.getD 0 0 < sel.leaves.getD 1 0
  s12 : sel.leaves.getD 1 0 < sel.leaves.getD 2 0

theorem SelOk.leaves_eq {sel : Selection} (h : SelOk sel) :
    sel.leaves = [sel.leaves.getD 0 0, sel.leaves.getD 1 0, sel.leaves.getD 2 0] := by
  have := h.len
  match hl : sel.leaves, this with
  | [a, b, c], _ => simp

theorem SelOk.selected {sel : Selection} (h : SelOk sel) :
    selectedLeaves sel = [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] := by
  unfold selectedLeaves selLeaf; rw [h.leaves_eq]; simp

/-- The coordinate's fold facts, from the LCA structure of its three leaves. -/
structure FoldFacts (leaves : List Nat) (segs : List Segment) : Prop where
  /-- every fold's sibling subtree is empty -/
  empty : ∀ i < 5, ∀ r < (segs.getD i default).a,
    hasLeaf leaves ((segs.getD i default).lo + r)
      ((segs.getD i default).g / 2 ^ ((segs.getD i default).lo + r) ^^^ 1) = false
  /-- folds stay below the root -/
  top : ∀ i < 5, (segs.getD i default).lo + (segs.getD i default).a ≤ 11
  /-- every segment follows a selected leaf -/
  leaf : ∀ i < 5, (segs.getD i default).g ∈ leaves
  /-- distinct folds have distinct siblings -/
  inj : ∀ i < 5, ∀ i' < 5, ∀ r < (segs.getD i default).a, ∀ r' < (segs.getD i' default).a,
    (segs.getD i default).sib r = (segs.getD i' default).sib r' → i = i' ∧ r = r'
  len : segs.length = 5

theorem foldFacts (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    FoldFacts (selectedLeaves sel) (coordSchedule coord sel) := by
  have hsel := hs.selected
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s01; have := hs.s12; have := hs.l2; omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s12; have := hs.l2; omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight hs.l2
  unfold coordSchedule
  rw [hsel]
  simp only []
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  have sib : ∀ g k, (∀ g' ∈ [g0, g1, g2], g' ≠ g → lcaLevel g g' ≠ k + 1) →
      hasLeaf [g0, g1, g2] k (g / 2 ^ k ^^^ 1) = false := fun g k h => hasLeaf_sib_false h
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · simp only [if_pos hA]
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)
  · simp only [if_neg hA]
    have hB : d12 < d01 := by omega
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)

theorem xor_one_div_pow (x m : Nat) (hm : 1 ≤ m) : (x ^^^ 1) / 2 ^ m = x / 2 ^ m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, xor_one_div_two]

theorem SelOk.bucket_div {sel : Selection} (hs : SelOk sel) {g : Nat} (hg : g ∈ selectedLeaves sel) :
    g / 2 ^ 7 = sel.bucket := by
  rw [hs.selected] at hg
  have := hs.s01; have := hs.s12; have := hs.l2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact bucket_div_eight (by omega)

/-- Every fold sibling of the schedule is one of Core's proof positions. -/
theorem fold_sib_mem (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ∀ i < 5, ∀ r < ((coordSchedule coord sel).getD i default).a,
      ((coordSchedule coord sel).getD i default).sib r ∈ slotPositions sel := by
  intro i hi r hr
  have F := foldFacts coord sel hs
  set seg := (coordSchedule coord sel).getD i default with hseg
  have hb := hs.bucket_div (F.leaf i hi)
  have htop := F.top i hi
  have hem := F.empty i hi r hr
  rw [← hseg] at hb htop hem
  unfold slotPositions Segment.sib
  by_cases hk : seg.lo + r < 7
  · apply List.mem_append_left
    apply frontier_mem 7 sel.bucket _ _ (by omega)
    · rw [xor_one_div_pow _ _ (by omega), Nat.div_div_eq_div_mul, ← pow_add,
        show seg.lo + r + (7 - (seg.lo + r)) = 7 by omega, hb]
    · exact hem
    · right
      rw [xor_one_div_two, Nat.div_div_eq_div_mul, ← pow_succ]
      exact hasLeaf_self (F.leaf i hi) _
  · apply List.mem_append_right
    simp only [List.mem_map, List.mem_range]
    refine ⟨seg.lo + r - 7, by omega, ?_⟩
    have e : seg.g / 2 ^ (seg.lo + r) = sel.bucket / 2 ^ (seg.lo + r - 7) := by
      rw [show seg.lo + r = 7 + (seg.lo + r - 7) by omega, pow_add, ← Nat.div_div_eq_div_mul, hb]
      simp
    rw [e, show 7 + (seg.lo + r - 7) = seg.lo + r by omega]

/-- The folds of one coordinate are as many as its proof positions (`authCount + 3`). -/
theorem SelOk.exists {sel : Selection} (h : SelOk sel) :
    ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 ∧ x2 < 128 := by
  have hl := h.leaves_eq
  refine ⟨_, _, _, hl, h.s01, h.s12, h.l2⟩

theorem coord_fold_count (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ((coordSchedule coord sel).map Segment.a).sum = (slotPositions sel).length := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  have hf := Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb
  unfold slotPositions selectedLeaves
  rw [List.length_append, hf]
  simp only [List.length_map, List.length_range]
  have ha : authCount sel.leaves = 3 + lcaLevel x0 x1 + lcaLevel x1 x2 := by
    rw [hl]; simp [authCount, lcaLevel]; omega
  rw [ha]
  have e01 := lca_bucket (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have e12 := lca_bucket (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have l01 := lca_le_eight (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have l12 := lca_le_eight (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have p01 := lcaLevel_pos (sel.bucket * 128 + x0) (sel.bucket * 128 + x1)
  have p12 := lcaLevel_pos (sel.bucket * 128 + x1) (sel.bucket * 128 + x2)
  have hne := lca_ne (show sel.bucket * 128 + x0 < sel.bucket * 128 + x1 by omega)
    (show sel.bucket * 128 + x1 < sel.bucket * 128 + x2 by omega)
  unfold coordSchedule selLeaf
  simp only [hl, List.getD_cons_zero, List.getD_cons_succ]
  rw [e01, e12] at *
  split <;> simp <;> omega

/-! ## The schedule of seven coordinates -/

theorem getD_flatMap_five {α : Type} (f : Nat → List α) (hf : ∀ c, (f c).length = 5) (d : α) :
    ∀ m n, n < 5 * m → ((List.range m).flatMap f).getD n d = (f (n / 5)).getD (n % 5) d := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
      intro n hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen : ((List.range m).flatMap f).length = 5 * m := by
        rw [List.length_flatMap]; simp [hf, List.sum_replicate]; ring
      by_cases h : n < 5 * m
      · rw [List.getD_append _ _ _ _ (by omega), ih n h]
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen]
        rw [show n / 5 = m by omega, show n % 5 = n - 5 * m by omega]

theorem coordSchedule_length (coord : Nat) (sel : Selection) : (coordSchedule coord sel).length = 5 := by
  unfold coordSchedule; dsimp only; split <;> rfl

theorem schedule_length (chosen : List Selection) : (schedule chosen).length = 35 := by
  unfold schedule; rw [List.length_flatMap]; simp [coordSchedule_length]

theorem schedule_getD (chosen : List Selection) {n : Nat} (hn : n < 35) :
    (schedule chosen).getD n default = (coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default :=
  getD_flatMap_five _ (fun c => coordSchedule_length _ _) default 7 n (by omega)

theorem coordSchedule_coord (coord : Nat) (sel : Selection) {i : Nat} (hi : i < 5) :
    ((coordSchedule coord sel).getD i default).coord = coord := by
  unfold coordSchedule; dsimp only; split <;> interval_cases i <;> rfl

theorem schedule_coord (chosen : List Selection) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).coord = n / 5 := by
  rw [schedule_getD chosen hn, coordSchedule_coord _ _ (by omega)]

theorem slotBase_succ (chosen : List Selection) (c : Nat) :
    slotBase chosen (c + 1) = slotBase chosen c + (slotPositions (chosen.getD c ⟨0, []⟩)).length := by
  unfold slotBase; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem slotBase_mono (chosen : List Selection) {c c' : Nat} (h : c ≤ c') : slotBase chosen c ≤ slotBase chosen c' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [slotBase_succ]; omega

theorem slotBase_inj (chosen : List Selection) {c c' x x' : Nat}
    (hx : x < (slotPositions (chosen.getD c ⟨0, []⟩)).length)
    (hx' : x' < (slotPositions (chosen.getD c' ⟨0, []⟩)).length)
    (h : slotBase chosen c + x = slotBase chosen c' + x') : c = c' ∧ x = x' := by
  rcases Nat.lt_trichotomy c c' with hc | rfl | hc
  · have := slotBase_mono chosen (show c + 1 ≤ c' by omega)
    rw [slotBase_succ] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := slotBase_mono chosen (show c' + 1 ≤ c by omega)
    rw [slotBase_succ] at this; omega

/-- Selections the machine and Core accept. -/
def ChosenOk (chosen : List Selection) : Prop := ∀ c < 7, SelOk (chosen.getD c ⟨0, []⟩)

theorem mem_foldPositions {segs : List Segment} {p : Nat × Nat} :
    p ∈ foldPositions segs ↔ p.1 < segs.length ∧ p.2 < (segs.getD p.1 default).a := by
  obtain ⟨n, r⟩ := p
  simp only [foldPositions, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', r', hr', rfl, rfl⟩; exact ⟨hn', hr'⟩
  · rintro ⟨hn, hr⟩; exact ⟨n, hn, r, hr, rfl, rfl⟩

/-- A fold's slot, its coordinate's base, and its index among the coordinate's proof positions. -/
theorem foldSlot_split (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a) :
    foldSlot chosen ((schedule chosen).getD n default) r =
      slotBase chosen (n / 5) + (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) ∧
    (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) <
      (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).length := by
  rw [schedule_getD chosen hn] at hr ⊢
  refine ⟨?_, List.idxOf_lt_length_of_mem (fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr)⟩
  unfold foldSlot
  rw [coordSchedule_coord _ _ (by omega)]

/-- **`foldSlot` is injective** on the folds of the schedule. -/
theorem foldSlot_inj (chosen : List Selection) (hc : ChosenOk chosen) {n n' r r' : Nat} (hn : n < 35)
    (hn' : n' < 35) (hr : r < ((schedule chosen).getD n default).a) (hr' : r' < ((schedule chosen).getD n' default).a)
    (h : foldSlot chosen ((schedule chosen).getD n default) r = foldSlot chosen ((schedule chosen).getD n' default) r') :
    n = n' ∧ r = r' := by
  obtain ⟨e1, l1⟩ := foldSlot_split chosen hc hn hr
  obtain ⟨e2, l2⟩ := foldSlot_split chosen hc hn' hr'
  rw [e1, e2] at h
  obtain ⟨hcc, hx⟩ := slotBase_inj chosen l1 l2 h
  rw [schedule_getD chosen hn] at hr
  rw [schedule_getD chosen hn'] at hr'
  rw [← hcc] at hx hr'
  have hm := fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr
  have hsib := (List.idxOf_inj hm).mp hx
  obtain ⟨hi, hrr⟩ := (foldFacts _ _ (hc _ (by omega))).inj _ (by omega) _ (by omega) _ hr _ hr' hsib
  exact ⟨by omega, hrr⟩

theorem find?_unique {α : Type} (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) (hp : p x = true)
    (hu : ∀ y ∈ l, p y = true → y = x) : l.find? p = some x := by
  cases h : l.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h x hx)
  | some y => exact congrArg some (hu y (List.mem_of_find?_eq_some h) (List.find?_some h))

/-- **`streamPlan` inverts `foldSlot`.** -/
theorem streamPlan_foldSlot (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a)
    (hk : foldSlot chosen ((schedule chosen).getD n default) r < 117) :
    streamPlan chosen ⟨_, hk⟩ = some (n, r) := by
  unfold streamPlan
  apply find?_unique
  · exact mem_foldPositions.mpr ⟨by rw [schedule_length]; exact hn, hr⟩
  · simp
  · rintro ⟨n', r'⟩ hy hp
    have := mem_foldPositions.mp hy
    rw [schedule_length] at this
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc this.1 hn this.2 hr hp
    exact Prod.ext h1 h2

end SigGolfCandidate.T3M
