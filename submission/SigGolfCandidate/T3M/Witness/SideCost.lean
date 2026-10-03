import SigGolfCandidate.T3M.Witness.Slots

/-! Pure segment-cost arithmetic for an unintegrated prototype.
These theorems do not assert a machine refinement or an accepting-run bound. -/
namespace SigGolfCandidate.T3M.SideCost
set_option autoImplicit false

def credit (a : Nat) : Nat := min (a - 1) 2
def segCost (a : Nat) : Nat := 15 + 15*a - 2*credit a

theorem credit_le_two (a : Nat) : credit a ≤ 2 := Nat.min_le_right _ _
theorem segCost_identity (a : Nat) : segCost a + 2*credit a = 15+15*a := by
  have h := credit_le_two a
  unfold segCost
  omega

theorem relaxed_one (a : Nat) (ha : a ≤ 11) : 5*segCost a ≤ 77+73*a := by
  have h := segCost_identity a
  unfold credit at h
  omega

theorem relaxed_sum (xs : List Nat) (h : ∀ a ∈ xs, a ≤ 11) :
    5*(xs.map segCost).sum ≤ 77*xs.length+73*xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := relaxed_one a (h a (by simp))
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem relaxed_35 (xs : List Nat) (hl : xs.length = 35) (hs : xs.sum ≤ 115)
    (h : ∀ a ∈ xs, a ≤ 11) : 395+(xs.map segCost).sum ≤ 2613 := by
  have ht := relaxed_sum xs h
  omega

/-- The five canonical DFS segment lengths, parametrized by the two distinct
adjacent-XOR heights in1..7; includes the four outer bucket levels. -/
def bankShape (x y : Nat) : List Nat :=
  if x < y then [x-1,x-1,y-1-x,y-1,11-y]
  else [x-1,y-1,y-1,x-1-y,11-x]

theorem bank_finite : ∀ (x y : Fin 8), 0 < x.val → 0 < y.val → x ≠ y →
    5*(bankShape x.val y.val).sum ≤ 36+8*((bankShape x.val y.val).map credit).sum := by
  decide

/-- This accepts the finite per-bank inequality as an explicit premise; the
connection from an arbitrary accepting witness to canonical shapes is separate. -/
theorem bank_sum (banks : List (List Nat))
    (h : ∀ xs ∈ banks, 5*xs.sum ≤ 36+8*(xs.map credit).sum) :
    5*(banks.map List.sum).sum ≤ 36*banks.length+8*(banks.map fun xs => (xs.map credit).sum).sum := by
  induction banks with
  | nil => simp
  | cons xs banks ih =>
    have ha := h xs (by simp)
    have ht := ih (fun ys hy => h ys (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem canonical_seven (banks : List (List Nat)) (hn : banks.length = 7)
    (hf : (banks.map List.sum).sum ≤ 115)
    (h : ∀ xs ∈ banks, 5*xs.sum ≤ 36+8*(xs.map credit).sum) :
    920+15*(banks.map List.sum).sum-2*(banks.map fun xs => (xs.map credit).sum).sum ≤ 2563 := by
  have ht := bank_sum banks h
  by_cases h114 : (banks.map List.sum).sum ≤ 114
  · omega
  · have h115 : (banks.map List.sum).sum = 115 := by omega
    have hc : 41 ≤ (banks.map fun xs => (xs.map credit).sum).sum := by omega
    omega


open SigGolfCandidate.T3 (Selection)

theorem coord_lengths (c : Nat) (sel : Selection) :
    (coordSchedule c sel).map Segment.a = bankShape (lcaLevel (selLeaf sel 0) (selLeaf sel 1))
      (lcaLevel (selLeaf sel 1) (selLeaf sel 2)) := by
  simp only [coordSchedule,bankShape]
  split_ifs <;> rfl

theorem coord_inequality (c : Nat) (sel : Selection) (hs : SelOk sel) :
    5*((coordSchedule c sel).map Segment.a).sum ≤
      36+8*(((coordSchedule c sel).map Segment.a).map credit).sum := by
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s01; have := hs.s12; have := hs.l2; omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s12; have := hs.l2; omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight hs.l2
  have l01 : lcaLevel (selLeaf sel 0) (selLeaf sel 1) ≤ 7 :=
    (div_eq_iff_lca (by omega) 7).mp (by rw [bk0,bk1])
  have l12 : lcaLevel (selLeaf sel 1) (selLeaf sel 2) ≤ 7 :=
    (div_eq_iff_lca (by omega) 7).mp (by rw [bk1,bk2])
  have hne := lca_ne g01 g12
  rw [coord_lengths]
  let x : Fin 8 := ⟨lcaLevel (selLeaf sel 0) (selLeaf sel 1),by omega⟩
  let y : Fin 8 := ⟨lcaLevel (selLeaf sel 1) (selLeaf sel 2),by omega⟩
  exact bank_finite x y (lcaLevel_pos _ _) (lcaLevel_pos _ _)
    (by intro hh; have := congrArg Fin.val hh; exact hne this)

def sourceBanks (chosen : List Selection) : List (List Nat) :=
  (List.range 7).map fun c => (coordSchedule c (chosen.getD c ⟨0,[]⟩)).map Segment.a

theorem source_seven (chosen : List Selection)
    (hc : ∀ c, c < 7 → SelOk (chosen.getD c ⟨0,[]⟩))
    (hf : ((sourceBanks chosen).map List.sum).sum ≤ 115) :
    920+15*((sourceBanks chosen).map List.sum).sum -
      2*((sourceBanks chosen).map fun xs => (xs.map credit).sum).sum ≤ 2563 := by
  apply canonical_seven _ (by simp [sourceBanks]) hf
  intro xs hx
  obtain ⟨c,hc7,rfl⟩ := List.mem_map.mp hx
  exact coord_inequality c _ (hc c (List.mem_range.mp hc7))


/-- Accepting-cycle potential for `n` remaining segments and `folds` consumed. -/
def remaining (n folds : Nat) : Nat := (77*n+73*(115-folds))/5

theorem remaining_segment (n folds a : Nat) (hn : 0 < n) (ha : a ≤ 11)
    (hf : folds+a ≤ 115) : segCost a + remaining (n-1) (folds+a) ≤ remaining n folds := by
  have hc := relaxed_one a ha
  unfold remaining
  omega

theorem remaining_nonneg (n f : Nat) : 0 ≤ remaining n f := Nat.zero_le _
theorem remaining_initial : remaining 35 0 = 2218 := by decide


/-- Exact cost of the remaining nonempty fold suffix, including HASH charges. -/
def foldRemaining (i n : Nat) : Nat := 15*n-2-2*min (2-i) (n-1)

theorem foldRemaining_one (i : Nat) : foldRemaining i 1 = 13 := by
  simp [foldRemaining]

theorem foldRemaining_succ (i n : Nat) (hn : 0 < n) :
    foldRemaining i (n+1) = (if i < 2 then 13 else 15) + foldRemaining (i+1) n := by
  unfold foldRemaining
  split_ifs <;> omega

theorem foldRemaining_le (i n : Nat) : foldRemaining i n ≤ 15*n-2 := by
  unfold foldRemaining
  omega

theorem foldRemaining_segment (a : Nat) (ha : 0 < a) : 17+foldRemaining 0 a = segCost a := by
  unfold foldRemaining segCost credit
  omega

end SigGolfCandidate.T3M.SideCost
