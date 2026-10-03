import SigGolfCandidate.T3M.Expand.RcBlocks
import SigGolfCandidate.T3M.Witness.Dfs

/-!
# `recover_child`: the stream emission model (stream E)

`rcEm leaves pf level node used e` is the machine's stream emission for the DFS of `(level, node)` (pure: it depends
on the leaves and the proof slots `pf`, not on HASH answers): a fold `L` / `R` appends `(side, sibling)` to the open
segment, a leaf after the first closes the open segment, a node with two live children closes it with the merge flag,
both open a new one. `img e` is the stream's doublewords (closed segments, the open segment's zero header word, its
folds); `rcCost` the cycle bound.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest hasLeaf)

set_option autoImplicit false

/-- A fold of the stream: the side (`true` = sibling at `L`, the folded node is a right child) and the sibling. -/
abbrev Fold := Bool × Digest

/-- A closed segment: header byte and folds. -/
structure MSeg where
  byte0 : Nat
  folds : List Fold

/-- The emission state: closed segments, the open segment's folds and parity. -/
structure Em where
  segs : List MSeg
  cur : List Fold
  par : Nat

/-- The doublewords of a fold block (64 bytes and the 16-byte gap). -/
def foldWords (f : Fold) : List Word :=
  if f.1 then [f.2.extractLsb' 0 64, f.2.extractLsb' 64 64, 0, 0, 0, 0, 0, 0, 0, 0]
  else [0, 0, 0, 0, 0, 0, f.2.extractLsb' 0 64, f.2.extractLsb' 64 64, 0, 0]

/-- The doublewords of a closed segment. -/
def segWords (m : MSeg) : List Word := BitVec.ofNat 64 m.byte0 :: m.folds.flatMap foldWords

/-- The stream image: closed segments, the open segment's (zero) header word and its folds. -/
def img (e : Em) : List Word := e.segs.flatMap segWords ++ [0] ++ e.cur.flatMap foldWords

/-- Close the open segment (header byte `|cur| + 16 merge + 32 par`) and open one with parity `p`. -/
def Em.close (e : Em) (merge : Bool) (p : Nat) : Em :=
  ⟨e.segs ++ [⟨e.cur.length + (if merge then 16 else 0) + 32 * e.par, e.cur⟩], [], p⟩

/-- **The emission of the DFS of `(level, node)`** (`used` = the next proof slot). -/
def rcEm (leaves : List Nat) (pf : Nat → Digest) : Nat → Nat → Nat → Em → Em
  | level, node, used, e =>
    if hasLeaf leaves level node = false then e
    else match level with
    | 0 => if leaves.idxOf node = 0 then ⟨e.segs, e.cur, node % 2⟩ else e.close false (node % 2)
    | l + 1 =>
      let e1 := rcEm leaves pf l (2 * node) used e
      let u1 := used + (T3.frontier leaves l (2 * node)).length
      let e2 := rcEm leaves pf l (2 * node + 1) u1 e1
      if hasLeaf leaves l (2 * node) = false then ⟨e2.segs, e2.cur ++ [(true, pf used)], e2.par⟩
      else if hasLeaf leaves l (2 * node + 1) = false then ⟨e2.segs, e2.cur ++ [(false, pf u1)], e2.par⟩
      else e2.close true (node % 2)

/-- Cycles of `recover_child` at `(level, node)` (all oracles). -/
def rcCost (leaves : List Nat) : Nat → Nat → Nat
  | level, node =>
    if hasLeaf leaves level node = false then 53
    else match level with
    | 0 => 118
    | l + 1 => 144 + rcCost leaves l (2 * node) + rcCost leaves l (2 * node + 1)

theorem frontier_succ (leaves : List Nat) (l node : Nat) (h : hasLeaf leaves (l + 1) node = true) :
    T3.frontier leaves (l + 1) node = T3.frontier leaves l (2 * node) ++ T3.frontier leaves l (2 * node + 1) := by
  simp [T3.frontier, h]

theorem frontier_empty (leaves : List Nat) (level node : Nat) (h : hasLeaf leaves level node = false) :
    T3.frontier leaves level node = [(level, node)] := by
  cases level <;> simp [T3.frontier, h]

theorem frontier_leaf (leaves : List Nat) (node : Nat) (h : hasLeaf leaves 0 node = true) :
    T3.frontier leaves 0 node = [] := by
  simp [T3.frontier, h]

theorem length_foldWords (f : Fold) : (foldWords f).length = 10 := by
  unfold foldWords; split_ifs <;> rfl

theorem length_flatMap_foldWords (l : List Fold) : (l.flatMap foldWords).length = 10 * l.length := by
  induction l with
  | nil => rfl
  | cons f l ih => rw [List.flatMap_cons, List.length_append, length_foldWords, ih]; simp; ring

/-- The doublewords of the closed segments. -/
def wl (e : Em) : Nat := (e.segs.flatMap segWords).length

theorem length_img (e : Em) : (img e).length = wl e + 1 + 10 * e.cur.length := by
  rw [img, List.length_append, List.length_append, length_flatMap_foldWords]; rfl

theorem wl_close (e : Em) (m : Bool) (p : Nat) : wl (e.close m p) = wl e + 1 + 10 * e.cur.length := by
  unfold wl Em.close
  rw [List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, segWords,
    List.length_cons, length_flatMap_foldWords]
  ring

theorem img_len_fold (e : Em) (f : Fold) : (img ⟨e.segs, e.cur ++ [f], e.par⟩).length = (img e).length + 10 := by
  rw [length_img, length_img]; simp [wl]; ring

theorem img_len_close (e : Em) (m : Bool) (p : Nat) : (img (e.close m p)).length = (img e).length + 1 := by
  rw [length_img, length_img, wl_close]; simp [Em.close]

theorem img_len_par (e : Em) (p : Nat) : (img ⟨e.segs, e.cur, p⟩).length = (img e).length := by
  rw [length_img, length_img]; rfl

/-- The emission only grows the image. -/
theorem rcEm_mono (leaves : List Nat) (pf : Nat → Digest) (level : Nat) : ∀ node used e,
    (img e).length ≤ (img (rcEm leaves pf level node used e)).length := by
  induction level with
  | zero =>
    intro node used e
    unfold rcEm
    by_cases h0 : hasLeaf leaves 0 node = false
    · rw [if_pos h0]
    · rw [if_neg h0]
      by_cases hi : leaves.idxOf node = 0
      · simp only [hi, ↓reduceIte, img_len_par]; omega
      · simp only [hi, ↓reduceIte, img_len_close]; omega
  | succ l ih =>
    intro node used e
    unfold rcEm
    by_cases h0 : hasLeaf leaves (l + 1) node = false
    · rw [if_pos h0]
    · rw [if_neg h0]
      have h1 := ih (2 * node) used e
      have h2 := ih (2 * node + 1) (used + (T3.frontier leaves l (2 * node)).length)
        (rcEm leaves pf l (2 * node) used e)
      simp only []
      split_ifs
      · rw [img_len_fold]; omega
      · rw [img_len_fold]; omega
      · rw [img_len_close]; omega

/-! ## The stream in memory -/

/-- The stream doublewords at `0xC40` hold the image `img e` (zero past its end). -/
def StreamAt (t : MachineState) (e : Em) : Prop :=
  ∀ k < 1185, t.getMem (BitVec.ofNat 64 (0xC40 + 8 * k)) = (img e).getD k 0

theorem img_fold (e : Em) (f : Fold) : img ⟨e.segs, e.cur ++ [f], e.par⟩ = img e ++ foldWords f := by
  simp [img, List.flatMap_append]

theorem img_close (e : Em) (m : Bool) (p : Nat) :
    img (e.close m p) = (e.segs.flatMap segWords ++
      [BitVec.ofNat 64 (e.cur.length + (if m then 16 else 0) + 32 * e.par)] ++ e.cur.flatMap foldWords) ++ [0] := by
  simp [img, Em.close, List.flatMap_append, segWords]

theorem getD_append_of_lt {α : Type} (l₁ l₂ : List α) (d : α) (k : Nat) (h : k < l₁.length) :
    (l₁ ++ l₂).getD k d = l₁.getD k d := List.getD_append _ _ _ _ h

theorem getD_append_of_ge {α : Type} (l₁ l₂ : List α) (d : α) (k : Nat) (h : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k d = l₂.getD (k - l₁.length) d := List.getD_append_right _ _ _ _ h

theorem getD_of_ge_len {α : Type} (l : List α) (d : α) (k : Nat) (h : l.length ≤ k) : l.getD k d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- A fold block written after the image: `img` grows by the fold's doublewords. -/
theorem streamAt_fold {s t : MachineState} {e : Em} (f : Fold) (hS : StreamAt s e)
    (hroom : (img e).length + 10 ≤ 1185)
    (hw : ∀ r < 10, t.getMem (BitVec.ofNat 64 (0xC40 + 8 * ((img e).length + r))) =
      if (foldWords f).getD r 0 = 0 then s.getMem (BitVec.ofNat 64 (0xC40 + 8 * ((img e).length + r)))
      else (foldWords f).getD r 0)
    (hrest : ∀ k < 1185, (k < (img e).length ∨ (img e).length + 10 ≤ k) →
      t.getMem (BitVec.ofNat 64 (0xC40 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xC40 + 8 * k))) :
    StreamAt t ⟨e.segs, e.cur ++ [f], e.par⟩ := by
  intro k hk
  rw [img_fold]
  by_cases h1 : k < (img e).length
  · rw [hrest k hk (Or.inl h1), hS k hk, getD_append_of_lt _ _ _ _ h1]
  · by_cases h2 : (img e).length + 10 ≤ k
    · rw [hrest k hk (Or.inr h2), hS k hk, getD_of_ge_len _ _ _ (by omega), getD_of_ge_len _ _ _ (by
        rw [List.length_append, length_foldWords]; omega)]
    · obtain ⟨r, hr, rfl⟩ : ∃ r, r < 10 ∧ k = (img e).length + r := ⟨k - (img e).length, by omega, by omega⟩
      rw [hw r hr, getD_append_of_ge _ _ _ _ (by omega), show (img e).length + r - (img e).length = r by omega]
      split_ifs with hz
      · rw [hz, hS _ hk, getD_of_ge_len _ _ _ (by omega)]
      · rfl

theorem getD_append_zero (l : List Word) (k : Nat) : (l ++ [0]).getD k 0 = l.getD k 0 := by
  by_cases h : k < l.length
  · rw [getD_append_of_lt _ _ _ _ h]
  · rw [getD_append_of_ge _ _ _ _ (by omega), getD_of_ge_len l 0 k (by omega)]
    rcases Nat.eq_or_lt_of_le (show l.length ≤ k by omega) with h' | h'
    · rw [← h']; simp
    · rw [getD_of_ge_len _ _ _ (by simp; omega)]

theorem getD_mid (A B : List Word) (x y : Word) (k : Nat) (hk : k ≠ A.length) :
    (A ++ [x] ++ B).getD k 0 = (A ++ [y] ++ B).getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc, List.singleton_append]
  by_cases h : k < A.length
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨r, hr⟩ : ∃ r, k - A.length = r + 1 := ⟨k - A.length - 1, by omega⟩
    rw [hr]; rfl

theorem getD_mid_self (A B : List Word) (y : Word) : (A ++ [y] ++ B).getD A.length 0 = y := by
  rw [List.append_assoc, getD_append_of_ge _ _ _ _ (le_refl _), Nat.sub_self]; simp

/-- The header byte written at the open segment's (zero) header word: the segment is closed. -/
theorem streamAt_close {s t : MachineState} {e : Em} (m : Bool) (p : Nat) (hS : StreamAt s e)
    (hw : t.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e)) =
      BitVec.ofNat 64 (e.cur.length + (if m then 16 else 0) + 32 * e.par))
    (hrest : ∀ k < 1185, k ≠ wl e →
      t.getMem (BitVec.ofNat 64 (0xC40 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xC40 + 8 * k))) :
    StreamAt t (e.close m p) := by
  intro k hk
  rw [img_close, getD_append_zero]
  by_cases h0 : k = wl e
  · subst h0
    rw [hw]; exact (getD_mid_self _ _ _).symm
  · rw [hrest k hk h0, hS k hk, img, getD_mid _ _ _ _ k h0]

end SigGolfCandidate.T3M.Expand
