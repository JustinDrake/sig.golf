import SigGolfCandidate.T3M.Witness.Dfs

/-!
# Sign: the machine's iterative frontier is Core's `frontier`

The sign image emits the multiproof of a coordinate leaf by leaf (`fr_leaf`, words 280..330): for each
sorted leaf `g` it descends from the level where the previous leaf's walk stopped, emitting the left
siblings of the path where it goes right (`descL`), then ascends from level 0 emitting the right siblings
where it goes left, until the next leaf's ancestor is that right sibling (`ascR` up to the LCA level − 1).
`mf s e S` is that walk over a sorted leaf list `S` (entering at level `s`, leaving at level `e`).

`frontier_eq_mf` : for a block `(L, N)` whose leaves (among Core's `leaves`) are exactly the strictly
increasing nonempty list `S`, Core's recursive `frontier leaves L N` equals `mf L L S`.
-/

namespace SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3 (hasLeaf)
open SigGolfCandidate.T3M (lcaLevel hasLeaf_iff hasLeaf_false_iff lca_of_div_sib xor_one_eq)

/-- The level-`s` entry of a descent: the left sibling where the path of `g` goes right. -/
def topD (g s : Nat) : List (Nat × Nat) := if g / 2 ^ s % 2 = 1 then [(s, g / 2 ^ s ^^^ 1)] else []

/-- The level-`e` entry of an ascent: the right sibling where the path of `g` goes left. -/
def topA (g e : Nat) : List (Nat × Nat) := if g / 2 ^ e % 2 = 0 then [(e, g / 2 ^ e ^^^ 1)] else []

/-- Left siblings of the root path of `g` from level `s - 1` down to `0` (where the path goes right). -/
def descL (g : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | s + 1 => topD g s ++ descL g s

/-- Right siblings of the root path of `g` from level `0` up to `e - 1` (where the path goes left). -/
def ascR (g : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | e + 1 => ascR g e ++ topA g e

/-- The machine's frontier walk over a sorted leaf list, entering at level `s`, leaving at level `e`. -/
def mf (s e : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | [g] => descL g s ++ ascR g e
  | g :: g' :: rest => descL g s ++ ascR g (lcaLevel g g' - 1) ++ mf (lcaLevel g g' - 1) e (g' :: rest)

theorem mf_s_succ (s e g : Nat) (rest : List Nat) :
    mf (s + 1) e (g :: rest) = topD g s ++ mf s e (g :: rest) := by
  cases rest with
  | nil => simp [mf, descL]
  | cons g' r => simp [mf, descL]

theorem mf_e_succ (e : Nat) : ∀ (S : List Nat) (s : Nat) (hS : S ≠ []),
    mf s (e + 1) S = mf s e S ++ topA (S.getLast hS) e
  | [], _, h => absurd rfl h
  | [g], s, _ => by simp only [mf, ascR, List.getLast_singleton, List.append_assoc]
  | g :: g' :: rest, s, _ => by
    simp only [mf]
    rw [mf_e_succ e (g' :: rest) _ (List.cons_ne_nil _ _)]
    simp

theorem mf_append (e : Nat) : ∀ (A B : List Nat) (s : Nat) (hA : A ≠ []) (hB : B ≠ []),
    mf s e (A ++ B) = mf s (lcaLevel (A.getLast hA) (B.head hB) - 1) A ++
      mf (lcaLevel (A.getLast hA) (B.head hB) - 1) e B
  | [], _, _, h, _ => absurd rfl h
  | [a], b :: B', s, _, _ => by simp [mf]
  | a :: a' :: A', B, s, _, hB => by
    have := mf_append e (a' :: A') B (lcaLevel a a' - 1) (List.cons_ne_nil _ _) hB
    simp only [List.cons_append] at this ⊢
    simp only [mf]
    rw [this]
    simp

/-- An empty block is one frontier position. -/
theorem frontier_empty {leaves : List Nat} {L N : Nat} (h : hasLeaf leaves L N = false) :
    T3.frontier leaves L N = [(L, N)] := by
  cases L with
  | zero => simp [T3.frontier, h]
  | succ L => simp [T3.frontier, h]

/-- A sorted list splits at a predicate that, along the list, only switches from true to false. -/
theorem split_sorted (p : Nat → Bool) :
    ∀ (S : List Nat), S.Pairwise (· < ·) →
      (∀ x ∈ S, ∀ y ∈ S, x < y → p x = false → p y = false) → S = S.filter p ++ S.filter (fun x => !p x)
  | [], _, _ => rfl
  | x :: xs, h, hp => by
    have hxs := split_sorted p xs (List.pairwise_cons.mp h).2
      (fun a ha b hb hab hpa => hp a (by simp [ha]) b (by simp [hb]) hab hpa)
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, if_true, Bool.not_true, Bool.false_eq_true, if_false, List.cons_append]
      exact congrArg _ hxs
    · have hall : ∀ y ∈ xs, p y = false := fun y hy =>
        hp x (by simp) y (by simp [hy]) ((List.pairwise_cons.mp h).1 y hy) (by simpa using hx)
      have h1 : xs.filter p = [] := List.filter_eq_nil_iff.mpr (fun y hy => by simp [hall y hy])
      have h2 : xs.filter (fun x => !p x) = xs := List.filter_eq_self.mpr (fun y hy => by simp [hall y hy])
      simp only [List.filter_cons, hx, Bool.false_eq_true, if_false, Bool.not_false, if_true, h1, h2,
        List.nil_append]

theorem xor_one_even (N : Nat) : 2 * N ^^^ 1 = 2 * N + 1 := by
  rw [xor_one_eq]; omega

theorem xor_one_odd (N : Nat) : (2 * N + 1) ^^^ 1 = 2 * N := by
  rw [xor_one_eq]; omega

/-- **The iterative frontier is Core's `frontier`.** For a block `(L, N)` whose leaves among `leaves` are
exactly the strictly increasing nonempty list `S`: `frontier leaves L N = mf L L S`. -/
theorem frontier_eq_mf (leaves : List Nat) : ∀ (L N : Nat) (S : List Nat),
    S.Pairwise (· < ·) → S ≠ [] → (∀ g, g ∈ S ↔ g ∈ leaves ∧ g / 2 ^ L = N) →
    T3.frontier leaves L N = mf L L S
  | 0, N, S, hs, hne, hm => by
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hg : g = N := by have := ((hm g).mp (by simp)).2; simpa using this
    have hrest : rest = [] := by
      cases rest with
      | nil => rfl
      | cons g' r =>
        have h1 : g' = N := by have := ((hm g').mp (by simp)).2; simpa using this
        have : g < g' := (List.pairwise_cons.mp hs).1 g' (by simp)
        omega
    subst hrest
    have hl : hasLeaf leaves 0 N = true :=
      (hasLeaf_iff _ _ _).mpr ⟨g, ((hm g).mp (by simp)).1, by simpa using hg⟩
    simp [T3.frontier, hl, mf, descL, ascR]
  | k + 1, N, S, hs, hne, hm => by
    have hl : hasLeaf leaves (k + 1) N = true := by
      obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil S hne
      exact (hasLeaf_iff _ _ _).mpr ⟨g, ((hm g).mp hg).1, ((hm g).mp hg).2⟩
    have hf : T3.frontier leaves (k + 1) N =
        T3.frontier leaves k (2 * N) ++ T3.frontier leaves k (2 * N + 1) := by
      simp [T3.frontier, hl]
    have hup : ∀ g, g / 2 ^ (k + 1) = g / 2 ^ k / 2 := fun g => by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hdiv : ∀ g ∈ S, g / 2 ^ k = 2 * N ∨ g / 2 ^ k = 2 * N + 1 := by
      intro g hg
      have := ((hm g).mp hg).2
      rw [hup] at this
      omega
    let p : Nat → Bool := fun g => decide (g / 2 ^ k = 2 * N)
    have hsplit : S = S.filter p ++ S.filter (fun x => !p x) := by
      refine split_sorted p S hs (fun x hx y hy hxy hpx => ?_)
      have h1 := hdiv x hx
      have h2 := hdiv y hy
      have : x / 2 ^ k ≤ y / 2 ^ k := Nat.div_le_div_right hxy.le
      simp only [p, decide_eq_false_iff_not] at hpx ⊢
      omega
    set A := S.filter p with hA
    set B := S.filter (fun x => !p x) with hB
    have hmA : ∀ g, g ∈ A ↔ g ∈ leaves ∧ g / 2 ^ k = 2 * N := by
      intro g
      rw [hA, List.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨((hm g).mp h1).1, by simpa [p] using h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hm g).mpr ⟨h1, by rw [hup, h2]; omega⟩, by simpa [p] using h2⟩
    have hmB : ∀ g, g ∈ B ↔ g ∈ leaves ∧ g / 2 ^ k = 2 * N + 1 := by
      intro g
      rw [hB, List.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨((hm g).mp h1).1, ?_⟩
        have := hdiv g h1
        simp only [p, Bool.not_eq_true', decide_eq_false_iff_not] at h2
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨(hm g).mpr ⟨h1, by rw [hup, h2]; omega⟩, by simp [p, h2]⟩
    have hsA : A.Pairwise (· < ·) := hs.filter _
    have hsB : B.Pairwise (· < ·) := hs.filter _
    have hA2 : ∀ g ∈ A, g / 2 ^ k = 2 * N := fun g hg => ((hmA g).mp hg).2
    have hB2 : ∀ g ∈ B, g / 2 ^ k = 2 * N + 1 := fun g hg => ((hmB g).mp hg).2
    have emptyA : A = [] → hasLeaf leaves k (2 * N) = false := by
      intro h
      rw [hasLeaf_false_iff]
      intro g hg he
      have := (hmA g).mpr ⟨hg, he⟩
      rw [h] at this; simp at this
    have emptyB : B = [] → hasLeaf leaves k (2 * N + 1) = false := by
      intro h
      rw [hasLeaf_false_iff]
      intro g hg he
      have := (hmB g).mpr ⟨hg, he⟩
      rw [h] at this; simp at this
    rw [hf]
    by_cases ha : A = []
    · -- all leaves in the right child
      have hb : B ≠ [] := by
        intro hb; rw [hsplit, ha, hb] at hne; exact hne rfl
      have hSB : S = B := by rw [hsplit, ha, List.nil_append]
      rw [frontier_empty (emptyA ha), frontier_eq_mf leaves k (2 * N + 1) B hsB hb hmB, hSB]
      obtain ⟨b0, rest, hb0⟩ := List.exists_cons_of_ne_nil hb
      rw [hb0, mf_s_succ, mf_e_succ k (b0 :: rest) k (List.cons_ne_nil _ _)]
      have h0 := hB2 b0 (by rw [hb0]; simp)
      have hlast := hB2 ((b0 :: rest).getLast (List.cons_ne_nil _ _)) (by rw [hb0]; exact List.getLast_mem _)
      simp only [topD, topA, h0, hlast]
      simp [xor_one_odd]
    · by_cases hb : B = []
      · -- all leaves in the left child
        have hSA : S = A := by rw [hsplit, hb, List.append_nil]
        rw [frontier_empty (emptyB hb), frontier_eq_mf leaves k (2 * N) A hsA ha hmA, hSA]
        obtain ⟨a0, rest, ha0⟩ := List.exists_cons_of_ne_nil ha
        rw [ha0, mf_s_succ, mf_e_succ k (a0 :: rest) k (List.cons_ne_nil _ _)]
        have h0 := hA2 a0 (by rw [ha0]; simp)
        have hlast := hA2 ((a0 :: rest).getLast (List.cons_ne_nil _ _)) (by rw [ha0]; exact List.getLast_mem _)
        simp only [topD, topA, h0, hlast]
        simp [xor_one_even]
      · -- the split happens here
        rw [frontier_eq_mf leaves k (2 * N) A hsA ha hmA, frontier_eq_mf leaves k (2 * N + 1) B hsB hb hmB]
        have hlca : lcaLevel (A.getLast ha) (B.head hb) = k + 1 := by
          apply lca_of_div_sib
          rw [hB2 _ (List.head_mem hb), hA2 _ (List.getLast_mem ha), xor_one_even]
        conv_rhs => rw [hsplit]
        obtain ⟨a0, rest, ha0⟩ := List.exists_cons_of_ne_nil ha
        have h0 := hA2 a0 (by rw [ha0]; simp)
        have hAB : A ++ B = a0 :: (rest ++ B) := by rw [ha0]; rfl
        rw [hAB, mf_s_succ, ← hAB, mf_append (k + 1) A B k ha hb, hlca, Nat.add_sub_cancel,
          mf_e_succ k B k hb]
        have hlast := hB2 (B.getLast hb) (List.getLast_mem hb)
        simp only [topD, topA, h0, hlast]
        simp

end SigGolfCandidate.T3M.Sign
