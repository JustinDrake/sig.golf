import SigGolfCandidate.T3M.Witness.Shaped
import SigGolfCandidate.T3M.Witness.Normal

/-! # The control skeleton of the stream machine (stream W)

`segShape`/`coordShape`/`ftsShape` (in `Normal`) are the stream machine without hashing. Here: the skeleton of an
honest coordinate runs through the five scheduled segments (`coordShape_sched`), and conversely an accepting run
forces the headers to be the scheduled ones (`coordShape_inv`: the `Q` checks determine the LCA levels through
`Bits.heap_sib_inv`). Together: **`stream_shaped_iff`**. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## One segment -/

theorem segShape_stop (w : WBytes) (stack : List Nat) (E ptr A : Nat) (h : HdrOk (wbyte w ptr).toNat A 0 E) :
    segShape w stack E ptr = some (E / 2 ^ A, segNext ptr A, stack) := by
  rw [segShape.eq_1]
  simp only [h.a, h.m]
  rw [if_neg (Nat.not_lt.mpr h.le), if_neg (by rintro ⟨hp, hne⟩; exact hne (h.t hp))]
  rcases stack with _ | ⟨Q, rest⟩ <;> simp

theorem segShape_merge (w : WBytes) (Q : Nat) (rest : List Nat) (E ptr A : Nat) (h : HdrOk (wbyte w ptr).toNat A 1 E)
    (hQ : Q = E / 2 ^ A) :
    segShape w (Q :: rest) E ptr = segShape w rest (E / 2 ^ A / 2) (segNext ptr A) := by
  rw [segShape.eq_1]
  simp only [h.a, h.m]
  rw [if_neg (Nat.not_lt.mpr h.le), if_neg (by rintro ⟨hp, hne⟩; exact hne (h.t hp))]
  simp [hQ]

/-- What an accepting segment tells about its header byte. -/
structure SegInv (b A E : Nat) : Prop where
  a : b % 16 = A
  le : A ≤ 11
  t : 0 < A → b / 32 % 2 = E % 2

theorem segShape_inv_nil (w : WBytes) (E ptr E' p' : Nat) (s' : List Nat)
    (h : segShape w [] E ptr = some (E', p', s')) :
    SegInv (wbyte w ptr).toNat ((wbyte w ptr).toNat % 16) E ∧ (wbyte w ptr).toNat / 16 % 2 = 0 ∧
      E' = E / 2 ^ ((wbyte w ptr).toNat % 16) ∧ p' = segNext ptr ((wbyte w ptr).toNat % 16) ∧ s' = [] := by
  rw [segShape.eq_1] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      simp only [] at h
      split at h
      · simp at h
      · rename_i h3
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨⟨rfl, by omega, fun hp => by by_contra hc; exact h2 ⟨hp, hc⟩⟩, by omega, rfl, rfl, rfl⟩

theorem segShape_inv_cons (w : WBytes) (Q : Nat) (rest : List Nat) (E ptr E' p' : Nat) (s' : List Nat)
    (h : segShape w (Q :: rest) E ptr = some (E', p', s')) :
    SegInv (wbyte w ptr).toNat ((wbyte w ptr).toNat % 16) E ∧
      (((wbyte w ptr).toNat / 16 % 2 = 0 ∧ E' = E / 2 ^ ((wbyte w ptr).toNat % 16) ∧
          p' = segNext ptr ((wbyte w ptr).toNat % 16) ∧ s' = Q :: rest) ∨
        ((wbyte w ptr).toNat / 16 % 2 = 1 ∧ Q = E / 2 ^ ((wbyte w ptr).toNat % 16) ∧
          segShape w rest (E / 2 ^ ((wbyte w ptr).toNat % 16) / 2) (segNext ptr ((wbyte w ptr).toNat % 16)) =
            some (E', p', s'))) := by
  rw [segShape.eq_1] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      have hI : SegInv (wbyte w ptr).toNat ((wbyte w ptr).toNat % 16) E :=
        ⟨rfl, by omega, fun hp => by by_contra hc; exact h2 ⟨hp, hc⟩⟩
      simp only [] at h
      split at h
      · rename_i h3
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hI, Or.inl ⟨h3, rfl, rfl, rfl⟩⟩
      · rename_i h3
        split at h
        · simp at h
        · rename_i h4
          exact ⟨hI, Or.inr ⟨by omega, by omega, h⟩⟩

/-! ## The honest run -/

theorem hdrOk_of_matches' {seg : Segment} {b : Nat} (h : seg.Matches b) (hle : seg.a ≤ 11) {E : Nat}
    (hE : E = (2048 + seg.g) / 2 ^ seg.lo) :
    HdrOk b seg.a (if seg.merge then 1 else 0) E := hE ▸ hdrOk_of_matches h hle

/-- Matching headers on every segment of a coordinate (at its pointers). -/
def HdrsOk (w : WBytes) : Nat → List Segment → Prop
  | _, [] => True
  | ptr, s :: rest => s.Matches (wbyte w ptr).toNat ∧ HdrsOk w (segNext ptr s.a) rest

theorem SegsOk.hdrs {w : WBytes} {val pad : Nat × Nat → Digest} : ∀ {ptr : Nat} {segs : List Segment},
    SegsOk w val pad ptr segs → HdrsOk w ptr segs
  | _, [], _ => trivial
  | _, _ :: _, ⟨h, hs⟩ => ⟨h.1, SegsOk.hdrs hs⟩

/-- **The skeleton of a matching coordinate** reaches the end of its five segments. -/
theorem coordShape_sched (w : WBytes) (coord : Nat) (sel : Selection) (ptr : Nat) (hs : SelOk sel)
    (hok : HdrsOk w ptr (coordSchedule coord sel)) :
    coordShape w sel ptr = some (segsEnd ptr (coordSchedule coord sel)) := by
  have hsel := hs.selected
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have g2l : selLeaf sel 2 < 2048 := by unfold selLeaf; have := hs.l2; have := hs.b; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  unfold coordShape
  unfold coordSchedule at hok ⊢
  simp only [] at hok ⊢
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have e0 : ∀ g, 2048 + g = (2048 + g) / 2 ^ 0 := by intro g; simp
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  have dd : ∀ g a b, (2048 + g) / 2 ^ a / 2 ^ b = (2048 + g) / 2 ^ (a + b) := fun g a b => heap_div_pow g a b
  have d2 : ∀ g a, (2048 + g) / 2 ^ a / 2 = (2048 + g) / 2 ^ (a + 1) := fun g a => heap_div_two g a
  by_cases hA : d01 < d12
  · simp only [if_pos hA] at hok ⊢
    simp only [HdrsOk, segsEnd] at hok ⊢
    obtain ⟨m0, m1, m2, m3, m4, -⟩ := hok
    have H0 := hdrOk_of_matches' m0 (by dsimp only; omega) (e0 g0)
    have H1 := hdrOk_of_matches' m1 (by dsimp only; omega) (e0 g1)
    have H2 := hdrOk_of_matches' m2 (by dsimp only; omega)
      (show (2048 + g1) / 2 ^ (d01 - 1) / 2 = (2048 + g1) / 2 ^ d01 by rw [d2, show d01 - 1 + 1 = d01 by omega])
    have H3 := hdrOk_of_matches' m3 (by dsimp only; omega) (e0 g2)
    have H4 := hdrOk_of_matches' m4 (by dsimp only; omega)
      (show (2048 + g2) / 2 ^ (d12 - 1) / 2 = (2048 + g2) / 2 ^ d12 by rw [d2, show d12 - 1 + 1 = d12 by omega])
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    have q1 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g1) / 2 ^ (d01 - 1) :=
      heap_sib (by omega) (by omega) (by omega)
    have q3 : (2048 + g1) / 2 ^ (d01 - 1) / 2 / 2 ^ (d12 - 1 - d01) ^^^ 1 = (2048 + g2) / 2 ^ (d12 - 1) := by
      rw [d2, dd, show d01 - 1 + 1 + (d12 - 1 - d01) = d12 - 1 by omega]
      exact heap_sib (by omega) (by omega) (by omega)
    rw [segShape_stop w [] _ _ _ H0]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [segShape_merge w _ [] _ _ _ H1 q1, segShape_stop w [] _ _ _ H2]
    simp only [Option.bind_some]
    rw [segShape_merge w _ [] _ _ _ H3 q3, segShape_stop w [] _ _ _ H4]
    simp only [Option.bind_some]
    have hroot : (2048 + g2) / 2 ^ (d12 - 1) / 2 / 2 ^ (11 - d12) = 1 := by
      rw [d2, dd, show d12 - 1 + 1 + (11 - d12) = 11 by omega]; omega
    simp [hroot]
  · simp only [if_neg hA] at hok ⊢
    have hB : d12 < d01 := by omega
    simp only [HdrsOk, segsEnd] at hok ⊢
    obtain ⟨m0, m1, m2, m3, m4, -⟩ := hok
    have H0 := hdrOk_of_matches' m0 (by dsimp only; omega) (e0 g0)
    have H1 := hdrOk_of_matches' m1 (by dsimp only; omega) (e0 g1)
    have H2 := hdrOk_of_matches' m2 (by dsimp only; omega) (e0 g2)
    have H3 := hdrOk_of_matches' m3 (by dsimp only; omega)
      (show (2048 + g2) / 2 ^ (d12 - 1) / 2 = (2048 + g2) / 2 ^ d12 by rw [d2, show d12 - 1 + 1 = d12 by omega])
    have H4 := hdrOk_of_matches' m4 (by dsimp only; omega)
      (show (2048 + g2) / 2 ^ (d12 - 1) / 2 / 2 ^ (d01 - 1 - d12) / 2 = (2048 + g2) / 2 ^ d01 by
        rw [d2, dd, d2, show d12 - 1 + 1 + (d01 - 1 - d12) + 1 = d01 by omega])
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    have q2 : (2048 + g1) / 2 ^ (d12 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (d12 - 1) :=
      heap_sib (by omega) (by omega) (by omega)
    have q3 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (d12 - 1) / 2 / 2 ^ (d01 - 1 - d12) := by
      rw [d2, dd, show d12 - 1 + 1 + (d01 - 1 - d12) = d01 - 1 by omega]
      exact heap_sib (by omega) (by omega) (by rw [l02]; omega)
    rw [segShape_stop w [] _ _ _ H0]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [segShape_stop w _ _ _ _ H1]
    simp only [Option.bind_some]
    rw [segShape_merge w _ _ _ _ _ H2 q2, segShape_merge w _ [] _ _ _ H3 q3, segShape_stop w [] _ _ _ H4]
    simp only [Option.bind_some]
    have hroot : (2048 + g2) / 2 ^ (d12 - 1) / 2 / 2 ^ (d01 - 1 - d12) / 2 / 2 ^ (11 - d01) = 1 := by
      rw [d2, dd, d2, dd, show d12 - 1 + 1 + (d01 - 1 - d12) + 1 + (11 - d01) = 11 by omega]; omega
    simp [hroot]

/-! ## The converse: an accepting coordinate has the scheduled headers -/

theorem heap_one {g K : Nat} (hg : g < 2048) (h : (2048 + g) / 2 ^ K = 1) : K = 11 := by
  by_contra hK
  rcases Nat.lt_or_gt_of_ne hK with hl | hl
  · rw [heap_eq (by omega)] at h
    have : 2 ≤ 2 ^ (11 - K) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (11 - K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize g / 2 ^ K = d at *
    omega
  · have : (2048 + g) / 2 ^ K = 0 := Nat.div_eq_of_lt (by
      calc 2048 + g < 2 ^ 12 := by norm_num; omega
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega))
    omega

theorem heap_two_le {g K : Nat} (hK : K ≤ 10) : 2 ≤ (2048 + g) / 2 ^ K := by
  rw [heap_eq (by omega)]
  have : 2 ≤ 2 ^ (11 - K) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (11 - K) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize g / 2 ^ K = d at *
  omega

theorem matches_of_inv {seg : Segment} {b E : Nat} (hi : SegInv b seg.a E)
    (hm : b / 16 % 2 = (if seg.merge then 1 else 0)) (hE : E = (2048 + seg.g) / 2 ^ seg.lo) : seg.Matches b := by
  refine ⟨hi.a, ?_, fun hp => ?_⟩
  · cases h : seg.merge <;> simp [h] at hm ⊢ <;> omega
  · rw [hi.t hp, hE]; simp [Segment.t, Segment.heap]

/-- **Converse (stack invariant).** An accepting coordinate run reads exactly the scheduled headers. -/
theorem coordShape_inv (w : WBytes) (coord : Nat) (sel : Selection) (ptr p : Nat) (hs : SelOk sel)
    (h : coordShape w sel ptr = some p) :
    HdrsOk w ptr (coordSchedule coord sel) ∧ p = segsEnd ptr (coordSchedule coord sel) := by
  have hsel := hs.selected
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have g2l : selLeaf sel 2 < 2048 := by unfold selLeaf; have := hs.l2; have := hs.b; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hsel]; simp)
  unfold coordShape at h
  unfold coordSchedule
  simp only [] at h ⊢
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have dd : ∀ g a b, (2048 + g) / 2 ^ a / 2 ^ b = (2048 + g) / 2 ^ (a + b) := fun g a b => heap_div_pow g a b
  have d2 : ∀ g a, (2048 + g) / 2 ^ a / 2 = (2048 + g) / 2 ^ (a + 1) := fun g a => heap_div_two g a
  have e0 : ∀ g, 2048 + g = (2048 + g) / 2 ^ 0 := by intro g; simp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨E0, p0, s0⟩, h0, h⟩ := h
  obtain ⟨⟨E1, p1, s1⟩, h1, h⟩ := h
  obtain ⟨⟨E2, p2, s2⟩, h2, h⟩ := h
  split at h
  swap; · simp at h
  rename_i hfin
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hE2, rfl⟩ := hfin
  obtain ⟨I0, m0, rfl, rfl, rfl⟩ := segShape_inv_nil w _ _ _ _ _ h0
  generalize hb0 : (wbyte w ptr).toNat = b0 at *
  generalize hA0 : b0 % 16 = A0 at *
  obtain ⟨I1, hc1⟩ := segShape_inv_cons w _ _ _ _ _ _ _ h1
  generalize hb1 : (wbyte w (segNext ptr A0)).toNat = b1 at *
  generalize hA1 : b1 % 16 = A1 at *
  rcases hc1 with ⟨m1, rfl, rfl, rfl⟩ | ⟨m1, hq0, h1'⟩
  · -- leaf 1 stopped: the coordinate is case `d12 < d01`
    obtain ⟨I2, hc2⟩ := segShape_inv_cons w _ _ _ _ _ _ _ h2
    generalize hb2 : (wbyte w (segNext (segNext ptr A0) A1)).toNat = b2 at *
    generalize hA2 : b2 % 16 = A2 at *
    rcases hc2 with ⟨_, _, _, hs2⟩ | ⟨m2, hq1, h2'⟩
    · simp at hs2
    obtain ⟨I3, hc3⟩ := segShape_inv_cons w _ _ _ _ _ _ _ h2'
    generalize hb3 : (wbyte w (segNext (segNext (segNext ptr A0) A1) A2)).toNat = b3 at *
    generalize hA3 : b3 % 16 = A3 at *
    rcases hc3 with ⟨_, _, _, hs3⟩ | ⟨m3, hq2, h3'⟩
    · simp at hs3
    obtain ⟨I4, m4, rfl, rfl, -⟩ := segShape_inv_nil w _ _ _ _ _ h3'
    generalize hb4 : (wbyte w (segNext (segNext (segNext (segNext ptr A0) A1) A2) A3)).toNat = b4 at *
    generalize hA4 : b4 % 16 = A4 at *
    rw [d2, dd, d2, dd] at hE2
    have hK := heap_one g2l hE2
    rw [d2, dd] at hq2
    obtain ⟨_, hk0, hl0⟩ := heap_sib_inv (by omega) g2l hq2 (heap_two_le (by omega))
    obtain ⟨_, hk1, hl1⟩ := heap_sib_inv (by omega) g2l hq1 (heap_two_le (by omega))
    generalize hd01 : lcaLevel g0 g1 = d01 at *
    generalize hd12 : lcaLevel g1 g2 = d12 at *
    rw [l02] at hl0
    have hB : d12 < d01 := by omega
    have hd1 : d01 = A0 + 1 := by omega
    rw [if_neg (by omega)]
    simp only [HdrsOk, segsEnd]
    have ea0 : A0 = d01 - 1 := by omega
    have ea1 : A1 = d12 - 1 := by omega
    have ea2 : A2 = d12 - 1 := by omega
    have ea3 : A3 = d01 - 1 - d12 := by omega
    have ea4 : A4 = 11 - d01 := by omega
    subst ea0 ea1 ea2 ea3 ea4
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, trivial⟩, rfl⟩
    · rw [hb0]; exact matches_of_inv (by simpa [hA0] using I0) (by simpa using m0) (e0 g0)
    · rw [hb1]; exact matches_of_inv (by simpa [hA1] using I1) (by simpa using m1) (e0 g1)
    · rw [hb2]; exact matches_of_inv (by simpa [hA2] using I2) (by simpa using m2) (e0 g2)
    · rw [hb3]; exact matches_of_inv (by simpa [hA3] using I3) (by simpa using m3)
        (by rw [d2, show d12 - 1 + 1 = d12 by omega])
    · rw [hb4]; exact matches_of_inv (by simpa [hA4] using I4) (by simpa using m4)
        (by rw [d2, dd, d2, show d12 - 1 + 1 + (d01 - 1 - d12) + 1 = d01 by omega])
  · -- leaf 1 merged: the coordinate is case `d01 < d12`
    obtain ⟨I2, m2, rfl, rfl, rfl⟩ := segShape_inv_nil w _ _ _ _ _ h1'
    generalize hb2 : (wbyte w (segNext (segNext ptr A0) A1)).toNat = b2 at *
    generalize hA2 : b2 % 16 = A2 at *
    obtain ⟨I3, hc3⟩ := segShape_inv_cons w _ _ _ _ _ _ _ h2
    generalize hb3 : (wbyte w (segNext (segNext (segNext ptr A0) A1) A2)).toNat = b3 at *
    generalize hA3 : b3 % 16 = A3 at *
    rcases hc3 with ⟨_, _, _, hs3⟩ | ⟨m3, hq1, h3'⟩
    · simp at hs3
    obtain ⟨I4, m4, rfl, rfl, -⟩ := segShape_inv_nil w _ _ _ _ _ h3'
    generalize hb4 : (wbyte w (segNext (segNext (segNext (segNext ptr A0) A1) A2) A3)).toNat = b4 at *
    generalize hA4 : b4 % 16 = A4 at *
    rw [d2, dd] at hE2
    have hK := heap_one g2l hE2
    rw [d2, dd] at hq1
    obtain ⟨_, hk1, hl1⟩ := heap_sib_inv (by omega) g2l hq1 (heap_two_le (by omega))
    obtain ⟨_, hk0, hl0⟩ := heap_sib_inv (by omega) (by omega) hq0 (heap_two_le (by omega))
    generalize hd01 : lcaLevel g0 g1 = d01 at *
    generalize hd12 : lcaLevel g1 g2 = d12 at *
    have hA : d01 < d12 := by omega
    rw [if_pos hA]
    simp only [HdrsOk, segsEnd]
    have ea0 : A0 = d01 - 1 := by omega
    have ea1 : A1 = d01 - 1 := by omega
    have ea2 : A2 = d12 - 1 - d01 := by omega
    have ea3 : A3 = d12 - 1 := by omega
    have ea4 : A4 = 11 - d12 := by omega
    subst ea0 ea1 ea2 ea3 ea4
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, trivial⟩, rfl⟩
    · rw [hb0]; exact matches_of_inv (by simpa [hA0] using I0) (by simpa using m0) (e0 g0)
    · rw [hb1]; exact matches_of_inv (by simpa [hA1] using I1) (by simpa using m1) (e0 g1)
    · rw [hb2]; exact matches_of_inv (by simpa [hA2] using I2) (by simpa using m2)
        (by rw [d2, show d01 - 1 + 1 = d01 by omega])
    · rw [hb3]; exact matches_of_inv (by simpa [hA3] using I3) (by simpa using m3) (e0 g2)
    · rw [hb4]; exact matches_of_inv (by simpa [hA4] using I4) (by simpa using m4)
        (by rw [d2, show d12 - 1 + 1 = d12 by omega])

/-! ## Seven coordinates: `stream_shaped_iff` -/

theorem hdrsOk_of_getD (w : WBytes) : ∀ (segs : List Segment) (f : Nat → Nat),
    (∀ i < segs.length, f (i + 1) = segNext (f i) (segs.getD i default).a) →
    ((∀ i < segs.length, (segs.getD i default).Matches (wbyte w (f i)).toNat) ↔ HdrsOk w (f 0) segs) ∧
      segsEnd (f 0) segs = f segs.length := by
  intro segs
  induction segs with
  | nil => intro f _; simp [HdrsOk, segsEnd]
  | cons s rest ih =>
      intro f hf
      have h0 := hf 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      obtain ⟨h1, h2⟩ := ih (fun i => f (i + 1)) (fun i hi => by
        have := hf (i + 1) (by simp; omega); simpa using this)
      simp only [h0] at h1 h2
      refine ⟨⟨fun H => ⟨by simpa using H 0 (by simp), h1.mp (fun i hi => by
          simpa using H (i + 1) (by simp; omega))⟩, fun H i hi => ?_⟩, ?_⟩
      · rcases i with _ | i
        · simpa using H.1
        · simpa using h1.mpr H.2 i (by simpa using hi)
      · simp only [segsEnd, h2, List.length_cons]

theorem coord_ptrs (chosen : List Selection) {c : Nat} (hc7 : c < 7) :
    ∀ i < (coordSchedule c (chosen.getD c ⟨0, []⟩)).length,
      segPtr (schedule chosen) (5 * c + (i + 1)) =
        segNext (segPtr (schedule chosen) (5 * c + i)) ((coordSchedule c (chosen.getD c ⟨0, []⟩)).getD i default).a := by
  intro i hi
  rw [coordSchedule_length] at hi
  have hn : 5 * c + i < 35 := by omega
  have := segPtr_succ (schedule chosen) (m := 5 * c + i) (by rw [schedule_length]; exact hn)
  rw [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this
  simpa only [Nat.add_assoc] using this

theorem fold_shape_sched (w : WBytes) (chosen : List Selection) (hc : ChosenOk chosen)
    (hm : StreamMatches chosen w) : ∀ n ≤ 7,
      (List.range n).foldlM (fun ptr c => coordShape w (chosen.getD c ⟨0, []⟩) ptr) streamBase =
        some (segPtr (schedule chosen) (5 * n)) := by
  intro n
  induction n with
  | zero => intro _; simp [segPtr_zero]
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [Option.bind_eq_bind, List.foldlM_cons, List.foldlM_nil, Option.bind_some]
      obtain ⟨hiff, hend⟩ := hdrsOk_of_getD w (coordSchedule n (chosen.getD n ⟨0, []⟩))
        (fun i => segPtr (schedule chosen) (5 * n + i)) (coord_ptrs chosen (by omega))
      simp only [Nat.add_zero, coordSchedule_length] at hiff hend
      have hh := hiff.mp (fun i hi => by
        have := hm (5 * n + i) (by rw [schedule_length]; omega)
        rwa [schedule_getD _ (by omega), show (5 * n + i) / 5 = n by omega, show (5 * n + i) % 5 = i by omega] at this)
      rw [coordShape_sched w n _ _ (hc n (by omega)) hh, hend]
      simp only [Option.pure_def, Option.bind_some]
      ring_nf

theorem fold_shape_inv (w : WBytes) (chosen : List Selection) (hc : ChosenOk chosen) : ∀ n ≤ 7, ∀ P,
    (List.range n).foldlM (fun ptr c => coordShape w (chosen.getD c ⟨0, []⟩) ptr) streamBase = some P →
      P = segPtr (schedule chosen) (5 * n) ∧
        ∀ m < 5 * n, ((schedule chosen).getD m default).Matches (wbyte w (segPtr (schedule chosen) m)).toNat := by
  intro n
  induction n with
  | zero => intro _ P h; simp at h; subst h; exact ⟨by simp [segPtr_zero], fun m hm => by omega⟩
  | succ n ih =>
      intro hn P h
      rw [List.range_succ, List.foldlM_append] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, List.foldlM_cons, List.foldlM_nil] at h
      obtain ⟨P', h1, h2⟩ := h
      obtain ⟨rfl, hlow⟩ := ih (by omega) P' h1
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right] at h2
      obtain ⟨hh, rfl⟩ := coordShape_inv w n _ _ _ (hc n (by omega)) h2
      obtain ⟨hiff, hend⟩ := hdrsOk_of_getD w (coordSchedule n (chosen.getD n ⟨0, []⟩))
        (fun i => segPtr (schedule chosen) (5 * n + i)) (coord_ptrs chosen (by omega))
      simp only [Nat.add_zero, coordSchedule_length] at hiff hend
      refine ⟨by rw [hend]; ring_nf, fun m hm => ?_⟩
      by_cases hmn : m < 5 * n
      · exact hlow m hmn
      · have := hiff.mpr hh (m - 5 * n) (by omega)
        rw [show 5 * n + (m - 5 * n) = m by omega] at this
        rwa [schedule_getD _ (by omega), show m / 5 = n by omega, show m % 5 = m - 5 * n by omega]

theorem admissible_of_slotBase (N : HashOutput) (hc : ChosenOk (selections N))
    (h : slotBase (selections N) 7 ≤ 115) : admissible (selections N) = true := by
  rw [slotBase_seven_eq N hc] at h
  simp only [admissible, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun sel hm => ?_, h⟩
  obtain ⟨c, hc', rfl⟩ := List.mem_iff_getElem.mp hm
  rw [selections_length] at hc'
  obtain ⟨x0, x1, x2, hl, h01, h12, _⟩ := (hc c hc').exists
  rw [List.getD_eq_getElem _ _ (by rw [selections_length]; exact hc')] at hl
  rw [hl]; simp; omega

/-- **`stream_shaped_iff`** (both halves). -/
theorem stream_shaped_iff (N : HashOutput) (w : WBytes) (hsel : selectionsOk (selections N) = true) :
    (ftsShape w (selections N)).isSome = true ↔
      admissible (selections N) = true ∧ StreamMatches (selections N) w := by
  have hc := chosenOk_of N hsel
  unfold ftsShape
  constructor
  · intro h
    rcases hf : (List.range 7).foldlM (fun ptr c => coordShape w ((selections N).getD c ⟨0, []⟩) ptr)
      streamBase with _ | P
    · rw [hf] at h; simp at h
    · rw [hf] at h
      have hle : P ≤ streamEnd := by
        by_contra hc'
        simp [Option.filter, hc'] at h
      obtain ⟨rfl, hm⟩ := fold_shape_inv w _ hc 7 le_rfl P hf
      rw [show 5 * 7 = 35 by rfl, segPtr_end _ hc] at hle
      unfold streamBase streamEnd at hle
      exact ⟨admissible_of_slotBase N hc (by omega), fun n hn => hm n (by rw [schedule_length] at hn; omega)⟩
  · rintro ⟨hadm, hm⟩
    rw [fold_shape_sched w _ hc hm 7 le_rfl]
    have hle := slotBase_seven_le N hc hadm
    have he := segPtr_end (selections N) hc
    simp only [Option.filter, show 5 * 7 = 35 by rfl, he]
    unfold streamBase streamEnd
    simp only [decide_eq_true_eq]
    rw [if_pos (by omega)]; rfl

theorem streamShapedIff_holds : StreamShapedIff := stream_shaped_iff

/-! ## The machine's decisions do not depend on hash answers -/

theorem folds_support (w : WBytes) (index coord ptr : Nat) : ∀ (a r0 : Nat) (v : Digest) (E : Nat),
    ∀ x ∈ support ((List.range' r0 a).foldlM (foldStep w index coord ptr) (v, E)), x.2 = E / 2 ^ a := by
  intro a
  induction a with
  | zero => intro r0 v E x hx; simp at hx; subst hx; simp
  | succ a ih =>
      intro r0 v E x hx
      rw [List.range'_succ, List.foldlM_cons, mem_support_bind_iff] at hx
      obtain ⟨y, hy, hx⟩ := hx
      have hy2 : y.2 = E / 2 := by
        unfold foldStep at hy
        split at hy <;> · rw [mem_support_bind_iff] at hy; obtain ⟨_, _, hy⟩ := hy; simp at hy; rw [hy]
      have := ih (r0 + 1) y.1 y.2 x (by simpa using hx)
      rw [this, hy2, Nat.div_div_eq_div_mul, ← pow_succ']

theorem foldsP_support (w : WBytes) (index coord ptr a : Nat) (v : Digest) (E : Nat) :
    ∀ x ∈ support (foldsP w index coord ptr a v E), x.2 = E / 2 ^ a := by
  unfold foldsP; rw [List.range_eq_range']; exact folds_support w index coord ptr a 0 v E

/-- `segLoop`'s non-hash outputs are its skeleton's. -/
theorem segLoop_support (w : WBytes) (index coord : Nat) : ∀ (stack : List (Digest × Nat)) (pending : Pending)
    (E ptr : Nat) (node : Digest), ∀ r ∈ support (segLoop w index coord stack pending E ptr node),
      r.map (fun x => (x.2.1, x.2.2.1, x.2.2.2.map Prod.snd)) = segShape w (stack.map Prod.snd) E ptr := by
  intro stack
  induction stack with
  | nil =>
      intro pending E ptr node r hr
      rw [segLoop.eq_1] at hr
      rw [segShape.eq_1]
      split
      · rename_i h; rw [if_pos h] at hr; simp at hr; subst hr; rfl
      · rename_i h; rw [if_neg h] at hr
        split
        · rename_i h'; rw [if_pos h'] at hr; simp at hr; subst hr; rfl
        · rename_i h'; rw [if_neg h'] at hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨n, -, hr⟩ := hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨x, hx, hr⟩ := hr
          have hx2 := foldsP_support w index coord ptr _ n E x hx
          simp only [] at hr
          simp at hr
          subst hr
          split <;> simp [hx2]
  | cons top rest ih =>
      intro pending E ptr node r hr
      obtain ⟨pnode, Q⟩ := top
      rw [segLoop.eq_1] at hr
      rw [segShape.eq_1]
      split
      · rename_i h; rw [if_pos h] at hr; simp at hr; subst hr; rfl
      · rename_i h; rw [if_neg h] at hr
        split
        · rename_i h'; rw [if_pos h'] at hr; simp at hr; subst hr; rfl
        · rename_i h'; rw [if_neg h'] at hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨n, -, hr⟩ := hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨x, hx, hr⟩ := hr
          have hx2 := foldsP_support w index coord ptr _ n E x hx
          simp only [List.map_cons] at hr ⊢
          split
          · rename_i hm; rw [if_pos hm] at hr; simp at hr; subst hr; simp [hx2]
          · rename_i hm; rw [if_neg hm] at hr
            split
            · rename_i hq; rw [if_pos (by rw [hx2]; exact hq)] at hr; simp at hr; subst hr; rfl
            · rename_i hq; rw [if_neg (by rw [hx2]; exact hq)] at hr
              rw [ih _ _ _ _ r hr, hx2]

theorem ftsCoordP_support (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    ∀ r ∈ support (ftsCoordP w index coord sel ptr), r.map Prod.snd = coordShape w sel ptr := by
  intro r hr
  unfold ftsCoordP at hr
  unfold coordShape
  rw [mem_support_bind_iff] at hr
  obtain ⟨r0, h0, hr⟩ := hr
  have s0 := segLoop_support w index coord [] _ _ _ _ r0 h0
  simp only [List.map_nil] at s0
  rcases r0 with _ | ⟨n0, E0, p0, st0⟩
  · simp at hr; subst hr; rw [← s0]; rfl
  · simp only [Option.map_some] at s0
    rw [← s0]
    simp only [Option.bind_eq_bind, Option.bind_some] at hr ⊢
    rw [mem_support_bind_iff] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have s1 := segLoop_support w index coord _ _ _ _ _ r1 h1
    simp only [List.map_cons] at s1
    rcases r1 with _ | ⟨n1, E1, p1, st1⟩
    · simp at hr; subst hr; rw [← s1]; rfl
    · simp only [Option.map_some] at s1
      rw [← s1]
      simp only [Option.bind_some] at hr ⊢
      rw [mem_support_bind_iff] at hr
      obtain ⟨r2, h2, hr⟩ := hr
      have s2 := segLoop_support w index coord _ _ _ _ _ r2 h2
      simp only [List.map_cons] at s2
      rcases r2 with _ | ⟨n2, E2, p2, st2⟩
      · simp at hr; subst hr; rw [← s2]; rfl
      · simp only [Option.map_some] at s2
        rw [← s2]
        simp only [Option.bind_some]
        dsimp only at hr
        by_cases hc : E2 = 1 ∧ st2 = []
        · rw [if_pos hc] at hr; simp at hr; subst hr
          rw [if_pos ⟨hc.1, by rw [hc.2]; rfl⟩]; rfl
        · rw [if_neg hc] at hr; simp at hr; subst hr
          rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1, List.map_eq_nil_iff.mp h2⟩)]; rfl

theorem streamFold_support (w : WBytes) (index : Nat) (chosen : List Selection) : ∀ (l : List Nat)
    (st : Option (List Digest × Nat)), ∀ r ∈ support (l.foldlM (ftsStreamStep w index chosen) st),
      r.map Prod.snd = (st.map Prod.snd).bind fun p => l.foldlM (fun ptr c => coordShape w (chosen.getD c ⟨0, []⟩) ptr) p := by
  intro l
  induction l with
  | nil => intro st r hr; simp at hr; rw [hr]; cases st <;> rfl
  | cons c l ih =>
      intro st r hr
      rw [List.foldlM_cons, mem_support_bind_iff] at hr
      obtain ⟨st', h1, hr⟩ := hr
      rw [ih st' r hr]
      have hst : st'.map Prod.snd = (st.map Prod.snd).bind fun p => coordShape w (chosen.getD c ⟨0, []⟩) p := by
        unfold ftsStreamStep at h1
        rcases st with _ | ⟨roots, ptr⟩
        · simp at h1; subst h1; rfl
        · simp only [] at h1
          rw [mem_support_bind_iff] at h1
          obtain ⟨x, hx, h1⟩ := h1
          have := ftsCoordP_support w index c _ ptr x hx
          rcases x with _ | ⟨root, ptr'⟩
          · simp at h1; subst h1; simp only [Option.map_none, Option.map_some, Option.bind_some]; rw [← this]; rfl
          · simp at h1; subst h1; simp only [Option.map_some, Option.bind_some]; rw [← this]; rfl
      rw [hst]
      rcases st with _ | ⟨roots, ptr⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some, List.foldlM_cons]
        rcases coordShape w (chosen.getD c ⟨0, []⟩) ptr with _ | p <;> rfl

/-- **The FTS rejects on every path when its skeleton does.** -/
theorem ftsP_none_of_shape (w : WBytes) (index : Nat) (chosen : List Selection) (h : ftsShape w chosen = none) :
    ∀ r ∈ support (ftsP w index chosen), r = none := by
  intro r hr
  rw [ftsP_eq, mem_support_bind_iff] at hr
  obtain ⟨st, hst, hr⟩ := hr
  have hs := streamFold_support w index chosen _ _ st hst
  simp only [Option.map_some, Option.bind_some] at hs
  unfold ftsShape at h
  rcases st with _ | ⟨roots, ptr⟩
  · simp at hr; exact hr
  · simp only [Option.map_some] at hs
    rw [← hs] at h
    simp only [Option.filter, decide_eq_true_eq] at h
    split at h
    · simp at h
    · rename_i hle
      simp only [] at hr
      rw [if_pos (by unfold streamEnd at hle ⊢; omega)] at hr
      simpa using hr

/-! ## `verifyP_normal` -/

/-- **`verifyP_normal`** (SEC handoff item 5): `verifyP` is Core's verification with pads on honestly shaped streams
and a never-accepting rejection (`rejectTail`) otherwise. -/
theorem verifyP_normal (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w =
      if (wdc w).toNat ≥ attemptLimit then pure false else (do
        let N ← digest (wrho w) m (wdc w)
        if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N) := by
  rw [verifyP_eq_tail]
  unfold digestP
  split_ifs with h
  · simp
  · rw [bind_map_left]
    refine bind_congr (fun N => ?_)
    dsimp only
    split_ifs with hS
    · exact verifyTailP_shaped pk N w hS
    · unfold verifyTailP rejectTail
      by_cases hsel : selectionsOk (selections N) = true
      · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false]
        have hnot : ftsShape w (selections N) = none := by
          rcases hf : ftsShape w (selections N) with _ | P
          · rfl
          · exfalso
            obtain ⟨ha, hm⟩ := (stream_shaped_iff N w hsel).mp (by rw [hf]; rfl)
            exact hS ⟨hsel, ha, hm⟩
        split_ifs with hg
        · rfl
        · rw [map_eq_bind_pure_comp]
          apply OracleComp.bind_congr_of_forall_mem_support
          intro r hr
          rw [ftsP_none_of_shape w _ _ hnot r hr]
          rfl
      · simp [hsel]

theorem verifyPNormal_holds : VerifyPNormal := verifyP_normal

end SigGolfCandidate.T3M
