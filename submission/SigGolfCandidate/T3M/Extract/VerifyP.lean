import SigGolfCandidate.T3M.Witness.Shaped
import SigGolfCandidate.T3M.Witness.Normal
import SigGolfCandidate.T3M.Extract.Layer
section
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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
theorem hdrOk_of_matches' {seg : Segment} {b : Nat} (h : seg.Matches b) (hle : seg.a ≤ 11) {E : Nat}
    (hE : E = (2048 + seg.g) / 2 ^ seg.lo) :
    HdrOk b seg.a (if seg.merge then 1 else 0) E := hE ▸ hdrOk_of_matches h hle
def HdrsOk (w : WBytes) : Nat → List Segment → Prop
  | _, [] => True
  | ptr, s :: rest => s.Matches (wbyte w ptr).toNat ∧ HdrsOk w (segNext ptr s.a) rest
theorem SegsOk.hdrs {w : WBytes} {val pad : Nat × Nat → Digest} : ∀ {ptr : Nat} {segs : List Segment},
    SegsOk w val pad ptr segs → HdrsOk w ptr segs
  | _, [], _ => trivial
  | _, _ :: _, ⟨h, hs⟩ => ⟨h.1, SegsOk.hdrs hs⟩
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
  ·
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
  ·
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
end
section
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : LayerMessage) (digits : List Nat) :
    Prop :=
  (wctr w lay).toNat < counterLimit ∧
    decode lay (evalWithAnswerFn answers
      (shortHash (encodingInput lay (route index lay).2 (route index lay).1 msg (wctr w lay)))) = some digits
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : LayerMessage) : Spec.Domain :=
  .inl (.inr (pad64 (encodingInput lay (route index lay).2 (route index lay).1 msg (wctr w lay))))
def Good (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∃ digits, Frame answers w index lay (honestMsg answers index lay) digits ∧ LayerShaped answers w index lay digits
def Diverge (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (qs : List Spec.Domain) : Prop :=
  ∃ msg digits, msg ≠ honestMsg answers index lay ∧ Frame answers w index lay msg digits ∧
    LayerShaped answers w index lay digits ∧ encodingQuery w index lay msg ∈ qs
theorem Diverge.mono {answers : Answers} {w : WBytes} {index : Nat} {lay : Layer} {qs qs' : List Spec.Domain}
    (h : Diverge answers w index lay qs) (hsub : ∀ q ∈ qs, q ∈ qs') : Diverge answers w index lay qs' := by
  obtain ⟨msg, digits, hne, hf, hs, hq⟩ := h
  exact ⟨msg, digits, hne, hf, hs, hsub _ hq⟩
noncomputable def walkTarget (answers : Answers) (index : Nat) : Nat → LayerMessage
  | 0 => (honestRoot answers 0 (route index 0).2, 0, 0)
  | n + 1 => if h : n < 4 then honestMsg answers index ⟨n, h⟩ else 0
theorem walkTarget_pair (answers : Answers) (index n : Nat) (hn : n < 4) (h0 : n ≠ 0) :
    walkTarget answers index n = honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
  rcases n with _ | k
  · exact absurd rfl h0
  · have hk : k < 4 := by omega
    have hk3 : k < 3 := by omega
    have hl : (⟨k + 1, by omega⟩ : Layer) = Fin.ofNat 4 (k + 1) := Fin.ext (by simp [Fin.val_ofNat]; omega)
    simp only [walkTarget, dif_pos hk, honestMsg, dif_pos hk3, hl]
theorem layerNextP_zero (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerNextP w index 0 lay digits = (fun value => (value, 0, 0)) <$> layerP w index lay digits := by
  rw [layerNextP, if_pos rfl]
theorem layerNextP_ne (w : WBytes) (index n : Nat) (lay : Layer) (digits : List Nat) (h : n ≠ 0) :
    layerNextP w index n lay digits = layerPairP w index lay digits := by
  rw [layerNextP, if_neg h]
theorem layersP_succ_eq (w : WBytes) (index n : Nat) (root : LayerMessage) :
    layersP w index (n + 1) root =
      if (wctr w (Fin.ofNat 4 n)).toNat ≥ counterLimit then pure none else
      (shortHash (encodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          root (wctr w (Fin.ofNat 4 n))) >>= fun answer =>
        match decode (Fin.ofNat 4 n) answer with
        | some digits => layerNextP w index n (Fin.ofNat 4 n) digits >>= fun next => layersP w index n next
        | _ => pure none) := by
  conv_lhs => unfold layersP
  rfl
theorem layersP_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (root : LayerMessage) (out : Digest)
    (h : evalWithAnswerFn answers (layersP w index (n + 1) root) = some out) :
    ∃ digits, Frame answers w index (Fin.ofNat 4 n) root digits ∧
      evalWithAnswerFn answers
        (layersP w index n (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits))) = some out ∧
      encodingQuery w index (Fin.ofNat 4 n) root ∈ queried answers (layersP w index (n + 1) root) ∧
      (∀ q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits),
        q ∈ queried answers (layersP w index (n + 1) root)) ∧
      (∀ q ∈ queried answers
          (layersP w index n (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits))),
        q ∈ queried answers (layersP w index (n + 1) root)) := by
  rw [layersP_succ_eq] at h ⊢
  by_cases hc : (wctr w (Fin.ofNat 4 n)).toNat ≥ counterLimit
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  rw [evalWithAnswerFn_bind] at h
  rw [queried_bind]
  generalize hans : evalWithAnswerFn answers (shortHash (encodingInput (Fin.ofNat 4 n)
    (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 root (wctr w (Fin.ofNat 4 n)))) = answer at h ⊢
  cases hd : decode (Fin.ofNat 4 n) answer with
  | none => rw [hd] at h; simp at h
  | some digits =>
      rw [hd] at h
      simp only at h ⊢
      rw [evalWithAnswerFn_bind] at h
      refine ⟨digits, ⟨by omega, by rw [hans]; exact hd⟩, h, ?_, ?_, ?_⟩
      · apply List.mem_append_left
        rw [queried_shortHash]; exact List.mem_singleton_self _
      · intro q hq
        apply List.mem_append_right
        rw [queried_bind]; exact List.mem_append_left _ hq
      · intro q hq
        apply List.mem_append_right
        rw [queried_bind]; exact List.mem_append_right _ hq
theorem layerNextP_merkle (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (digits : List Nat)
    (hv : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    NodeHitIn answers (queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ∨
      (MerkleShaped answers w index (Fin.ofNat 4 n) ∧
        evalWithAnswerFn answers (layerLeafP w index (Fin.ofNat 4 n) digits) =
          treeValue (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2) 0
            (route index (Fin.ofNat 4 n)).1 ∧
        ∀ q ∈ queried answers (layerLeafP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) := by
  by_cases h0 : n = 0
  · subst h0
    have hq : queried answers (layerNextP w index 0 (Fin.ofNat 4 0) digits) =
        queried answers (layerP w index (Fin.ofNat 4 0) digits) := by
      rw [layerNextP_zero, map_eq_bind_pure_comp, queried_bind]
      simp
    have hr : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
        honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
      have h1 := congrArg Prod.fst hv
      rw [layerNextP_zero, evalWithAnswerFn_map] at h1
      exact h1
    rw [hq]
    rcases layerP_merkle answers w index (Fin.ofNat 4 0) digits hr with hn | ⟨hm, hv0⟩
    · exact Or.inl hn
    · refine Or.inr ⟨hm, hv0, fun q hq' => ?_⟩
      rw [layerP_eq_hashPath, queried_bind]
      exact List.mem_append_left _ hq'
  · have hq : layerNextP w index n (Fin.ofNat 4 n) digits = layerPairP w index (Fin.ofNat 4 n) digits :=
      layerNextP_ne w index n (Fin.ofNat 4 n) digits h0
    rw [hq] at hv ⊢
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
      intro h; apply h0; have := congrArg Fin.val h; simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using this
    rw [walkTarget_pair answers index n hn h0] at hv
    rcases layerPairP_merkle answers w index (Fin.ofNat 4 n) hlay digits hv with hn' | ⟨hm, hv0⟩
    · exact Or.inl hn'
    · refine Or.inr ⟨hm, hv0, fun q hq' => ?_⟩
      rw [layerPairP_eq_hashPath, queried_bind]
      exact List.mem_append_left _ hq'
theorem layerNextP_extract (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits (Fin.ofNat 4 n) digits)
    (hv : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    HitIn answers (queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) ∨
      LayerShaped answers w index (Fin.ofNat 4 n) digits := by
  rcases layerNextP_merkle answers w index n hn digits hv with hnode | ⟨hm, hv0, hsub⟩
  · exact Or.inl (hnode.hitIn (route_tree_bound index _ hidx) (route_leaf_bound index _))
  rcases leafChains_extract answers w index (Fin.ofNat 4 n) digits hidx hvalid hv0 with hh | hc
  · exact Or.inl (hh.mono hsub)
  · exact Or.inr ⟨hm, hc⟩
theorem next_target (answers : Answers) (w : WBytes) (index n : Nat) (digits : List Nat)
    (hv : if n = 0 then (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits)).1 =
        (walkTarget answers index 0).1
      else evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n := by
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl] at hv
    rw [layerNextP_zero, evalWithAnswerFn_map] at hv ⊢
    simp only [walkTarget] at hv ⊢
    rw [hv]
  · rw [if_neg h0] at hv
    exact hv
theorem layersP_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : LayerMessage,
    evalWithAnswerFn answers (layersP w index n root) = some (walkTarget answers index 0).1 →
    HitIn answers (queried answers (layersP w index n root)) ∨
    (∃ lay : Layer, lay.val < n ∧ Diverge answers w index lay (queried answers (layersP w index n root)) ∧
      ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
    ((∀ l : Layer, l.val < n → Good answers w index l) ∧
      (if n = 0 then root.1 = (walkTarget answers index 0).1 else root = walkTarget answers index n))
  | 0, _, root, h => by
      right; right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_walk answers w index hidx n (by omega) _ hrest with hhit | ⟨lay, hlay, hdiv, hgood⟩ | ⟨hgood, hv⟩
      · exact Or.inl (hhit.mono hqR)
      · exact Or.inr (Or.inl ⟨lay, by omega, hdiv.mono hqR, hgood⟩)
      · have hv' := next_target answers w index n digits hv
        rcases layerNextP_extract answers w index n (by omega) digits hidx
            (Cost.validDigits_decode hframe.2) hv' with hhit | hshape
        · exact Or.inl (hhit.mono hqL)
        · have hmsg : honestMsg answers index (Fin.ofNat 4 n) = walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [walkTarget, dif_pos (show n < 4 by omega), hl]
          by_cases heq : root = honestMsg answers index (Fin.ofNat 4 n)
          · right; right
            refine ⟨fun l hl => ?_, by simpa only [Nat.succ_ne_zero, if_false] using heq.trans hmsg⟩
            by_cases hle : l.val < n
            · exact hgood l hle
            · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
              subst hl
              exact ⟨digits, heq ▸ hframe, hshape⟩
          · right; left
            exact ⟨Fin.ofNat 4 n, by omega, ⟨root, digits, heq, hframe, hshape, henc⟩,
              fun l hl => hgood l (by omega)⟩
end SigGolfCandidate.T3M.Extract
end
section
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def FtsExtractSpec (FtsShaped : Answers → WBytes → Nat → List Selection → Prop) : Prop :=
  ∀ (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection) (ptr : Nat),
    selectionsOk chosen = true → ptr ≤ streamEnd →
    evalWithAnswerFn answers (ftsRoots w index chosen) = some (ftsRootsHonest answers index, ptr) →
    HitIn answers (queried answers (ftsRoots w index chosen)) ∨ FtsShaped answers w index chosen
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem ftsRoots_length (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (ptr : Nat) (h : evalWithAnswerFn answers (ftsRoots w index chosen) = some (roots, ptr)) :
    roots.length = 7 := by
  unfold ftsRoots at h
  revert roots ptr
  refine Correctness.eval_foldlM_range_inv (Inv := fun i (state : Option (List Digest × Nat)) =>
    ∀ roots ptr, state = some (roots, ptr) → roots.length = i) answers 7 _ _ ?_ ?_
  · intro roots ptr h
    cases h
    rfl
  · intro i _ state hstate
    rcases state with _ | ⟨roots, ptr⟩
    · intro roots ptr h
      simp at h
    · intro roots' ptr' h
      simp only [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn answers (ftsCoordP w index i (chosen.getD i ⟨0, []⟩) ptr) = r at h
      rcases r with _ | ⟨root, ptr''⟩
      · simp at h
      · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hstate roots ptr rfl]
theorem ftsP_queried_roots (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection) :
    ∀ q ∈ queried answers (ftsRoots w index chosen), q ∈ queried answers (ftsP w index chosen) := by
  intro q hq
  rw [ftsP_eq, queried_bind]
  exact List.mem_append_left _ hq
theorem ftsP_queried_forest (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (ptr : Nat) (h : evalWithAnswerFn answers (ftsRoots w index chosen) = some (roots, ptr))
    (hcap : ¬ streamEnd < ptr) :
    ∀ q ∈ queried answers (forestPk index roots), q ∈ queried answers (ftsP w index chosen) := by
  intro q hq
  rw [ftsP_eq, queried_bind, h]
  simp only
  rw [if_neg hcap, queried_bind]
  exact List.mem_append_right _ (List.mem_append_left _ hq)
theorem keygen_pk (answers : Answers) : (evalWithAnswerFn answers keygen).1 = honestRoot answers 0 0 := by
  unfold keygen keygenPayload
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [Correctness.eval_buildTree_levels answers 0 0 0 [] (Cost.validDigits_nil 0)]
  rfl
theorem verifyP_walk_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers (ftsP w (N.toNat % 2 ^ 31) (selections N)) =
            some (honestForest answers (N.toNat % 2 ^ 31)) ∧
          ∀ q ∈ queried answers (ftsP w (N.toNat % 2 ^ 31) (selections N)),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  rw [verifyP_eq_tail] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · have h0 : digestP m w = pure none := by unfold digestP; rw [if_pos hdc]
    rw [h0] at hv; simp at hv
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg hdc]
  rw [hD] at hv ⊢
  rw [queried_map]
  simp only [evalWithAnswerFn_map] at hv ⊢
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv ⊢
  try simp only at hv ⊢
  refine ⟨N, by omega, rfl, ?_, ?_⟩
  · apply List.mem_append_left
    unfold digest publicHash
    rw [show (liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) : M HashOutput) =
      liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) >>= pure from (bind_pure _).symm,
      queried_query_bind]
    exact List.mem_cons_self
  unfold verifyTailP at hv ⊢
  simp only at hv ⊢
  by_cases hsel : selectionsOk (selections N) = true
  swap
  · rw [if_pos (by simpa using hsel)] at hv; simp at hv
  rw [if_neg (by simpa using hsel)] at hv ⊢
  by_cases hg : digestGate N = true
  swap
  · rw [if_pos (by simpa using hg)] at hv
    simp at hv
  rw [if_neg (by simpa using hg)] at hv ⊢
  refine ⟨hsel, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  generalize N.toNat % 2 ^ 31 = index at hidx hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers (ftsP w index (selections N)) = rr at hv ⊢
  rcases rr with _ | root
  · simp at hv
  simp only at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hL : evalWithAnswerFn answers (layersP w index 4 (root, 0, 0)) = ll at hv ⊢
  rcases ll with _ | root'
  · simp at hv
  simp only [evalWithAnswerFn_pure, beq_iff_eq] at hv
  subst hv
  have htop : (walkTarget answers index 0).1 = root' := by
    rw [hpk]; simp only [walkTarget, route_top_tree index hidx]
  rcases layersP_walk answers w index hidx 4 le_rfl (root, 0, 0) (by rw [hL, htop]) with
    hhit | ⟨lay, _, hdiv, hgood⟩ | ⟨hgood, hroot⟩
  · exact Or.inl (hhit.mono fun q hq => by simp only [List.mem_append]; tauto)
  · exact Or.inr (Or.inl ⟨lay, hdiv.mono fun q hq => by simp only [List.mem_append]; tauto, hgood⟩)
  have hroot' : root = honestForest answers index := by
    have h4 : ((root, 0, 0) : LayerMessage) = walkTarget answers index 4 := by simpa using hroot
    simp [walkTarget, honestMsg] at h4
    exact h4
  exact Or.inr (Or.inr ⟨fun l => hgood l l.isLt, by rw [hroot'],
    fun q hq => by simp only [List.mem_append]; tauto⟩)
theorem verifyP_extract {FtsShaped : Answers → WBytes → Nat → List Selection → Prop}
    (hF : FtsExtractSpec FtsShaped) (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧
          FtsShaped answers w (N.toNat % 2 ^ 31) (selections N))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hsel, hcase⟩ := verifyP_walk_extract answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hsel, ?_⟩
  rcases hcase with hhit | hdiv | ⟨hgood, hR, hqV⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
  generalize N.toNat % 2 ^ 31 = index at hgood hR hqV hidx ⊢
  have hR' := hR
  rw [ftsP_eq, evalWithAnswerFn_bind] at hR'
  generalize hS : evalWithAnswerFn answers (ftsRoots w index (selections N)) = ss at hR'
  rcases ss with _ | ⟨roots, ptr⟩
  · simp at hR'
  simp only at hR'
  by_cases hcap : streamEnd < ptr
  · rw [if_pos hcap] at hR'; simp at hR'
  rw [if_neg hcap, evalWithAnswerFn_bind] at hR'
  simp only [evalWithAnswerFn_pure, Option.some.injEq] at hR'
  have hqR := ftsP_queried_roots answers w index (selections N)
  have hqF := ftsP_queried_forest answers w index (selections N) roots ptr hS hcap
  rcases forestPk_honest_extract answers index hidx roots
      (ftsRoots_length answers w index (selections N) roots ptr hS) hR' with hroots | hhit
  · subst hroots
    rcases hF answers w index (selections N) ptr hsel (by omega) hS with hhit | hshape
    · exact Or.inl (hhit.mono fun q hq => hqV q (hqR q hq))
    · exact Or.inr (Or.inr ⟨hgood, hshape⟩)
  · exact Or.inl (hhit.mono fun q hq => hqV q (hqF q hq))
def FtsExtractSpecN (FtsShaped : Answers → HashOutput → WBytes → Prop) : Prop :=
  ∀ (answers : Answers) (N : HashOutput) (w : WBytes), Shaped N w →
    evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (honestForest answers (N.toNat % 2 ^ 31)) →
    HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))) ∨
      FtsShaped answers N w
theorem eval_rejectTail (answers : Answers) (w : WBytes) (N : HashOutput) :
    evalWithAnswerFn answers (rejectTail w N) = false := by
  unfold rejectTail
  split
  · rfl
  · split
    · rfl
    · rw [evalWithAnswerFn_map]
theorem shaped_of_verifyP (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    Shaped (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w := by
  classical
  rw [verifyP_normal] at hv
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · rw [if_pos hdc] at hv; simp at hv
  rw [if_neg hdc, evalWithAnswerFn_bind] at hv
  by_contra hS
  rw [if_neg hS, eval_rejectTail] at hv
  exact Bool.false_ne_true hv
theorem verifyP_extract_normal {FtsShaped : Answers → HashOutput → WBytes → Prop}
    (hF : FtsExtractSpecN FtsShaped) (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsShaped answers N w)) := by
  classical
  have hS := shaped_of_verifyP answers m pk w hv
  obtain ⟨N, hdc, hN, hdq, _, hcase⟩ := verifyP_walk_extract answers m pk w hpk hv
  rw [hN] at hS
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hhit | hdiv | ⟨hgood, hR, hqV⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  rw [ftsP_shaped N w hS] at hR hqV
  rcases hF answers N w hS hR with hhit | hshape
  · exact Or.inl (hhit.mono hqV)
  · exact Or.inr (Or.inr ⟨hgood, hshape⟩)
end SigGolfCandidate.T3M.Extract
end
