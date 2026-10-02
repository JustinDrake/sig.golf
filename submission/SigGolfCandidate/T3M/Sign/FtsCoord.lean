import SigGolfCandidate.T3M.Sign.FtsCollect
import SigGolfCandidate.T3M.Sign.FtsTree
import SigGolfCandidate.T3M.Sign.Front
import SigGolfCandidate.T3M.Witness.Honest

/-!
# Sign: the seven FTS coordinates (words 172..356)

Core's coordinate fold of `payloadRest` (`buildFts`, the opened secrets, the multiproof `frontier`, the
outer siblings, the root) on the machine: `ftsBody_tbsim` (one coordinate), `fts_fold` (all seven).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest HashOutput Selection selections admissible buildFts)
open SigGolfCandidate.T3M (lcaLevel heap_eq xor_one_eq SelOk ChosenOk slotBase slotPositions selectedLeaves
  selLeaf lca_le_eight)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  HeapAt LevW)

/-! ## Positions of the walk -/

theorem mem_descL {g : Nat} : ∀ {s : Nat} {p : Nat × Nat}, p ∈ descL g s → p.1 < s ∧ p.2 = g / 2 ^ p.1 ^^^ 1
  | 0, _, h => by simp [descL] at h
  | s + 1, p, h => by
    simp only [descL, topD, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hb
      · simp only [List.mem_singleton] at h; subst h; simp
      · simp at h
    · have := mem_descL h; omega

theorem mem_ascR {g : Nat} : ∀ {e : Nat} {p : Nat × Nat}, p ∈ ascR g e → p.1 < e ∧ p.2 = g / 2 ^ p.1 ^^^ 1
  | 0, _, h => by simp [ascR] at h
  | e + 1, p, h => by
    simp only [ascR, topA, List.mem_append] at h
    rcases h with h | h
    · have := mem_ascR h; omega
    · split_ifs at h with hb
      · simp only [List.mem_singleton] at h; subst h; simp
      · simp at h

theorem mem_mf (L : Nat) : ∀ {S : List Nat} {s e : Nat} {p : Nat × Nat},
    (∀ g ∈ S, ∀ g' ∈ S, g ≠ g' → lcaLevel g g' ≤ L) → s ≤ L → e ≤ L → p ∈ mf s e S →
    p.1 < L ∧ ∃ g ∈ S, p.2 = g / 2 ^ p.1 ^^^ 1
  | [], _, _, _, _, _, _, h => by simp [mf] at h
  | [g], s, e, p, _, hs, he, h => by
    simp only [mf, List.mem_append] at h
    rcases h with h | h
    · have := mem_descL h; exact ⟨by omega, g, by simp, this.2⟩
    · have := mem_ascR h; exact ⟨by omega, g, by simp, this.2⟩
  | g :: g' :: rest, s, e, p, hl, hs, he, h => by
    have hgg : g ≠ g' ∨ g = g' := by omega
    have hlca : lcaLevel g g' - 1 ≤ L := by
      rcases hgg with hne | heq
      · have := hl g (by simp) g' (by simp) hne; omega
      · subst heq; simp [lcaLevel]
    simp only [mf, List.mem_append] at h
    rcases h with (h | h) | h
    · have := mem_descL h; exact ⟨by omega, g, by simp, this.2⟩
    · have := mem_ascR h; exact ⟨by omega, g, by simp, this.2⟩
    · obtain ⟨h1, g'', hg'', h2⟩ := mem_mf L (S := g' :: rest)
        (fun a ha b hb hab => hl a (by simp_all) b (by simp_all) hab) hlca he h
      exact ⟨h1, g'', by simp_all, h2⟩

/-! ## Heap values as Core's levels -/

theorem nodeVal_heap {t : MachineState} {c idx : Nat} {levels : List (List Digest)}
    (h : HeapAt t (ftsLev c idx) 11 levels) {l i : Nat} (hl : l ≤ 11) (hi : i < 2 ^ (11 - l)) :
    nodeVal t (l, i) = (levels.getD l []).getD i 0 := by
  obtain ⟨hlen, hd⟩ := h.2 l hl
  have := (hd i (by simp only [ftsLev] at hlen; rw [hlen]; exact hi))
  unfold nodeVal hp
  simp only [ftsLev] at this
  rw [show FTS + 16 * (2 ^ (11 - l) + i) = FTS + 16 * 2 ^ (11 - l) + 16 * i by ring]
  exact memDig_eq this

/-- The values written for a list of positions are Core's values when every position's node matches. -/
theorem Emitted.digsAt {t0 u : MachineState} {pp : Nat} {L : List (Nat × Nat)} (h : Emitted t0 u pp L)
    (f : Nat × Nat → Digest) (hf : ∀ p ∈ L, nodeVal t0 p = f p) : DigsAt u pp (L.map f) := by
  intro i hi
  rw [List.length_map] at hi
  have := h i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  rw [List.getD_eq_getElem _ _ hi, hf _ (List.getElem_mem _)] at this
  exact this

theorem DigsAt.append {t : MachineState} {A : Nat} {L M : List Digest} (h1 : DigsAt t A L)
    (h2 : DigsAt t (A + 16 * L.length) M) : DigsAt t A (L ++ M) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i < L.length
  · have := h1 i hlt
    rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  · have := h2 (i - L.length) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
    rw [show A + 16 * L.length + 16 * (i - L.length) = A + 16 * i by omega] at this
    exact this

theorem DigsAt.three {t : MachineState} {A : Nat} {a b c : Digest} (ha : DigAt t A a) (hb : DigAt t (A + 16) b)
    (hc : DigAt t (A + 32) c) : DigsAt t A [a, b, c] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-! ## The coordinate fold -/

/-- Core's coordinate body of `payloadRest`. -/
def ftsBody (chosen : List Selection) (index : Nat) (state : List Digest × List Digest × List Digest)
    (coord : Nat) : M (List Digest × List Digest × List Digest) := do
  let sel := chosen.getD coord ⟨0,[]⟩
  let (levels,secrets) ← buildFts index coord
  let selected := sel.leaves.map (fun s => sel.bucket*128+s)
  let opened := selected.map (fun s => secrets.getD s 0)
  let inner := (T3.frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
  let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
  pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
    state.2.2 ++ [(levels.getD 11 []).getD 0 0])

/-- Scratch doublewords of the FTS phase. -/
def FtsScr (A : Nat) : Prop :=
  FlW A ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
    (NOUT ≤ A ∧ A < NOUT + 32) ∨ (FTS + 16 ≤ A ∧ A < FTS + 32768)

/-- The doublewords written by the first coordinates (`nsec` secrets, `nproof` proof slots so far). -/
def CoordW (nsec nproof : Nat) (A : Nat) : Prop :=
  FtsScr A ∨ (SIG + 16 ≤ A ∧ A < SIG + 16 + 16 * nsec) ∨ (SIG + 352 ≤ A ∧ A < SIG + 352 + 16 * nproof) ∨
    (FOREST ≤ A ∧ A < FOREST + 128)

/-- At `fts_coord` (186) after `c` coordinates with Core state `st = (opened, proof, roots)`. -/
structure CoordInv (sk : SecretKey) (cache : Bytes 32768) (N : HashOutput) (s0 : MachineState) (c : Nat)
    (st : List Digest × List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 186
  x2 : t.getReg .x2 = BitVec.ofNat 64 FTS
  x8 : t.getReg .x8 = BitVec.ofNat 64 c
  x9 : t.getReg .x9 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  x16 : t.getReg .x16 = BitVec.ofNat 64 (SIG + 352 + 16 * st.2.1.length)
  x26 : t.getReg .x26 = BitVec.ofNat 64 (SIG + 16 + 16 * st.1.length)
  base : Base sk cache t
  hc : c ≤ 7
  len1 : st.1.length = 3 * c
  len2 : st.2.1.length = slotBase (selections N) c
  len3 : st.2.2.length = c
  opened : DigsAt t (SIG + 16) st.1
  proofs : DigsAt t (SIG + 352) st.2.1
  roots : ∀ j < c, DigAt t (FOREST + rootOff j) (st.2.2.getD j 0)
  sel : SelRows t N
  frame : Frame s0 t (CoordW st.1.length st.2.1.length)

open SigGolfCandidate.T3M (bucket_div_eight bucket_div_outer) in
/-- The leaves of an accepted selection and Core's `frontier` of them. -/
theorem sel_facts {sel : Selection} (hs : SelOk sel) :
    sel.leaves.map (fun s => sel.bucket * 128 + s) = [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] ∧
    selLeaf sel 0 < selLeaf sel 1 ∧ selLeaf sel 1 < selLeaf sel 2 ∧ selLeaf sel 2 < 2048 ∧
    lcaLevel (selLeaf sel 0) (selLeaf sel 1) ≤ 7 ∧ lcaLevel (selLeaf sel 1) (selLeaf sel 2) ≤ 7 ∧
    (∀ g ∈ [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2], g / 2 ^ 7 = sel.bucket) ∧
    T3.frontier [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] 7 sel.bucket =
      mf 7 7 [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb := hs.b
  have e0 : selLeaf sel 0 = sel.bucket * 128 + x0 := by unfold selLeaf; rw [hl]; rfl
  have e1 : selLeaf sel 1 = sel.bucket * 128 + x1 := by unfold selLeaf; rw [hl]; rfl
  have e2 : selLeaf sel 2 = sel.bucket * 128 + x2 := by unfold selLeaf; rw [hl]; rfl
  have hdiv : ∀ g ∈ [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2], g / 2 ^ 7 = sel.bucket := by
    intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [e0]; exact bucket_div_eight (by omega)
    · rw [e1]; exact bucket_div_eight (by omega)
    · rw [e2]; exact bucket_div_eight (by omega)
  refine ⟨by rw [hl, e0, e1, e2]; rfl, by omega, by omega, by omega, ?_, ?_, hdiv, ?_⟩
  · rw [e0, e1]; exact lca_le_eight (by omega) (by omega) (by omega)
  · rw [e1, e2]; exact lca_le_eight (by omega) (by omega) (by omega)
  · refine frontier_eq_mf _ 7 sel.bucket _ ?_ (by simp) (fun g => ⟨fun h => ⟨h, hdiv g h⟩, fun h => h.1⟩)
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    omega

/-- Cycle bound of one coordinate (exact tree, bounded collection). -/
def ftsCoordC : Nat := (3 + 1024 * 126 + 9 + 94233) + 1200

open SigGolfCandidate.T3M (chosenOk_of selectionsOk_of_admissible slotBase_succ slotBase_seven_le slotBase_mono
  bucket_div_outer) in
/-- **One FTS coordinate** (`fts_coord` .. `fr_root0`): Core's coordinate body, bounded by `ftsCoordC`. -/
theorem ftsBody_tbsim {sk : SecretKey} {cache : Bytes 32768} {N : HashOutput} {s0 : MachineState}
    (hadm : admissible (selections N) = true) {c : Nat} (hc : c < 7)
    {st : List Digest × List Digest × List Digest} {t : MachineState} (ht : CoordInv sk cache N s0 c st t) :
    TBSim image sk t ftsCoordC (ftsBody (selections N) (N.toNat % 2 ^ 31) st c)
      (CoordInv sk cache N s0 (c + 1)) := by
  set idx := N.toNat % 2 ^ 31 with hidx_def
  have hidx : idx < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hchosen : ChosenOk (selections N) := chosenOk_of N (selectionsOk_of_admissible N hadm)
  set sel := (selections N).getD c ⟨0, []⟩ with hsel_def
  have hs : SelOk sel := hchosen c hc
  obtain ⟨hselected, h01, h12, hg2, hl01, hl12, hdiv, hfront⟩ := sel_facts hs
  have hfl : FlPre sk cache c idx t := ⟨ht.base, ht.x2, ht.x8, ht.x9, hc, hidx⟩
  have hb := TSim.toTBSim (buildFts_tsim hfl ht.pc) (by norm_num)
  unfold ftsBody
  refine TBSim.of_eq (TBSim.bind hb (fun r u hu => ?_)) rfl rfl
  obtain ⟨levels, secrets⟩ := r
  obtain ⟨upc, uheap, ulen, usec, ur, uf⟩ := hu
  simp only [← hsel_def]
  have hsl : sel.leaves.length = 3 := hs.len
  have hsl' : ((selections N).getD c ⟨0, []⟩).leaves.length = 3 := hs.len
  -- the SEL row of coordinate `c` survives the tree
  have hrow : ∀ j < 3, u.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
      BitVec.ofNat 64 (selLeaf sel j) := by
    intro j hj
    rw [uf.get (by sgo) (by unfold FtW FlW LevW ftsLev; simp only; sgo), ht.sel c hc j hj]
    rfl
  set pp := SIG + 352 + 16 * st.2.1.length with hpp
  set sd := SIG + 16 + 16 * st.1.length with hsd
  have hsb7 : slotBase (selections N) 7 ≤ 119 := slotBase_seven_le N hchosen hadm
  have hsbc : slotBase (selections N) (c + 1) ≤ 119 :=
    le_trans (slotBase_mono _ (by omega)) hsb7
  have hsb0 : slotBase (selections N) c ≤ 119 := le_trans (slotBase_mono _ (by omega)) hsb7
  have hl2 := ht.len2
  have hl1 := ht.len1
  obtain ⟨v, k, stv, hk, vpc, vx8, vx16, vx26, vsec, vem, vroot, vlen, vr, vf⟩ :=
    fts_collect u c (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2) pp sd hc hg2 h01 h12 hl01 hl12 upc
      (by rw [ur.get (by decide)]; exact ht.x8) (by rw [ur.get (by decide)]; exact ht.x2)
      (by rw [ur.get (by decide)]; exact ht.x16) (by rw [ur.get (by decide)]; exact ht.x26)
      (by simpa using hrow 0 (by omega)) (by simpa using hrow 1 (by omega)) (by simpa using hrow 2 (by omega))
      (by sgo) (by sgo) (by sgo) (by sgo)
  set g0 := selLeaf sel 0 with hg0
  set g1 := selLeaf sel 1 with hg1
  set g2 := selLeaf sel 2 with hg2'
  set coreVal : Nat × Nat → Digest := fun p => (levels.getD p.1 []).getD p.2 0 with hcore
  -- positions below the root
  have hpos : ∀ g, g < 2048 → ∀ l, l ≤ 10 → g / 2 ^ l ^^^ 1 < 2 ^ (11 - l) := by
    intro g hg l hl
    have h1 : g / 2 ^ l < 2 ^ (11 - l) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l), ← pow_add, Nat.sub_add_cancel (by omega)]; omega
    exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))
  have hval : ∀ p ∈ mf 7 7 [g0, g1, g2] ++ outerL g2 7 4, nodeVal u p = coreVal p := by
    intro p hp
    rcases List.mem_append.mp hp with hm | hm
    · have hlca : ∀ a ∈ [g0, g1, g2], ∀ b ∈ [g0, g1, g2], a ≠ b → lcaLevel a b ≤ 7 :=
        fun a ha b hb hab => (SigGolfCandidate.T3M.div_eq_iff_lca hab 7).mp (by rw [hdiv a ha, hdiv b hb])
      obtain ⟨hl, g, hg, he⟩ := mem_mf 7 hlca le_rfl le_rfl hm
      have hg' : g < 2048 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg; omega
      obtain ⟨l, i⟩ := p
      simp only at hl he
      subst he
      exact nodeVal_heap uheap (by omega) (hpos g hg' l (by omega))
    · simp only [outerL, List.mem_map, List.mem_range] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      exact nodeVal_heap uheap (by omega) (hpos g2 hg2 (7 + j) (by omega))
  have hprf : DigsAt v pp ((mf 7 7 [g0, g1, g2] ++ outerL g2 7 4).map coreVal) := vem.digsAt coreVal hval
  -- Core's lists
  have hinner : (T3.frontier (sel.leaves.map fun s => sel.bucket * 128 + s) 7 sel.bucket).map
      (fun p => (levels.getD p.1 []).getD p.2 0) = (mf 7 7 [g0, g1, g2]).map coreVal := by
    rw [hselected, hfront]
  have houter : ((List.range 4).map fun j => (levels.getD (7 + j) []).getD (sel.bucket / 2 ^ j ^^^ 1) 0) =
      (outerL g2 7 4).map coreVal := by
    unfold outerL
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, hcore]
    rw [hg2', SigGolfCandidate.T3M.selLeaf, bucket_div_outer (by have := hs.l2; omega)]
  have hflen : (T3.frontier (sel.leaves.map fun s => sel.bucket * 128 + s) 7 sel.bucket).length =
      (mf 7 7 [g0, g1, g2]).length := by rw [hselected, hfront]
  have hsecv : ∀ i < 3, memDig u (SEC + 16 * [g0, g1, g2].getD i 0) =
      secrets.getD ([g0, g1, g2].getD i 0) 0 := by
    intro i hi
    have hgi : [g0, g1, g2].getD i 0 < 2048 := by interval_cases i <;> simp <;> omega
    exact memDig_eq (usec _ (by rw [ulen]; exact hgi))
  have hroot : memDig u (FTS + 16) = (levels.getD 11 []).getD 0 0 := by
    have := nodeVal_heap uheap (l := 11) (i := 0) le_rfl (by norm_num)
    simpa [nodeVal, hp] using this
  -- frames
  have hFu : Frame t u FtsScr := uf.mono (fun A _ h => by
    unfold FtW at h; unfold FtsScr
    rcases h with h | h
    · exact Or.inl h
    · unfold LevW ftsLev at h; simp only at h
      rcases h with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by sgo⟩))))))))
  have hnS : ∀ A, A < 2 ^ 64 → SIG ≤ A → A < SIG + 5744 → ¬ FtsScr A := by
    intro A _ h1 h2 h; unfold FtsScr FlW at h; sgo
  have hnF : ∀ A, A < 2 ^ 64 → FOREST ≤ A → A < FOREST + 128 → ¬ FtsScr A := by
    intro A _ h1 h2 h; unfold FtsScr FlW at h; sgo
  have hnSel : ∀ A, A < 2 ^ 64 → SEL ≤ A → A < SEL + 168 → ¬ FtsScr A := by
    intro A _ h1 h2 h; unfold FtsScr FlW at h; sgo
  have hml := vlen
  set W2 : Nat → Prop := fun A => (sd ≤ A ∧ A < sd + 48) ∨
    (pp ≤ A ∧ A < pp + 16 * ((mf 7 7 [g0, g1, g2]).length + 4)) ∨ A = FOREST + rootOff c ∨
    A = FOREST + rootOff c + 8 with hW2
  have hro : rootOff c ≤ 112 := by unfold rootOff; split_ifs <;> omega
  have hro' : ∀ j < c, rootOff j + 16 ≤ rootOff c := by
    intro j hj; unfold rootOff; split_ifs <;> omega
  refine TBSim.mono (TBSim.pure_steps stv ⟨vpc, ?_, vx8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) hk
    (fun _ _ h => h)
  · rw [vr.get (by decide), ur.get (by decide)]; exact ht.x2
  · rw [vr.get (by decide), ur.get (by decide)]; exact ht.x9
  · rw [vx16]; congr 1
    simp only [List.length_append, List.length_map, List.length_range, hflen, hpp]; ring
  · rw [vx26]; congr 1
    simp only [List.length_append, List.length_map, hselected, List.length_cons, List.length_nil, hsd]; ring
  · refine (ht.base.frame hFu ur (by decide) (fun A hA hb h => ?_)).frame vf vr (by decide) (fun A hA hb h => ?_)
    · unfold BaseA NeverW at hb; unfold FtsScr FlW at h; sgo
    · unfold BaseA NeverW at hb; rcases h with h | h | h | h <;> sgo
  · omega
  · simp only [List.length_append, List.length_map, hselected, List.length_cons, List.length_nil, ht.len1]; ring
  · rw [slotBase_succ]
    simp only [List.length_append, List.length_map, ht.len2, SigGolfCandidate.T3M.slotPositions,
      SigGolfCandidate.T3M.selectedLeaves, List.length_range]
    rfl
  · simp [ht.len3]
  · -- the opened secrets
    show DigsAt v (SIG + 16) (st.1 ++ (sel.leaves.map fun s => sel.bucket * 128 + s).map fun s => secrets.getD s 0)
    refine DigsAt.append ((ht.opened.frame hFu (by sgo) (fun A h1 h2 => hnS A (by sgo) (by sgo) (by sgo))).frame vf
      (by sgo) (fun A h1 h2 h => by rcases h with h | h | h | h <;> sgo)) ?_
    rw [hselected]
    have e0 := vsec 0 (by norm_num)
    have e1 := vsec 1 (by norm_num)
    have e2 := vsec 2 (by norm_num)
    rw [hsecv 0 (by norm_num)] at e0
    rw [hsecv 1 (by norm_num)] at e1
    rw [hsecv 2 (by norm_num)] at e2
    simp only [List.map_cons, List.map_nil]
    refine DigsAt.three ?_ ?_ ?_
    · simpa using e0
    · simpa [show sd + 16 * 1 = SIG + 16 + 16 * st.1.length + 16 by omega] using e1
    · simpa [show sd + 16 * 2 = SIG + 16 + 16 * st.1.length + 32 by omega] using e2
  · -- the proof slots
    show DigsAt v (SIG + 352) (st.2.1 ++
      (T3.frontier (sel.leaves.map fun s => sel.bucket * 128 + s) 7 sel.bucket).map
        (fun p => (levels.getD p.1 []).getD p.2 0) ++
      (List.range 4).map fun j => (levels.getD (7 + j) []).getD (sel.bucket / 2 ^ j ^^^ 1) 0)
    rw [hinner, houter, List.append_assoc, ← List.map_append]
    refine DigsAt.append ((ht.proofs.frame hFu (by sgo) (fun A h1 h2 => hnS A (by sgo) (by sgo) (by sgo))).frame vf
      (by sgo) (fun A h1 h2 h => by rcases h with h | h | h | h <;> sgo)) hprf
  · -- the roots
    intro j hj
    by_cases hjc : j < c
    · have e : (st.2.2 ++ [(levels.getD 11 []).getD 0 0]).getD j 0 = st.2.2.getD j 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [ht.len3]; exact hjc),
          ← List.getD_eq_getElem?_getD]
      rw [e]
      have hrj := hro' j hjc
      exact ((ht.roots j hjc).frame hFu (by sgo) (hnF _ (by sgo) (by sgo) (by unfold rootOff at hrj ⊢; split_ifs at hrj ⊢ <;> sgo))
        (hnF _ (by sgo) (by sgo) (by unfold rootOff at hrj ⊢; split_ifs at hrj ⊢ <;> sgo))).frame vf (by sgo)
        (by intro h; rcases h with h | h | h | h <;> sgo) (by intro h; rcases h with h | h | h | h <;> sgo)
    · have hjc' : j = c := by omega
      subst hjc'
      have e : (st.2.2 ++ [(levels.getD 11 []).getD 0 0]).getD j 0 = (levels.getD 11 []).getD 0 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [ht.len3]), ht.len3, Nat.sub_self]
        rfl
      rw [e, ← hroot]
      exact vroot
  · -- the selection rows
    intro c' hc' j hj
    rw [vf.get (by sgo) (by intro h; rcases h with h | h | h | h <;> sgo),
      uf.get (by sgo) (by unfold FtW FlW LevW ftsLev; simp only; sgo)]
    exact ht.sel c' hc' j hj
  · -- the frame
    have hflen' : (T3.frontier [g0, g1, g2] 7 sel.bucket).length = (mf 7 7 [g0, g1, g2]).length := by rw [hfront]
    refine (ht.frame.trans (hFu.trans vf)).mono (fun A _ h => ?_)
    unfold CoordW at *
    simp only [List.length_append, List.length_map, hselected, List.length_cons, List.length_nil,
      houter, outerL_length]
    rcases h with h | h | h
    · rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
    · rcases h with h | h | h | h
      · exact Or.inr (Or.inl ⟨by sgo, by sgo⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by sgo, by sgo⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by sgo, by sgo⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by sgo, by sgo⟩))

/-- **The seven coordinates.** -/
theorem fts_fold {sk : SecretKey} {cache : Bytes 32768} {N : HashOutput} {s0 : MachineState}
    (hadm : admissible (selections N) = true) (h0 : CoordInv sk cache N s0 0 ([], [], []) s0) :
    TBSim image sk s0 (7 * ftsCoordC) ((List.range 7).foldlM (ftsBody (selections N) (N.toNat % 2 ^ 31)) ([], [], []))
      (CoordInv sk cache N s0 7) := by
  rw [List.range_eq_range']
  exact TBSim.foldlM_range' 0 7 _ _ (CoordInv sk cache N s0) ftsCoordC
    (fun j hj acc t ht => by simpa using ftsBody_tbsim hadm hj ht) h0

/-- The low doubleword of `N` modulo `2^31` is `N`'s. -/
theorem lo64_mod31 (N : HashOutput) : (N.extractLsb' 0 64).toNat % 2 ^ 31 = N.toNat % 2 ^ 31 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-- From `ds_done` (172): the index, the pointers, `coord = 0` (`CoordInv` 0 at word 186). -/
theorem fts_entry {sk : SecretKey} {cache : Bytes 32768} {m : Message} {rho : Digest} {N : HashOutput}
    {t : MachineState} (h : AfterDs sk cache m rho N t) :
    ∃ s0, Steps image t 14 14 s0 ∧ CoordInv sk cache N s0 0 ([], [], []) s0 ∧
      s0.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧
      RegsExcept t s0 [.x2, .x8, .x9, .x16, .x26, .x28] ∧ Frame t s0 (fun A => A = IDXV) := by
  obtain ⟨s0, st, pc0, x9, idxv, x2, x16, x26, x8, r0, f0⟩ := blk172_spec t h.pc
  have hn : (t.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31 = N.toNat % 2 ^ 31 := by
    have := h.nbuf 0 (by norm_num)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [this, lo64_mod31]
  rw [hn] at x9 idxv
  refine ⟨s0, st, ⟨pc0, x2, x8, x9, by simpa using x16, by simpa using x26,
    h.base.frame f0 r0 (by decide) (fun A _ hb h => by unfold BaseA NeverW at hb; rw [h] at hb; sgo),
    by norm_num, rfl, rfl, rfl, DigsAt.nil _ _, DigsAt.nil _ _, fun j hj => absurd hj (by omega),
    fun c hc j hj => by rw [f0.get (by sgo) (by sgo)]; exact h.sel c hc j hj, Frame.refl _ _⟩,
    idxv, r0, f0⟩

end SigGolfCandidate.T3M.Sign
