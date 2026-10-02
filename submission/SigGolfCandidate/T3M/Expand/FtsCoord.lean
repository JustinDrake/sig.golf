import SigGolfCandidate.T3M.Expand.FtsBlocks
import SigGolfCandidate.T3M.Expand.FtsEm
import SigGolfCandidate.T3M.Expand.Fts

/-!
# `expand`: one FTS coordinate (stream E)

`fts_coord_step`: from the coordinate invariant `CoordInv` at `fts_coord` (word 65) for coordinate `c < 7` with
Core's state `(roots, used)`, the machine refines `ftsStep sig index (selections N) (some (roots, used)) c` within
`coordCost` cycles: the secret copies, `recover_child` at level 7 on the bucket (`rc_tbsim`), the four outer folds,
the segment close and the root store, ending in `CoordInv` for `c + 1` (or `FailedAt 354`).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Signature Selection hasLeaf recoverChild nodeHash shortHash pad64 header
  zero16)
open SigGolfCandidate.T3M.Search (NODE NOUT SEL FailedAt SelRows selEntry kernAt_expand cs0_spec)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

/-! ## Cost of the bucket DFS -/

/-- The number of the three leaves below `(level, node)`. -/
def cnt3 (g0 g1 g2 level node : Nat) : Nat :=
  (if g0 / 2 ^ level = node then 1 else 0) + (if g1 / 2 ^ level = node then 1 else 0) +
    (if g2 / 2 ^ level = node then 1 else 0)

theorem cnt3_succ (g0 g1 g2 l node : Nat) :
    cnt3 g0 g1 g2 (l + 1) node = cnt3 g0 g1 g2 l (2 * node) + cnt3 g0 g1 g2 l (2 * node + 1) := by
  unfold cnt3
  simp only [div_pow_succ']
  split_ifs <;> omega

theorem cnt3_pos (g0 g1 g2 level node : Nat) (h : hasLeaf [g0, g1, g2] level node = true) :
    1 ≤ cnt3 g0 g1 g2 level node := by
  rcases (hasLeaf_three _ _ _ _ _).mp h with h | h | h <;> unfold cnt3 <;> split_ifs <;> omega

theorem cnt3_le (g0 g1 g2 level node : Nat) : cnt3 g0 g1 g2 level node ≤ 3 := by
  unfold cnt3; split_ifs <;> omega

/-- `recover_child` costs at most `53 + 169 level + 89` per leaf below. -/
theorem rcCost_le (g0 g1 g2 : Nat) : ∀ level node,
    rcCost [g0, g1, g2] level node ≤ 53 + cnt3 g0 g1 g2 level node * (169 * level + 89) := by
  intro level
  induction level with
  | zero =>
    intro node
    rw [rcCost]
    by_cases h : hasLeaf [g0, g1, g2] 0 node = false
    · rw [if_pos h]; omega
    · rw [if_neg h]
      have := cnt3_pos g0 g1 g2 0 node (by simpa using h)
      nlinarith
  | succ l ih =>
    intro node
    by_cases h : hasLeaf [g0, g1, g2] (l + 1) node = false
    · rw [rcCost, if_pos h]; omega
    · have h' : hasLeaf [g0, g1, g2] (l + 1) node = true := by simpa using h
      rw [rcCost_inner _ _ _ h', cnt3_succ]
      have h1 := ih (2 * node)
      have h2 := ih (2 * node + 1)
      have hp := cnt3_pos g0 g1 g2 (l + 1) node h'
      rw [cnt3_succ] at hp
      nlinarith

theorem rcCost_eight (g0 g1 g2 b : Nat) : rcCost [g0, g1, g2] 7 b ≤ 4376 := by
  have h1 := rcCost_le g0 g1 g2 7 b
  have h2 := cnt3_le g0 g1 g2 7 b
  nlinarith

/-! ## The secret loop -/

/-- `fts_sec` (words 67 .. 88): the coordinate's three secrets to their witness leaf blocks. -/
theorem fts_sec_loop (s : MachineState) (hpc : s.pc = pcOf 67) (c : Nat) (hc : c < 7)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 66 66 t ∧ t.pc = pcOf 89 ∧
      (∀ j < 3, t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j))) =
          s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j))) ∧
        t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j) + 8)) =
          s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j) + 8))) ∧
      RegsExcept s t [.x6, .x7, .x13, .x14, .x19, .x28, .x29] ∧
      Frame s t (fun A => ∃ j < 3, A = 0x860 + 48 * (3 * c + j) ∨ A = 0x860 + 48 * (3 * c + j) + 8) := by
  obtain ⟨t1, s1, p1, x19_1, r1, f1⟩ := f67_spec s hpc
  have key : ∀ n ≤ 3, ∃ t, Steps image t1 (21 * n) (21 * n) t ∧ t.pc = pcOf 68 ∧
      t.getReg .x19 = BitVec.ofNat 64 n ∧
      (∀ j < n, t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j))) =
          s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j))) ∧
        t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j) + 8)) =
          s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j) + 8))) ∧
      RegsExcept t1 t [.x6, .x7, .x13, .x14, .x19, .x28, .x29] ∧
      Frame t1 t (fun A => ∃ j < n, A = 0x860 + 48 * (3 * c + j) ∨ A = 0x860 + 48 * (3 * c + j) + 8) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨t1, Steps.refl _, p1, x19_1, fun j hj => absurd hj (by omega), RegsExcept.refl _ _,
        fun A _ _ => rfl⟩
    | succ n ih =>
      intro hn
      obtain ⟨t, st, pt, x19t, ht, rt, ft⟩ := ih (by omega)
      obtain ⟨t2, s2, p2, r2, f2⟩ := f68_spec t pt n (by omega) x19t
      rw [if_neg (by omega)] at p2
      have x8t : t.getReg .x8 = BitVec.ofNat 64 c := by
        rw [rt.get (by decide), r1.get (by decide)]; exact h8
      obtain ⟨t3, s3, p3, m0, m8, x19_3, r3, f3⟩ := f70_spec t2 p2 c n hc (by omega)
        (by rw [r2.get (by decide)]; exact x8t) (by rw [r2.get (by decide)]; exact x19t)
      have g1 : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
        fun A hA => f1.get hA (fun h => h)
      refine ⟨t3, (st.trans (s2.trans s3)).of_eq (by ring) (by ring), p3, x19_3, fun j hj => ?_,
        (rt.trans (r2.trans r3)).mono (by decide), fun A hA hn' => ?_⟩
      · rcases (show j < n ∨ j = n by omega) with hj' | rfl
        · obtain ⟨a, b⟩ := ht j hj'
          refine ⟨?_, ?_⟩
          · rw [f3.get (by omega) (by omega), f2.get (by omega) (fun h => h)]; exact a
          · rw [f3.get (by omega) (by omega), f2.get (by omega) (fun h => h)]; exact b
        · refine ⟨?_, ?_⟩
          · rw [m0, f2.get (by omega) (fun h => h), ft.get (by omega) (by
              rintro ⟨j', hj', h | h⟩ <;> omega), g1 _ (by omega)]
          · rw [m8, f2.get (by omega) (fun h => h), ft.get (by omega) (by
              rintro ⟨j', hj', h | h⟩ <;> omega), g1 _ (by omega)]
      · rw [f3.get hA (fun h => hn' ⟨n, by omega, h⟩), f2.get hA (fun h => h),
          ft.get hA (fun ⟨j', hj', h⟩ => hn' ⟨j', by omega, h⟩)]
  obtain ⟨t, st, pt, x19t, ht, rt, ft⟩ := key 3 le_rfl
  obtain ⟨t2, s2, p2, r2, f2⟩ := f68_spec t pt 3 le_rfl x19t
  rw [if_pos le_rfl] at p2
  refine ⟨t2, (s1.trans (st.trans s2)).of_eq (by ring) (by ring), p2, fun j hj => ?_,
    (r1.trans (rt.trans r2)).mono (by decide), fun A hA hn => ?_⟩
  · obtain ⟨a, b⟩ := ht j hj
    exact ⟨by rw [f2.get (by omega) (fun h => h)]; exact a, by rw [f2.get (by omega) (fun h => h)]; exact b⟩
  · rw [f2.get hA (fun h => h), ft.get hA hn, f1.get hA (fun h => h)]

/-! ## Static facts of the FTS phase -/

/-- The facts of `FtsPre` no FTS block changes. -/
structure Stat (sig : Signature) (N : HashOutput) (u : MachineState) : Prop where
  x5 : u.getReg .x5 = 0
  x9 : u.getReg .x9 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  rows : SelRows u N
  secrets : ∀ k (h : k < 21), DigAt u (0x7010 + 16 * k) (sig.secrets ⟨k, h⟩)
  proof : ∀ k (h : k < 115), DigAt u (0x7160 + 16 * k) (sig.proof ⟨k, h⟩)
  f0 : u.getMem (BitVec.ofNat 64 FLEAF) = 0
  f8 : u.getMem (BitVec.ofNat 64 (FLEAF + 8)) = 0
  f48 : u.getMem (BitVec.ofNat 64 (FLEAF + 48)) = 0
  f56 : u.getMem (BitVec.ofNat 64 (FLEAF + 56)) = 0
  n32 : u.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : u.getMem (BitVec.ofNat 64 (NODE + 40)) = 0

/-- The addresses of the static facts. -/
def StatA (A : Nat) : Prop :=
  (SEL ≤ A ∧ A < SEL + 168) ∨ (0x7000 ≤ A ∧ A < 0x7000 + 5680) ∨ A = FLEAF ∨ A = FLEAF + 8 ∨
    A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40

theorem stat_of_pre {sig : Signature} {N : HashOutput} {s : MachineState} (h : FtsPre sig N s) : Stat sig N s :=
  ⟨h.x5, h.x9, h.rows, h.secrets, h.proof, h.f0, h.f8, h.f48, h.f56, h.n32, h.n40⟩

theorem Stat.frame {sig : Signature} {N : HashOutput} {u v : MachineState} (h : Stat sig N u) {L : List Reg}
    (hr : RegsExcept u v L) (h5 : Reg.x5 ∉ L) (h9 : Reg.x9 ∉ L) {W : Nat → Prop} (hf : Frame u v W)
    (hW : ∀ A, StatA A → ¬ W A) : Stat sig N v := by
  refine ⟨by rw [hr.get h5]; exact h.x5, by rw [hr.get h9]; exact h.x9, fun c hc j hj => ?_, fun k hk => ?_,
    fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.get (by simp only [SEL]; omega) (hW _ (Or.inl (by simp only [SEL]; omega)))]; exact h.rows c hc j hj
  · exact (h.secrets k hk).frame hf (by omega) (hW _ (Or.inr (Or.inl (by omega))))
      (hW _ (Or.inr (Or.inl (by omega))))
  · exact (h.proof k hk).frame hf (by omega) (hW _ (Or.inr (Or.inl (by omega))))
      (hW _ (Or.inr (Or.inl (by omega))))
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.f0
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.f8
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.f48
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.f56
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.n32
  · rw [hf.get (by decide) (hW _ (by simp [StatA]))]; exact h.n40

/-- Core's secret values of coordinate `c` (the `values` of `ftsStep`). -/
def coordValues (sig : Signature) (c : Nat) : List Digest :=
  (List.range 3).map fun j => sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩

theorem rcCtx_of_stat {sig : Signature} {N : HashOutput} {u : MachineState} (h : Stat sig N u) {c : Nat}
    (hc : c < 7) (h8 : u.getReg .x8 = BitVec.ofNat 64 c) :
    RcCtx c (N.toNat % 2 ^ 31) (selEntry N c 0) (selEntry N c 1) (selEntry N c 2) (coordValues sig c) sig.proof u := by
  refine ⟨h.x5, h8, h.x9, h.rows c hc 0 (by decide), h.rows c hc 1 (by decide), h.rows c hc 2 (by decide),
    fun j hj => ?_, fun k hk => ?_, h.f0, h.f8, h.f48, h.f56, h.n32, h.n40⟩
  · have e : (coordValues sig c).getD j 0 = sig.secrets ⟨3 * c + j, by omega⟩ := by
      unfold coordValues
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      simp only [Option.map_some, Option.getD_some]
      congr 2; omega
    rw [e]; exact h.secrets _ _
  · rw [pfN_lt _ _ hk]; exact h.proof k hk

/-! ## The outer folds -/

/-- One outer fold of Core's `ftsStep` (level `7 + j`, sibling slot `used`). -/
def outerStep (sig : Signature) (index c b : Nat) (state : Option (Digest × Nat)) (j : Nat) :
    T3.M (Option (Digest × Nat)) := do
  let some (value, used) := state | pure none
  if h : used < 115 then
    let other := sig.proof ⟨used, h⟩
    let pair := if b / 2 ^ j % 2 = 0 then (value, other) else (other, value)
    let parent ← nodeHash 10 c index (2 ^ (4 - j - 1) + b / 2 ^ (j + 1)) pair.1 pair.2
    pure (some (parent, used + 1))
  else pure none

/-- The stream fold of outer fold `j` (sibling slot `next + j`). -/
def outerFold (b : Nat) (proof : Fin 115 → Digest) (next j : Nat) : Fold :=
  (decide (b / 2 ^ j % 2 = 1), pfN proof (next + j))

/-- The written doublewords of the outer loop. -/
def OW (A : Nat) : Prop :=
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
    (NOUT ≤ A ∧ A < NOUT + 32) ∨ (0xC40 ≤ A ∧ A < 0x3418)

/-- The outer loop at `fts_outer` (word 100) before fold `j`: the value `value` at `NOUT`, the slot `u' = next + j`,
the stream with the bucket DFS's emission `e1` and `j` outer folds. -/
structure OInv (proof : Fin 115 → Digest) (b : Nat) (e1 : Em) (next : Nat) (t4 : MachineState) (j : Nat)
    (value : Digest) (u' : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf 100
  x19 : u.getReg .x19 = BitVec.ofNat 64 j
  x18 : u.getReg .x18 = BitVec.ofNat 64 u'
  hu : u' = next + j
  nout : DigAt u NOUT value
  x23 : u.getReg .x23 = BitVec.ofNat 64 (e1.cur.length + j)
  stream : StreamAt u ⟨e1.segs, e1.cur ++ (List.range j).map (outerFold b proof next), e1.par⟩
  regs : RegsExcept t4 u [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x18, .x19, .x23, .x28, .x29, .x30]
  frame : Frame t4 u OW

theorem not_OW_stat {A : Nat} (h : StatA A) : ¬ OW A := by
  unfold StatA at h; unfold OW; simp only [SEL, FLEAF, NODE, NOUT] at h ⊢; omega

/-- **One outer fold** (words 100 .. 192). -/
theorem outer_step {sk : BitVec 256} {sig : Signature} {N : HashOutput} {c b : Nat} (hc : c < 7) (hb : b < 16)
    (hb0 : selEntry N c 0 / 2 ^ 7 = b) (hg0 : selEntry N c 0 < 2 ^ 64) {e1 : Em} {next : Nat}
    {t4 : MachineState} (hst : Stat sig N t4) (h8 : t4.getReg .x8 = BitVec.ofNat 64 c)
    (h22 : t4.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e1))
    (hroom : wl e1 + 1 + 10 * (e1.cur.length + 4) ≤ 1275) (hnext : next ≤ 115)
    {j : Nat} (hj : j < 4) {value : Digest} {u' : Nat} {u : MachineState}
    (hinv : OInv sig.proof b e1 next t4 j value u' u) :
    TBSim image sk u 77 (outerStep sig (N.toNat % 2 ^ 31) c b (some (value, u')) j)
      (fun st w => match st with
        | none => FailedAt 354 w
        | some (v', u'') => OInv sig.proof b e1 next t4 (j + 1) v' u'' w) := by
  obtain ⟨p, x19, x18, hu, nout, x23, str, R4, F4⟩ := hinv
  have hstu : Stat sig N u := hst.frame R4 (by decide) (by decide) F4 (fun A h => not_OW_stat h)
  have x8u : u.getReg .x8 = BitVec.ofNat 64 c := by rw [R4.get (by decide)]; exact h8
  have x22u : u.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e1) := by rw [R4.get (by decide)]; exact h22
  have hi : N.toNat % 2 ^ 31 < 2 ^ 32 := by have := Nat.mod_lt N.toNat (show 0 < 2 ^ 31 by norm_num); omega
  obtain ⟨u1, s1, p1, r1, f1⟩ := f100_spec u p j (by omega) x19
  rw [if_neg (by omega)] at p1
  obtain ⟨u2, s2, p2, r2, f2⟩ := f102_spec u1 p1 u' (by omega) (by rw [r1.get (by decide)]; exact x18)
  unfold outerStep
  simp only []
  by_cases hu124 : 115 ≤ u'
  · rw [if_pos hu124] at p2
    obtain ⟨u3, s3, p3, x5_3, x10_3, _⟩ := cs0_spec kernAt_expand u2 p2
    rw [dif_neg (by omega)]
    exact (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure (Q := fun st w => match st with
        | none => FailedAt 354 w
        | some (v', u'') => OInv sig.proof b e1 next t4 (j + 1) v' u'' w) (a := none)
      ⟨p3, x5_3, x10_3⟩)).mono (by omega) (fun _ _ h => h)
  rw [if_neg hu124] at p2
  rw [dif_pos (by omega)]
  have hu' : u' < 115 := by omega
  have hslot : DigAt u2 (0x7160 + 16 * u') (sig.proof ⟨u', hu'⟩) :=
    (hstu.proof u' hu').frame (f1.trans f2) (by omega) (fun h => by rcases h with h | h <;> exact h)
      (fun h => by rcases h with h | h <;> exact h)
  have hoth : pfN sig.proof (next + j) = sig.proof ⟨u', hu'⟩ := by rw [← hu]; exact pfN_lt _ _ hu'
  generalize sig.proof ⟨u', hu'⟩ = other at hslot hoth ⊢
  have hpair : (if b / 2 ^ j % 2 = 0 then (value, other) else (other, value)) =
      (if b / 2 ^ j % 2 = 0 then value else other, if b / 2 ^ j % 2 = 0 then other else value) := by
    split_ifs <;> rfl
  rw [hpair]
  dsimp only
  set pl := if b / 2 ^ j % 2 = 0 then value else other with hpl
  set pr := if b / 2 ^ j % 2 = 0 then other else value with hpr
  have R02 : RegsExcept u u2 ([.x6] ++ [.x6]) := r1.trans r2
  have F02 : Frame u u2 (fun A => False ∨ False) := f1.trans f2
  have hrow : u2.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 0)) = BitVec.ofNat 64 (selEntry N c 0) := by
    rw [F02.get (by simp only [SEL]; omega) (fun h => by rcases h with h | h <;> exact h)]
    exact hstu.rows c hc 0 (by decide)
  obtain ⟨u3, s3, p3, x13_3, x18_3, x14_3, r3, f3⟩ := f104_spec u2 p2 c (selEntry N c 0) u' j hc hg0 hu' hj
    (by rw [R02.get (by decide)]; exact x8u) (by rw [R02.get (by decide)]; exact x18)
    (by rw [R02.get (by decide)]; exact x19) hrow
  rw [hb0] at p3 x14_3
  have R03 : RegsExcept u u3 ([.x6] ++ [.x6] ++ [.x13, .x14, .x18, .x28]) := R02.trans r3
  have hslot3 : DigAt u3 (0x7160 + 16 * u') other := hslot.frame f3 (by omega) (fun h => h) (fun h => h)
  have x22_3 : u3.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e1) := by rw [R03.get (by decide)]; exact x22u
  have x23_3 : u3.getReg .x23 = BitVec.ofNat 64 (e1.cur.length + j) := by rw [R03.get (by decide)]; exact x23
  have str3 : StreamAt u3 ⟨e1.segs, e1.cur ++ (List.range j).map (outerFold b sig.proof next), e1.par⟩ :=
    str.frame (F02.trans f3) (fun k hk h => by rcases h with (h | h) | h <;> exact h)
  have nout3 : DigAt u3 NOUT value :=
    nout.frame (F02.trans f3) (by decide) (fun h => by rcases h with (h | h) | h <;> exact h)
      (fun h => by rcases h with (h | h) | h <;> exact h)
  set e := (⟨e1.segs, e1.cur ++ (List.range j).map (outerFold b sig.proof next), e1.par⟩ : Em) with he
  have hlenE : (img e).length = wl e1 + 1 + 10 * (e1.cur.length + j) := by
    rw [length_img]; simp [he, wl, List.length_append, List.length_map, List.length_range]
  have hfold : ∃ k4 u4, Steps image u3 k4 k4 u4 ∧ k4 ≤ 24 ∧ u4.pc = pcOf 167 ∧
      DigAt u4 NODE pl ∧ DigAt u4 (NODE + 48) pr ∧ u4.getReg .x23 = BitVec.ofNat 64 (e1.cur.length + j + 1) ∧
      StreamAt u4 ⟨e.segs, e.cur ++ [outerFold b sig.proof next j], e.par⟩ ∧
      RegsExcept u3 u4 [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame u3 u4 (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨ (0xC40 ≤ A ∧ A < 0x3418)) := by
    have hcnt3 := hlenE
    by_cases hbit : b / 2 ^ j % 2 = 0
    · rw [if_pos hbit] at p3
      have hside : outerFold b sig.proof next j = (false, other) := by
        unfold outerFold; rw [hoth]; simp [hbit]
      obtain ⟨u4, s4, p4, m0, m8, m48, m56, w56, w64, x23_4, r4, f4⟩ := f144_spec u3 p3 (0x7160 + 16 * u')
        (0xC40 + 8 * wl e1) (e1.cur.length + j) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) x13_3 x22_3 x23_3
      refine ⟨23, u4, s4, by omega, p4, ?_, ?_, x23_4, ?_, r4, f4.mono (fun A _ h => by
        simp only [NODE] at h ⊢; omega)⟩
      · rw [hpl, if_pos hbit]; exact ⟨by rw [m0]; exact nout3.1, by rw [m8]; exact nout3.2⟩
      · rw [hpr, if_pos hbit]; exact ⟨by rw [m48]; exact hslot3.1, by rw [m56]; exact hslot3.2⟩
      · refine streamAt_fold' _ str3 (fun r hr hrk => ?_) (fun k hk hk' => f4.get (by omega) (by
          simp only [NODE]; omega))
        have hpos : 0xC40 + 8 * ((img e).length + r) =
            0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * r := by
          rw [hlenE]; ring
        rw [hpos, hside]
        have hz : ∀ r, r < 10 → r ≠ 6 → r ≠ 7 → (img e).length + r < 1275 →
            u4.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * r)) = 0 := by
          intro r hr h6 h7 hrk
          rw [f4.get (by omega) (by simp only [NODE]; omega), show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 +
            8 * r = 0xC40 + 8 * ((img e).length + r) by rw [hlenE]; ring, streamAt_zero str3 _ (by omega) (by omega)]
        interval_cases r
        · rw [hz 0 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 1 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 2 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 3 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 4 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 5 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * 6 =
              0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 56 by ring, w56]
          exact hslot3.1
        · rw [show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * 7 =
              0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 64 by ring, w64]
          exact hslot3.2
        · rw [hz 8 (by omega) (by omega) (by omega) hrk]; rfl
        · rw [hz 9 (by omega) (by omega) (by omega) hrk]; rfl
    · rw [if_neg hbit] at p3
      have hside : outerFold b sig.proof next j = (true, other) := by
        unfold outerFold; rw [hoth]; simp only [Prod.mk.injEq, and_true, decide_eq_true_eq]; omega
      obtain ⟨u4, s4, p4, m0, m8, m48, m56, w8, w16, x23_4, r4, f4⟩ := f120_spec u3 p3 (0x7160 + 16 * u')
        (0xC40 + 8 * wl e1) (e1.cur.length + j) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) x13_3 x22_3 x23_3
      refine ⟨24, u4, s4, le_rfl, p4, ?_, ?_, x23_4, ?_, r4, f4.mono (fun A _ h => by
        simp only [NODE] at h ⊢; omega)⟩
      · rw [hpl, if_neg hbit]; exact ⟨by rw [m0]; exact hslot3.1, by rw [m8]; exact hslot3.2⟩
      · rw [hpr, if_neg hbit]; exact ⟨by rw [m48]; exact nout3.1, by rw [m56]; exact nout3.2⟩
      · refine streamAt_fold' _ str3 (fun r hr hrk => ?_) (fun k hk hk' => f4.get (by omega) (by
          simp only [NODE]; omega))
        have hpos : 0xC40 + 8 * ((img e).length + r) =
            0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * r := by
          rw [hlenE]; ring
        rw [hpos, hside]
        have hz : ∀ r, r < 10 → r ≠ 0 → r ≠ 1 → (img e).length + r < 1275 →
            u4.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * r)) = 0 := by
          intro r hr h6 h7 hrk
          rw [f4.get (by omega) (by simp only [NODE]; omega), show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 +
            8 * r = 0xC40 + 8 * ((img e).length + r) by rw [hlenE]; ring, streamAt_zero str3 _ (by omega) (by omega)]
        interval_cases r
        · rw [show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * 0 =
              0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 by ring, w8]
          exact hslot3.1
        · rw [show 0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 8 + 8 * 1 =
              0xC40 + 8 * wl e1 + 80 * (e1.cur.length + j) + 16 by ring, w16]
          exact hslot3.2
        all_goals (rw [hz _ (by omega) (by omega) (by omega) hrk]; rfl)
  obtain ⟨k4, u4, s4, hk4, p4, n0, n48, x23_4, str4, r4, f4⟩ := hfold
  have R04 : RegsExcept u u4 ([.x6] ++ [.x6] ++ [.x13, .x14, .x18, .x28] ++ [.x6, .x7, .x23, .x28, .x29, .x30]) :=
    R03.trans r4
  obtain ⟨u5, s5, p5, m16, m24, x10_5, x11_5, x12_5, r5, f5⟩ := f167_spec u4 p4 c (N.toNat % 2 ^ 31) j b hc hi hj hb
    (by rw [R04.get (by decide)]; exact x8u) (by rw [R04.get (by decide)]; exact hstu.x9)
    (by rw [R04.get (by decide)]; exact x19) (by rw [r4.get (by decide)]; exact x14_3)
  have R05 : RegsExcept u u5 (([.x6] ++ [.x6] ++ [.x13, .x14, .x18, .x28] ++ [.x6, .x7, .x23, .x28, .x29, .x30]) ++
      [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := R04.trans r5
  have F35 : Frame u3 u5 (fun A => (A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
      (0xC40 ≤ A ∧ A < 0x3418)) ∨ (A = NODE + 16 ∨ A = NODE + 24)) := f4.trans f5
  set heap := 2 ^ (3 - j) + b / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (3 - j) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : b / 2 ^ (j + 1) ≤ b := Nat.div_le_self _ _
    omega
  have F05 : Frame u u5 (fun A => ((False ∨ False) ∨ False) ∨ ((A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨
      A = NODE + 56 ∨ (0xC40 ≤ A ∧ A < 0x3418)) ∨ (A = NODE + 16 ∨ A = NODE + 24))) := (F02.trans f3).trans F35
  have hn32 : u5.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [F05.get (A := NODE + 32) (by decide) (by simp only [NODE]; decide)]; exact hstu.n32
  have hn40 : u5.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [F05.get (A := NODE + 40) (by decide) (by simp only [NODE]; decide)]; exact hstu.n40
  have hq : hashInput u5 = toQ (pad64 (bytesLE 16 pl ++ bytesLE 16 (header 10 c (N.toNat % 2 ^ 31) 0 heap) ++
      zero16 ++ bytesLE 16 pr)) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length'])]
    refine hashInput_toQ u5 _ 0 NODE (nodeInput_length' _ _ _ _ _ _) x10_5 (by decide) (by decide) x11_5
      (by decide) ?_
    rw [wordsOf_nodeInput' 10 _ _ _ _ _ (by decide), readWords_eight, f5.get (A := NODE) (by decide) (by simp only [NODE]; omega),
      f5.get (A := NODE + 8) (by decide) (by simp only [NODE]; omega), m16, m24, hn32, hn40,
      f5.get (A := NODE + 48) (by decide) (by simp only [NODE]; omega),
      f5.get (A := NODE + 56) (by decide) (by simp only [NODE]; omega),
      n0.1, n0.2, n48.1, n48.2,
      hdr0_eq 10 c (N.toNat % 2 ^ 31) (N.toNat % 2 ^ 31) (by decide) (by omega) hi hi,
      hdr1_eq heap 0 hheap' (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  have hv : hashArgumentsValid u5 = true :=
    hashArgs_const u5 NODE 64 NOUT x10_5 x11_5 x12_5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : u5.getReg .x5 = 0 := by rw [R05.get (by decide)]; exact hstu.x5
  have hblk : (toQ (pad64 (bytesLE 16 pl ++ bytesLE 16 (header 10 c (N.toNat % 2 ^ 31) 0 heap) ++ zero16 ++
      bytesLE 16 pr))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length']), blocks_toQ ⟨by rw [nodeInput_length']; omega,
      by rw [nodeInput_length']⟩, nodeInput_length']
  rw [show 4 - j - 1 = 3 - j by omega]
  unfold nodeHash
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans (s4.trans s5)))) (tb_shortHash_bind' (W := 2)
    (fetch_190 u5 p5) h5 hv hq (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  have p6 : (writeHash u5 a).pc = pcOf 191 := by rw [pc_writeHash, p5, pcOf_add4]
  have R06 : RegsExcept u (writeHash u5 a) ((([.x6] ++ [.x6] ++ [.x13, .x14, .x18, .x28] ++
      [.x6, .x7, .x23, .x28, .x29, .x30]) ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) ++ []) :=
    R05.trans (fun r _ => getReg_writeHash u5 a r)
  obtain ⟨u7, s7, p7, x19_7, r7, f7⟩ := f191_spec (writeHash u5 a) p6 j (by rw [R06.get (by decide)]; exact x19)
  refine (TBSim.steps s7 (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  have fw := Frame.writeHash u5 a NOUT x12_5 (by decide)
  have hd := DigAt.writeHash_lo u5 a NOUT x12_5 (by decide)
  have R07 := R06.trans r7
  have F37 : Frame u3 u7 (fun A => ((A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
      (0xC40 ≤ A ∧ A < 0x3418)) ∨ (A = NODE + 16 ∨ A = NODE + 24)) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ False) :=
    F35.trans (fw.trans f7)
  refine ⟨p7, x19_7, ?_, by omega, ⟨by rw [f7.get (by decide) (fun h => h)]; exact hd.1,
    by rw [f7.get (by decide) (fun h => h)]; exact hd.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [r7.get (by decide), getReg_writeHash, r5.get (by decide), r4.get (by decide)]; exact x18_3
  · rw [r7.get (by decide), getReg_writeHash, r5.get (by decide), x23_4, Nat.add_assoc]
  · have hS := str4.frame (f5.trans (fw.trans f7)) (fun k hk h => by
      rcases h with (h | h) | (h | h) <;> first | exact h.elim | (simp only [NODE, NOUT] at h; omega))
    have e2 : (⟨e.segs, e.cur ++ [outerFold b sig.proof next j], e.par⟩ : Em) =
        ⟨e1.segs, e1.cur ++ (List.range (j + 1)).map (outerFold b sig.proof next), e1.par⟩ := by
      simp only [he, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    rw [e2] at hS; exact hS
  · exact (R4.trans R07).mono (by decide)
  · refine (F4.trans ((F02.trans f3).trans F37)).mono (fun A _ h => ?_)
    unfold OW at h ⊢
    simp only [NODE, NOUT, false_or, or_false] at h ⊢
    omega

/-! ## One coordinate -/

theorem ftsStep_some (sig : Signature) (index : Nat) (chosen : List Selection) (roots : List Digest) (used c : Nat) :
    ftsStep sig index chosen (some (roots, used)) c =
      recoverChild index c ((chosen.getD c ⟨0, []⟩).leaves.map fun s => (chosen.getD c ⟨0, []⟩).bucket * 128 + s)
          (coordValues sig c) sig.proof 7 (chosen.getD c ⟨0, []⟩).bucket used >>= fun r => match r with
        | some (value, next) =>
          (List.range 4).foldlM (outerStep sig index c (chosen.getD c ⟨0, []⟩).bucket) (some (value, next)) >>=
            fun result => match result with
            | some (root, next') => pure (some (roots ++ [root], next'))
            | none => pure none
        | none => pure none := by
  unfold ftsStep
  simp only []
  congr 1
  funext r
  rcases r with _ | ⟨value, next⟩
  · rfl
  · simp only []
    congr 1
    funext result
    rcases result with _ | ⟨root, next'⟩ <;> rfl

/-- The emission state at the start of coordinate `c`. -/
def emAt (chosen : List Selection) (proof : Fin 115 → Digest) (c : Nat) : Em := ⟨emSegs chosen proof c, [], 0⟩

/-- The doublewords the FTS phase writes (`FtsW` without the zero words of the FTS leaf block). -/
def FtsW' (A : Nat) : Prop :=
  (0x22000 - 512 ≤ A ∧ A < 0x22000) ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
    A = NODE + 56 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = FLEAF + 16 ∨ A = FLEAF + 24 ∨ A = FLEAF + 32 ∨
    A = FLEAF + 40 ∨ (FOREST ≤ A ∧ A < FOREST + 128 ∧ A ≠ FOREST + 16 ∧ A ≠ FOREST + 24) ∨ (0x840 ≤ A ∧ A < 0x3418)

theorem not_FtsW'_stat {A : Nat} (h : StatA A) : ¬ FtsW' A := by
  unfold StatA at h; unfold FtsW'; simp only [SEL, FLEAF, NODE, NOUT, FOREST] at h ⊢; omega

/-- The coordinate invariant at `fts_coord` (word 65) before coordinate `c` with Core's state `(roots, used)`. -/
structure CoordInv (s0 : MachineState) (sig : Signature) (N : HashOutput) (c : Nat) (roots : List Digest)
    (used : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 65
  x8 : t.getReg .x8 = BitVec.ofNat 64 c
  x18 : t.getReg .x18 = BitVec.ofNat 64 used
  x22 : t.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl (emAt (T3.selections N) sig.proof c))
  x2 : t.getReg .x2 = BitVec.ofNat 64 0x22000
  hc : c ≤ 7
  hused : used = slotBase (T3.selections N) c
  hlen : roots.length = c
  roots : ∀ c' < c, DigAt t (FOREST + slotOff c') (roots.getD c' 0)
  stream : StreamAt t (emAt (T3.selections N) sig.proof c)
  sec : ∀ k (h : k < 21), k < 3 * c → DigAt t (0x860 + 48 * k) (sig.secrets ⟨k, h⟩)
  wz : ∀ A, 0x840 ≤ A → A < 0xC40 → (∀ k < 3 * c, A ≠ 0x860 + 48 * k ∧ A ≠ 0x860 + 48 * k + 8) →
    t.getMem (BitVec.ofNat 64 A) = 0
  regs : RegsExcept s0 t ftsRegs
  frame : Frame s0 t FtsW'

/-! ## The emission of one coordinate -/

theorem idxOf_slot_frontier (sel : Selection) (i : Nat)
    (hi : i < (T3.frontier (selectedLeaves sel) 7 sel.bucket).length) :
    (slotPositions sel).idxOf ((T3.frontier (selectedLeaves sel) 7 sel.bucket)[i]) = i := by
  have h : (slotPositions sel)[i]'(by unfold slotPositions; rw [List.length_append]; omega) =
      (T3.frontier (selectedLeaves sel) 7 sel.bucket)[i] := by
    unfold slotPositions; rw [List.getElem_append_left hi]
  rw [← h]; exact (slotPositions_nodup sel).idxOf_getElem i _

theorem idxOf_slot_outer (sel : Selection) (j : Nat) (hj : j < 4) :
    (slotPositions sel).idxOf (7 + j, sel.bucket / 2 ^ j ^^^ 1) =
      (T3.frontier (selectedLeaves sel) 7 sel.bucket).length + j := by
  have hl : (T3.frontier (selectedLeaves sel) 7 sel.bucket).length + j < (slotPositions sel).length := by
    unfold slotPositions; rw [List.length_append, List.length_map, List.length_range]; omega
  have h : (slotPositions sel)[(T3.frontier (selectedLeaves sel) 7 sel.bucket).length + j] =
      (7 + j, sel.bucket / 2 ^ j ^^^ 1) := by
    simp [slotPositions, List.getElem_append_right]
  rw [← h]; exact (slotPositions_nodup sel).idxOf_getElem _ _

/-- The bucket DFS from slot `slotBase c` emits with the positional values of coordinate `c`. -/
theorem rcEm_coord (chosen : List Selection) (proof : Fin 115 → Digest) (c : Nat) (e : Em) :
    rcEm (selectedLeaves (chosen.getD c ⟨0, []⟩)) (pfN proof) 7 (chosen.getD c ⟨0, []⟩).bucket (slotBase chosen c) e =
      emV (selectedLeaves (chosen.getD c ⟨0, []⟩)) (valC chosen proof c) 7 (chosen.getD c ⟨0, []⟩).bucket e := by
  apply rcEm_eq_emV
  intro i hi
  unfold valC
  rw [idxOf_slot_frontier _ i hi]

theorem img_len_climbE (val : Nat × Nat → Digest) (g lo a : Nat) (e : Em) :
    (img (climbE val g lo a e)).length = (img e).length + 10 * a := by
  unfold climbE
  rw [length_img, length_img]
  simp [wl]
  ring

theorem wl_emAt (chosen : List Selection) (proof : Fin 115 → Digest) (hC : ChosenOk chosen) {c : Nat} (hc : c ≤ 7) :
    wl (emAt chosen proof c) = 5 * c + 10 * slotBase chosen c :=
  length_emSegs_words chosen proof hC c hc

theorem wl_climbE (val : Nat × Nat → Digest) (g lo a : Nat) (e : Em) : wl (climbE val g lo a e) = wl e := rfl

theorem cur_climbE (val : Nat × Nat → Digest) (g lo a : Nat) (e : Em) :
    (climbE val g lo a e).cur.length = e.cur.length + a := by
  simp [climbE]

/-- Closing coordinate `c`'s emission (the bucket DFS and the four outer folds) gives `emAt (c + 1)`. -/
theorem emAt_succ (chosen : List Selection) (proof : Fin 115 → Digest) (hC : ChosenOk chosen) {c : Nat}
    (hc : c < 7) :
    (climbE (valC chosen proof c) (selLeaf (chosen.getD c ⟨0, []⟩) 2) 7 4
      (emV (selectedLeaves (chosen.getD c ⟨0, []⟩)) (valC chosen proof c) 7 (chosen.getD c ⟨0, []⟩).bucket
        (emAt chosen proof c))).close false 0 = emAt chosen proof (c + 1) := by
  unfold emAt
  rw [emV_bucket _ c _ (hC c hc), emSegs_succ]

/-- The machine's outer folds are the climb of the last leaf through levels 8 .. 10. -/
theorem outerFold_eq (chosen : List Selection) (proof : Fin 115 → Digest) (hC : ChosenOk chosen) {c : Nat}
    (hc : c < 7) {j : Nat} (hj : j < 4) :
    outerFold (chosen.getD c ⟨0, []⟩).bucket proof
        (slotBase chosen c + (T3.frontier (selectedLeaves (chosen.getD c ⟨0, []⟩)) 7
          (chosen.getD c ⟨0, []⟩).bucket).length) j =
      climbF (valC chosen proof c) (selLeaf (chosen.getD c ⟨0, []⟩) 2) 7 j := by
  have hs := hC c hc
  have hdiv : selLeaf (chosen.getD c ⟨0, []⟩) 2 / 2 ^ (7 + j) = (chosen.getD c ⟨0, []⟩).bucket / 2 ^ j := by
    unfold selLeaf; exact bucket_div_outer hs.l2
  unfold outerFold climbF valC
  rw [hdiv, idxOf_slot_outer _ j hj, Nat.add_assoc]

/-- The cycles of one coordinate (all oracles). -/
def coordCost : Nat := 5000

/-- **One coordinate** (`fts_coord` .. `fts_root0`, words 65 .. 214, with `recover_child`). -/
theorem fts_coord_step {sk : BitVec 256} {sig : Signature} {N : HashOutput} {s0 : MachineState}
    (hpre : FtsPre sig N s0) {c : Nat} (hc : c < 7) {roots : List Digest} {used : Nat} {t : MachineState}
    (hinv : CoordInv s0 sig N c roots used t) :
    TBSim image sk t coordCost (ftsStep sig (N.toNat % 2 ^ 31) (T3.selections N) (some (roots, used)) c)
      (fun st u => match st with
        | none => FailedAt 354 u
        | some (roots', used') => CoordInv s0 sig N (c + 1) roots' used' u) := by
  have hC : ChosenOk (T3.selections N) := chosenOk_of N (selectionsOk_of_admissible N hpre.adm)
  have h7 : slotBase (T3.selections N) 7 ≤ 115 := slotBase_seven_le N hC hpre.adm
  have hs : SelOk ((T3.selections N).getD c ⟨0, []⟩) := hC c hc
  have hb : ((T3.selections N).getD c ⟨0, []⟩).bucket < 16 := hs.b
  have l0 := hs.s01; have l1 := hs.s12; have l2 := hs.l2
  have hsl : ((T3.selections N).getD c ⟨0, []⟩).leaves.map
      (fun s => ((T3.selections N).getD c ⟨0, []⟩).bucket * 128 + s) =
      [selEntry N c 0, selEntry N c 1, selEntry N c 2] := hs.selected
  have hg : selEntry N c 0 < selEntry N c 1 ∧ selEntry N c 1 < selEntry N c 2 ∧ selEntry N c 2 < 2 ^ 11 := by
    unfold selEntry; omega
  have hb0 : selEntry N c 0 / 2 ^ 7 = ((T3.selections N).getD c ⟨0, []⟩).bucket := by
    unfold selEntry; exact bucket_div_eight (by omega)
  have hi : N.toNat % 2 ^ 31 < 2 ^ 32 := by have := Nat.mod_lt N.toNat (show 0 < 2 ^ 31 by norm_num); omega
  have hsel := hs.selected
  rw [ftsStep_some]
  change TBSim image sk t coordCost (recoverChild _ c (selectedLeaves ((T3.selections N).getD c ⟨0, []⟩)) _ _ _ _ _
    >>= _) _
  rw [hsel]
  -- the static facts and the prefix (65 .. 98)
  have hst : Stat sig N t := (stat_of_pre hpre).frame hinv.regs (by decide) (by decide) hinv.frame
    (fun A h => not_FtsW'_stat h)
  obtain ⟨t1, s1, p1, r1, f1⟩ := f65_spec t hinv.pc c (by omega) hinv.x8
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, hsec, r2, f2⟩ := fts_sec_loop t1 p1 c hc (by rw [r1.get (by decide)]; exact hinv.x8)
  have R02 : RegsExcept t t2 ([.x6] ++ [.x6, .x7, .x13, .x14, .x19, .x28, .x29]) := r1.trans r2
  have F02 : Frame t t2 (fun A => False ∨ ∃ j < 3, A = 0x860 + 48 * (3 * c + j) ∨
      A = 0x860 + 48 * (3 * c + j) + 8) := f1.trans f2
  have hst2 : Stat sig N t2 := hst.frame R02 (by decide) (by decide) F02 (fun A h hw => by
    unfold StatA at h; simp only [SEL, FLEAF, NODE] at h
    rcases hw with hw | ⟨j, hj, hw | hw⟩
    · exact hw
    · omega
    · omega)
  have x8_2 : t2.getReg .x8 = BitVec.ofNat 64 c := by rw [R02.get (by decide)]; exact hinv.x8
  obtain ⟨t3, s3, p3, x1_3, x10_3, x11_3, r3, f3⟩ := f89_spec t2 p2 c (selEntry N c 0) hc (by omega) x8_2
    (hst2.rows c hc 0 (by decide))
  rw [hb0] at x11_3
  have R03 : RegsExcept t t3 (([.x6] ++ [.x6, .x7, .x13, .x14, .x19, .x28, .x29]) ++
      [.x1, .x10, .x11, .x14, .x28]) := R02.trans r3
  have hst3 : Stat sig N t3 := hst2.frame r3 (by decide) (by decide) f3 (fun _ _ h => h)
  have x8_3 : t3.getReg .x8 = BitVec.ofNat 64 c := by rw [r3.get (by decide)]; exact x8_2
  -- the emission before and after the bucket DFS
  set chosen := T3.selections N with hch
  set sel := chosen.getD c ⟨0, []⟩ with hseldef
  set e0 := emAt chosen sig.proof c with he0
  have hwl0 : wl e0 = 5 * c + 10 * slotBase chosen c := wl_emAt chosen sig.proof hC (by omega)
  have hwl1 : wl (emAt chosen sig.proof (c + 1)) = 5 * (c + 1) + 10 * slotBase chosen (c + 1) :=
    wl_emAt chosen sig.proof hC (by omega)
  have hsb : slotBase chosen (c + 1) ≤ 115 := le_trans (slotBase_mono chosen (by omega)) h7
  set e1 := emV (selectedLeaves sel) (valC chosen sig.proof c) 7 sel.bucket e0 with he1
  have hE1 : rcEm [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] (pfN sig.proof) 7 sel.bucket used e0 = e1 := by
    rw [he1, ← rcEm_coord, hsel, hinv.hused]
  have hclose := emAt_succ chosen sig.proof hC hc
  rw [← he0, ← he1] at hclose
  have hlen1 : (img e1).length + 41 = 5 * (c + 1) + 10 * slotBase chosen (c + 1) + 1 := by
    have := congrArg (fun e => (img e).length) hclose
    simp only [img_len_close, img_len_climbE] at this
    rw [this, length_img, hwl1]; simp [emAt]
  have hused124 : used ≤ 115 := by
    rw [hinv.hused]; exact le_trans (slotBase_mono chosen (by omega)) h7
  have hgl : selLeaf sel 0 < selLeaf sel 1 ∧ selLeaf sel 1 < selLeaf sel 2 ∧ selLeaf sel 2 < 2 ^ 11 := hg
  have hpreR : RcPre c (N.toNat % 2 ^ 31) (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2) (coordValues sig c)
      sig.proof t3 7 sel.bucket used e0 true 99 0x22000 := by
    refine ⟨p3, x1_3, by rw [R03.get (by decide)]; exact hinv.x2, x10_3, x11_3,
      by rw [R03.get (by decide)]; exact hinv.x18, by rw [R03.get (by decide)]; exact hinv.x22,
      fun h => absurd h (by decide), ?_, fun _ => rfl, by simp [he0, emAt], by simp [he0, emAt], ?_, ?_,
      by norm_num, le_rfl, by norm_num, by decide, by omega, hused124, rcCtx_of_stat hst3 hc x8_3⟩
    · simp only [true_iff, List.mem_cons, List.mem_nil_iff, or_false]
      unfold selLeaf
      rintro g (rfl | rfl | rfl) <;> omega
    · exact hinv.stream.frame (F02.trans f3) (fun k hk h => by
        rcases h with (h | ⟨j, hj, h | h⟩) | h <;> first | exact h.elim | omega)
    · rw [hE1]; omega
  have hrc := rc_tbsim (sk := sk) hc hi hgl 7 sel.bucket used e0 true 99 0x22000 t3 hpreR
  have hcost := rcCost_eight (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2) sel.bucket
  refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.bind (W₂ := 333) hrc (fun r t4 h4 => ?_))).mono
    (by unfold coordCost; omega) (fun _ _ h => h)
  rcases r with _ | ⟨v, next⟩
  · exact (TBSim.pure (Q := fun st u => match st with
        | none => FailedAt 354 u
        | some (roots', used') => CoordInv s0 sig N (c + 1) roots' used' u) (a := none) h4).mono (by omega)
      (fun _ _ h => h)
  have hb0' : selLeaf sel 0 / 2 ^ 7 = sel.bucket := hb0
  have hL8 : hasLeaf [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] 7 sel.bucket = true :=
    (hasLeaf_three _ _ _ _ _).mpr (Or.inl hb0')
  obtain ⟨p4, x1_4, x2_4, x10_4, nout4, hnext, hnext124, _, x18_4, x22_4, regs4, _, cntl4, cnt4, par4, str4,
    R34, F34, ctx4⟩ := h4
  simp only [hL8, Bool.not_true, Bool.and_false, hE1] at hnext x22_4 regs4 cntl4 cnt4 par4 str4
  obtain ⟨x23_4, x24_4⟩ := regs4 trivial
  have hcur4 := cntl4 trivial
  have hst4 : Stat sig N t4 := hst3.frame R34 (by decide) (by decide) F34 (fun A hA h =>
    not_RcW_static (sp := 0x22000) (level := 7) (by norm_num) le_rfl hA h)
  have x8_4 : t4.getReg .x8 = BitVec.ofNat 64 c := ctx4.x8
  have hroom : wl e1 + 1 + 10 * (e1.cur.length + 4) ≤ 1275 := by
    have := length_img e1; omega
  obtain ⟨t5, s5, p5, x19_5, r5, f5⟩ := f99_spec t4 p4
  have hO0 : OInv sig.proof sel.bucket e1 next t4 0 v next t5 := by
    refine ⟨p5, x19_5, by rw [r5.get (by decide)]; exact x18_4, rfl,
      nout4.frame f5 (by decide) (fun h => h) (fun h => h), by rw [r5.get (by decide)]; exact x23_4, ?_,
      r5.mono (by decide), f5.mono (fun _ _ h => h.elim)⟩
    simp only [List.range_zero, List.map_nil, List.append_nil]
    exact str4.frame f5 (fun _ _ h => h)
  simp only []
  rw [List.range_eq_range']
  have hbody : ∀ j < 4, ∀ (acc : Option (Digest × Nat)) (u : MachineState),
      (match acc with
        | none => FailedAt 354 u
        | some (value, u') => OInv sig.proof sel.bucket e1 next t4 j value u' u) →
      TBSim image sk u 77 (outerStep sig (N.toNat % 2 ^ 31) c sel.bucket acc (0 + j))
        (fun acc' u' => match acc' with
          | none => FailedAt 354 u'
          | some (value, u'') => OInv sig.proof sel.bucket e1 next t4 (j + 1) value u'' u') := by
    intro j hj acc u hu
    rcases acc with _ | ⟨value, u'⟩
    · simp only [outerStep]
      exact (TBSim.pure (a := none) hu).mono (by omega) (fun _ _ h => h)
    · rw [Nat.zero_add]
      exact outer_step hc hb hb0 (by omega) hst4 x8_4 x22_4 hroom hnext124 hj hu
  refine (TBSim.steps s5 (TBSim.bind (W₂ := 24) (TBSim.foldlM_range' 0 4 _ _ _ 77 hbody hO0)
    (fun res t6 h6 => ?_))).mono (by omega) (fun _ _ h => h)
  rcases res with _ | ⟨root, next'⟩
  · exact (TBSim.pure (Q := fun st u => match st with
        | none => FailedAt 354 u
        | some (roots', used') => CoordInv s0 sig N (c + 1) roots' used' u) (a := none) h6).mono (by omega)
      (fun _ _ h => h)
  simp only [] at h6 ⊢
  obtain ⟨p6, x19_6, x18_6, hu6, nout6, x23_6, str6, R46, F46⟩ := h6
  obtain ⟨t7, s7, p7, r7, f7⟩ := f100_spec t6 p6 4 le_rfl x19_6
  rw [if_pos le_rfl] at p7
  have R47 : RegsExcept t4 t7 ([.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x18, .x19, .x23, .x28, .x29, .x30] ++
      [.x6]) := R46.trans r7
  obtain ⟨t8, s8, p8, w8, x22_8, x28_8, r8, f8⟩ := f193_spec t7 p7 c (0xC40 + 8 * wl e1) (e1.cur.length + 4)
    e1.par hc (by omega) (by omega) (by omega) par4 (by omega) (by rw [R47.get (by decide)]; exact x8_4)
    (by rw [R47.get (by decide)]; exact x22_4) (by rw [r7.get (by decide)]; exact x23_6)
    (by rw [R47.get (by decide)]; exact x24_4)
  have h9 : ∃ k9 t9, Steps image t8 k9 k9 t9 ∧ k9 ≤ 1 ∧ t9.pc = pcOf 204 ∧
      t9.getReg .x28 = BitVec.ofNat 64 (slotOff c) ∧ RegsExcept t8 t9 [.x28] ∧ Frame t8 t9 (fun _ => False) := by
    by_cases h0 : c = 0
    · rw [if_pos h0] at p8
      refine ⟨0, t8, Steps.refl _, by omega, p8, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [x28_8, h0]; rfl
    · rw [if_neg h0] at p8
      obtain ⟨t9, s9, p9, x28_9, r9, f9⟩ := f203_spec t8 p8 (16 * c) x28_8
      exact ⟨1, t9, s9, le_rfl, p9, by rw [x28_9]; unfold slotOff; rw [if_neg h0], r9, f9⟩
  obtain ⟨k9, t9, s9, hk9, p9, x28_9, r9, f9⟩ := h9
  have hso : slotOff c + 16 ≤ 128 ∧ slotOff c % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  obtain ⟨t10, s10, p10, m0, m8, x8_10, r10, f10⟩ := f204_spec t9 p9 c (slotOff c) hc hso.1 hso.2 x28_9
    (by rw [r9.get (by decide), r8.get (by decide), R47.get (by decide)]; exact x8_4)
  refine (TBSim.steps (s7.trans (s8.trans (s9.trans s10))) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  -- the slots and the closed segment
  have hnextF : next = slotBase chosen c + (T3.frontier (selectedLeaves sel) 7 sel.bucket).length := by
    rw [hnext, hsel, hinv.hused]
  have hF : (List.range 4).map (outerFold sel.bucket sig.proof next) =
      (List.range 4).map (climbF (valC chosen sig.proof c) (selLeaf sel 2) 7) := by
    apply List.map_congr_left
    intro j hj
    rw [hnextF]; exact outerFold_eq chosen sig.proof hC hc (List.mem_range.mp hj)
  have hE6 : (⟨e1.segs, e1.cur ++ (List.range 4).map (outerFold sel.bucket sig.proof next), e1.par⟩ : Em) =
      climbE (valC chosen sig.proof c) (selLeaf sel 2) 7 4 e1 := by
    rw [hF]; rfl
  rw [hE6] at str6
  have str7 := str6.frame f7 (fun _ _ h => h)
  have hz7 : t7.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e1)) = 0 := by
    have := str7 (wl e1) (by omega)
    rw [this]
    simp only [img, climbE]
    exact getD_mid_self _ _ _
  have str8 : StreamAt t8 ((climbE (valC chosen sig.proof c) (selLeaf sel 2) 7 4 e1).close false 0) := by
    refine streamAt_close false 0 str7 ?_ (fun k hk hne => f8.get (by omega) (by
      rw [wl_climbE] at hne; omega))
    rw [wl_climbE, w8, hz7, replaceByte_zero _ (by omega), cur_climbE]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1; simp [climbE]; ring
  rw [hclose] at str8
  -- frames
  have Fpost : Frame t2 t10 (fun A => RcW 0x22000 7 A ∨ OW A ∨ A = 0xC40 + 8 * wl e1 ∨ A = FOREST + slotOff c ∨
      A = FOREST + slotOff c + 8) :=
    ((((((f3.trans F34).trans F46).trans f7).trans f8).trans f9).trans f10).mono (fun A _ h => by
      rcases h with ((((((h | h) | h) | h) | h) | h) | h | h)
      · exact h.elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact h.elim
      · exact Or.inr (Or.inr (Or.inl h))
      · exact h.elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  have nW : ∀ A, A < 0xC40 → ¬ (RcW 0x22000 7 A ∨ OW A ∨ A = 0xC40 + 8 * wl e1 ∨ A = FOREST + slotOff c ∨
      A = FOREST + slotOff c + 8) := by
    intro A hA h
    unfold RcW OW at h
    simp only [NODE, NOUT, FLEAF, FOREST] at h
    omega
  have nWr : ∀ c', c' < c → ∀ d, d = 0 ∨ d = 8 → ¬ (RcW 0x22000 7 (FOREST + slotOff c' + d) ∨
      OW (FOREST + slotOff c' + d) ∨ FOREST + slotOff c' + d = 0xC40 + 8 * wl e1 ∨
      FOREST + slotOff c' + d = FOREST + slotOff c ∨ FOREST + slotOff c' + d = FOREST + slotOff c + 8) := by
    intro c' hc' d hd h
    have hs' : slotOff c' + 16 ≤ slotOff c := by unfold slotOff; split_ifs <;> omega
    have hs'' : slotOff c' + 16 ≤ 128 := by unfold slotOff; split_ifs <;> omega
    unfold RcW OW at h
    simp only [NODE, NOUT, FLEAF, FOREST] at h
    omega
  have R0t := (((((R03.trans R34).trans R46).trans r7).trans r8).trans r9).trans r10
  refine ⟨p10, x8_10, ?_, ?_, ?_, by omega, ?_, by simp [hinv.hlen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r10.get (by decide), r9.get (by decide), r8.get (by decide), r7.get (by decide)]; exact x18_6
  · rw [r10.get (by decide), r9.get (by decide), x22_8, ← hclose, wl_close, wl_climbE, cur_climbE]
    exact congrArg _ (by ring)
  · rw [R0t.get (by decide)]; exact hinv.x2
  · rw [hu6, hnextF, slotBase_succ]
    unfold slotPositions
    rw [List.length_append, List.length_map, List.length_range]
    ring
  · intro c' hc'
    rcases (show c' < c ∨ c' = c by omega) with hlt | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hinv.hlen]; exact hlt)]
      have h1 := (hinv.roots c' hlt).frame F02 (by simp only [FOREST]; unfold slotOff; split_ifs <;> omega)
        (fun h => by rcases h with h | ⟨j, hj, h | h⟩ <;> first | exact h | (simp only [FOREST] at h; omega))
        (fun h => by rcases h with h | ⟨j, hj, h | h⟩ <;> first | exact h | (simp only [FOREST] at h; omega))
      refine h1.frame Fpost (by simp only [FOREST]; unfold slotOff; split_ifs <;> omega)
        (by have := nWr c' hlt 0 (Or.inl rfl); simpa using this) (nWr c' hlt 8 (Or.inr rfl))
    · rw [List.getD_append_right _ _ _ _ (by rw [hinv.hlen]), hinv.hlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      have hn9 : DigAt t9 NOUT root := (nout6.frame f7 (by decide) (fun h => h) (fun h => h)).frame (f8.trans f9)
        (by decide) (fun h => by rcases h with h | h <;> first | exact h | (simp only [NOUT] at h; omega))
        (fun h => by rcases h with h | h <;> first | exact h | (simp only [NOUT] at h; omega))
      exact ⟨by rw [m0]; exact hn9.1, by rw [m8]; exact hn9.2⟩
  · exact str8.frame (f9.trans f10) (fun k hk h => by
      rcases h with h | h | h
      · exact h
      · simp only [FOREST] at h; omega
      · simp only [FOREST] at h; omega)
  · intro k hk hk3
    rcases (show k < 3 * c ∨ 3 * c ≤ k by omega) with hlt | hge
    · have h1 := (hinv.sec k hk hlt).frame F02 (by omega)
        (fun h => by rcases h with h | ⟨j, hj, h | h⟩ <;> first | exact h | omega)
        (fun h => by rcases h with h | ⟨j, hj, h | h⟩ <;> first | exact h | omega)
      exact h1.frame Fpost (by omega) (nW _ (by omega)) (nW _ (by omega))
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 3 ∧ k = 3 * c + j := ⟨k - 3 * c, by omega, by omega⟩
      obtain ⟨a0, a8⟩ := hsec j hj
      have hsrc := hst.secrets (3 * c + j) hk
      have hsrc1 : DigAt t1 (0x7010 + 16 * (3 * c + j)) (sig.secrets ⟨3 * c + j, hk⟩) :=
        hsrc.frame f1 (by omega) (fun h => h) (fun h => h)
      have h2 : DigAt t2 (0x860 + 48 * (3 * c + j)) (sig.secrets ⟨3 * c + j, hk⟩) :=
        ⟨by rw [a0]; exact hsrc1.1, by rw [a8]; exact hsrc1.2⟩
      exact h2.frame Fpost (by omega) (nW _ (by omega)) (nW _ (by omega))
  · intro A hA1 hA2 hAk
    have h0 := hinv.wz A hA1 hA2 (fun k hk => hAk k (by omega))
    rw [Fpost.get (by omega) (nW _ hA2), F02.get (by omega) (fun h => by
      rcases h with h | ⟨j, hj, h | h⟩
      · exact h
      · exact (hAk (3 * c + j) (by omega)).1 h
      · exact (hAk (3 * c + j) (by omega)).2 h)]
    exact h0
  · exact (hinv.regs.trans R0t).mono (by decide)
  · refine (hinv.frame.trans (F02.trans Fpost)).mono (fun A _ h => ?_)
    rcases h with h | (h | ⟨j, hj, h | h⟩) | h
    · exact h
    · exact h.elim
    · unfold FtsW'; simp only [NODE, NOUT, FLEAF, FOREST]; omega
    · unfold FtsW'; simp only [NODE, NOUT, FLEAF, FOREST]; omega
    · unfold RcW OW at h; unfold FtsW'
      have hs'' : slotOff c + 16 ≤ 128 := hso.1
      have hs3 : slotOff c ≠ 16 ∧ slotOff c ≠ 8 ∧ slotOff c + 8 ≠ 16 ∧ slotOff c + 8 ≠ 24 ∧ slotOff c ≠ 24 := by
        unfold slotOff; split_ifs <;> omega
      simp only [NODE, NOUT, FLEAF, FOREST] at h ⊢
      omega

end SigGolfCandidate.T3M.Expand
