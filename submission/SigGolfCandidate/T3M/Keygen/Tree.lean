import SigGolfCandidate.T3M.Keygen.TreeBlocks

/-!
# The shared `build_levels` subroutine refines Core's `buildLevels`

The heap arena holds node `k` at `arena + 16 k`; level `ℓ` (`0` = leaves) of a height-`h` tree is the
`2^(h-ℓ)` nodes from heap index `2^(h-ℓ)` (Core's `nodeHash … (2^(h-level) + i)`).

`buildLevels_tsim` : for any image holding the shared code at base `b`, from the entry (offset 113)
with the leaves at heap indices `2^h ..`, the machine refines `T3.buildLevels tag lay tree h leaves`
exactly (`levK B` steps, `levC B` cycles, `2^h - 1` calls and compressions) and returns with every
level in the heap.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)

/-- The arguments of one `build_levels` call. -/
structure LevArgs where
  tag : Nat
  lay : Nat
  tree : Nat
  h : Nat
  arena : Nat
  ret : Nat

namespace LevArgs
variable (B : LevArgs)

/-- Steps of `build_levels`. -/
def levK : Nat := 3 + sumTo (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
/-- Cycles of `build_levels` (tag 10 nodes run the 28-instruction reversal stub). -/
def levC : Nat := 3 + sumTo (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
/-- Calls (= compressions) of `build_levels`. -/
def levN : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) B.h

end LevArgs

/-- The doublewords `build_levels` may change. -/
def LevW (B : LevArgs) (X : Nat) : Prop :=
  X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨ X = NODE + 56 ∨
    (NOUT ≤ X ∧ X < NOUT + 32) ∨ (B.arena + 16 ≤ X ∧ X < B.arena + 16 * 2 ^ B.h)

/-- The registers `build_levels` may change. -/
def levRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x24, .x28, .x29, .x30]

/-- Entry conditions of `build_levels` (offset 113). -/
structure LevPre (s : MachineState) (B : LevArgs) (leaves : List Digest) : Prop where
  x1 : s.getReg .x1 = pcOf B.ret
  x2 : s.getReg .x2 = BitVec.ofNat 64 B.arena
  x5 : s.getReg .x5 = 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 B.tree
  x15 : s.getReg .x15 = BitVec.ofNat 64 B.h
  x21 : s.getReg .x21 = BitVec.ofNat 64 (hdr0 B.tag B.lay B.tree 0)
  tag3 : B.tag = 3 ∨ B.tag = 10
  htree : B.tree < 2 ^ 32
  hh1 : 1 ≤ B.h
  hh : B.h ≤ 12
  ha8 : B.arena % 8 = 0
  ha : B.arena + 16 * 2 ^ (B.h + 1) ≤ 2 ^ 24
  has : NOUT + 32 ≤ B.arena ∨ B.arena + 16 * 2 ^ (B.h + 1) ≤ NODE
  z32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  hlen : leaves.length = 2 ^ B.h
  hleaves : DigsAt s (B.arena + 16 * 2 ^ B.h) leaves

/-- The levels `0 .. ℓ` are in the heap. -/
def HeapAt (t : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest)) : Prop :=
  levels.length = ℓ + 1 ∧ ∀ l ≤ ℓ, (levels.getD l []).length = 2 ^ (B.h - l) ∧
    DigsAt t (B.arena + 16 * 2 ^ (B.h - l)) (levels.getD l [])

/-- At `lv_level` (offset 116) after the levels `1 .. ℓ`. -/
structure LevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels

/-- At `lv_node` (offset 118) computing level `ℓ + 1` (`lo = 2^(h-ℓ-1)` nodes): `pre` done. -/
structure NodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre

theorem nodeInput_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]

theorem wordsOf_nodeInput (tag lay tree heap : Nat) (l r : Digest)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 tag lay tree tree),
        BitVec.ofNat 64 (T3.nodeWord tag 0 heap), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_packed_header _ _ _ _ _ hn, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl

/-- Tag 3: word 1 of the node header is the plain `hdr1 heap 0`. -/
theorem wordsOf_nodeInput_3 (lay tree heap : Nat) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header 3 lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 3 lay tree tree),
        BitVec.ofNat 64 (hdr1 heap 0), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_nodeInput 3 lay tree heap l r (by decide), nodeWord_3]

theorem two_pow_split {h l : Nat} (hl : l < h) : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

section lev
variable {image : Image} {b : Nat} (hsub : SubAt image b) (sk : BitVec 256) {s0 : MachineState}
  {B : LevArgs} {leaves : List Digest} (hpre : LevPre s0 B leaves)
include hsub hpre

/-- One node `k = lo + i` of level `ℓ + 1`. -/
theorem lev_node {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (B.h - ℓ - 1)) {t : MachineState} (ht : NodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf (b + 118)) :
    TSim image sk t (39 + revX B.tag) (46 + revX B.tag) 1 1
      (nodeHash B.tag B.lay B.tree (2 ^ (B.h - (ℓ + 1)) + pre.length)
        ((levels.getD ℓ []).getD (2 * pre.length) 0) ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  have hh := hpre.hh
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (B.h - ℓ) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  have hZ : 2 ^ B.h ≤ 4096 := by
    calc 2 ^ B.h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hk' : 2 ^ (B.h - (ℓ + 1)) = lo := by rw [hlo_def]; congr 1
  have g : ∀ r, r ∉ levRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [levRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [levRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [levRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (hdr0 B.tag B.lay B.tree 0) := by
    rw [g _ (by simp [levRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec hsub t hpc lo (lo + i) (by omega) (by omega) ht.x20 ht.x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full hsub t1 t1pc B.tag B.lay B.arena (lo + i) B.tree hpre.tag3 ha8 (by omega) (by omega) hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact ht.x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  -- the children in the heap (level ℓ, nodes 2i and 2i+1)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  have hL : DigAt t (B.arena + 32 * (lo + i)) ((levels.getD ℓ []).getD (2 * i) 0) := by
    have := hlv.get (i := 2 * i) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i) = B.arena + 32 * (lo + i) by ring] at this
  have hR : DigAt t (B.arena + 32 * (lo + i) + 16) ((levels.getD ℓ []).getD (2 * i + 1) 0) := by
    have := hlv.get (i := 2 * i + 1) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i + 1) = B.arena + 32 * (lo + i) + 16 by ring] at this
  have hL1 := hL.frame t1f (by omega) (by simp) (by simp)
  have hR1 := hR.frame t1f (by omega) (by simp) (by simp)
  have fr : ∀ X, (X = NODE + 32 ∨ X = NODE + 40) → t2.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [t2f.get hX' (by simp only [NODE] at hX ⊢; omega), t1f.get hX' (by simp),
      ht.frame.get hX' (by unfold LevW; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have hq : hashInput t2 = toQ (pad64 (bytesLE 16 ((levels.getD ℓ []).getD (2 * i) 0) ++
      bytesLE 16 (header B.tag B.lay B.tree 0 (lo + i)) ++ zero16 ++
      bytesLE 16 ((levels.getD ℓ []).getD (2 * i + 1) 0))) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length])]
    refine hashInput_toQ t2 _ 0 NODE (nodeInput_length _ _ _ _ _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_nodeInput _ _ _ _ _ _ (by rcases hpre.tag3 with h | h <;> rw [h] <;> decide), readWords_eight, t2n0, t2n8, t2n16, t2n24, fr (NODE + 32) (by simp),
      fr (NODE + 40) (by simp), t2n48, t2n56, hpre.z32, hpre.z40, hL1.1, hL1.2, hR1.1, hR1.2,
      t1r.get (by simp), r21, hdr0_or_tree B.tag B.lay B.tree hpre.htree]
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by simp), t1r.get (by simp), r5]
  have hblk : (toQ (pad64 (bytesLE 16 ((levels.getD ℓ []).getD (2 * i) 0) ++
      bytesLE 16 (header B.tag B.lay B.tree 0 (lo + i)) ++ zero16 ++
      bytesLE 16 ((levels.getD ℓ []).getD (2 * i + 1) 0)))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length]),
      blocks_toQ ⟨by rw [nodeInput_length]; omega, by rw [nodeInput_length]⟩, nodeInput_length]
  unfold nodeHash
  rw [hk']
  refine (TSim.steps (st1.trans st2)
    ((TSim.shortHash_bind (k := 10) (c := 10) (n := 0) (b := 0) (f := Pure.pure)
      (fetch_sub146 hsub t2 t2pc) h5 hv hq (fun a => ?_)).of_eq (bind_pure _) rfl rfl rfl rfl)).of_eq
    rfl ?_ ?_ ?_ ?_
  · have hwf := Frame.writeHash t2 a NOUT t2x12 (by decide)
    obtain ⟨u, st3, upc, ux24, um0, um8, ur, uf⟩ := sub147_spec hsub (writeHash t2 a)
      (by rw [pc_writeHash, t2pc, pcOf_add4]) B.arena (lo + i) ha8 (by omega)
      (by sc_omega)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact r2)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x24)
    have hlo := DigAt.writeHash_lo t2 a NOUT t2x12 (by decide)
    have hnew : DigAt u (B.arena + 16 * (lo + i)) (a.extractLsb' 0 128) := ⟨um0.trans hlo.1, by
      rw [um8]; exact hlo.2⟩
    have fall : Frame t u (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨
        X = NODE + 48 ∨ X = NODE + 56) ∨ (NOUT ≤ X ∧ X < NOUT + 32) ∨
        (X = B.arena + 16 * (lo + i) ∨ X = B.arena + 16 * (lo + i) + 8)) :=
      ((t1f.trans t2f).trans (hwf.trans uf)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; left; exact h
        · right; right; exact h)
    refine TSim.pure_steps st3 ⟨upc, ⟨?_, ?_, ?_, ?_, ⟨hlen, fun l hl' => ?_⟩, ?_⟩⟩
    · rw [ur.get (by simp), getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x20
    · rw [ux24, List.length_append, List.length_singleton]; congr 1
    · have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
      exact (ht.regs.trans (((t1r.trans t2r).trans hw0).trans ur)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      unfold LevW at *
      rcases h with h | (h | h | h)
      · exact h
      · rcases h with h | h | h | h | h | h <;> simp_all
      · right; right; right; right; right; right; left; exact h
      · right; right; right; right; right; right; right; simp only [NODE, NOUT] at has; omega
    · obtain ⟨hl1, hl2⟩ := hlev l hl'
      have hYl : 2 * lo ≤ 2 ^ (B.h - l) := by
        rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hYlZ : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
      rw [hl1] at h2
      simp only [NODE, NOUT] at h has
      omega
    · refine (ht.cur.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
      · simp only [NODE, NOUT] at h has
        omega
      · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hnew
  all_goals (try rw [hblk])
  all_goals (first | rfl | omega)

/-- One level `ℓ + 1` (`lo = 2^(h-ℓ-1)` nodes) from `lv_level`. -/
theorem lev_level {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {t : MachineState}
    (ht : LevInv s0 B ℓ levels t) (hpc : t.pc = pcOf (b + 116)) :
    TSim image sk t (6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - ℓ)) (6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (do let nodes ← buildLevel B.tag B.lay B.tree B.h (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = pcOf (b + 116) ∧ LevInv s0 B (ℓ + 1) levels' u) := by
  have hh := hpre.hh
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hlo_def, show B.h = (ℓ + 1) + (B.h - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (B.h - 1 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec hsub t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec hsub t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : NodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1]
        have := hpre.ha
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), r20]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    rw [show 1 + ℓ - 1 = ℓ by omega, (ht.heap.2 ℓ le_rfl).1, hY]; omega
  unfold buildLevel
  rw [hnodes]
  refine (TSim.steps (st1.trans st2) (TSim.bind (k₂ := 4) (c₂ := 4) (n₂ := 0) (b₂ := 0)
    (TSim.mapM_range lo _ (fun _ => 39 + revX B.tag) (fun _ => 46 + revX B.tag) (fun _ => 1) (fun _ => 1)
      (fun pre w => w.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => ?_) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · rw [show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega]
    exact lev_node hsub sk hpre hl hpre' hw.2 hw.1
  · obtain ⟨hlen, wpc, hw⟩ := hw
    obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec hsub w wpc lo (lo + nodes.length) (by omega) (by omega)
      hw.x20 (by rw [hw.x24])
    rw [if_neg (by omega)] at w1pc
    obtain ⟨w2, st4, w2pc, w2x20, w2r, w2f⟩ := sub157_spec hsub w1 w1pc lo (by omega)
      (by rw [w1r.get (by simp)]; exact hw.x20)
    have f12 : Frame w w2 (fun _ => False) := (w1f.trans w2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps (st3.trans st4) ⟨w2pc, ?_, ?_, ?_, ?_⟩
    · rw [w2x20, hx20']
    · exact (hw.regs.trans (w1r.trans w2r)).mono (by decide)
    · exact (hw.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · obtain ⟨hlen0, hlev⟩ := hw.heap
      refine ⟨by simp [hlen0], fun l hl' => ?_⟩
      have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
      have := hpre.ha
      by_cases hle : l ≤ ℓ
      · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
        rw [hg]
        obtain ⟨h1, h2⟩ := hlev l hle
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
      · have hl2 : l = ℓ + 1 := by omega
        subst hl2
        have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
          simp [List.getD_eq_getElem?_getD, hlen0]
        rw [hg, show B.h - (ℓ + 1) = B.h - ℓ - 1 by omega]
        have : lo ≤ 2 ^ B.h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show B.h - ℓ - 1 ≤ B.h by omega)
          omega
        exact ⟨hlen, hw.cur.frame f12 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [sumTo_const, hl1]
  all_goals (first | omega | ring)

/-- **`build_levels`** (any image holding the shared code at base `b`): from the entry (offset 113)
with the `2^h` leaves at heap indices `2^h ..`, the machine refines Core's
`buildLevels tag lay tree h leaves` exactly and returns to `B.ret` with every level in the heap. -/
theorem buildLevels_tsim (hpc : s0.pc = pcOf (b + 113)) :
    TSim image sk s0 B.levK B.levC B.levN B.levN (buildLevels B.tag B.lay B.tree B.h leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B B.h levels ∧ RegsExcept s0 t levRegs ∧
        Frame s0 t (LevW B)) := by
  have hh := hpre.hh
  have hh1 := hpre.hh1
  have ha := hpre.ha
  have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  obtain ⟨t1, st1, t1pc, t1x20, t1r, t1f⟩ := sub113_spec hsub s0 hpc B.h hh1 (by omega) hpre.x15
  have h0 : LevInv s0 B 0 [leaves] t1 := by
    refine ⟨?_, t1r.mono (by decide), t1f.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    · rw [t1x20]; congr 1
      rw [show B.h = 1 + (B.h - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _ (by norm_num)]
      congr 1; omega
    · have hl0 : l = 0 := by omega
      subst hl0
      simp only [List.getD_cons_zero, Nat.sub_zero]
      exact ⟨hpre.hlen, hpre.hleaves.frame t1f (by rw [hpre.hlen]; omega) (fun X _ _ h => h.elim)⟩
  unfold buildLevels
  refine (TSim.steps st1 (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) (f := Pure.pure)
    (TSim.foldlM_range' 1 B.h _ [leaves]
      (fun j levels t => t.pc = pcOf (b + 116) ∧ LevInv s0 B j levels t)
      (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 2 ^ (B.h - 1 - j)) (fun j => 2 ^ (B.h - 1 - j))
      (fun j hj levels t ht => lev_level hsub sk hpre hj ht.2 ht.1) ⟨t1pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) ?_ ?_ ?_ ?_
  · obtain ⟨tpc, hinv⟩ := ht
    have hx : 2 ^ B.h / 2 ^ (B.h + 1) = 0 := Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    obtain ⟨u1, st2, u1pc, u1r, u1f⟩ := sub116_spec hsub t tpc 0 (by omega) (by rw [hinv.x20, hx])
    rw [if_pos rfl] at u1pc
    obtain ⟨u2, st3, u2pc, u2r, u2f⟩ := sub159_spec hsub u1 u1pc B.ret
      (by rw [u1r.get (by simp), hinv.regs.get (by simp [levRegs]), hpre.x1])
    have f12 : Frame t u2 (fun _ => False) := (u1f.trans u2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps (st2.trans st3) ⟨u2pc, ⟨hinv.heap.1, fun l hl => ?_⟩,
      (hinv.regs.trans (u1r.trans u2r)).mono (by decide),
      (hinv.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    obtain ⟨h1, h2⟩ := hinv.heap.2 l hl
    have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [LevArgs.levK, LevArgs.levC, LevArgs.levN]
  all_goals omega

end lev

end SigGolfCandidate.T3M.Keygen
