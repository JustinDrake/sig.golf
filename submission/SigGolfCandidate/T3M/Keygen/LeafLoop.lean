import SigGolfCandidate.T3M.Keygen.Leaf
import SigGolfCandidate.T3M.Keygen.Tree
import SigGolfCandidate.T3M.Keygen.Init

/-!
# The keygen top tree: `buildTree 0 0 0 []`

The leaf loop (`kg_leaf`, words 26..36) runs `build_leaf` for the leaves `0 .. 4095` with
`kgLeaf j` (no digits, values to `DUMMY`, root to heap node `4096 + j`); then `build_levels`
(`kgLev`: tag 3, height 12, arena `TOP`) returns to word 39 with every level in the heap.

`buildTree_tsim` : from `KStart`, exactly `29,704,235` steps, `37,072,932` cycles, `987,135` calls
and `1,044,479` compressions.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeaf buildLevels buildTree height chainCount width)

/-- The arguments of keygen leaf `j`. -/
def kgLeaf (j : Nat) : LeafArgs := ⟨0, 0, j, [], false, ZDIG, DUMMY, TOP + 16 * (4096 + j), 34⟩

/-- The arguments of the top-tree `build_levels` call. -/
def kgLev : LevArgs := ⟨3, 0, 0, 12, TOP, 39⟩

theorem kgLeaf_n (j : Nat) : (kgLeaf j).n = 54 := rfl

theorem kgLeaf_costs (j : Nat) : (kgLeaf j).leafK = 7259 ∧ (kgLeaf j).leafC = 9050 ∧
    (kgLeaf j).leafN = 241 ∧ (kgLeaf j).leafB = 254 := by
  have e : (kgLeaf j).leafK = (kgLeaf 0).leafK ∧ (kgLeaf j).leafC = (kgLeaf 0).leafC ∧
      (kgLeaf j).leafN = (kgLeaf 0).leafN ∧ (kgLeaf j).leafB = (kgLeaf 0).leafB := ⟨rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  decide

theorem kgLev_costs : kgLev.levK = 159782 ∧ kgLev.levC = 188447 ∧ kgLev.levN = 4095 := by decide

/-- The doublewords the leaf loop may change. -/
def W1 (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 880) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 864) ∨ (TOP + 65536 ≤ X ∧ X < TOP + 131072)

/-- The registers the leaf loop may change. -/
def loopRegs : List Reg := leafRegs ++ [.x18, .x25]

/-- At `kg_leaf` (word 26) after the leaves `0 .. j-1`, Core state `st = (roots, values)`. -/
structure LoopInv (s1 : MachineState) (j : Nat) (st : List Digest × List Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 26
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  regs : RegsExcept s1 t loopRegs
  frame : Frame s1 t W1
  len : st.1.length = j
  roots : DigsAt t (TOP + 65536) st.1

theorem extractByte_zero (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]

section loop
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs

theorem loopInv_zero : LoopInv s1 0 ([], []) s1 :=
  ⟨hs.pc, hs.x18, RegsExcept.refl _ _, Frame.refl _ _, rfl, DigsAt.nil _ _⟩

/-- The entry conditions of `build_leaf` for leaf `j`. -/
theorem kgLeaf_pre {j : Nat} (hj : j < 4096) {t : MachineState} (hr : RegsExcept s1 t loopRegs)
    (hf : Frame s1 t W1) (h18 : t.getReg .x18 = BitVec.ofNat 64 j) (h1 : t.getReg .x1 = pcOf 34)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 DUMMY)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 (TOP + 16 * (4096 + j))) :
    LeafPre sk t (kgLeaf j) := by
  have g : ∀ r, r ∉ loopRegs → t.getReg r = s1.getReg r := fun r hr' => hr.get hr'
  have m : ∀ X, X < 2 ^ 64 → ¬ W1 X → t.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => hf.get hX hn
  have z : ∀ X, X < 2 ^ 64 → ¬ W1 X → (X < 0x80 ∨ 0xA0 ≤ X) → (X < PRIV ∨ PRIV + 64 ≤ X) →
      t.getMem (BitVec.ofNat 64 X) = 0 := fun X hX hn h1 h2 => (m X hX hn).trans (hs.zero X hX h1 h2)
  refine
    { x1 := h1
      x5 := by rw [g _ (by decide), hs.x5]
      x8 := by rw [g _ (by decide), hs.x8]; rfl
      x9 := by rw [g _ (by decide), hs.x9]; rfl
      x18 := h18
      x22 := by rw [g _ (by decide), hs.x22]; rfl
      x23 := h23
      x25 := h25
      x26 := by rw [g _ (by decide), hs.x26]; rfl
      x27 := by rw [g _ (by decide), hs.x27]; rfl
      x31 := by rw [g _ (by decide), hs.x31]; rfl
      htree := show 0 < 2 ^ 32 by norm_num
      hleaf := by show j < 2 ^ 32; omega
      p0 := by rw [m _ (by decide) (by unfold W1; decide), hs.p0]
      p8 := by rw [m _ (by decide) (by unfold W1; decide), hs.p8]
      p32 := by rw [m _ (by decide) (by unfold W1; decide), hs.p32]
      p40 := by rw [m _ (by decide) (by unfold W1; decide), hs.p40]
      p48 := by rw [m _ (by decide) (by unfold W1; decide), hs.p48]
      p56 := by rw [m _ (by decide) (by unfold W1; decide), hs.p56]
      z0 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      z8 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      z32 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      z40 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      ztail := fun _ => ⟨z _ (by decide) (by unfold W1; decide) (by decide) (by decide),
        z _ (by decide) (by unfold W1; decide) (by decide) (by decide)⟩
      hdig := fun i hi => by
        rw [kgLeaf_n] at hi
        have hw : ¬ W1 ((ZDIG + i) / 8 * 8) := by unfold W1; kg_omega
        show t.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0
        rw [hf.getByte (by kg_omega) hw, getByte_eq_word s1 _ (by kg_omega),
          hs.zero _ (by kg_omega) (by kg_omega) (by kg_omega), extractByte_zero]
        rfl
      hdigb := fun i _ => ⟨by show [].getD i 0 < 256; simp, fun _ => by show [].getD i 0 ≤ _; simp⟩
      hdigp := by show ZDIG + 54 ≤ 2 ^ 24; decide
      hdigW := fun i hi => by
        rw [kgLeaf_n] at hi
        unfold LeafW
        rw [kgLeaf_n]
        dsimp only [kgLeaf]
        kg_omega
      hv8 := show DUMMY % 8 = 0 by decide
      hv := by show DUMMY + 16 * 54 ≤ 2 ^ 24; decide
      hvs := Or.inr (by show LEAFPK + 960 ≤ DUMMY; decide)
      hd8 := by show (TOP + 16 * (4096 + j)) % 8 = 0; kg_omega
      hd := by show TOP + 16 * (4096 + j) + 16 ≤ 2 ^ 24; kg_omega
      hds := Or.inr (Or.inl (by show LEAFPK + 960 ≤ TOP + 16 * (4096 + j); kg_omega))
      hdv := Or.inr (by show DUMMY + 16 * 54 ≤ TOP + 16 * (4096 + j); kg_omega) }

/-- One leaf: `kg_leaf`, the call, `build_leaf`, `LEAF += 1`. -/
theorem leafLoop_body {j : Nat} (hj : j < 4096) (acc : List Digest × List Digest) (t : MachineState)
    (ht : LoopInv s1 j acc t) :
    TSim image sk t 7269 9060 241 254
      (do
        let (root, values) ← buildLeaf 0 0 j (if j = 0 then [] else [])
        pure (acc.1 ++ [root], if j = 0 then values else acc.2))
      (LoopInv s1 (j + 1)) := by
  rw [ite_self]
  have g : ∀ r, r ∉ loopRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk26_spec t ht.pc j (by omega) ht.x18
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x23, t2x25, t2r, t2f⟩ := blk28_spec t1 t1pc j
    (by rw [t1r.get (by decide)]; exact ht.x18) t1x6
    (by rw [t1r.get (by decide), g _ (by decide), hs.x2])
  have r12 : RegsExcept t t2 [.x6, .x1, .x7, .x23, .x25] := t1r.trans t2r
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp at h)
  have hpre : LeafPre sk t2 (kgLeaf j) :=
    kgLeaf_pre hs hj ((ht.regs.trans r12).mono (by decide)) ((ht.frame.trans f12).mono
      (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
      (by rw [r12.get (by decide)]; exact ht.x18) t2x1 t2x23 t2x25
  have hleaf := buildLeaf_tsim subAt_keygen sk hpre t2pc
  obtain ⟨cK, cC, cN, cB⟩ := kgLeaf_costs j
  rw [cK, cC, cN, cB] at hleaf
  refine (TSim.steps st1 (TSim.steps st2 (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) hleaf
    (fun r u hu => ?_)))).of_eq rfl rfl rfl rfl rfl
  obtain ⟨upc, uroot, -, -, ur, uf⟩ := hu
  obtain ⟨root, values⟩ := r
  obtain ⟨t3, st3, t3pc, t3x18, t3r, t3f⟩ := blk34_spec u upc j
    (by rw [ur.get (by decide), r12.get (by decide)]; exact ht.x18)
  refine TSim.pure_steps st3 ⟨t3pc, t3x18, ?_, ?_, by simp [ht.len], ?_⟩
  · exact (((ht.regs.trans r12).trans ur).trans t3r).mono (by decide)
  · refine (((ht.frame.trans f12).trans uf).trans t3f).mono (fun X _ h => ?_)
    rcases h with ((h | h) | h) | h
    · exact h
    · exact h.elim
    · unfold LeafW at h
      simp only [kgLeaf_n] at h
      unfold W1
      change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨
        X = CHAIN + 24 ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * (54 + 1)) ∨
        (LOUT ≤ X ∧ X < LOUT + 32) ∨ (DUMMY ≤ X ∧ X < DUMMY + 16 * 54) ∨
        (TOP + 16 * (4096 + j) ≤ X ∧ X < TOP + 16 * (4096 + j) + 16) at h
      kg_omega
    · exact h.elim
  · have hd : DigAt u (TOP + 65536 + 16 * acc.1.length) root := by
      rw [ht.len, show TOP + 65536 + 16 * j = TOP + 16 * (4096 + j) by kg_omega]
      exact uroot rfl
    have hold : DigsAt u (TOP + 65536) acc.1 := by
      refine ht.roots.frame ((f12.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; kg_omega) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h
      · exact h
      · unfold LeafW at h
        simp only [kgLeaf_n] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨
          B = CHAIN + 24 ∨ (CHAIN + 48 ≤ B ∧ B < CHAIN + 80) ∨ (LEAFPK ≤ B ∧ B < LEAFPK + 16 * (54 + 1)) ∨
          (LOUT ≤ B ∧ B < LOUT + 32) ∨ (DUMMY ≤ B ∧ B < DUMMY + 16 * 54) ∨
          (TOP + 16 * (4096 + j) ≤ B ∧ B < TOP + 16 * (4096 + j) + 16) at h
        kg_omega
    exact (hold.snoc hd).frame t3f (by simp only [List.length_append, List.length_singleton, ht.len]; kg_omega)
      (fun _ _ _ h => h)

/-- The registers `buildTree` may change. -/
def treeRegs : List Reg := loopRegs ++ [.x6] ++ [.x1, .x15, .x21] ++ levRegs

/-- **The keygen top tree** `buildTree 0 0 0 []`: the 4096 leaves, then `build_levels`. -/
theorem buildTree_tsim :
    TSim image sk s1 29933611 37298212 991231 1044479 (buildTree 0 0 0 [])
      (fun r t => t.pc = pcOf 39 ∧ HeapAt t kgLev 12 r.1 ∧ RegsExcept s1 t treeRegs ∧
        Frame s1 t (fun X => W1 X ∨ LevW kgLev X)) := by
  unfold buildTree
  refine (TSim.bind (k₂ := 159787) (c₂ := 188452) (n₂ := 4095) (b₂ := 4095)
    (TSim.foldlM_range 4096 _ _ (LoopInv s1) (fun _ => 7269) (fun _ => 9060)
    (fun _ => 241) (fun _ => 254) (fun j hj acc t ht => leafLoop_body hs hj acc t ht) (loopInv_zero hs))
    (fun st t ht => ?_)).of_eq rfl ?_ ?_ ?_ ?_
  rotate_left
  · rw [sumTo_const]
  · rw [sumTo_const]
  · rw [sumTo_const]
  · rw [sumTo_const]
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk26_spec t ht.pc 4096 (by norm_num) ht.x18
  rw [if_neg (by norm_num)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x15, t2x21, t2r, t2f⟩ := blk36_spec t1 t1pc
  have r02 : RegsExcept s1 t2 (loopRegs ++ [.x6] ++ [.x1, .x15, .x21]) := (ht.regs.trans t1r).trans t2r
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp at h)
  have f02 : Frame s1 t2 W1 := (ht.frame.trans f12).mono
    (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have hpre : LevPre t2 kgLev st.1 :=
    { x1 := t2x1
      x2 := by rw [r02.get (by decide), hs.x2]; rfl
      x5 := by rw [r02.get (by decide), hs.x5]
      x9 := by rw [r02.get (by decide), hs.x9]; rfl
      x15 := t2x15
      x21 := by rw [t2x21]; decide
      tag3 := Or.inl rfl
      htree := show 0 < 2 ^ 32 by norm_num
      hh1 := show 1 ≤ 12 by norm_num
      hh := show 12 ≤ 12 by norm_num
      ha8 := show TOP % 8 = 0 by decide
      ha := show TOP + 16 * 2 ^ (12 + 1) ≤ 2 ^ 24 by decide
      has := Or.inl (show NOUT + 32 ≤ TOP by decide)
      z32 := by
        rw [f02.get (by decide) (by unfold W1; decide)]
        exact hs.zero _ (by decide) (by decide) (by decide)
      z40 := by
        rw [f02.get (by decide) (by unfold W1; decide)]
        exact hs.zero _ (by decide) (by decide) (by decide)
      hlen := ht.len
      hleaves := ht.roots.frame f12 (by rw [ht.len]; decide) (fun _ _ _ h => h) }
  have hlev := buildLevels_tsim subAt_keygen sk hpre t2pc
  rw [kgLev_costs.1, kgLev_costs.2.1, kgLev_costs.2.2] at hlev
  exact TSim.steps st1 (TSim.steps st2 (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) hlev
    (fun levels u hu => TSim.pure ⟨hu.1, hu.2.1, r02.trans hu.2.2.1, f02.trans hu.2.2.2⟩)))

end loop

end SigGolfCandidate.T3M.Keygen
