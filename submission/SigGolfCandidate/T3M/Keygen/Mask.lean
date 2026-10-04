import SigGolfCandidate.T3M.Keygen.Leaf
import SigGolfCandidate.T3M.Keygen.Tree
import SigGolfCandidate.T3M.Keygen.Init
import SigGolfCandidate.T3M.Keygen.MainBlocks

section



namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeaf buildLevels buildTree height chainCount width)
def kgLeaf (j : Nat) : LeafArgs := ⟨0, 0, j, [], false, ZDIG, DUMMY, TOP + 16 * (4096 + j), 34⟩
def kgLev : LevArgs := ⟨3, 0, 0, 12, TOP, 39⟩
theorem kgLeaf_n (j : Nat) : (kgLeaf j).n = 54 := rfl
theorem kgLeaf_costs (j : Nat) : (kgLeaf j).leafK = 10667 ∧ (kgLeaf j).leafC = 12458 ∧
    (kgLeaf j).leafN = 241 ∧ (kgLeaf j).leafB = 254 := by
  have e : (kgLeaf j).leafK = (kgLeaf 0).leafK ∧ (kgLeaf j).leafC = (kgLeaf 0).leafC ∧
      (kgLeaf j).leafN = (kgLeaf 0).leafN ∧ (kgLeaf j).leafB = (kgLeaf 0).leafB := ⟨rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  decide
theorem kgLev_costs : kgLev.levK = 159782 ∧ kgLev.levC = 188447 ∧ kgLev.levN = 4095 := by decide
def W1 (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 880) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 864) ∨ (TOP + 65536 ≤ X ∧ X < TOP + 131072)
def loopRegs : List Reg := leafRegs ++ [.x18, .x25]
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
      hroute := by change 0 * 2 ^ 12 + j < 2 ^ 31; omega
      hleafHeight := hj
      hsteps := fun i _ => by
        change T3.maxDigit 0 i ≤ 8
        unfold T3.maxDigit
        split_ifs <;> omega
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
theorem leafLoop_body {j : Nat} (hj : j < 4096) (acc : List Digest × List Digest) (t : MachineState)
    (ht : LoopInv s1 j acc t) :
    TSim image sk t 10677 12468 241 254
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
def treeRegs : List Reg := loopRegs ++ [.x6] ++ [.x1, .x15, .x21] ++ levRegs
theorem buildTree_tsim :
    TSim image sk s1 43892779 51257380 991231 1044479 (buildTree 0 0 0 [])
      (fun r t => t.pc = pcOf 39 ∧ HeapAt t kgLev 12 r.1 ∧ RegsExcept s1 t treeRegs ∧
        Frame s1 t (fun X => W1 X ∨ LevW kgLev X)) := by
  unfold buildTree
  refine (TSim.bind (k₂ := 159787) (c₂ := 188452) (n₂ := 4095) (b₂ := 4095)
    (TSim.foldlM_range 4096 _ _ (LoopInv s1) (fun _ => 10677) (fun _ => 12468)
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
end

section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem blk277_spec (s : MachineState) (hpc : s.pc = pcOf 277) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 289 ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧ t.getReg .x22 = 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 REGION ∧
      t.getMem (BitVec.ofNat 64 0xA0) = s.getMem (BitVec.ofNat 64 (TOP+16)) ∧
      t.getMem (BitVec.ofNat 64 0xA8) = s.getMem (BitVec.ofNat 64 (TOP+24)) ∧
      RegsExcept s t [.x2,.x6,.x7,.x20,.x22,.x24,.x30] ∧
      Frame s t (fun A => A=0xA0 ∨ A=0xA8) := by
  refine ⟨_,symRun_sound blk_277 codeAt_277 s hpc (by simp [blk_277.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_277.res,E.eval]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp,REGION]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_277.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,blk_277.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem blk289_spec (s : MachineState) (hpc : s.pc = pcOf 289) (lo : Nat)
    (hlo : lo ≤ 4096) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 295 ∧ t.getReg .x23 = 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x21 = BitVec.ofNat 64 (TOP+16*lo) ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      RegsExcept s t [.x2,.x21,.x23,.x26] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_289 codeAt_289 s hpc (by simp [blk_289.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_289.res,E.eval]
  · simp [blk_289.res,rv_simp]
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    congr 1; unfold TOP; omega
  · simp [blk_289.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_289.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_289.res,rv_simp]
theorem blk295_spec (s : MachineState) (hpc : s.pc = pcOf 295) (level i : Nat)
    (hlev : level < 2^32) (hi : i < 2^32)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 309 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 level) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  refine ⟨_,symRun_sound blk_295 codeAt_295 s hpc (by simp [blk_295.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_295.res,E.eval]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp,MOUT]
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h22]
    rw [ofNat_or_disjoint' 3329 (level*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 level (by norm_num) (by norm_num) (by norm_num) hlev]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h23]
    rw [hdr1_eq 0 i (by norm_num) hi]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_295.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_295.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem fetch_309 (s : MachineState) (hpc : s.pc = pcOf 309) :
    fetch image s = some (.base .ECALL) := (codeAt_309.fetch s hpc).trans rfl
theorem blk330_spec (s : MachineState) (hpc : s.pc = pcOf 330) (lo level : Nat)
    (hlo : lo ≤ 4096) (hl : level < 12)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if level+1<12 then pcOf 289 else pcOf 334) ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧ t.getReg .x22 = BitVec.ofNat 64 (level+1) ∧
      RegsExcept s t [.x6,.x20,.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_330 codeAt_330 s hpc (by simp [blk_330.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_330.res,E.eval,CmpOp.eval,h22]
    have hx : (BitVec.ofNat 64 level+1#64).toNat=level+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,BinOp.eval,hx]
    rfl
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_330.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_330.res,rv_simp]
theorem blk310_spec (s : MachineState) (hpc : s.pc = pcOf 310)
    (nodep endp i cap : Nat)
    (hn0 : TOP ≤ nodep) (hn : nodep+32 ≤ 0x70000) (hn8 : nodep%8=0)
    (he0 : REGION ≤ endp) (he : endp+32 ≤ 0xA0000) (he8 : endp%8=0)
    (hi : i < 4096) (hc : cap ≤ 4096)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 nodep)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 endp)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 cap)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = (if i+1<cap then pcOf 295 else pcOf 330) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (endp+8*j.val)) =
        s.getMem (BitVec.ofNat 64 (nodep+8*j.val)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+8*j.val))) ∧
      t.getReg .x21 = BitVec.ofNat 64 (nodep+32) ∧
      t.getReg .x24 = BitVec.ofNat 64 (endp+32) ∧
      t.getReg .x23 = BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x6,.x7,.x21,.x23,.x24] ∧
      Frame s t (fun A => A=endp ∨ A=endp+8 ∨ A=endp+16 ∨ A=endp+24) := by
  have hobl : Oblig.all s blk_310.res.st.obl := by
    simp only [blk_310.res]
    t3n [h21,h24,h12]
    simp only [TOP,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    norm_num [Nat.add_mod,hn8,he8] <;> omega
  refine ⟨_,symRun_sound blk_310 codeAt_310 s hpc hobl,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_310.res,E.eval,CmpOp.eval,BinOp.eval,h23,h26]
    have hx : (BitVec.ofNat 64 i+1#64).toNat=i+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show cap<2^64 by omega)]
  · intro j
    fin_cases j <;> simp only [Fin.val_mk,Nat.reduceMul,Nat.add_zero,
      Result.toState_getMem,blk_310.res,MOUT] <;>
      t3n [h21,h24,h12] <;>
      (simp only [TOP,REGION,MOUT] at *; split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h21]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_310.res,rv_simp] <;> rfl
  · intro A hA hnot
    simp only [Result.toState_getMem,blk_310.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen
end

section


namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest pairedMask maskedLevel header privateInput)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem TSim.post_steps {α : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {k c n b k' c' : Nat}
    {p : T3.M α} {Q Q' : α → MachineState → Prop} (h : TSim image sk s k c n b p Q)
    (hs : ∀ a t, Q a t → ∃ u, Steps image t k' c' u ∧ Q' a u) :
    TSim image sk s (k + k') (c + c') n b p Q' :=
  (TSim.bind (k₂ := k') (c₂ := c') (n₂ := 0) (b₂ := 0) (f := fun a => (Pure.pure a : T3.M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TSim.pure_steps hu hq)).of_eq (bind_pure p)
    rfl rfl (Nat.add_zero n) (Nat.add_zero b)
def MW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (MOUT ≤ X ∧ X < MOUT + 32) ∨ (REGION ≤ X ∧ X < REGION + 131040)
def maskRegs : List Reg := [.x2, .x6, .x7, .x10, .x11, .x12, .x20, .x21, .x22, .x23, .x24, .x26, .x28]
structure MaskPre (sk : SecretKey) (s : MachineState) (levels : List (List Digest)) : Prop where
  pc : s.pc = pcOf 289
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = 0
  x20 : s.getReg .x20 = BitVec.ofNat 64 4096
  x24 : s.getReg .x24 = BitVec.ofNat 64 REGION
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  nodes : ∀ l, l ≤ 11 → (levels.getD l []).length = 2 ^ (12 - l) ∧
    DigsAt s (TOP + 16 * 2 ^ (12 - l)) (levels.getD l [])
structure LevelInv (s4 : MachineState) (pre : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if pre.length < 12 then pcOf 289 else pcOf 334
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * pre.flatten.length)
  flen : pre.flatten.length + 2 ^ (13 - pre.length) = 8192
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION pre.flatten
structure MaskInv (s4 : MachineState) (pre cur : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if cur.length < 2 ^ (11 - pre.length) then pcOf 295 else pcOf 330
  x23 : t.getReg .x23 = BitVec.ofNat 64 cur.length
  x26 : t.getReg .x26 = BitVec.ofNat 64 (2 ^ (11 - pre.length))
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x21 : t.getReg .x21 = BitVec.ofNat 64 (TOP + 16 * (2 ^ (12 - pre.length) + 2 * cur.length))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * (pre.flatten.length + cur.flatten.length))
  flen : cur.flatten.length = 2 * cur.length
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION (pre.flatten ++ cur.flatten)
theorem two_pow_twelve_sub {j : Nat} (hj : j < 12) :
    2 ≤ 2 ^ (12-j) ∧ 2 ^ (12-j) ≤ 4096 ∧ 1 ≤ 2 ^ (11-j) ∧
    2 ^ (12-j) = 2 * 2 ^ (11-j) ∧
    2 ^ (13-j) = 2 * 2 ^ (12-j) ∧
    2 ^ (12-(j+1)) = 2 ^ (12-j) / 2 ∧
    2 ^ (13-(j+1)) = 2 ^ (12-j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (12-j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ (12-j) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4096 := by norm_num
  · exact Nat.one_le_pow _ _ (by decide)
  · rw [show 12-j=(11-j)+1 by omega, pow_succ]; ring
  · rw [show 13-j=(12-j)+1 by omega, pow_succ]; ring
  · rw [show 12-j=(12-(j+1))+1 by omega, pow_succ]; omega
  · congr 1; omega
section masks
variable {sk : SecretKey} {s4 : MachineState} {levels : List (List Digest)} (hm : MaskPre sk s4 levels)
include hm
theorem mask_one {pre : List (List Digest)} (hpl : pre.length < 12) {cur : List (List Digest)}
    (hcl : cur.length < 2 ^ (11 - pre.length))
    (hfl : pre.flatten.length + 2 ^ (13 - pre.length) = 8192) {t : MachineState}
    (ht : MaskInv s4 pre cur t) :
    TSim image sk t 35 42 1 1
      (do
        let values ← pairedMask pre.length cur.length
        pure [(levels.getD pre.length []).getD (2*cur.length) 0 ^^^ values.1,
          (levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ values.2])
      (fun ds u => MaskInv s4 pre (cur ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, -, -⟩ := two_pow_twelve_sub hpl
  have g : ∀ r, r ∉ maskRegs → t.getReg r = s4.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2a, t2b, t2r, t2f⟩ :=
    blk295_spec t (by simpa only [if_pos hcl] using ht.pc) pre.length cur.length
      (by omega) (by omega) ht.x22 ht.x23
  have fr : ∀ X, (X = PRIV ∨ X = PRIV+8 ∨ X = PRIV+32 ∨ X = PRIV+40 ∨ X = PRIV+48 ∨ X = PRIV+56) →
      t2.getMem (BitVec.ofNat 64 X) = s4.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (t2f.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (by kg_omega)).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
        (by unfold MW; kg_omega))
  have hq : hashInput t2 = toQ (privateInput sk (.inl (header 13 0 0 pre.length cur.length))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide)
      t2x11 (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV+8) (by simp), t2a, t2b, fr (PRIV+32) (by simp), fr (PRIV+40) (by simp),
      fr (PRIV+48) (by simp), fr (PRIV+56) (by simp), hm.p0, hm.p8, hm.p32, hm.p40, hm.p48, hm.p56]
    rfl
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by decide), g _ (by decide), hm.x5]
  unfold pairedMask
  refine (TSim.steps st2 (TSim.privatePair_bind (k := 20) (c := 20) (n := 0) (b := 0)
    (fetch_309 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc = pcOf 310 := by rw [pc_writeHash, t2pc, pcOf_add4]
  have hmo0 := DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
  have hmo1 := DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have fsu := ht.frame.trans (t2f.trans hwf)
  obtain ⟨hlen, hds⟩ := hm.nodes pre.length (by omega)
  have hnode (i : Nat) (hi : i < 2 ^ (12-pre.length)) :
      DigAt (writeHash t2 a) (TOP + 16 * (2 ^ (12-pre.length)+i)) ((levels.getD pre.length []).getD i 0) := by
    have hn := hds.get (show i < _ by rw [hlen]; exact hi)
    rw [show TOP+16*2^(12-pre.length)+16*i=TOP+16*(2^(12-pre.length)+i) by ring] at hn
    exact hn.frame fsu (by kg_omega) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  have hn0 := hnode (2*cur.length) (by omega)
  have hn1 := hnode (2*cur.length+1) (by omega)
  have rw2 : RegsExcept t (writeHash t2 a) [.x6, .x7, .x10, .x11, .x12, .x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hcf := ht.flen
  obtain ⟨t3, st3, t3pc, t3mem, t3x21, t3x24, t3x23, t3r, t3f⟩ :=
    blk310_spec (writeHash t2 a) upc
      (TOP+16*(2^(12-pre.length)+2*cur.length))
      (REGION+16*(pre.flatten.length+cur.flatten.length)) cur.length (2^(11-pre.length))
      (by kg_omega) (by kg_omega) (by kg_omega)
      (by kg_omega) (by kg_omega) (by kg_omega) (by omega) (by omega)
      (by rw [rw2.get (by decide)]; exact ht.x21)
      (by rw [rw2.get (by decide)]; exact ht.x24)
      (by rw [rw2.get (by decide)]; exact ht.x23)
      (by rw [rw2.get (by decide)]; exact ht.x26) (by rw [getReg_writeHash]; exact t2x12)
  have t3a := t3mem ⟨0,by decide⟩
  have t3b := t3mem ⟨1,by decide⟩
  have t3c := t3mem ⟨2,by decide⟩
  have t3d := t3mem ⟨3,by decide⟩
  simp only [Fin.val_mk, Nat.reduceMul, Nat.add_zero] at t3a t3b t3c t3d
  have r23 := rw2.trans t3r
  refine TSim.pure_steps st3 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using t3pc
  · rw [t3x23, List.length_append, List.length_singleton]
  · rw [r23.get (by decide)]; exact ht.x26
  · rw [r23.get (by decide)]; exact ht.x20
  · rw [r23.get (by decide)]; exact ht.x22
  · rw [t3x21, List.length_append, List.length_singleton]
    congr 1
  · rw [t3x24, List.flatten_concat, List.length_append]
    simp only [List.length_cons, List.length_nil]
    congr 1
  · rw [List.flatten_concat, List.length_append, ht.flen, List.length_append, List.length_singleton]
    simp only [List.length_cons, List.length_nil]; omega
  · exact (ht.regs.trans r23).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold MW at h ⊢
    have hc := ht.flen
    kg_omega
  · rw [List.flatten_concat, ← List.append_assoc]
    have hout := ht.out.frame ((t2f.trans hwf).trans t3f)
      (by rw [List.length_append]; have hc := ht.flen; kg_omega)
      (fun B h1 h2 h => by rw [List.length_append] at h2; kg_omega)
    have hd0 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length))
        ((levels.getD pre.length []).getD (2*cur.length) 0 ^^^ a.extractLsb' 0 128) := by
      constructor
      · rw [t3a, hn0.1, hmo0.1, ← BitVec.extractLsb'_xor]
      · rw [t3b, hn0.2, hmo0.2, ← BitVec.extractLsb'_xor]
    have hd1 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length)+16)
        ((levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ a.extractLsb' 128 128) := by
      constructor
      · rw [t3c, show TOP+16*(2^(12-pre.length)+2*cur.length)+16=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1)) by ring, hn1.1, hmo1.1, ← BitVec.extractLsb'_xor]
      · rw [t3d, show TOP+16*(2^(12-pre.length)+2*cur.length)+24=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1))+8 by ring, hn1.2, hmo1.2, ← BitVec.extractLsb'_xor]
    have hs0 := DigsAt.snoc hout (by simpa only [List.length_append] using hd0)
    have hs1 := DigsAt.snoc hs0 (by
      simpa only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hd1)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs1
theorem levelInv_zero : LevelInv s4 [] s4 :=
  ⟨hm.pc, hm.x20, hm.x22, hm.x24, rfl, RegsExcept.refl _ _, Frame.refl _ _, DigsAt.nil _ _⟩
theorem mask_level {pre : List (List Digest)} (hpl : pre.length < 12) {t : MachineState}
    (ht : LevelInv s4 pre t) :
    TSim image sk t (10+35*2^(11-pre.length)) (10+42*2^(11-pre.length))
      (2^(11-pre.length)) (2^(11-pre.length))
      (maskedLevel (levels.getD pre.length []) pre.length)
      (fun ds u => LevelInv s4 (pre ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, h12', h13'⟩ := two_pow_twelve_sub hpl
  have hfl := ht.flen
  obtain ⟨t2, st2, t2pc, t2x23, t2x26, t2x21, t2x2, t2r, t2f⟩ :=
    blk289_spec t (by simpa only [if_pos hpl] using ht.pc) (2^(12-pre.length)) (by omega) ht.x20
  have h0 : MaskInv s4 pre [] t2 := by
    refine ⟨?_, t2x23, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [List.length_nil, if_pos (by omega : 0<2^(11-pre.length))] using t2pc
    · rw [t2x26, hpair, Nat.mul_div_cancel_left _ (by decide)]
    · rw [t2r.get (by decide)]; exact ht.x20
    · rw [t2r.get (by decide)]; exact ht.x22
    · simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using t2x21
    · rw [t2r.get (by decide), ht.x24]; rfl
    · exact (ht.regs.trans t2r).mono (by decide)
    · exact (ht.frame.trans t2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · simpa only [List.flatten_nil, List.append_nil] using ht.out.frame t2f (by kg_omega) (fun _ _ _ h => h)
  have hin := TSim.mapM_range (image := image) (sk := sk) (2^(11-pre.length))
    (fun i => do
      let values ← pairedMask pre.length i
      pure [(levels.getD pre.length []).getD (2*i) 0 ^^^ values.1,
        (levels.getD pre.length []).getD (2*i+1) 0 ^^^ values.2])
    (fun _ => 35) (fun _ => 42) (fun _ => 1) (fun _ => 1) (MaskInv s4 pre)
    (fun cur u hc hu => mask_one hm hpl hc ht.flen hu) h0
  simp only [sumTo_const] at hin
  refine (TSim.steps st2 (TSim.map List.flatten
    (TSim.post_steps (k' := 4) (c' := 4) hin (fun ds u hu => ?_)))).of_eq ?_
      (by ring) (by ring) (by simp) (by simp)
  · obtain ⟨hdl, hu⟩ := hu
    obtain ⟨u2, su2, u2pc, u2x20, u2x22, u2r, u2f⟩ :=
      blk330_spec u (by simpa only [hdl, if_neg (Nat.lt_irrefl _)] using hu.pc)
        (2^(12-pre.length)) pre.length (by omega) (by omega) hu.x20 hu.x22
    refine ⟨u2, su2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using u2pc
    · rw [u2x20, List.length_append, List.length_singleton, h12']
    · rw [u2x22, List.length_append, List.length_singleton]
    · rw [u2r.get (by decide), hu.x24, List.flatten_concat, List.length_append]
    · rw [List.flatten_concat, List.length_append, hu.flen, hdl,
        List.length_append, List.length_singleton, h13', ← hpair]
      omega
    · exact (hu.regs.trans u2r).mono (by decide)
    · exact (hu.frame.trans u2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · rw [List.flatten_concat]
      exact hu.out.frame u2f (by rw [List.length_append, hu.flen, hdl]; kg_omega) (fun _ _ _ h => h)
  · simp only [maskedLevel, map_eq_bind_pure_comp]
    rfl
theorem masks_tsim :
    TSim image sk s4 143445 172110 4095 4095
      ((List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level)
      (fun masked u => masked.length = 12 ∧ LevelInv s4 masked u) := by
  rw [List.range'_eq_map_range, List.mapM_map]
  simp only [Nat.zero_add]
  exact (TSim.mapM_range 12 _ (fun j => 10+35*2^(11-j)) (fun j => 10+42*2^(11-j))
    (fun j => 2^(11-j)) (fun j => 2^(11-j)) (LevelInv s4)
    (fun pre t hl ht => mask_level hm hl ht) (levelInv_zero hm)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)
end masks
end SigGolfCandidate.T3M.Keygen
end
