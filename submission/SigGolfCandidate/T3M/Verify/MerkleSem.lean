import SigGolfCandidate.T3M.Verify.MerkleCheckA
import SigGolfCandidate.T3M.Verify.MerkleCheckB
import SigGolfCandidate.T3M.Verify.MerkleCheckC
import SigGolfCandidate.T3M.Verify.LayerLower
import SigGolfCandidate.T3M.Verify.Arith
section
namespace SigGolfCandidate.T3M
theorem mkBlockCheck_at (lay ci sh : Nat) (hlay : lay < 4) (hci : ci < mkNch lay) (hsh : sh < 2 ^ mkBits lay ci) :
    mkBlockCheck lay ci sh = true := by
  have hall : ∀ lo n, mkChunkCheck lay ci lo n = true → lo ≤ sh → sh < lo + n → mkBlockCheck lay ci sh = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h sh (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · have hci' : ci < 2 := by simpa [mkNch] using hci
    interval_cases ci
    · exact hall 0 64 mkChunk_00 (by omega) (by simpa [mkBits] using hsh)
    · exact hall 0 64 mkChunk_01 (by omega) (by simpa [mkBits] using hsh)
  all_goals (have hci0 : ci = 0 := by simp [mkNch] at hci; omega); subst hci0
  · have : sh < 128 := by simpa [mkBits, hL] using hsh
    by_cases h64 : sh < 64
    · exact hall 0 64 mkChunk_1a (by omega) (by omega)
    · exact hall 64 64 mkChunk_1b (by omega) (by omega)
  · exact hall 0 64 mkChunk_2 (by omega) (by simpa [mkBits, hL] using hsh)
  · exact hall 0 64 mkChunk_3 (by omega) (by simpa [mkBits, hL] using hsh)
theorem mkEnt_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) : mkEntCheck lay ci sh = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h; exact h.1
theorem mkLvl_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) (kk : Nat) (hkk : kk < mkLvls lay ci) :
    mkLvlCheck lay ci sh kk = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 kk (List.mem_range.mpr hkk)
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount pad64 shortHash leafHash header)
def mkStep (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : T3.M Digest :=
  let other := wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1))
    pair.1 (wmerklePad w lay j) pair.2
theorem mkFinRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem merkleP_eq (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) :
    merkleP w index lay value = (List.range (height lay)).foldlM (mkStep w index lay) value := by
  rw [← mkFinRange_map_val, List.foldlM_map]
  rfl
def mkIn (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : List UInt8 :=
  let other := wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  blk4 pair.1 (header 3 lay.val (route index lay).2 0 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1)))
    (wmerklePad w lay j) pair.2
theorem mkStep_eq (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkStep w index lay value j = shortHash (mkIn w index lay value j) := rfl
theorem mkIn_length (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (mkIn w index lay value j).length = 64 := blk4_length _ _ _ _
theorem mkIn_blocks (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (toQ (pad64 (mkIn w index lay value j))).blocks = 1 := blocks_blk4 _ _ _ _
def mkCi (lay k : Nat) : Nat := if lay = 0 ∧ 6 ≤ k then 1 else 0
def mkSh (lay ci leaf : Nat) : Nat := leaf / 2 ^ mkLo lay ci % 2 ^ mkBits lay ci
def mkEc (lay leaf k : Nat) : Nat :=
  mkShp lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) + mkOff lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) + 1
def mkFin (lay leaf : Nat) : Nat :=
  mkShp lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) + mkOff lay (mkNch lay - 1) (mkBits lay (mkNch lay - 1)) + (if lay = 0 then 0 else 1)
def mkLvlSt (lay k : Nat) : Nat := mkBody lay k + mkMove lay k + (if lay = 0 ∧ k = 5 then 4 else 0)
theorem mk_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkCi lay k < mkNch lay ∧ mkLo lay (mkCi lay k) ≤ k ∧ k - mkLo lay (mkCi lay k) < mkBits lay (mkCi lay k) ∧
    mkIsDisp lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) = decide (lay = 0 ∧ k = 5) ∧
    (k + 1 < hL lay → ¬ (lay = 0 ∧ k = 5) → mkCi lay (k + 1) = mkCi lay k ∧
      k + 1 - mkLo lay (mkCi lay k) = k - mkLo lay (mkCi lay k) + 1 ∧
      k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
    (k + 1 = hL lay → mkCi lay k = mkNch lay - 1 ∧ ¬ (k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
      k - mkLo lay (mkCi lay k) + 1 = mkBits lay (mkCi lay k)) := by
  interval_cases lay
  · change k < 12 at hk; interval_cases k <;> decide
  · change k < 7 at hk; interval_cases k <;> decide
  · change k < 6 at hk; interval_cases k <;> decide
  · change k < 6 at hk; interval_cases k <;> decide
theorem mk_disp_facts : mkCi 0 5 = 0 ∧ mkLo 0 0 = 0 ∧ mkCi 0 6 = 1 ∧ mkLo 0 1 = 6 ∧ mkBits 0 0 = 6 ∧ mkBits 0 1 = 6 ∧
    mkNch 0 = 2 := by decide
theorem mkLvlSt_ne (lay k : Nat) (h : ¬ (lay = 0 ∧ k = 5)) : mkLvlSt lay k = mkBody lay k + mkMove lay k := by
  simp [mkLvlSt, h]
theorem mkBlk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  have h1 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
theorem mkSh_bit (lay ci leaf kk : Nat) (hkk : kk < mkBits lay ci) :
    mkSh lay ci leaf / 2 ^ kk % 2 = leaf / 2 ^ (mkLo lay ci + kk) % 2 := mkBlk_bit _ _ _ _ hkk
theorem mkSh_lt (lay ci leaf : Nat) : mkSh lay ci leaf < 2 ^ mkBits lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem mkBit_lt (x k : Nat) : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
theorem mkBase_eq (lay : Layer) : mkBase lay.val = layerBase lay := by fin_cases lay <;> rfl
theorem mkBo_eq (lay : Layer) (k : Nat) : mkBo lay.val k = merkleBlock lay k := by
  unfold mkBo merkleBlock; rw [mkBase_eq, hL_eq]
theorem mkBo_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkBo lay k % 8 = 0 ∧ 10568 ≤ mkBo lay k ∧ mkBo lay k + 80 ≤ 25256 ∧ mkBase lay ≤ mkBo lay k ∧
    (k + 1 < hL lay → mkBo lay (k + 1) + 64 = mkBo lay k) ∧ (k + 1 = hL lay → mkBo lay k = mkBase lay) ∧
    mkBo lay k + 64 ≤ mkBase lay + 64 * hL lay := by
  interval_cases lay <;> simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hk ⊢ <;>
    simp only [mkBo, mkBase, hL, List.getD_cons_succ, List.getD_cons_zero] <;> omega
theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 10568 ≤ mkBase lay ∧ mkBase lay % 8 = 0 := by
  interval_cases lay <;> decide
theorem layerBase_add (lay : Layer) : layerBase lay + 64 * height lay = mkBase lay.val + 64 * hL lay.val := by
  rw [mkBase_eq, hL_eq]
theorem mkPow_add_div (h k x : Nat) (hk : k < h) :
    (2 ^ h + x) / 2 ^ (k + 1) = 2 ^ (h - k - 1) + x / 2 ^ (k + 1) := by
  have : 2 ^ h = 2 ^ (k + 1) * 2 ^ (h - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_add_div (Nat.two_pow_pos _)]
theorem mkDiv64_mul_div (leaf k : Nat) (hk : 6 ≤ k) : leaf / 64 * 64 / 2 ^ (k + 1) = leaf / 2 ^ (k + 1) := by
  have e : 2 ^ (k + 1) = 64 * 2 ^ (k - 5) := by
    rw [show (64 : Nat) = 2 ^ 6 by rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm 64 (2 ^ (k - 5)), Nat.mul_div_mul_right _ _ (by decide : 0 < 64), Nat.div_div_eq_div_mul,
    Nat.mul_comm 64]
theorem mkHeap_eq (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (hci : ¬ (lay = 0 ∧ mkCi lay k = 0)) :
    mkHeap lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k = 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1) := by
  unfold mkHeap
  by_cases h0 : lay = 0
  · subst h0
    have hk6 : 6 ≤ k := by
      by_contra hk6; exact hci ⟨rfl, by simp [mkCi]; omega⟩
    have hci1 : mkCi 0 k = 1 := by simp [mkCi]; omega
    rw [hci1]
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hsh : mkSh 0 1 leaf = leaf / 64 := by
      simp only [mkSh, mkLo, mkBits]; norm_num; omega
    rw [hsh, show mkLo 0 1 = 6 by rfl, show hL 0 = 12 by rfl, show (2 : Nat) ^ 6 = 64 by rfl,
      mkPow_add_div 12 k _ (by simpa [hL] using hk), mkDiv64_mul_div leaf k hk6]
  · have hci0 : mkCi lay k = 0 := by simp [mkCi, h0]
    rw [hci0]
    have hsh : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    rw [hsh, show mkLo lay 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.mul_one, mkPow_add_div _ k _ hk]
theorem mkHeapE_eval (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay + leaf)) :
    (mkHeapE lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k).eval s =
      BitVec.ofNat 64 (2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) := by
  have hh : hL lay ≤ 12 := by interval_cases lay <;> decide
  have hpow : 2 ^ hL lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hh
  unfold mkHeapE
  split_ifs with hc
  · apply BitVec.eq_of_toNat_eq
    simp only [E.eval, BinOp.eval, kw, h23]
    have h1 : 2 ^ (hL lay - k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : leaf / 2 ^ (k + 1) ≤ leaf := Nat.div_le_self _ _
    rw [toNat_srl _ _ (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ hL lay + leaf < 2 ^ 64 by omega), mkPow_add_div _ k _ hk]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [E.eval, kw]
    rw [mkHeap_eq lay leaf k hlay hleaf hk hc]
def mkP (lay k b : Nat) (o : Nat) : Prop :=
  10568 ≤ o ∧ o < mkBo lay k + 64 ∧ (0x800 + o + 8 ≤ mkCur lay k b ∨ mkCur lay k b + 32 ≤ 0x800 + o)
structure MAfter (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (k : Nat) (v : Digest)
    (s : MachineState) : Prop where
  pc : s.pc = pcOf (mkEc lay leaf k + 1)
  glob : Glob baseK w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  node : DigAt s (mkCur lay k (leaf / 2 ^ k % 2)) v
  orig : Orig w (mkP lay k (leaf / 2 ^ k % 2)) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkCur lay k (leaf / 2 ^ k % 2))
  x4 : k ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (u.getReg .x30)
structure MkEnd (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob baseK w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 10568 ≤ o ∧ o < mkBase lay) t
  dstReg : t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf)
def mkHashInputOf (a b : Word) (f : Word → BitVec 8) : Query :=
  ⟨b.toNat / 64 - 1, BitVec.ofNat (8 * (64 * (b.toNat / 64 - 1 + 1))) ((List.range (64 * (b.toNat / 64 - 1 + 1))).foldl
    (fun acc i => acc + (f (a + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
theorem mkHashInput_eq_of (s : MachineState) : hashInput s = mkHashInputOf (s.getReg .x10) (s.getReg .x11) s.getByte := rfl
theorem mkHashInput_congr {s t : MachineState} (h10 : t.getReg .x10 = s.getReg .x10)
    (h11 : t.getReg .x11 = s.getReg .x11) (hm : ∀ A, t.getMem A = s.getMem A) : hashInput t = hashInput s := by
  have hb : t.getByte = s.getByte := funext fun a => by simp only [MachineState.getByte, hm]
  rw [mkHashInput_eq_of, mkHashInput_eq_of, h10, h11, hb]
theorem mkK_sub (lay : Nat) (l : List (Reg × Word)) : ∀ p ∈ mkK lay, p ∈ mkK lay ++ l :=
  fun p hp => List.mem_append_left _ hp
theorem mkKeep_sub (l : List Reg) : ∀ r ∈ mkKeep, r ∈ mkKeep ++ l := fun r hr => List.mem_append_left _ hr
theorem mkKc_mkK (lay : Nat) : ∀ p ∈ mkKc lay, p ∈ mkK lay := by
  intro p hp
  simp only [mkKc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> simp [mkK, hp]
theorem mkK_cases (lay : Nat) (p : Reg × Word) (hp : p ∈ mkK lay) :
    p ∈ mkKc lay ∨ p = (.x4, BitVec.ofNat 64 (hw 3 lay)) := by
  simp only [mkK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> simp [mkKc, hp]
theorem mkX4_eval (lay : Nat) (s : MachineState) :
    (mkX4 lay).eval s = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) := rfl
theorem lvlMem_read (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64) (hB : mkBlk lay l + 24 < 2 ^ 64)
    (h4 : l ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30)) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) =
      if A = mkBlk lay l + 24 then
        (mkHeapE lay ci sh l).eval s
      else if A = mkBlk lay l + 16 then StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) else s.getMem (BitVec.ofNat 64 A) := by
  have hH : (mkHdrE lay l).eval s = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) := by
    unfold mkHdrE
    split_ifs with hl
    · exact mkX4_eval lay s
    · exact h4 hl
  unfold mkLvlMem
  rw [memEval_cons_ofNat _ _ _ _ _ hA hB, memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil, hH]
theorem lvl_input (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s t : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k)) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧ Orig w (fun o => 10568 ≤ o ∧ o < mkBo lay.val k) t := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have htree : (route index lay).2 < 2 ^ 32 := tree_lt index lay hidx
  obtain ⟨hB8, hBlo, hBhi, -, -, -, -⟩ := mkBo_facts lay.val k hlay hk
  have h4s : k ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (s.getReg .x30) :=
    fun hk0 => (hs.x4 hk0).trans (by rw [hs.keep .x30 (by simp [mkKeep])])
  have hrd : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = mkBlk lay.val k + 24 then
        (mkHeapE lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k).eval s
      else if A = mkBlk lay.val k + 16 then StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (s.getReg .x30) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (hmem _).trans (lvlMem_read _ _ _ _ s A hA (by unfold mkBlk; omega) h4s)
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ mkBlk lay.val k + 24 → A ≠ mkBlk lay.val k + 16 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2; rw [hrd A hA, if_neg h1, if_neg h2]
  have h30 : s.getReg .x30 = BitVec.ofNat 64 (route index lay).2 := (hs.keep .x30 (by simp [mkKeep])).trans ht5
  have h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) :=
    (hs.keep .x23 (by simp [mkKeep])).trans hs7
  have hheap : 2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1) < 2^32 := by
    have hp : (2 : Nat) ^ (height lay - k - 1) ≤ 2^12 :=
      Nat.pow_le_pow_right (by decide) (by
        have hh : height lay ≤ 12 := by fin_cases lay <;> decide
        omega)
    have hph : (2 : Nat)^hL lay.val ≤ 2^12 :=
      Nat.pow_le_pow_right (by decide) (by rw [hL_eq]; fin_cases lay <;> decide)
    have hd := Nat.div_le_self (route index lay).1 (2^(k+1))
    omega
  have hT1 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 24)) = BitVec.ofNat 64
      (hdr1 (2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1)) 0) := by
    rw [hrd _ (by unfold mkBlk; omega), if_pos rfl,
      mkHeapE_eval lay.val (route index lay).1 k hlay hleaf hk s h23, hL_eq]
    congr 1
    unfold hdr1
    simp only [Nat.mod_eq_of_lt hheap, Nat.div_eq_of_lt hheap, Nat.zero_mod, Nat.zero_add, Nat.add_zero, Nat.zero_mul]
  have hT0 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 16)) =
      BitVec.ofNat 64 (hdr0 3 lay.val (route index lay).2 (route index lay).2) := by
    rw [hrd _ (by unfold mkBlk; omega), if_neg (by omega), if_pos rfl, h30, merge_hi,
      hdr0_eq 3 lay.val _ _ (by decide) (by omega) htree htree]
    congr 1
    unfold hdr1 hw
    omega
  have hO := hs.orig
  have hlen := mkIn_length w index lay v k
  refine ⟨?_, ?_⟩
  · rw [pad64_of_aligned _ (by rw [hlen])]
    apply hashInput_words8 t _ (mkBlk lay.val k) hlen h10 (by unfold mkBlk; omega) (by unfold mkBlk; omega) h11
    have hpad := hO.dig (mkBo lay.val k + 32) (by omega) (by unfold WX; omega)
      ⟨by omega, by omega, by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; interval_cases (route index lay).1 / 2 ^ k % 2 <;> omega⟩
      ⟨by omega, by omega, by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; interval_cases (route index lay).1 / 2 ^ k % 2 <;> omega⟩
    have e32 : WIT + (mkBo lay.val k + 32) = mkBlk lay.val k + 32 := by unfold WIT mkBlk; omega
    rw [e32, show mkBlk lay.val k + 32 + 8 = mkBlk lay.val k + 40 by omega] at hpad
    have f32 := hfr (mkBlk lay.val k + 32) (by unfold mkBlk; omega) (by omega) (by omega)
    have f40 := hfr (mkBlk lay.val k + 40) (by unfold mkBlk; omega) (by omega) (by omega)
    have f0 := hfr (mkBlk lay.val k) (by unfold mkBlk; omega) (by omega) (by omega)
    have f8 := hfr (mkBlk lay.val k + 8) (by unfold mkBlk; omega) (by omega) (by omega)
    have f48 := hfr (mkBlk lay.val k + 48) (by unfold mkBlk; omega) (by omega) (by omega)
    have f56 := hfr (mkBlk lay.val k + 56) (by unfold mkBlk; omega) (by omega) (by omega)
    have hnode := hs.node
    unfold mkIn wpath wmerklePad
    rw [← mkBo_eq lay k]
    rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide, if_false]
      have hsib := hO.dig (mkBo lay.val k + 48) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩
      have e48 : WIT + (mkBo lay.val k + 48) = mkBlk lay.val k + 48 := by unfold WIT mkBlk; omega
      rw [e48, show mkBlk lay.val k + 48 + 8 = mkBlk lay.val k + 56 by omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkCur] using this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 8)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkCur] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn0, hn8, hpad.1, hpad.2, hsib.1, hsib.2]
      simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10]
    · rw [hb] at hnode hO
      simp only [hb, show (1 : Nat) ≠ 0 by decide, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo lay.val k) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
      have e0 : WIT + mkBo lay.val k = mkBlk lay.val k := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      have hn48 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 48)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkCur] using this
      have hn56 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 56)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkCur, Nat.add_assoc] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn48, hn56, hpad.1, hpad.2, hsib.1, hsib.2]
      simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10]
  · intro j hj ⟨h1, h2⟩
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT mkBlk; omega) (by unfold WIT mkBlk; omega)]
    exact hO j hj ⟨h1, by omega, Or.inl (by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; omega)⟩
theorem mkDst_bound (lay leaf : Nat) :
    mkDst lay leaf % 8 = 0 ∧ mkDst lay leaf + 32 ≤ 2^23 := by
  have hm : leaf / 2048 % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold mkDst
  split <;> omega
theorem safeDest_dst (lay leaf : Nat) (hlay : lay < 4) : safeDest (mkDst lay leaf) = true := by
  by_cases h : lay = 0
  · apply safeDest_hi _ _ (mkDst_bound lay leaf).1 (mkDst_bound lay leaf).2
    simp [mkDst,h,WLO,WIT]; omega
  · simp [mkDst,h,safeDest,pSlots,CTRW,WIT,MEMORY_BYTES]
    intro x hx; right; omega
theorem mkDst_chunk (leaf : Nat) :
    13336 + 48 * (mkSh 0 1 leaf / 32 % 2) = mkDst 0 leaf := by
  have h := mkSh_bit 0 1 leaf 5 (by decide)
  change 13336 + 48 * (mkSh 0 1 leaf / 2^5 % 2) =
    13336 + 48 * (leaf / 2^(mkLo 0 1+5) % 2)
  exact congrArg (fun x => 13336 + 48*x) h
theorem mkMove_next (lay k : Nat) (hk : k+1 < hL lay) : mkMove lay k = 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k < 11 := by change k+1<12 at hk; omega
    simp [mkMove]; omega
  · simp [mkMove,h]
theorem mkMove_last (lay k : Nat) (hk : k+1 = hL lay) :
    mkMove lay k = if lay = 0 then 0 else 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k = 11 := by change k+1=12 at hk; omega
    simp [mkMove,this]
  · simp [mkMove,h]
theorem lvl_after (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob baseK w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (u.getReg .x30))
    (horig : Orig w (fun o => 10568 ≤ o ∧ o < mkBo lay k) t) (a : BitVec 256) :
    (k + 1 < hL lay → t.pc = pcOf (mkEc lay leaf (k + 1)) →
      t.getReg .x12 = BitVec.ofNat 64 (mkCur lay (k + 1) (leaf / 2 ^ (k + 1) % 2)) →
      MAfter w pk lay leaf u (k + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
    (k + 1 = hL lay → t.pc = pcOf (mkFin lay leaf) → t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf) →
      MkEnd w pk lay leaf u (a.extractLsb' 0 128) (writeHash t a)) := by
  obtain ⟨hB8, hBlo, hBhi, hBase, hBnext, hBlast, -⟩ := mkBo_facts lay k hlay hk
  refine ⟨fun hk1 hpc h12 => ?_, fun hk1 hpc h12 => ?_⟩
  · obtain ⟨hB8', hBlo', hBhi', -, -, -, -⟩ := mkBo_facts lay (k + 1) hlay hk1
    have hnx := hBnext hk1
    have hb := mkBit_lt leaf (k + 1)
    have hd : mkCur lay (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
        (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
    · intro p hp
      rw [writeHash_getReg]
      exact hknown p (by simpa [mkLvlK] using hp)
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12 hd
    · have hw2 := Orig_writeHash horig a _ h12 hd
      exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by omega⟩, by unfold WIT; omega⟩)
    · rw [writeHash_getReg]; exact h12
    · intro _; rw [writeHash_getReg]; exact h4
  · have hbl := hBlast hk1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_dst lay leaf hlay)
    · intro p hp; rw [writeHash_getReg]; exact hknown p hp
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12 (by have := (mkDst_bound lay leaf).2; omega)
    · have hw2 := Orig_writeHash horig a _ h12 (by have := (mkDst_bound lay leaf).2; omega)
      apply hw2.mono
      intro o ho
      refine ⟨⟨ho.1,by omega⟩,?_⟩
      by_cases hl : lay = 0
      · simp [hl,mkBase] at ho; omega
      · right; simp [mkDst,hl,WIT]; omega
    · rw [writeHash_getReg]; exact h12
theorem dispTgt_eval (leaf : Nat) (hleaf : leaf < 4096) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + leaf)) :
    mkDispTgt.eval s = pcOf (mkTab 0 1 + mkSh 0 1 leaf) := by
  have hsh : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  rw [hsh, show mkTab 0 1 = 209832 from rfl]
  simp only [mkDispTgt, E.eval, BinOp.eval, kw, h23, show hL 0 = 12 from rfl]
  have hq : (BitVec.ofNat 64 (2 ^ 12 + leaf) >>> ((BitVec.ofNat 64 6).toNat % 64)) =
      BitVec.ofNat 64 (64 + leaf / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_srl _ _ (by norm_num)]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega
  rw [hq]
  have hm : (BitVec.ofNat 64 (64 + leaf / 64) <<< ((BitVec.ofNat 64 2).toNat % 64)) =
      BitVec.ofNat 64 (256 + 4 * (leaf / 64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ _ (by norm_num)]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
theorem lfK_mkK (lay : Nat) : ∀ p ∈ mkK lay, p ∈ lfK lay := by
  intro p hp
  simp only [mkK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lfK, postLf, leafK, lfKeepK, baseK]
theorem lvl_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (hk1 : lay.val = 0 ∨ k + 1 < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    ∃ t, Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      ∀ a : BitVec 256,
        (k + 1 < hL lay.val →
          MAfter w pk lay.val (route index lay).1 u (k + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (k + 1 = hL lay.val → MkEnd w pk lay.val (route index lay).1 u (a.extractLsb' 0 128) (writeHash t a)) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hci, hlo, hkk, hdisp, hnext, hlast⟩ := mk_facts lay.val k hlay hk
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, -⟩ := mkBo_facts lay.val k hlay hk
  have hlk : mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) = k := by omega
  have hblk := mkBlockCheck_at lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) hlay hci
    (mkSh_lt _ _ _)
  have hkk' : k - mkLo lay.val (mkCi lay.val k) < mkLvls lay.val (mkCi lay.val k) := by
    unfold mkLvls
    by_cases h0 : lay.val = 0
    · rw [if_pos h0]; exact hkk
    · rw [if_neg h0]
      have hc : mkCi lay.val k = 0 := by simp [mkCi, h0]
      rw [hc]
      simp only [mkLo, mkBits, h0, false_and, if_false]
      rcases hk1 with h | h
      · exact absurd h h0
      · omega
  have hlvl := mkLvl_of hblk _ hkk'
  have hpc0 : s.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
      mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) + 2) := by rw [hs.pc]; rfl
  have hkn0 : KnownOK (mkLvlK lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) s := by
    rw [hlk]; exact hs.known
  have h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) :=
    (hs.keep .x23 (by simp [mkKeep])).trans hs7
  by_cases hd : lay.val = 0 ∧ k = 5
  ·
    obtain ⟨hl0, hk5⟩ := hd
    have hdt : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = true := by
      rw [hdisp]; simp [hl0, hk5]
    have hD : mkLvlCheckD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [mkLvlCheck, hdt, if_true] at hlvl; exact hlvl
    obtain ⟨t1, ht1⟩ := spec_run hD s hpc0 hkn0 (by simp [mkLvlSpecD]) (by simp)
    have hleaf0 : (route index lay).1 < 4096 := by rw [hl0] at hleaf; simpa [hL] using hleaf
    have hpc1 : t1.pc = pcOf (mkTab 0 1 + mkSh 0 1 (route index lay).1) := by
      rw [ht1.spc mkDispTgt rfl, dispTgt_eval _ hleaf0 s (by rw [h23, hl0])]
    have hkn1 : KnownOK (mkKc 0) t1 := fun p hp => ht1.known p (List.mem_append_left _ (by rw [hl0]; exact hp))
    have hent := mkEnt_of (mkBlockCheck_at 0 1 (mkSh 0 1 (route index lay).1) (by decide) (by decide) (mkSh_lt _ _ _))
    obtain ⟨t, ht⟩ := spec_run hent t1 hpc1 hkn1 (by simp [mkEntSpec]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht1.steps.trans ht.steps
      simp only [mkLvlSpecD, mkEntSpec, hlk] at this
      rw [show mkLvlSt lay.val k = mkBody lay.val k + 3 + 2 by simp [mkLvlSt,hl0,hk5,mkMove]]
      exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A
      rw [ht.mem]
      show memEval t1 [] A = _
      rw [memEval_nil, ht1.mem]
      show memEval s (mkLvlMem _ _ _ (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) A = _
      rw [hlk]
    have hkt1 : KnownOK (mkLvlPostD lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k))) t1 := ht1.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k) := by
      rw [ht.keep .x10 (by simp [mkEntKeep])]
      have := hkt1 (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLo lay.val (mkCi lay.val k) +
        (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostD])
      rw [this, hlk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
      rw [ht.keep .x11 (by simp [mkEntKeep])]
      exact hkt1 (.x11, 64) (by simp [mkLvlPostD])
    have hkt : KnownOK (mkEntPost 0 1 (mkSh 0 1 (route index lay).1)) t := ht.known
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2)) := by
      have hb : mkSh 0 1 (route index lay).1 % 2 = (route index lay).1 / 64 % 2 := by
        have := mkSh_bit 0 1 (route index lay).1 0 (by decide)
        rw [show mkLo 0 1 = 6 from rfl] at this
        simpa using this
      rw [hkt (.x12, BitVec.ofNat 64 (mkCur 0 (mkLo 0 1) (mkSh 0 1 (route index lay).1 % 2))) (by simp [mkEntPost]),
        hl0, hk5, show mkLo 0 1 = 6 from rfl, hb]
      rfl
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by rw [← hl0]; simp [mkEntPost, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr
      rw [ht.keep r (mkKeep_sub _ r hr), ht1.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have hkp4 : Reg.x4 ∈ mkLvlKeep (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
      rw [hlk]; simp [mkLvlKeep, hk5]
    have h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (u.getReg .x30) := by
      rw [ht.keep .x4 (by simp [mkEntKeep]), ht1.keep .x4 (List.mem_append_right _ hkp4)]
      exact hs.x4 (by omega)
    have hk6 : k + 1 < hL lay.val := by rw [hl0, hk5]; decide
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 h12 (by unfold mkBlk; omega) (by decide) (by unfold mkBlk; omega)
        (by have := mkBit_lt (route index lay).1 (k + 1); have := (mkBo_facts lay.val (k + 1) hlay hk6).1
            unfold mkCur mkBlk; omega)
        (by have := mkBit_lt (route index lay).1 (k + 1); have := (mkBo_facts lay.val (k + 1) hlay hk6).2.2.1
            unfold mkCur mkBlk; omega), hinp, fun a => ?_⟩
    obtain ⟨hA1, -⟩ := lvl_after w pk lay.val (route index lay).1 u hlay k hk t hglob hknown hkeep h4 horig a
    refine ⟨fun _ => hA1 hk6 ?_ h12, fun h => absurd h (by omega)⟩
    rw [ht.pc rfl]
    simp only [mkEntSpec, mkEc, hl0, hk5, show mkCi 0 6 = 1 from rfl, show mkLo 0 1 = 6 from rfl]
    rfl
  ·
    have hdf : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = false := by
      rw [hdisp]; exact decide_eq_false hd
    have hN : mkLvlCheckN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [mkLvlCheck, hdf, Bool.false_eq_true, if_false] at hlvl; exact hlvl
    have hknN : KnownOK (mkLvlKN lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k-mkLo lay.val (mkCi lay.val k))) s := by
      intro p hp
      simp only [mkLvlKN,List.mem_append] at hp
      rcases hp with hp | hp
      · exact hkn0 p hp
      · split_ifs at hp with hret
        · simp only [List.mem_singleton] at hp
          subst p
          have hk11 : k=11 := by omega
          rw [hs.dstReg]
          simp only [hret.1,hk11]
          rw [show mkCi 0 11=1 from rfl,mkDst_chunk]
          rfl
        · simp at hp
    obtain ⟨t, ht⟩ := spec_run hN s hpc0 hknN (by simp [mkLvlSpecN]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht.steps
      simp only [mkLvlSpecN, hlk] at this
      rw [mkLvlSt_ne _ _ hd]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A; rw [ht.mem]; simp only [mkLvlSpecN, hlk]
    have hkt : KnownOK (mkLvlPostN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k))) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k) := by
      have := hkt (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLo lay.val (mkCi lay.val k) +
        (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostN])
      rw [this, hlk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [mkLvlPostN])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) :=
      hkt (.x12, BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))) (by simp [mkLvlPostN])
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by simp [mkLvlPostN, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr; rw [ht.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (u.getReg .x30) := by
      by_cases hk0 : k = 0
      · have hreg : mkLvlRegs lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) =
            [(.x4, mkX4 lay.val)] := by
          rw [hlk, hk0]; simp [mkLvlRegs]
        have hr : t.getReg .x4 = (mkX4 lay.val).eval s :=
          ht.regs (.x4, mkX4 lay.val) (by simp only [mkLvlSpecN]; rw [hreg]; exact List.mem_singleton.mpr rfl)
        rw [hr, mkX4_eval, hs.keep .x30 (by simp [mkKeep])]
      · have hkp4 : Reg.x4 ∈ mkLvlKeep (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
          rw [hlk]; simp [mkLvlKeep, hk0]
        rw [ht.keep .x4 (List.mem_append_right _ (List.mem_cons_of_mem _ hkp4))]
        exact hs.x4 hk0
    have hpcT : t.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
        mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k) + 1) + mkMove lay.val k) := by
      have h := ht.pc rfl
      simpa only [mkLvlSpecN,hlk] using h
    have hdst : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 24 := by
      by_cases hk1 : k + 1 < hL lay.val
      · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
        refine ⟨_, h12, ?_⟩
        have := (mkBo_facts lay.val (k + 1) hlay hk1)
        simp only [mkNextA2, if_pos hn3, mkCur, mkBlk]
        have := mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k) + 1)
        rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega]
        omega
      · have hk1' : k + 1 = hL lay.val := by omega
        obtain ⟨-, hn2, -⟩ := hlast hk1'
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_neg hn2]
        have hm : mkSh lay.val (mkCi lay.val k) (route index lay).1 / 32 % 2 < 2 := Nat.mod_lt _ (by decide)
        split <;> omega
    obtain ⟨d, hd12, hd8, hd32⟩ := hdst
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 hd12 (by unfold mkBlk; omega) (by decide) (by unfold mkBlk; omega) hd8 hd32,
      hinp, fun a => ?_⟩
    obtain ⟨hA1, hA2⟩ := lvl_after w pk lay.val (route index lay).1 u hlay k hk t hglob hknown hkeep h4 horig a
    refine ⟨fun hk1 => hA1 hk1 ?_ ?_, fun hk1 => hA2 hk1 ?_ ?_⟩
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [hpcT,mkMove_next _ _ hk1]; unfold mkEc; rw [hn1, hn2]
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [h12]; simp only [mkNextA2, if_pos hn3]
      rw [mkSh_bit _ _ _ _ hn3, show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
        show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k) + 1) = k + 1 by omega]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [hpcT,mkMove_last _ _ hk1]; unfold mkFin; rw [← hl1, hl3]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [h12]; simp only [mkNextA2, if_neg hl2]
      by_cases h0 : lay.val = 0
      · have hk11 : k=11 := by norm_num [h0,hL] at hk1; omega
        simp only [h0,hk11,if_true]
        rw [show mkCi 0 11=1 from rfl,mkDst_chunk]
      · simp [h0,mkDst]
def mkCycR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 8 + mkCycR lay (k + 1) n
def mkFuelR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 1 + mkFuelR lay (k + 1) n
theorem merkle_rest (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkEnd w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root))
    (h0 : lay.val = 0) :
    ∀ n k v s, k + n = hL lay.val → 0 < n → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQ s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero => intro k v s _ h; omega
  | succ m ih =>
    intro k v s hkn _ hs
    have hk : k < hL lay.val := by omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 ht5 k hk (Or.inl h0) v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') (a.extractLsb' 0 128)) K) := by
      intro a
      by_cases hm : m = 0
      · subst hm
        simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        exact hK _ _ ((hpost a).2 (by omega))
      · exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := GoodQ.shortHash_bind (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def mkFuel (lay : Nat) : Nat := 3 + mkFuelR lay 0 (hL lay)
def mkCyc (lay : Nat) : Nat := 2 + 8 * lfBlocks lay + mkCycR lay 0 (hL lay)
theorem mkCyc_vals : mkCyc 0 = 273 ∧ mkCyc 1 = 181 ∧ mkCyc 2 = 168 ∧ mkCyc 3 = 168 := by decide
theorem mkFuel_vals : mkFuel 0 = 78 ∧ mkFuel 1 = 45 ∧ mkFuel 2 = 39 ∧ mkFuel 3 = 39 := by decide
theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide
theorem merkle_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkEnd w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root))
    (h0 : lay.val = 0) :
    GoodQ u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (ccM (leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide
  have hent := mkEnt_of (mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTab lay.val 0 + mkSh lay.val 0 (route index lay).1) := by
    rw [hu.pc]
    have e1 : mkTab lay.val 0 = stabIdx lay.val := by simp [mkTab]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e1, e2]
  obtain ⟨t, ht⟩ := spec_run hent u hpc hknown (by simp [mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (if lay.val = 0 then 512 else 768)) (by simp [lfK, postLf])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLo lay.val 0) (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo]]
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, hBtop⟩ := mkBo_facts lay.val 0 hlay hhL
  have hb := mkBit_lt (route index lay).1 0
  have hd : mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
  have hin : hashInput t = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by unfold lfBase; split <;> decide) (by unfold lfBytes; split <;> decide) (by unfold lfBase lfBytes; split <;> decide)
      (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega)
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val 0 (hL lay.val))
      (C + mkCycR lay.val 0 (hL lay.val)) Q (A + mkCycR lay.val 0 (hL lay.val))
      (ccM (merkleP w index lay (a.extractLsb' 0 128)) K) := by
    intro a
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
          (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        ·
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact DigAt.writeHash_lo t a _ h12 hd
      · have hO : Orig w (fun o => 10568 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by rw [layerBase_add]; omega⟩, by unfold WIT; omega⟩)
      · rw [writeHash_getReg]; exact h12
    rw [merkleP_eq, List.range_eq_range', ← hL_eq]
    exact merkle_rest w pk index lay u hidx hu.s7 hu.t5 K N C A Q hK h0 (hL lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQ.shortHash_bind (f := merkleP w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [leafHash_eq]
  have hst := ht.steps
  simp only [mkEntSpec] at hst
  exact GoodQ.steps' hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)
theorem merklePairP_eq (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) :
    merklePairP w index lay value = (List.range (height lay - 1)).foldlM (mkStep w index lay) value >>= fun node =>
      pure (T3.pairOf (route index lay).1 (height lay) (wpath w lay (route index lay).1 (height lay - 1))
        ((wmerklePad w lay (height lay - 1)).extractLsb' 32 96) node) := by
  unfold merklePairP
  rw [← mkFinRange_map_val, List.foldlM_map]
  rfl
theorem merkle_rest_pair (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, MAfter w pk lay.val (route index lay).1 u (hL lay.val - 1) v t → GoodQ t N C Q A (K v)) :
    ∀ n k v s, k + n + 1 = hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQ s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero =>
    intro k v s hkn hs
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
    exact hK v s (by rw [show hL lay.val - 1 = k by omega]; exact hs)
  | succ m ih =>
    intro k v s hkn hs
    have hk : k < hL lay.val := by omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 ht5 k hk (Or.inr (by omega)) v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') (a.extractLsb' 0 128)) K) :=
      fun a => ih (k + 1) _ _ (by omega) ((hpost a).1 (by omega))
    have hg := GoodQ.shortHash_bind (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def mkFuelP (lay : Nat) : Nat := 3 + mkFuelR lay 0 (hL lay - 1)
def mkCycP (lay : Nat) : Nat := 2 + 8 * lfBlocks lay + mkCycR lay 0 (hL lay - 1)
theorem merkle_pair_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest)
    (u : MachineState) (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, MAfter w pk lay.val (route index lay).1 u (hL lay.val - 1) v t → GoodQ t N C Q A (K v)) :
    GoodQ u (N + mkFuelP lay.val) (C + mkCycP lay.val) Q (A + mkCycP lay.val)
      (ccM (leafHash lay (route index lay).2 (route index lay).1 ends >>= fun v =>
        (List.range (hL lay.val - 1)).foldlM (mkStep w index lay) v) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide
  have hent := mkEnt_of (mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTab lay.val 0 + mkSh lay.val 0 (route index lay).1) := by
    rw [hu.pc]
    have e1 : mkTab lay.val 0 = stabIdx lay.val := by simp [mkTab]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e1, e2]
  obtain ⟨t, ht⟩ := spec_run hent u hpc hknown (by simp [mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (if lay.val = 0 then 512 else 768)) (by simp [lfK, postLf])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLo lay.val 0) (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo]]
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, hBtop⟩ := mkBo_facts lay.val 0 hlay hhL
  have hb := mkBit_lt (route index lay).1 0
  have hd : mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
  have hin : hashInput t = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by unfold lfBase; split <;> decide) (by unfold lfBytes; split <;> decide) (by unfold lfBase lfBytes; split <;> decide)
      (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega)
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val 0 (hL lay.val - 1))
      (C + mkCycR lay.val 0 (hL lay.val - 1)) Q (A + mkCycR lay.val 0 (hL lay.val - 1))
      (ccM ((List.range (hL lay.val - 1)).foldlM (mkStep w index lay) (a.extractLsb' 0 128)) K) := by
    intro a
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
          (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        ·
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact DigAt.writeHash_lo t a _ h12 hd
      · have hO : Orig w (fun o => 10568 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by rw [layerBase_add]; omega⟩, by unfold WIT; omega⟩)
      · rw [writeHash_getReg]; exact h12
    rw [List.range_eq_range']
    exact merkle_rest_pair w pk index lay u hidx hu.s7 hu.t5 K N C A Q hK (hL lay.val - 1) 0 _ _ (by omega) hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQ.shortHash_bind (f := fun v => (List.range (hL lay.val - 1)).foldlM (mkStep w index lay) v) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [leafHash_eq]
  have hst := ht.steps
  simp only [mkEntSpec] at hst
  exact GoodQ.steps' hst hg (by unfold mkFuelP; omega) (by unfold mkCycP; omega) (fun q => ⟨q, by unfold mkCycP; omega⟩)
end SigGolfCandidate.T3M
end
