import Mathlib
import SigGolfCandidate.T3M.Verify.BCWords
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Verify.BCCheck
import SigGolfCandidate.T3M.Verify.ChainGood
import SigGolfCandidate.T3M.Verify.Decode

section

namespace SigGolfCandidate.T3M.Verify
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
end SigGolfCandidate.T3M.Verify
end

section


namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
open ClaudeWCT.WCT9 (LayerMsg)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [14792,17992,21128,24264].getD lay 0
def MsgAt (w : WBytes) (lay : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  match msg with
  | .forest root => lay = 3 ∧ DigAt s 256 root
  | .pair left right => lay < 3 ∧ DigAt s (x10In lay) left ∧
      DigAt s (x10In lay + 48) right ∧
      (∀ j, j = 4 ∨ j = 5 →
        s.getMem (BitVec.ofNat 64 (x10In lay + 8 * j)) =
          wword w ((x10In lay - WIT) / 8 + j))
structure LayerIn (w : WBytes) (pk : Digest) (index lay : Nat) (msg : LayerMsg)
    (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : ∃ c, c < nCopy lay ∧ s.pc = pcOf (trPc lay c)
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  msg : MsgAt w lay msg s
  orig : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd lay) s
structure EncPre (w : WBytes) (pk : Digest) (index lay c : Nat)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay) w pk t
  tp : ∀ L : Layer, L.val = lay →
    t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index L).2 (route index L).1)
  s7 : ∀ L : Layer, L.val = lay →
    t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay + (route index L).1)
  t5 : ∀ L : Layer, L.val = lay → lay ≠ 0 →
    t.getReg .x30 = BitVec.ofNat 64 (route index L).2
  orig : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd lay) t
def rejectSteps (lay : Nat) : Nat := stepsA lay + if lay = 3 then 1 else 2
def EncodingSetup : Prop :=
  ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ T3.counterLimit →
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < T3.counterLimit →
    ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay))) ∧
      ∃ c, c < nCopy lay.val ∧ EncPre w pk index lay.val c t)
def layerLoop (w : WBytes) (index : Nat) : Nat → LayerMsg → T3.M (Option Digest)
  | 0, .forest root => pure (some root)
  | 0, .pair _ _ => pure none
  | n + 1, msg => ClaudeWCT.W9.T3M.layersBC w index (n + 1) msg
end SigGolfCandidate.T3M.BC
end

section





set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [14792,17992,21128,24264].getD lay 0
theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = target lay := by fin_cases lay <;> rfl
abbrev LayerIn := BC.LayerIn
theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]
theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]
theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide
theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem tree_actual_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 < 2 ^ (31 - height lay) := by
  rw [route_snd]
  fin_cases lay <;> norm_num [below, hL, height] at * <;> omega
theorem routed_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  rw [route_snd, route_fst, ← hL_eq]
  fin_cases lay <;> norm_num [below, hL] at * <;> omega
theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x30 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · by_cases h0 : lay.val = 0
    ·
      have hz : (route index lay).2 = 0 := by
        have : lay = 0 := Fin.ext h0
        subst this
        rw [route_snd]; exact Nat.div_eq_of_lt (by simpa [below, hL] using hidx)
      simp only [tpE, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [hz, hdr1_eq _ _ (by norm_num) hl32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
        show 32 % 64 = 32 from rfl, Nat.shiftLeft_eq]
      have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      ring
    simp only [tpE, if_neg h0, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · simp only [s7E, E.eval, BinOp.eval, hlE, kw]
    apply BitVec.eq_of_toNat_eq
    have hp : 2 ^ hL lay.val < 2 ^ 64 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (show 2 ^ hL lay.val + (route index lay).1 < 2 ^ 64 by
        have : 2 * 2 ^ hL lay.val ≤ 2 ^ 13 := by
          rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)
        omega)]
    rw [Nat.lor_comm, show 2 ^ hL lay.val = 2 ^ hL lay.val * 1 by ring, ← Nat.two_pow_add_eq_or_of_lt hl]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
theorem ctrE_eval (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) :
    (ctrE lay.val).eval s = BitVec.ofNat 64 (wctr w lay).toNat := by
  have hj : 2 + (lay.val + 1) / 2 < 8 := by have := lay.isLt; omega
  have hw := hH (2 + (lay.val + 1) / 2) hj
  rw [show WIT + 8 * (2 + (lay.val + 1) / 2) = 0x810 + 8 * ((lay.val + 1) / 2) by unfold WIT; ring] at hw
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x810 + 8 * ((lay.val + 1) / 2))))
    (4 * ((lay.val + 1) % 2))).toNat = _
  rw [hw]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wctr, wle32, counterOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have e1 : 4 * ((lay.val + 1) % 2) / 4 * 32 = 32 * ((lay.val + 1) % 2) := by omega
  rw [e1]
  have e2 : w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) % 2 ^ 64 / 2 ^ (32 * ((lay.val + 1) % 2)) % 2 ^ 32 =
      w.toNat / 2 ^ (8 * (20 + 4 * lay.val)) % 2 ^ 32 := by
    have hk : 8 * (20 + 4 * lay.val) = 64 * (2 + (lay.val + 1) / 2) + 32 * ((lay.val + 1) % 2) := by omega
    rw [hk, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    generalize w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) = X
    have : (lay.val + 1) % 2 = 0 ∨ (lay.val + 1) % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num <;> omega
  rw [e2]
theorem ctr_lt (w : WBytes) (lay : Layer) : (wctr w lay).toNat < 2 ^ 32 := (wctr w lay).isLt
theorem ctrBr_iff (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) (d : Bool) :
    Br.holds s (ctrBr lay.val d) ↔ d = decide ((wctr w lay).toNat ≥ counterLimit) := by
  have hd := ctr_lt w lay
  simp only [ctrBr, Br.holds, CmpOp.eval, E.eval, ctrE_eval w lay s hH, kw]
  have key : (!BitVec.ult (BitVec.ofNat 64 (wctr w lay).toNat) (BitVec.ofNat 64 0x400000)) =
      decide ((wctr w lay).toNat ≥ counterLimit) := by
    have h1 : (wctr w lay).toNat < 2 ^ 64 := by omega
    unfold counterLimit
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
    by_cases h : (wctr w lay).toNat ≥ 2 ^ 22
    · rw [decide_eq_true h, decide_eq_false (by norm_num; omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by norm_num; omega)]; rfl
  rw [key]; exact eq_comm
theorem copy_parts (lay p : Nat) (h : BC.copyCheck lay p = true) :
    specB (BC.allowed lay) [] baseK (runAt (BC.preK lay) [] p [.br false]) (BC.specA lay p) [] (BC.bK lay) keepA = true ∧
    specB (BC.allowed lay) [] [] (runAt (BC.preK lay) [] p [.br true]) (BC.rejA lay p) [] [] [] = true ∧
    (lay = 0 →
      specB [] [] [] (runAt [] [724] (p + stepsA lay + 1) []) (specTopCall p) [] [] keepTopCall = true) ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (BC.bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
        (postBl lay p) keepB = true ∧
      specB [] [] [] (runAt (BC.bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] = true ∧
      specB [] [] [] (runAt (BC.bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] [] = true) ∧
    specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) (lfDirs lay)) (specLf lay) [] (postLf lay) keepLf = true := by
  unfold BC.copyCheck BC.setupCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun h0 => ?_, fun h0 => ?_, h4⟩
  · rw [if_pos h0] at h3; exact h3
  · rw [if_neg h0] at h3; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1.1, h3.1.2, h3.2⟩
abbrev EncPre := BC.EncPre
theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]
theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : u.getMem (BitVec.ofNat 64 256) = a.extractLsb' 0 64
  hi : u.getMem (BitVec.ofNat 64 264) = a.extractLsb' 64 64
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat
theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) :
    (sumE.eval u).toNat = lowSum (ansV a) := by
  have hb : (b1E.eval u).toNat = 2 * (ansV a / 2 ^ 64) := by
    simp only [b1E, E.eval, BinOp.eval, a7E_eval h, kw]
    rw [toNat_sll _ 1 (by norm_num), ← ansV_hi]
    rw [Nat.mod_eq_of_lt (by omega)]; ring
  have hsw : sw1E.eval u = sw1RefE.eval u := by
    have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide
    simp only [sw1E, swLowE, sw1RefE, E.eval, BinOp.eval, kw, M1c, he]
    exact swar7_eq _ _ (by rw [hb]; omega)
  have hs1 : (sw1E.eval u).toNat = sw1 (ansV a % 2 ^ 64) (2 * (ansV a / 2 ^ 64)) := by
    rw [hsw]
    simp only [sw1RefE, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_andc _ _ (by norm_num [M1c]),
      toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]),
      toNat_srl _ 3 (by norm_num), toNat_srl _ 3 (by norm_num)]
    have e1 := a6E_eval h
    simp only [a6E, E.eval] at e1
    simp only [a6E, E.eval]
    rw [e1, ← ansV_lo]
    have e2 : (E.eval u b1E) = BitVec.ofNat 64 (2 * (ansV a / 2 ^ 64)) := by
      apply BitVec.eq_of_toNat_eq; rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * (ansV a / 2 ^ 64) < 2 ^ 64 by omega)]
    unfold sw1; rfl
  unfold lowSum lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1]
  rfl
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
theorem rngBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (k : Nat) (hk : k < 64) (d : Bool) :
    Br.holds u (rngBr k d) ↔ d = decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
  simp only [rngBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a7E_eval h, kw]
  have e : ((a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) != BitVec.ofNat 64 0) =
      decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
    by_cases h0 : (a.extractLsb' 64 64).toNat / 2 ^ k = 0
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) = BitVec.ofNat 64 0 := by
        apply BitVec.eq_of_toNat_eq; rw [toNat_srl _ _ hk, h0]; rfl
      rw [this, decide_eq_false (by omega)]; rfl
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) ≠ BitVec.ofNat 64 0 := by
        intro he; have := congrArg BitVec.toNat he
        rw [toNat_srl _ _ hk, BitVec.toNat_ofNat, Nat.zero_mod] at this; exact h0 this
      rw [decide_eq_true h0]; exact bne_iff_ne.mpr this
  rw [e]; exact eq_comm
theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) (lay : Layer)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
  have hS := lowSum_lt (ansV a)
  have hT : tgtL lay.val ≤ 197 := by fin_cases lay <;> decide
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hr, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔
      (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by omega
  have key : BitVec.ult (BitVec.ofNat 64 7) ((t4E lay.val).eval u) =
      decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
    simp only [BitVec.ult, ht4, BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 7 by norm_num, decide_eq_decide]
    constructor
    · intro h1 h2
      have := hiff.mpr h2
      omega
    · intro h1
      by_contra h2
      exact h1 (hiff.mp (by omega))
  simp only [ckBr, Br.holds, CmpOp.eval]
  show BitVec.ult ((kw 7).eval u) ((t4E lay.val).eval u) = d ↔ _
  rw [show (kw 7).eval u = BitVec.ofNat 64 7 from rfl, key]; exact eq_comm
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64
def a7lW (a : BitVec 256) : Word := ((a.extractLsb' 64 64) <<< 1) ||| ((a.extractLsb' 0 64) >>> 63)
def lctxOf (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a7lW a, ckOf lay a,
    p + retOff lay.val⟩
theorem a7lW_toNat (a : BitVec 256) (hr : ansV a / 2 ^ 64 < 2 ^ 62) : (a7lW a).toNat = ansV a / 2 ^ 63 := by
  have hv := ansV_split a
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 : (a.extractLsb' 64 64).toNat < 2 ^ 62 := by rw [← ansV_hi]; exact hr
  unfold a7lW
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show (a.extractLsb' 64 64).toNat * 2 ^ 1 < 2 ^ 64 by omega)]
  have hc : (a.extractLsb' 0 64).toNat / 2 ^ 63 < 2 ^ 1 := by omega
  rw [show (a.extractLsb' 64 64).toNat * 2 ^ 1 = 2 ^ 1 * (a.extractLsb' 64 64).toNat by ring,
    ← Nat.two_pow_add_eq_or_of_lt hc, hv]
  omega
theorem lctx_digits (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    ∀ i < 43, (lctxOf w index lay a p).dig i = ds.getD i 0 := by
  rw [decode_lower lay hlay] at hds
  have hr : ansV a / 2 ^ 64 / 2 ^ 62 = 0 := by
    by_contra hne; rw [if_pos hne] at hds; cases hds
  rw [if_neg (by simpa using hr)] at hds
  split at hds
  · rename_i hck
    simp only [Option.some.injEq] at hds
    subst hds
    intro i hi
    unfold LCtx.dig lctxOf
    simp only []
    by_cases h21 : i < 21
    · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      show (a.extractLsb' 0 64).toNat / 8 ^ i % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
      rw [← ansV_lo, show (8 : Nat) ^ i = 2 ^ (3 * i) by rw [Nat.pow_mul]]
      have hV : ansV a = ansV a % 2 ^ 64 + 2 ^ 64 * (ansV a / 2 ^ 64) := (Nat.mod_add_div _ _).symm
      conv_rhs => rw [hV]
      exact (div_mod_add_pow (ansV a % 2 ^ 64) (ansV a / 2 ^ 64) (3 * i) 64 3 (by omega)).symm
    · by_cases h42 : i < 42
      · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some]
        show (a7lW a).toNat / 8 ^ (i - 21) % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
        rw [a7lW_toNat a (by omega), Nat.div_div_eq_div_mul, show (2 : Nat) ^ 63 * 8 ^ (i - 21) = 2 ^ (3 * i) by
          rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega]
        rfl
      · have hi42 : i = 42 := by omega
        subst hi42
        rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
        rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
        show ckOf lay a = _
        unfold ckOf
        rw [tgtL_eq]
  · cases hds
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 40000)) = true := by decide
theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2
theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2
theorem trPc_lt (lay c : Nat) : trPc lay c < 40000 :=
  getD_getD_lt xtrTab lay c 40000 (by norm_num) xtrTab_bound
theorem packedRouteE_eval (lay : Layer) (tree leaf : Nat) (s : MachineState)
    (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ height lay)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 (hdr1 tree leaf))
    (h30 : s.getReg .x30 = BitVec.ofNat 64 tree) (hD : DataOK s) :
    (packedRouteE lay.val).eval s = BitVec.ofNat 64 (packedPrefix lay tree leaf) := by
  have hh : height lay ≤ 12 := by rw [← hL_eq]; exact (hL_le lay).2
  have hl32 : leaf < 2 ^ 32 := lt_of_lt_of_le hl
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : (hL lay.val + 16) % 2 ^ 64 % 64 = height lay + 16 := by rw [hL_eq]; omega
  simp only [packedRouteE, E.eval, BinOp.eval, kw, h4, h30,
    hD.prefix lay.val lay.isLt, hdr1_eq tree leaf ht hl32]
  rw [ofNat_shr', ofNat_shl', ofNat_shl']
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) |||
    BitVec.ofNat 64 ((tree + 2 ^ 32 * leaf) % 2 ^ 64 / 2 ^ 32 * 65536) |||
    BitVec.ofNat 64 (tree * 2 ^ ((hL lay.val + 16) % 2 ^ 64 % 64)) = _
  rw [Nat.mod_eq_of_lt (show tree + 2 ^ 32 * leaf < 2 ^ 64 by omega),
    show (tree + 2 ^ 32 * leaf) / 2 ^ 32 = leaf by omega, hs]
  have hb : BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) =
      BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| BitVec.ofNat 64 128 := by
    rw [ofNat_or_add _ _ 48 (by decide)]
    apply congrArg (BitVec.ofNat 64); ring
  rw [hb]
  have hj : BitVec.ofNat 64 (leaf * 65536) ||| BitVec.ofNat 64 (tree * 2 ^ (height lay + 16)) =
      BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) := by
    rw [BitVec.or_comm, ofNat_or_add _ tree (height lay + 16) (by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hl (by decide : 0 < 65536))]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.pow_add]; ring
  have hor (a b c d : Word) : ((a ||| b) ||| c) ||| d = a ||| ((c ||| d) ||| b) := by
    ac_rfl
  calc
    _ = BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) |||
        ((BitVec.ofNat 64 (leaf * 65536) ||| BitVec.ofNat 64 (tree * 2 ^ (height lay + 16))) |||
          BitVec.ofNat 64 128) := hor _ _ _ _
    _ = BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) |||
        BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536 + 128) := by
      rw [hj]
      apply congrArg (fun x : Word => BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| x)
      simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
        ofNat_or_add 128 (tree * 2 ^ height lay + leaf) 16 (by decide)
    _ = _ := by
      rw [ofNat_or_add _ _ 48 (by omega)]
      apply congrArg (BitVec.ofNat 64)
      unfold packedPrefix packedHi
      rw [Nat.mod_eq_of_lt hr]
      ring
theorem origW_of {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Verify.Orig w P s) (A : Nat)
    (hA : WIT ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - 0x800) by unfold WIT at *; omega]
theorem knownOK_cons (p : Reg × Word) (ps : List (Reg × Word)) (s : MachineState)
    (hp : s.getReg p.1 = p.2) (hps : KnownOK ps s) : KnownOK (p :: ps) s := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hps q hq
theorem knownOK_at (ps : List (Reg × Word)) (s : MachineState) (i : Nat) (p : Reg × Word)
    (hk : KnownOK ps s) (he : ps[i]? = some p) : s.getReg p.1 = p.2 :=
  hk p (List.mem_of_getElem? he)
theorem ofNat64_add_zero_bridge (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 n) :
    v = BitVec.ofNat 64 (n + 0) := by simpa only [Nat.add_zero] using h
theorem knownOK_eighteen (s : MachineState)
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 : Reg × Word}
    (h0 : s.getReg p0.1 = p0.2) (h1 : s.getReg p1.1 = p1.2)
    (h2 : s.getReg p2.1 = p2.2) (h3 : s.getReg p3.1 = p3.2)
    (h4 : s.getReg p4.1 = p4.2) (h5 : s.getReg p5.1 = p5.2)
    (h6 : s.getReg p6.1 = p6.2) (h7 : s.getReg p7.1 = p7.2)
    (h8 : s.getReg p8.1 = p8.2) (h9 : s.getReg p9.1 = p9.2)
    (h10 : s.getReg p10.1 = p10.2) (h11 : s.getReg p11.1 = p11.2)
    (h12 : s.getReg p12.1 = p12.2) (h13 : s.getReg p13.1 = p13.2)
    (h14 : s.getReg p14.1 = p14.2) (h15 : s.getReg p15.1 = p15.2)
    (h16 : s.getReg p16.1 = p16.2) (h17 : s.getReg p17.1 = p17.2) :
    KnownOK [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17] s := by
  iterate 18
    refine knownOK_cons _ _ _ ?_ ?_
    rotate_left
  · intro q hq; cases hq
  all_goals assumption
theorem lctxOf_known (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat)
    (s : MachineState) (hk : KnownOK (postBl lay.val p) s)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (packedPrefix lay (route index lay).2 (route index lay).1))
    (h4 : s.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1))
    (h16 : s.getReg .x16 = a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = a7lW a)
    (h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 (ckOf lay a)) :
    KnownOK (lctxOf w index lay a p).known s := by
  unfold LCtx.known
  refine knownOK_eighteen s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact knownOK_at _ s 0 (.x5, 0) hk rfl
  · exact knownOK_at _ s 7 (.x11, 64) hk rfl
  · exact knownOK_at _ s 8 (.x6, 1) hk rfl
  · exact knownOK_at _ s 9 (.x7, 2) hk rfl
  · exact knownOK_at _ s 10 (.x8, 3) hk rfl
  · exact knownOK_at _ s 11 (.x9, 4) hk rfl
  · exact knownOK_at _ s 12 (.x13, 5) hk rfl
  · exact knownOK_at _ s 13 (.x26, 6) hk rfl
  · exact ofNat64_add_zero_bridge _ _ h28
  · exact knownOK_at _ s 4 (.x2, 0x3fe00) hk rfl
  · exact knownOK_at _ s 16 (.x15, 0x6e000) hk rfl
  · exact knownOK_at _ s 17 (.x22, BitVec.ofNat 64 (s6v lay.val)) hk rfl
  · exact h4
  · exact knownOK_at _ s 2 (.x27, BitVec.ofNat 64 (0x401 + 65536 * lay.val)) hk rfl
  · exact h16
  · exact h17
  · exact h29
  · exact knownOK_at _ s 19 (.x1, pcOf (p + retOff lay.val)) hk rfl
theorem encB_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t) (a : BitVec 256) :
    (decode lay (a.extractLsb' 0 128) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (a.extractLsb' 0 128) ≠ none → ∃ s0, Steps image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ok ∧
        (∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a (trPc lay.val c)).Orig0 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) ∧
        s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2) := by
  set u := writeHash t a with hu
  have hcc := copy_parts lay.val (trPc lay.val c) (BC.copyCheck_at lay.val c lay.isLt hc)
  have hB := (hcc.2.2.2.1 (fun h => hlay (Fin.ext h)))
  have hkt : KnownOK (BC.bK lay.val) t := ht.glob.1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 256 := hkt (.x12, 256) (by unfold BC.bK; split <;> simp [bK])
  have hku : KnownOK (BC.bK lay.val) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := ⟨writeHash_at0 t a 256 h12 (by norm_num), writeHash_at8 t a 256 h12 (by norm_num)⟩
  have hdec := decode_lower lay hlay (a.extractLsb' 0 128)
  have hS := lowSum_lt (ansV a)
  constructor
  · intro hnone
    by_cases hr : (a.extractLsb' 64 64).toNat / 2 ^ 62 ≠ 0
    · obtain ⟨v, hv⟩ := spec_run hB.2.2 u hpcu hku (by
        intro b hb; simp only [rejRng, List.mem_singleton] at hb; subst hb
        exact (rngBr_iff hans 62 (by norm_num) true).mpr (by rw [decide_eq_true hr])) (by simp)
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejRng]),
        hv.regs (.x10, kw 1) (by simp [rejRng]), by norm_num, by norm_num⟩
    · have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
      have hck : ¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
        intro hck
        rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr)] at hnone
        rw [if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := spec_run hB.2.1 u hpcu hku (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hr' lay true).mpr (by rw [decide_eq_true hck])
        · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false hr])) (by simp)
      exact ⟨v, 21, 24, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by norm_num, by norm_num⟩
  · intro hsome
    have hr0 : (a.extractLsb' 64 64).toNat / 2 ^ 62 = 0 := by
      by_contra hne
      apply hsome; rw [hdec, if_pos (by rw [ansV_hi]; exact hne)]
    have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
    have hck : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr0), if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hku (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hr' lay false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false (fun h => h hr0)])) (by simp)
    set L := lctxOf w index lay a (trPc lay.val c) with hL
    have htp := trPc_lt lay.val c
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := hs0.known
    have hkeep := hs0.keep
    have e17 : (a7lE.eval u) = a7lW a := by
      simp only [a7lE, b1E, E.eval, BinOp.eval, a7E_eval hans, a6E_eval hans, kw, a7lW]
      rfl
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 197 := by fin_cases lay <;> decide
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
      have hS' : lowSum (ansV a) < 4095 := lowSum_lt (ansV a)
      have hle : lowSum (ansV a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSum (ansV a) < 8 := by omega
      have hcv : ckOf lay a = tgtL lay.val - lowSum (ansV a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hr', BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, ?_,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; unfold ckOf at hck ⊢; omega
      · simp only [hL, lctxOf]; unfold retOff; split_ifs <;> omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
    have hGu : Glob (BC.bK lay.val) w pk u := by
      have := Glob_writeHash ht.glob a 256 h12 (by decide)
      exact this
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a 256 h12 (by norm_num)
      exact this.mono (fun o ho => ⟨ho, Or.inr (by unfold WIT; omega)⟩)
    have hOs0 : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc tgtl rfl]
      simp only [tgtl, E.eval, BinOp.eval, a6E_eval hans, kw]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      rw [hm]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 448800 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_⟩
    ·
      apply lctxOf_known w index lay a (trPc lay.val c) s0 hko
      · rw [hs0.regs (.x28, packedRouteE lay.val) (by simp [specBl])]
        simpa only [Nat.add_zero] using packedRouteE_eval lay _ _ u
          (tree_lt index lay hidx) (by simpa only [hL_eq] using leaf_lt index lay)
          (routed_lt index lay hidx)
          (by rw [hu, writeHash_getReg, ht.tp lay rfl])
          (by rw [hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]) hGu.2.2.2.2.2
      · rw [hkeep .x4 (by simp [keepB]), hu, writeHash_getReg, ht.tp lay rfl]
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7lE) (by simp [specBl]), e17]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
    ·
      intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      have hlb : 0x800 + (layerEnd lay.val) = L.S6 + 64 + 64 * 0 + 0 ∨ True := Or.inr trivial
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hkeep .x23 (by simp [keepB]), hu, writeHash_getReg, ht.s7 lay rfl]
    · rw [hkeep .x30 (by simp [keepB]), hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
end SigGolfCandidate.T3M
end
