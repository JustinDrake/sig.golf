import SigGolfCandidate.T3M.Sign.Basic

/-!
# Sign: block specifications of layer 0 and the appended cached path

Words 427..446 set up the layer-0 counter search and signature-only leaf. Word 447
jumps to the appended path at 1433. Its twelve iterations (1438..1481) read one
cached sibling, obtain the appropriate half of a paired mask, and write their XOR
to `SIG + 3120 + 16 * level`. Word 1482 returns to the halt setup at 540.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)

/-! ## Bit operations on small values -/

theorem ofNat_and_mask (x k : Nat) (hk : k ≤ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk; omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk), Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) this)]

theorem ofNat_xor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

theorem ofNat_sub_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hb ha), Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le a b) ha)]
  omega

/-! ## The blocks -/

/-- `layer_0` (427..440): the layer registers, the leaf `index >> 19 & 4095`, `counter_search`. -/
theorem blk427_spec (s : MachineState) (hpc : s.pc = pcOf 427) (index : Nat) (hidx : index < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 441 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x9 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 58 ∧ t.getReg .x27 = BitVec.ofNat 64 49 ∧
      t.getReg .x17 = BitVec.ofNat 64 126 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 4096) ∧
      t.getReg .x14 = BitVec.ofNat 64 (index / 2 ^ 19 % 4096) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 19 &&& 4095#64) = BitVec.ofNat 64 (x / 2 ^ 19 % 4096) := by
    intro x hx
    rw [ofNat_shr x 19 hx]
    exact ofNat_and_mask (x / 2 ^ 19) 12 (by norm_num)
  refine ⟨_, symRun_sound blk_427 codeAt_427 s hpc (by simp [blk_427.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_427.res, E.eval]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp only [Result.toState_getReg, blk_427.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand index (by omega)]
    rfl
  · simp only [Result.toState_getReg, blk_427.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand index (by omega)]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_427.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_427.res, rv_simp]

/-- 441..446: the signature-only leaf (`t6 = 1`, digits at `DIGITS`, values to `SIG + 2192`). -/
theorem blk441_spec (s : MachineState) (hpc : s.pc = pcOf 441) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 447 ∧
      t.getReg .x31 = BitVec.ofNat 64 1 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = BitVec.ofNat 64 (SIG + 2192) ∧
      RegsExcept s t [.x1, .x22, .x23, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_441 codeAt_441 s hpc (by simp [blk_441.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_441.res, E.eval]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_441.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_441.res, rv_simp]

/-- `tp_done` (540): `t0 := 1`, `a0 := 0`, then the final `ECALL` (542). -/
theorem blk540_spec (s : MachineState) (hpc : s.pc = pcOf 540) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 542 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_540 codeAt_540 s hpc (by simp [blk_540.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_540.res, E.eval]
  · simp [blk_540.res, rv_simp]
  · simp [blk_540.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_540.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_540.res, rv_simp]

theorem fetch_542 (s : MachineState) (hpc : s.pc = pcOf 542) : fetch image s = some (.base .ECALL) :=
  (codeAt_542.fetch s hpc).trans rfl

theorem blk447_spec (s : MachineState) (hpc : s.pc = pcOf 447) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1433 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_447 codeAt_447 s hpc (by simp [blk_447.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_447.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_447.res,rv_simp]

theorem blk1433_spec (s : MachineState) (hpc : s.pc = pcOf 1433) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 1438 ∧
      t.getReg .x22 = 0 ∧ t.getReg .x24 = BitVec.ofNat 64 (SIG+3120) ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧
      RegsExcept s t [.x20,.x22,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1433 codeAt_1433 s hpc (by simp [blk_1433.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1433.res,E.eval]
  · simp [blk_1433.res,rv_simp]
  · simp [blk_1433.res,rv_simp,SIG]
  · simp [blk_1433.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1433.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_1433.res,rv_simp]

theorem blk1438_spec (s : MachineState) (hpc : s.pc = pcOf 1438) (leaf lv : Nat)
    (hl : leaf < 4096) (hlv : lv < 12)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf 1456 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getReg .x23 = BitVec.ofNat 64 (leaf/2^lv ^^^ 1) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 lv) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 ((leaf/2^lv ^^^ 1)/2)) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x23,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  have hq : leaf/2^lv < 2^12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hsib := Nat.xor_lt_two_pow hq (show 1<2^12 by norm_num)
  have hs : (BitVec.ofNat 64 leaf >>> (lv%18446744073709551616%64) ^^^ 1#64) =
      BitVec.ofNat 64 (leaf/2^lv ^^^ 1) := by
    rw [Nat.mod_eq_of_lt (by omega : lv<18446744073709551616), Nat.mod_eq_of_lt (by omega : lv<64),
      ofNat_shr leaf lv (by omega), ofNat_xor _ 1 (by omega) (by norm_num)]
  refine ⟨_,symRun_sound blk_1438 codeAt_1438 s hpc (by simp [blk_1438.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1438.res,E.eval]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp,MOUT]
  · simp only [Result.toState_getReg,blk_1438.res]; t3n [h14,h22]; exact hs
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h22]
    rw [ofNat_or_disjoint' 3329 (lv*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 lv (by norm_num) (by norm_num) (by norm_num) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h14,h22]
    rw [hs,ofNat_shr _ 1 (by omega),pow_one,ofNat_shl,
      hdr1_eq 0 _ (by norm_num) (by omega)]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1438.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_1438.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]

theorem fetch_1456 (s : MachineState) (hpc : s.pc = pcOf 1456) :
    fetch image s = some (.base .ECALL) := (codeAt_1456.fetch s hpc).trans rfl

theorem blk1457_spec (s : MachineState) (hpc : s.pc = pcOf 1457) (sib lo lv out : Nat)
    (hlo2 : 2≤lo) (hlo : lo≤4096) (hsib : sib<lo) (hlv : lv<12)
    (hout0 : SIG+3120≤out) (hout : out+16≤SIG+3312) (hout8 : out%8=0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 sib) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) (h24 : s.getReg .x24 = BitVec.ofNat 64 out)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps image s 25 25 t ∧ t.pc = (if lv+1<12 then pcOf 1438 else pcOf 1482) ∧
      t.getMem (BitVec.ofNat 64 out) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib))) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2))) ∧
      t.getMem (BitVec.ofNat 64 (out+8)) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib)+8)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2)+8)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (out+16) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x22 = BitVec.ofNat 64 (lv+1) ∧
      RegsExcept s t [.x6,.x7,.x20,.x22,.x24,.x28,.x29] ∧
      Frame s t (fun A => A=out ∨ A=out+8) := by
  have hmod : sib%2<2 := Nat.mod_lt _ (by decide)
  have ha : (8192#64-BitVec.ofNat 64 (lo*2)+BitVec.ofNat 64 sib) <<< 4 =
      BitVec.ofNat 64 (16*(8192-2*lo+sib)) := by
    rw [show (8192#64 : Word)=BitVec.ofNat 64 8192 from rfl,
      ofNat_sub_ofNat _ _ (by norm_num) (by omega), ofNat_add_ofNat,ofNat_shl]
    congr 1; omega
  have hm : (BitVec.ofNat 64 sib &&& 1#64) <<< 4 = BitVec.ofNat 64 (16*(sib%2)) := by
    rw [show (1#64 : Word)=BitVec.ofNat 64 (2^1-1) from rfl,
      ofNat_and_mask sib 1 (by norm_num),ofNat_shl]
    congr 1; omega
  have hobl : Oblig.all s blk_1457.res.st.obl := by
    simp only [blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    repeat' constructor <;> omega
  refine ⟨_,symRun_sound blk_1457 codeAt_1457 s hpc hobl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_1457.res,E.eval,CmpOp.eval,BinOp.eval,h22]
    have hx : (BitVec.ofNat 64 lv+1#64).toNat=lv+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx]
    rfl
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    rw [if_neg (by omega),if_pos (by omega)]
    congr 3 <;> omega
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    congr 3 <;> omega
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h20]
    rw [ofNat_shr lo 1 (by omega),pow_one]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1457.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG] at *
    simp only [Result.toState_getMem,blk_1457.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega)]

theorem blk1482_spec (s : MachineState) (hpc : s.pc = pcOf 1482) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 540 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1482 codeAt_1482 s hpc (by simp [blk_1482.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_1482.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_1482.res,rv_simp]

end SigGolfCandidate.T3M.Sign
