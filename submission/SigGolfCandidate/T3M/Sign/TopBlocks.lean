import SigGolfCandidate.T3M.Sign.Basic

/-!
# Sign: block specifications of layer 0 (words 427..542)

`layer_0` (427): `lay = tree = 0`, `N = 58`, `N4 = 49`, `target = 125`, the leaf `index >> 19 & 4095`
(`s2`, `a4`), `counter_search`; 441: the signature-only leaf (values to `SIG + 2240`); 447: the
sibling leaf (root to `SIG + 3168`); 456/464: the leaves of the sibling pair (roots to `NODE`,
`NODE + 48`); 470: the pair node `T3(2048 + pair)` and its HASH; 486: the pair node to `SIG + 3184`,
`level = 2`, `out = SIG + 3200`, `step = 1024`; `tp_mask` (498..539): the mask of the sibling at
`level` xor the cached node of `REGION`; 540: `HALT(0)`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)

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

/-- The cached-node address of `tp_mask`: `16 (sibling + 2048 - 2 step)`. -/
theorem addr515 (leaf lv st : Nat) (hl : leaf < 4096) (hlv : lv < 64) (hst : 2 * st ≤ 2048)
    (hsib : (leaf / 2 ^ lv ^^^ 1) < 2 * st) :
    ((BitVec.ofNat 64 leaf >>> (lv % 18446744073709551616 % 64) ^^^ 1#64) + 2048#64 -
      BitVec.ofNat 64 (st * 2)) <<< 4 = BitVec.ofNat 64 (16 * (2048 - 2 * st + (leaf / 2 ^ lv ^^^ 1))) := by
  have hq : leaf / 2 ^ lv < 2 ^ 12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hx := Nat.xor_lt_two_pow hq (show 1 < 2 ^ 12 by norm_num)
  rw [Nat.mod_eq_of_lt (show lv < 18446744073709551616 by omega), Nat.mod_eq_of_lt hlv, ofNat_shr leaf lv (by omega),
    ofNat_xor _ 1 (by omega) (by norm_num), show (2048#64 : Word) = BitVec.ofNat 64 2048 from rfl,
    ofNat_add_ofNat, ofNat_sub_ofNat _ _ (by omega) (by omega), ofNat_shl]
  congr 1
  omega

/-! ## The blocks -/

/-- `layer_0` (427..440): the layer registers, the leaf `index >> 19 & 4095`, `counter_search`. -/
theorem blk427_spec (s : MachineState) (hpc : s.pc = pcOf 427) (index : Nat) (hidx : index < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 441 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x9 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 58 ∧ t.getReg .x27 = BitVec.ofNat 64 49 ∧
      t.getReg .x17 = BitVec.ofNat 64 125 ∧
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

/-- 441..446: the signature-only leaf (`t6 = 1`, digits at `DIGITS`, values to `SIG + 2240`). -/
theorem blk441_spec (s : MachineState) (hpc : s.pc = pcOf 441) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 447 ∧
      t.getReg .x31 = BitVec.ofNat 64 1 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = BitVec.ofNat 64 (SIG + 2240) ∧
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

/-- 447..455: the sibling leaf `a4 xor 1` (zero digits, root to `SIG + 3168`). -/
theorem blk447_spec (s : MachineState) (hpc : s.pc = pcOf 447) (leaf : Nat) (hl : leaf < 4096)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 456 ∧
      t.getReg .x31 = BitVec.ofNat 64 0 ∧ t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ t.getReg .x25 = BitVec.ofNat 64 (SIG + 3168) ∧
      t.getReg .x18 = BitVec.ofNat 64 (leaf ^^^ 1) ∧
      RegsExcept s t [.x1, .x18, .x22, .x23, .x25, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_447 codeAt_447 s hpc (by simp [blk_447.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_447.res, E.eval]
  · simp [blk_447.res, rv_simp]
  · simp [blk_447.res, rv_simp]
  · simp [blk_447.res, rv_simp]
  · simp [blk_447.res, rv_simp]
  · simp [blk_447.res, rv_simp]
  · simp only [Result.toState_getReg, blk_447.res]; t3n [h14]
    rw [ofNat_xor leaf 1 (by omega) (by norm_num)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_447.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_447.res, rv_simp]

/-- 456..463: the left leaf of the sibling pair, `pairBase = (a4 / 2 xor 1) * 2` (root to `NODE`). -/
theorem blk456_spec (s : MachineState) (hpc : s.pc = pcOf 456) (leaf : Nat) (hl : leaf < 4096)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 464 ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ t.getReg .x25 = BitVec.ofNat 64 NODE ∧
      t.getReg .x18 = BitVec.ofNat 64 ((leaf / 2 ^^^ 1) * 2) ∧
      RegsExcept s t [.x1, .x18, .x23, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_456 codeAt_456 s hpc (by simp [blk_456.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_456.res, E.eval]
  · simp [blk_456.res, rv_simp]
  · simp [blk_456.res, rv_simp]
  · simp [blk_456.res, rv_simp]
  · simp only [Result.toState_getReg, blk_456.res]; t3n [h14]
    rw [ofNat_shr leaf 1 (by omega), pow_one, ofNat_xor (leaf / 2) 1 (by omega) (by norm_num), ofNat_shl]
    congr 1
  · intro r hr; simp at hr; cases r <;> simp_all [blk_456.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_456.res, rv_simp]

/-- 464..469: the right leaf of the sibling pair (root to `NODE + 48`). -/
theorem blk464_spec (s : MachineState) (hpc : s.pc = pcOf 464) (p : Nat) (hp : p < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 470 ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ t.getReg .x25 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getReg .x18 = BitVec.ofNat 64 (p + 1) ∧
      RegsExcept s t [.x1, .x18, .x23, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_464 codeAt_464 s hpc (by simp [blk_464.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_464.res, E.eval]
  · simp [blk_464.res, rv_simp]
  · simp [blk_464.res, rv_simp]
  · simp [blk_464.res, rv_simp]
  · simp only [Result.toState_getReg, blk_464.res]; t3n [h18]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_464.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_464.res, rv_simp]

/-- 470..484: the pair node header `T3(0, 0, 2048 + p / 2)` at `NODE + 16`; HASH `(NODE, 64, NOUT)`. -/
theorem blk470_spec (s : MachineState) (hpc : s.pc = pcOf 470) (p : Nat) (hp : p < 4096)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = pcOf 485 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (hdr0 3 0 0 0) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (hdr1 (2048 + p / 2) 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  refine ⟨_, symRun_sound blk_470 codeAt_470 s hpc (by simp [blk_470.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_470.res, E.eval]
  · simp [blk_470.res, rv_simp]
  · simp [blk_470.res, rv_simp]
  · simp [blk_470.res, rv_simp]
  · simp only [Result.toState_getMem, blk_470.res, NODE]; t3n []
    rw [hdr0_eq 3 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · simp only [Result.toState_getMem, blk_470.res, NODE]; t3n [h18]
    rw [ofNat_shr p 1 (by omega), pow_one, ofNat_add_ofNat, hdr1_eq (2048 + p / 2) 0 (by omega) (by norm_num)]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_470.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, blk_470.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_485 (s : MachineState) (hpc : s.pc = pcOf 485) : fetch image s = some (.base .ECALL) :=
  (codeAt_485.fetch s hpc).trans rfl

/-- 486..497: the pair node to `SIG + 3184`; `level = 2`, `out = SIG + 3200`, `step = 1024`. -/
theorem blk486_spec (s : MachineState) (hpc : s.pc = pcOf 486) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 498 ∧
      t.getMem (BitVec.ofNat 64 (SIG + 3184)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (SIG + 3192)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getReg .x22 = BitVec.ofNat 64 2 ∧ t.getReg .x24 = BitVec.ofNat 64 (SIG + 3200) ∧
      t.getReg .x20 = BitVec.ofNat 64 1024 ∧
      RegsExcept s t [.x6, .x7, .x20, .x22, .x24, .x29, .x30] ∧
      Frame s t (fun A => A = SIG + 3184 ∨ A = SIG + 3192) := by
  refine ⟨_, symRun_sound blk_486 codeAt_486 s hpc (by simp [blk_486.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_486.res, E.eval]
  · simp only [Result.toState_getMem, blk_486.res, SIG, NOUT]; t3n []
  · simp only [Result.toState_getMem, blk_486.res, SIG, NOUT]; t3n []
  · simp [blk_486.res, rv_simp]
  · simp [blk_486.res, rv_simp]
  · simp [blk_486.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_486.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG] at hn
    simp only [Result.toState_getMem, blk_486.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `tp_mask`: `level ≥ 12` ends the masks. -/
theorem blk498_spec (s : MachineState) (hpc : s.pc = pcOf 498) (lv : Nat) (hlv : lv < 2 ^ 63)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lv < 12 then pcOf 500 else pcOf 540) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_498 codeAt_498 s hpc (by simp [blk_498.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_498.res, E.eval, CmpOp.eval, h22, ofNat_slt lv 12 hlv (by norm_num)]
    by_cases h : lv < 12 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_498.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_498.res, rv_simp]

/-- 500..513: the mask header `T13(level, sibling)` at `PRIV + 16`; HASH `(PRIV, 64, MOUT)`. -/
theorem blk500_spec (s : MachineState) (hpc : s.pc = pcOf 500) (leaf lv : Nat) (hl : leaf < 4096)
    (hlv : lv < 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 514 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 13 0 0 lv) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 (leaf / 2 ^ lv ^^^ 1)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  have hsib : leaf / 2 ^ lv ^^^ 1 < 2 ^ 32 := by
    have : leaf / 2 ^ lv < 2 ^ 12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have := Nat.xor_lt_two_pow this (show 1 < 2 ^ 12 by norm_num)
    omega
  refine ⟨_, symRun_sound blk_500 codeAt_500 s hpc (by simp [blk_500.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_500.res, E.eval]
  · simp [blk_500.res, rv_simp]
  · simp [blk_500.res, rv_simp]
  · simp [blk_500.res, rv_simp]
  · simp only [Result.toState_getMem, blk_500.res, PRIV]; t3n [h22]
    rw [ofNat_or_disjoint' 3329 (lv * 4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 lv (by norm_num) (by norm_num) (by norm_num) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, blk_500.res, PRIV]; t3n [h14, h22]
    rw [Nat.mod_eq_of_lt (show lv < 18446744073709551616 by omega), Nat.mod_eq_of_lt hlv,
      ofNat_shr leaf lv (by omega), ofNat_xor (leaf / 2 ^ lv) 1 (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num), ofNat_shl,
      hdr1_eq 0 _ (by norm_num) hsib]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_500.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, blk_500.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_514 (s : MachineState) (hpc : s.pc = pcOf 514) : fetch image s = some (.base .ECALL) :=
  (codeAt_514.fetch s hpc).trans rfl

/-- 515..539: `[out] := REGION[16 (2048 - 2 step + sibling)] xor MOUT`, `out += 16`, `step >>= 1`,
`level += 1`. -/
theorem blk515_spec (s : MachineState) (hpc : s.pc = pcOf 515) (leaf lv st out : Nat) (hl : leaf < 4096)
    (hlv : lv < 64) (hst : 2 * st ≤ 2048) (hout8 : out % 8 = 0) (hout : out + 16 ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) (h22 : s.getReg .x22 = BitVec.ofNat 64 lv)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h24 : s.getReg .x24 = BitVec.ofNat 64 out)
    (hsib : (leaf / 2 ^ lv ^^^ 1) < 2 * st) :
    ∃ t, Steps image s 25 25 t ∧ t.pc = pcOf 498 ∧
      t.getMem (BitVec.ofNat 64 out) =
        s.getMem (BitVec.ofNat 64 (REGION + 16 * (2048 - 2 * st + (leaf / 2 ^ lv ^^^ 1)))) ^^^
          s.getMem (BitVec.ofNat 64 MOUT) ∧
      t.getMem (BitVec.ofNat 64 (out + 8)) =
        s.getMem (BitVec.ofNat 64 (REGION + 16 * (2048 - 2 * st + (leaf / 2 ^ lv ^^^ 1)) + 8)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT + 8)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (out + 16) ∧ t.getReg .x20 = BitVec.ofNat 64 (st / 2) ∧
      t.getReg .x22 = BitVec.ofNat 64 (lv + 1) ∧
      RegsExcept s t [.x6, .x7, .x20, .x22, .x24, .x28, .x29] ∧
      Frame s t (fun A => A = out ∨ A = out + 8) := by
  have hq : leaf / 2 ^ lv < 2 ^ 12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hx := Nat.xor_lt_two_pow hq (show 1 < 2 ^ 12 by norm_num)
  have ha := addr515 leaf lv st hl hlv hst hsib
  have hobl : Oblig.all s blk_515.res.st.obl := by
    simp only [blk_515.res]
    t3n [h14, h22, h20, h24]
    rw [ha]
    t3n []
    sg_omega
  refine ⟨_, symRun_sound blk_515 codeAt_515 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_515.res, E.eval]
  · simp only [Result.toState_getMem, blk_515.res, MOUT]
    t3n [h14, h22, h20, h24]
    rw [ha]
    t3n []
    rw [if_neg (by omega), if_pos (by omega)]
    congr 3; sg_omega
  · simp only [Result.toState_getMem, blk_515.res, MOUT]
    t3n [h14, h22, h20, h24]
    rw [ha]
    t3n []
    congr 3; sg_omega
  · simp only [Result.toState_getReg, blk_515.res]; t3n [h24]
  · simp only [Result.toState_getReg, blk_515.res]; t3n [h20]; rw [ofNat_shr st 1 (by omega), pow_one]
  · simp only [Result.toState_getReg, blk_515.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_515.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_515.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]

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

end SigGolfCandidate.T3M.Sign
