import SigGolfCandidate.Rv
import SigGolfCandidate.Ref.AddressQueries
import SigGolfCandidate.Sign.Base

namespace SigGolfCandidate.Rv.AddressAdapter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Sign
set_option exponentiation.threshold 1024
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def headCode : List (BitVec 32) := [0xfd063183, 0x0101de93, 0x0ffefe93, 0x00001537, 0xa8050513, 0x03d50533, 0x00001eb7, 0x380e8e93, 0x01d50533, 0x0281de93, 0x006e9e93, 0x01d50533, 0x0201de93, 0x007efe93, 0x020e9e93, 0x00ae8eb3, 0xfdd63823, 0xfd060513, 0x00000073]
def tailCode : List (BitVec 32) := [0xfc363823, 0x0201d193, 0x0071fe93]

sym_block preRun := symRun { noAlias := true } headCode 4096 20
sym_block postRun := symRun { noAlias := true } tailCode 4096 4

def addPc (pc : Word) : Nat → Word
  | 0 => pc
  | n + 1 => addPc (pc + 4) n

def preResult (pc : Word) : Result := { preRun.res with pc := .c (addPc pc 18) }
def postResult (pc : Word) : Result := { postRun.res with pc := .c (addPc pc 3) }

kernel_theorem pre_run : ∀ pc : Word,
    symRun { noAlias := true } headCode pc 20 = some (preResult pc)

kernel_theorem post_run : ∀ pc : Word,
    symRun { noAlias := true } tailCode pc 4 = some (postResult pc)

theorem header_fields (lay i mu : Nat) (hl : lay < 7) (hi : i < 42) (hm : mu < 8) :
    ((BitVec.ofNat 64 (oldHeader lay 0 i mu) >>> 16) &&& 255#64) = BitVec.ofNat 64 lay ∧
    (BitVec.ofNat 64 (oldHeader lay 0 i mu) >>> 40) = BitVec.ofNat 64 i ∧
    ((BitVec.ofNat 64 (oldHeader lay 0 i mu) >>> 32) &&& 7#64) = BitVec.ofNat 64 mu := by
  have hw : oldHeader lay 0 i mu < 2 ^ 64 := by unfold oldHeader; omega
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  all_goals simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  all_goals norm_num only [Nat.reducePow, Nat.reduceMod] at hw ⊢
  all_goals rw [Nat.mod_eq_of_lt hw]
  · rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [oldHeader, Nat.mul_zero, Nat.add_zero, Nat.reducePow] at *
    omega
  · simp only [oldHeader, Nat.mul_zero, Nat.add_zero, Nat.reducePow] at *
    omega
  · rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [oldHeader, Nat.mul_zero, Nat.add_zero, Nat.reducePow] at *
    omega

theorem pre_spec {image : Image} {pc : Word} (hc : CodeAt image pc headCode)
    (s : MachineState) (hpc : s.pc = pc) (B lay i mu : Nat)
    (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (hw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu)) :
    ∃ t, Steps image s 18 21 t ∧ fetch image t = some (.base .ECALL) ∧
      t.pc = addPc pc 18 ∧ t.getReg .x10 = BitVec.ofNat 64 B ∧
      t.getReg .x3 = BitVec.ofNat 64 (oldHeader lay 0 i mu) ∧
      t.getReg .x29 = BitVec.ofNat 64 (newHeader lay 0 i mu) ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x29 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = if A = BitVec.ofNat 64 B then
        BitVec.ofNat 64 (newHeader lay 0 i mu) else s.getMem A) ∧
      t = (preResult pc).toState s := by
  have haddr : s.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by
    rw [h12]; bvsimp []
  have ho : (preResult pc).obligs s := by
    simp only [preResult, preRun.res, rv_simp, haddr, accessValid_ofNat]
    norm_num
    omega
  have f := header_fields lay i mu hl hi hm
  have hval : ((preResult pc).toState s).getReg .x29 =
      BitVec.ofNat 64 (newHeader lay 0 i mu) := by
    simp only [preResult, preRun.res, rv_simp]
    simp only [show (32#64).toNat % 64 = 32 from rfl,
      show (16#64).toNat % 64 = 16 from rfl,
      show (40#64).toNat % 64 = 40 from rfl,
      show (6#64).toNat % 64 = 6 from rfl]
    simp only [haddr, hw]
    rw [f.1, f.2.1, f.2.2]
    change BitVec.ofNat 64 mu <<< 32 +
      (BitVec.ofNat 64 2688 * BitVec.ofNat 64 lay + BitVec.ofNat 64 4992 +
        (BitVec.ofNat 64 i <<< 6)) = _
    simp only [BitVec.ofNat_mul_ofNat, ofNat_shiftLeft, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    unfold newHeader
    norm_num only [Nat.reducePow, Nat.mul_zero, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound (pre_run _) hc s hpc ho,
    symRun_ecall (pre_run _) hc s ho rfl, rfl, ?_, ?_, hval, ?_, ?_, rfl⟩
  · simp only [preResult, preRun.res, rv_simp]; exact haddr
  · simp only [preResult, preRun.res, rv_simp]; rw [haddr, hw]
  · intro r h3 h10 h29
    cases r <;> first
      | exact False.elim (h3 rfl)
      | exact False.elim (h10 rfl)
      | exact False.elim (h29 rfl)
      | rfl
  · intro A
    have hv := hval
    simp only [preResult, preRun.res, rv_simp] at hv
    rw [haddr] at hv
    simp only [preResult, preRun.res, Result.toState_getMem, memEval_cons, rv_simp]
    rw [haddr]
    split_ifs
    · exact hv
    · rfl

/-- Restore the saved header and the two temporary registers. -/
theorem post_spec {image : Image} {pc : Word} (hc : CodeAt image pc tailCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = addPc pc 3 ∧
      t.getReg .x3 = s.getReg .x3 >>> 32 ∧
      t.getReg .x29 = (s.getReg .x3 >>> 32) &&& 7#64 ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = if A = BitVec.ofNat 64 B then s.getReg .x3 else s.getMem A) ∧
      t = (postResult pc).toState s := by
  have haddr : s.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by
    rw [h12]; bvsimp []
  have ho : (postResult pc).obligs s := by
    simp only [postResult, postRun.res, rv_simp, haddr, accessValid_ofNat]
    norm_num
    omega
  refine ⟨_, symRun_sound (post_run _) hc s hpc ho, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [postResult, postRun.res, rv_simp]
    rw [show (32#64).toNat % 64 = 32 from rfl]
  · simp only [postResult, postRun.res, rv_simp]
    rw [show (32#64).toNat % 64 = 32 from rfl]
  · intro r h3 h29
    cases r <;> first | exact False.elim (h3 rfl) | exact False.elim (h29 rfl) | rfl
  · intro A
    simp only [postResult, postRun.res, rv_simp, Result.toState_getMem, memEval_cons]
    rw [haddr]

/-- Changing the header changes only the query label. -/
theorem converted_query (s t : MachineState) (B lay i mu : Nat)
    (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24)
    (s10 : s.getReg .x10 = BitVec.ofNat 64 B)
    (t10 : t.getReg .x10 = BitVec.ofNat 64 B)
    (s11 : s.getReg .x11 = 64#64) (t11 : t.getReg .x11 = 64#64)
    (hB8 : B % 8 = 0)
    (sw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (tm : ∀ A, t.getMem A = if A = BitVec.ofNat 64 B then
        BitVec.ofNat 64 (newHeader lay 0 i mu) else s.getMem A) :
    hashInput t = queryPerm (hashInput s) := by
  have sal : (s.getReg .x10).toNat % 8 = 0 := by rw [s10]; bvsimp []; exact hB8
  have tal : (t.getReg .x10).toNat % 8 = 0 := by rw [t10]; bvsimp []; exact hB8
  rw [hashInput_eq_words s 0 s11 (by norm_num) sal,
    hashInput_eq_words t 0 t11 (by norm_num) tal, s10, t10]
  simp only [Nat.reduceAdd, Nat.reduceMul]
  have hw : oldHeader lay 0 i mu < 2 ^ 64 := by unfold oldHeader; omega
  rw [readWords_ofNat_succ t B 7, readWords_ofNat_succ s B 7, sw,
    queryPerm_words _ _ (readWords_length _ _ _) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold oldHeader; omega)]
  have hp : wordPerm (BitVec.ofNat 64 (oldHeader lay 0 i mu)).toNat = newHeader lay 0 i mu := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
    exact old_header lay 0 i mu hl (by norm_num) hi hm
  rw [hp, tm, if_pos rfl]
  congr 2
  apply readWords_congr
  intro j hj
  rw [tm, if_neg]
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at this
  norm_num only [Nat.reducePow] at this
  omega

/-- The conversion and restore leave the hash result and caller state unchanged. -/
theorem restored_state (s : MachineState) (prePc postPc : Word) (B lay i mu : Nat)
    (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 B)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (h3 : s.getReg .x3 = BitVec.ofNat 64 (mu + 256 * i))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 mu)
    (hw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (u : MachineState) (hu : u = (preResult prePc).toState s)
    (ur3 : u.getReg .x3 = BitVec.ofNat 64 (oldHeader lay 0 i mu))
    (ur10 : u.getReg .x10 = BitVec.ofNat 64 B)
    (urr : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x29 → u.getReg r = s.getReg r)
    (um : ∀ A, u.getMem A = if A = BitVec.ofNat 64 B then
        BitVec.ofNat 64 (newHeader lay 0 i mu) else s.getMem A)
    (a : BitVec 256) :
    (postResult postPc).toState (writeHash u a) =
      { writeHash s a with pc := addPc postPc 3 } := by
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (B + 48) := by rw [urr _ (by decide) (by decide) (by decide), h12]
  have addr : u.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by rw [u12]; bvsimp []
  have f := header_fields lay i mu hl hi hm
  apply MachineState.ext' <;> try (rw [hu]; rfl)
  · funext r
    cases r
    case x0 => rw [hu]; rfl
    case x3 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x3 = (writeHash s a).getReg .x3
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      rw [show (32#64).toNat % 64 = 32 from rfl, ur3, h3]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [oldHeader, Nat.mul_zero, Nat.add_zero]
      norm_num only [Nat.reducePow]
      omega
    case x29 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x29 = (writeHash s a).getReg .x29
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      rw [show (32#64).toNat % 64 = 32 from rfl, ur3, f.2.2, h29]
    case x10 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x10 = (writeHash s a).getReg .x10
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg, ur10, h10]
    case x1 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x1 = (writeHash s a).getReg .x1
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x2 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x2 = (writeHash s a).getReg .x2
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x4 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x4 = (writeHash s a).getReg .x4
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x5 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x5 = (writeHash s a).getReg .x5
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x6 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x6 = (writeHash s a).getReg .x6
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x7 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x7 = (writeHash s a).getReg .x7
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x8 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x8 = (writeHash s a).getReg .x8
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x9 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x9 = (writeHash s a).getReg .x9
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x11 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x11 = (writeHash s a).getReg .x11
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x12 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x12 = (writeHash s a).getReg .x12
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x13 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x13 = (writeHash s a).getReg .x13
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x14 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x14 = (writeHash s a).getReg .x14
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x15 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x15 = (writeHash s a).getReg .x15
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x16 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x16 = (writeHash s a).getReg .x16
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x17 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x17 = (writeHash s a).getReg .x17
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x18 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x18 = (writeHash s a).getReg .x18
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x19 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x19 = (writeHash s a).getReg .x19
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x20 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x20 = (writeHash s a).getReg .x20
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x21 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x21 = (writeHash s a).getReg .x21
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x22 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x22 = (writeHash s a).getReg .x22
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x23 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x23 = (writeHash s a).getReg .x23
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x24 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x24 = (writeHash s a).getReg .x24
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x25 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x25 = (writeHash s a).getReg .x25
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x26 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x26 = (writeHash s a).getReg .x26
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x27 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x27 = (writeHash s a).getReg .x27
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x28 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x28 = (writeHash s a).getReg .x28
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x30 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x30 = (writeHash s a).getReg .x30
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
    case x31 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x31 = (writeHash s a).getReg .x31
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact urr _ (by decide) (by decide) (by decide)
  · funext A
    change ((postResult postPc).toState (writeHash u a)).getMem A = (writeHash s a).getMem A
    simp only [postResult, postRun.res, Result.toState_getMem, memEval_cons, rv_simp,
      writeHash_getReg, addr]
    rw [writeHash_getMem, writeHash_getMem, u12, h12, um]
    by_cases he : A = BitVec.ofNat 64 B
    · subst A
      simp only [if_pos rfl, ur3, hw]
      bvsimp []
      have hn (k : Nat) (hk : k < 32) :
          BitVec.ofNat 64 B ≠ BitVec.ofNat 64 (B + 48 + k) := by
        intro he; have := congrArg BitVec.toNat he; simp only [BitVec.toNat_ofNat] at this; omega
      simp only [if_neg (hn 24 (by norm_num)),
        if_neg (hn 16 (by norm_num)), if_neg (hn 8 (by norm_num))]
      rw [if_neg (show BitVec.ofNat 64 B ≠ BitVec.ofNat 64 (B + 48) by simpa using hn 0 (by norm_num))]
    · rw [if_neg he, if_neg he]


theorem jump_step {image : Image} (s : MachineState) (pc target : Word) (off : BitVec 21)
    (hpc : s.pc = pc) (he : pc + off.signExtend 64 = target)
    (hf : fetch image s = some (.base (.JAL .x0 off))) :
    Steps image s 1 1 { s with pc := target } := by
  refine Steps.step hf ?_ (Steps.refl _)
  simp only [ordinaryStep, memoryArgumentsValid, if_true, execInstrBr, MachineState.setReg,
    MachineState.setPC, signExtend21, hpc, he]

end SigGolfCandidate.Rv.AddressAdapter

/-! The expand-side adapter (formerly `Rv/AddressExpand`). -/
namespace SigGolfCandidate.Rv.AddressExpand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Ref.AddressFormat SigGolfCandidate.Sign
open AddressAdapter (addPc header_fields)
set_option exponentiation.threshold 1024
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def headCode : List (BitVec 32) := [0xfd063703, 0x01075593, 0x0ff5f593, 0x00001537, 0xa8050513, 0x02b50533, 0x000015b7, 0x38058593, 0x00b50533, 0x02875593, 0x00659593, 0x00b50533, 0x02075593, 0x0075f593, 0x02059593, 0x00a585b3, 0xfcb63823, 0xfd060513, 0x04000593, 0x00000073]
def tailCode : List (BitVec 32) := [0xfce63823]
sym_block preRun := symRun { noAlias := true } headCode 4096 21
sym_block postRun := symRun { noAlias := true } tailCode 4096 2

def preResult (pc : Word) : Result := { preRun.res with pc := .c (addPc pc 19) }
def postResult (pc : Word) : Result := { postRun.res with pc := .c (addPc pc 1) }

kernel_theorem pre_run : ∀ pc : Word, symRun { noAlias := true } headCode pc 21 = some (preResult pc)
kernel_theorem post_run : ∀ pc : Word, symRun { noAlias := true } tailCode pc 2 = some (postResult pc)

theorem pre_spec {image : Image} {pc : Word} (hc : CodeAt image pc headCode)
    (s : MachineState) (hpc : s.pc = pc) (B lay i mu : Nat)
    (hl : lay < 7) (hi : i < 42) (hm : mu < 8)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (hw : s.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (oldHeader lay 0 i mu)) :
    ∃ t, Steps image s 19 22 t ∧ fetch image t = some (.base .ECALL) ∧
      t.pc = addPc pc 19 ∧ t.getReg .x10 = BitVec.ofNat 64 B ∧
      t.getReg .x14 = BitVec.ofNat 64 (oldHeader lay 0 i mu) ∧ t.getReg .x11 = 64#64 ∧
      (∀ r, r ≠ .x14 → r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = if A = BitVec.ofNat 64 B then
        BitVec.ofNat 64 (newHeader lay 0 i mu) else s.getMem A) ∧
      t = (preResult pc).toState s := by
  have haddr : s.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by rw [h12]; bvsimp []
  have ho : (preResult pc).obligs s := by
    simp only [preResult, preRun.res, rv_simp, haddr, accessValid_ofNat]
    norm_num
    omega
  have f := header_fields lay i mu hl hi hm
  have hval : ((preResult pc).toState s).getMem (BitVec.ofNat 64 B) =
      BitVec.ofNat 64 (newHeader lay 0 i mu) := by
    simp only [preResult, preRun.res, Result.toState_getMem, memEval_cons, rv_simp, haddr, if_pos rfl]
    simp only [show (32#64).toNat % 64 = 32 from rfl,
      show (16#64).toNat % 64 = 16 from rfl, show (40#64).toNat % 64 = 40 from rfl,
      show (6#64).toNat % 64 = 6 from rfl, hw]
    rw [f.1, f.2.1, f.2.2]
    change BitVec.ofNat 64 mu <<< 32 +
      (BitVec.ofNat 64 2688 * BitVec.ofNat 64 lay + BitVec.ofNat 64 4992 +
        (BitVec.ofNat 64 i <<< 6)) = _
    simp only [BitVec.ofNat_mul_ofNat, ofNat_shiftLeft, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    unfold newHeader
    norm_num only [Nat.reducePow, Nat.mul_zero, Nat.add_zero]
    omega
  refine ⟨_, symRun_sound (pre_run _) hc s hpc ho,
    symRun_ecall (pre_run _) hc s ho rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl⟩
  · simp only [preResult, preRun.res, rv_simp]; exact haddr
  · simp only [preResult, preRun.res, rv_simp]; rw [haddr, hw]
  · intro r h14 h10 h11
    cases r <;> first | exact False.elim (h14 rfl) | exact False.elim (h10 rfl) | exact False.elim (h11 rfl) | rfl
  · intro A
    have hv := hval
    simp only [preResult, preRun.res, Result.toState_getMem, memEval_cons, rv_simp, haddr, if_pos rfl] at hv
    simp only [preResult, preRun.res, Result.toState_getMem, memEval_cons, rv_simp, haddr]
    split_ifs
    · exact hv
    · rfl

theorem post_spec {image : Image} {pc : Word} (hc : CodeAt image pc tailCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat)
    (hB : B + 80 < 2 ^ 24) (hB8 : B % 8 = 0)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48)) :
    Steps image s 1 1 ((postResult pc).toState s) := by
  have haddr : s.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by rw [h12]; bvsimp []
  apply symRun_sound (post_run _) hc s hpc
  simp only [postResult, postRun.res, rv_simp, haddr, accessValid_ofNat]
  norm_num
  omega

theorem restored_state (s : MachineState) (prePc postPc : Word) (B : Nat)
    (hB : B + 80 < 2 ^ 24)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 B) (h11 : s.getReg .x11 = 64#64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + 48))
    (u : MachineState) (hu : u = (preResult prePc).toState s)
    (u10 : u.getReg .x10 = BitVec.ofNat 64 B) (u11 : u.getReg .x11 = 64#64)
    (u14 : u.getReg .x14 = s.getMem (BitVec.ofNat 64 B))
    (s14 : s.getReg .x14 = s.getMem (BitVec.ofNat 64 B))
    (ur : ∀ r, r ≠ .x14 → r ≠ .x10 → r ≠ .x11 → u.getReg r = s.getReg r)
    (um : ∀ A, u.getMem A = if A = BitVec.ofNat 64 B then u.getMem (BitVec.ofNat 64 B) else s.getMem A)
    (a : BitVec 256) :
    (postResult postPc).toState (writeHash u a) =
      {writeHash s a with pc := addPc postPc 1} := by
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (B + 48) := by rw [ur _ (by decide) (by decide) (by decide), h12]
  have addr : u.getReg .x12 - 48#64 = BitVec.ofNat 64 B := by rw [u12]; bvsimp []
  apply MachineState.ext' <;> try (rw [hu]; rfl)
  · funext r
    cases r
    case x0 => rw [hu]; rfl
    case x1 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x1 = (writeHash s a).getReg .x1
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x2 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x2 = (writeHash s a).getReg .x2
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x3 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x3 = (writeHash s a).getReg .x3
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x4 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x4 = (writeHash s a).getReg .x4
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x5 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x5 = (writeHash s a).getReg .x5
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x6 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x6 = (writeHash s a).getReg .x6
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x7 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x7 = (writeHash s a).getReg .x7
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x8 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x8 = (writeHash s a).getReg .x8
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x9 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x9 = (writeHash s a).getReg .x9
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x10 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x10 = (writeHash s a).getReg .x10
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      rw [u10, h10]
    case x11 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x11 = (writeHash s a).getReg .x11
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      rw [u11, h11]
    case x12 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x12 = (writeHash s a).getReg .x12
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x13 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x13 = (writeHash s a).getReg .x13
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x14 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x14 = (writeHash s a).getReg .x14
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      rw [u14, s14]
    case x15 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x15 = (writeHash s a).getReg .x15
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x16 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x16 = (writeHash s a).getReg .x16
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x17 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x17 = (writeHash s a).getReg .x17
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x18 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x18 = (writeHash s a).getReg .x18
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x19 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x19 = (writeHash s a).getReg .x19
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x20 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x20 = (writeHash s a).getReg .x20
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x21 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x21 = (writeHash s a).getReg .x21
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x22 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x22 = (writeHash s a).getReg .x22
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x23 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x23 = (writeHash s a).getReg .x23
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x24 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x24 = (writeHash s a).getReg .x24
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x25 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x25 = (writeHash s a).getReg .x25
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x26 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x26 = (writeHash s a).getReg .x26
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x27 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x27 = (writeHash s a).getReg .x27
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x28 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x28 = (writeHash s a).getReg .x28
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x29 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x29 = (writeHash s a).getReg .x29
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x30 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x30 = (writeHash s a).getReg .x30
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
    case x31 =>
      change ((postResult postPc).toState (writeHash u a)).getReg .x31 = (writeHash s a).getReg .x31
      simp only [postResult, postRun.res, rv_simp, writeHash_getReg]
      exact ur _ (by decide) (by decide) (by decide)
  · funext A
    change ((postResult postPc).toState (writeHash u a)).getMem A = (writeHash s a).getMem A
    simp only [postResult, postRun.res, Result.toState_getMem, memEval_cons, rv_simp, writeHash_getReg, addr]
    rw [writeHash_getMem, writeHash_getMem, u12, h12, um]
    by_cases he : A = BitVec.ofNat 64 B
    · subst A
      simp only [u14]
      bvsimp []
      have hn (k : Nat) (hk : k < 32) : BitVec.ofNat 64 B ≠ BitVec.ofNat 64 (B + 48 + k) := by
        intro he; have := congrArg BitVec.toNat he; simp only [BitVec.toNat_ofNat] at this; omega
      simp only [if_neg (hn 24 (by norm_num)), if_neg (hn 16 (by norm_num)), if_neg (hn 8 (by norm_num))]
      rw [if_neg (show BitVec.ofNat 64 B ≠ BitVec.ofNat 64 (B + 48) by simpa using hn 0 (by norm_num))]
    · rw [if_neg he, if_neg he]

end SigGolfCandidate.Rv.AddressExpand
