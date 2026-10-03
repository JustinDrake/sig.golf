import SigGolfCandidate.T3M.Sign.TopBlocks
import SigGolfCandidate.T3M.Sign.BaseInv

/-!
# Sign: the twelve masked cache nodes of `topPath`

`topNode cache leaf level` is Core's cached sibling at level 0 through 11.
`tp_mask_one` proves the appended loop, including the paired mask's parity-selected
half, in exactly 44 instructions, 51 cycles, and one HASH call. `tp_masks` proves
all twelve iterations and writes the path at `SIG + 3056`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)

/-! ## The cached nodes -/

/-- The sibling of `leaf` at `level` and its slot in the masked region (`8192 - 2^(13-level) + sib`). -/
def topSlot (leaf level : Nat) : Nat := 8192 - 2 ^ (13 - level) + (leaf / 2 ^ level ^^^ 1)

/-- Core's cached node of `topPath` at `level`. -/
def topNode (cache : Bytes 131072) (leaf level : Nat) : Digest :=
  readDigest (List.ofFn fun i : Fin 16 =>
    (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩)

theorem topSlot_lt {leaf level : Nat} (hl : leaf < 4096) (h11 : level ≤ 11) :
    leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) ∧ topSlot leaf level < 8190 := by
  have hp : 2 ^ level * 2 ^ (12 - level) = 2 ^ 12 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : leaf / 2 ^ level < 2 ^ (12 - level) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.mul_comm, hp]; omega
  have hx : leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) :=
    Nat.xor_lt_two_pow hq (Nat.one_lt_two_pow (by omega))
  have h13 : 2 ^ (13 - level) = 2 * 2 ^ (12 - level) := by
    rw [show 13 - level = (12 - level) + 1 by omega, Nat.pow_succ]; ring
  have hc2 : 2 ≤ 2 ^ (12 - level) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ 12 - level by omega); simpa using this
  refine ⟨hx, ?_⟩
  unfold topSlot
  have : 2 ^ (13 - level) ≤ 8192 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 13 - level ≤ 13 by omega); simpa using this
  omega

theorem topNode_toNat (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).toNat = cache.toNat / 2 ^ (8 * (32 + 16 * topSlot leaf level)) % 2 ^ 128 := by
  have e : (List.ofFn fun i : Fin 16 =>
      (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩) =
      List.ofFn fun i : Fin 16 =>
        UInt8.ofNat (cache.toNat / 256 ^ (32 + 16 * topSlot leaf level) / 256 ^ i.val % 256) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    show UInt8.ofNat (cache.toNat / 256 ^ (32 + (16 * topSlot leaf level + i.val) % 131040) % 256) = _
    rw [Nat.mod_eq_of_lt (show 16 * topSlot leaf level + i.val < 131040 by have := i.isLt; omega),
      ← Nat.add_assoc, pow_add, ← Nat.div_div_eq_div_mul]
  unfold topNode readDigest
  rw [e, readLE_ofFn_digits, BitVec.toNat_ofNat, show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num,
    Nat.mod_mod, show (256 : Nat) ^ (32 + 16 * topSlot leaf level) = 2 ^ (8 * (32 + 16 * topSlot leaf level)) by
      rw [pow_mul]; norm_num]

theorem topNode_lo (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 0 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 4)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 64 ∣ 2 ^ 128)]
  congr 3; ring


theorem topNode_hi (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 64 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 5)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; ring

/-! ## Twelve cached siblings, with parity-selected paired masks -/

def TMW (X : Nat) : Prop :=
  X=PRIV+16 ∨ X=PRIV+24 ∨ (MOUT≤X ∧ X<MOUT+32) ∨ (SIG+3056≤X ∧ X<SIG+3248)

def tmRegs : List Reg := [.x6,.x7,.x10,.x11,.x12,.x20,.x22,.x23,.x24,.x28,.x29]

structure MInv (w0 : MachineState) (pre : List Digest) (w : MachineState) : Prop where
  pc : w.pc = if pre.length<12 then pcOf 1438 else pcOf 1482
  x22 : w.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : w.getReg .x24 = BitVec.ofNat 64 (SIG+3056+16*pre.length)
  x20 : w.getReg .x20 = BitVec.ofNat 64 (2^(12-pre.length))
  regs : RegsExcept w0 w tmRegs
  frame : Frame w0 w TMW
  out : DigsAt w (SIG+3056) pre

section masks
variable {sk : SecretKey} {cache : Bytes 131072} {w0 : MachineState} {leaf : Nat}
  (hb : Base sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
include hb hl h14

theorem tp_mask_one {pre : List Digest} (hpl : pre.length<12) {w : MachineState}
    (hw : MInv w0 pre w) :
    TSim image sk w 44 51 1 1
      (mask pre.length (leaf/2^pre.length ^^^ 1) >>= fun m =>
        pure (topNode cache leaf pre.length ^^^ m))
      (fun d v => MInv w0 (pre++[d]) v) := by
  set lv := pre.length with hlv
  have g : ∀ r, r∉tmRegs → w.getReg r=w0.getReg r := fun r hr => hw.regs.get hr
  obtain ⟨hsib,hslot⟩ := topSlot_lt hl (show lv≤11 by omega)
  obtain ⟨t2,st2,t2pc,t2x10,t2x11,t2x12,t2x23,t2a,t2b,t2r,t2f⟩ :=
    blk1438_spec w (by rw [hw.pc, if_pos hpl]) leaf lv hl (by omega)
      (by rw [g _ (by decide),h14]) hw.x22
  have fr : ∀ X, X<2^64 → BaseA X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseA; simp),fr (PRIV+8) (by decide) (by unfold BaseA; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseA; simp),fr (PRIV+40) (by decide) (by unfold BaseA; simp),
      fr (PRIV+48) (by decide) (by unfold BaseA; simp),fr (PRIV+56) (by decide) (by unfold BaseA; simp),
      hb.p0,hb.p8,hb.p32,hb.p40,hb.p48,hb.p56]
    rfl
  have hv : hashArgumentsValid t2=true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5=0 := by rw [t2r.get (by decide),g _ (by decide),hb.x5]
  refine (TSim.steps st2 (TSim.mask_bind (k:=25) (c:=25) (n:=0) (b:=0)
    (fetch_1456 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc=pcOf 1457 := by rw [pc_writeHash,t2pc,pcOf_add4]
  have hmo : DigAt (writeHash t2 a) (MOUT+16*((leaf/2^lv ^^^ 1)%2))
      (if (leaf/2^lv ^^^ 1)%2=0 then a.extractLsb' 0 128 else a.extractLsb' 128 128) := by
    have hmod := Nat.mod_lt (leaf/2^lv ^^^ 1) (by decide : 0<2)
    by_cases hz : (leaf/2^lv ^^^ 1)%2=0
    · simpa [hz] using DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
    · have ho : (leaf/2^lv ^^^ 1)%2=1 := by omega
      simpa [ho] using DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have rw2 : RegsExcept w (writeHash t2 a) [.x6,.x7,.x10,.x11,.x12,.x23,.x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hlo2 : 2≤2^(12-lv) := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 1≤12-lv by omega); simpa using this
  have hlo : 2^(12-lv)≤4096 := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 12-lv≤12 by omega); simpa using this
  obtain ⟨t3,st3,t3pc,t3a,t3b,t3x24,t3x20,t3x22,t3r,t3f⟩ :=
    blk1457_spec (writeHash t2 a) upc (leaf/2^lv ^^^ 1) (2^(12-lv)) lv
      (SIG+3056+16*pre.length) hlo2 hlo hsib (by omega)
      (by sg_omega) (by sg_omega) (by sg_omega)
      (by rw [getReg_writeHash]; exact t2x23)
      (by rw [rw2.get (by decide)]; exact hw.x20)
      (by rw [rw2.get (by decide)]; exact hw.x22)
      (by rw [rw2.get (by decide)]; exact hw.x24)
      (by rw [getReg_writeHash]; exact t2x12)
  have hst : 2*2^(12-lv)=2^(13-lv) := by
    rw [show 13-lv=(12-lv)+1 by omega,Nat.pow_succ]; ring
  have hslot' : REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))=REGION+8*(2*topSlot leaf lv) := by
    unfold topSlot; rw [hst]; ring
  have fsu := hw.frame.trans (t2f.trans hwf)
  have reg : ∀ k<16380, (writeHash t2 a).getMem (BitVec.ofNat 64 (REGION+8*k))=
      cache.extractLsb' (64*(k+4)) 64 := fun k hk => by
    rw [fsu.get (by sg_omega) (by unfold TMW; sg_omega)]; exact hb.region k hk
  refine TSim.pure_steps st3 ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton] using t3pc
  · rw [t3x22,List.length_append,List.length_singleton]
  · rw [t3x24,List.length_append,List.length_singleton]; congr 1
  · rw [t3x20,List.length_append,List.length_singleton,
      show 12-lv=(12-(pre.length+1))+1 by omega,Nat.pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  · exact (hw.regs.trans (rw2.trans t3r)).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold TMW at h ⊢
    sg_omega
  · refine DigsAt.snoc (hw.out.frame ((t2f.trans hwf).trans t3f) (by sg_omega)
      (fun B h1 h2 h => by sg_omega)) ?_
    constructor
    · rw [t3a,hslot',reg _ (by omega),hmo.1,BitVec.extractLsb'_xor,topNode_lo cache leaf lv hslot]
    · rw [t3b,
        show REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))+8=REGION+8*(2*topSlot leaf lv+1) by
          rw [hslot']; ring,
        reg _ (by omega),hmo.2,BitVec.extractLsb'_xor,topNode_hi cache leaf lv hslot]

theorem tp_masks {w : MachineState} (hw : MInv w0 [] w) :
    TSim image sk w 528 612 12 12
      ((List.range 12).mapM fun level => mask level (leaf/2^level ^^^ 1) >>= fun m =>
        pure (topNode cache leaf level ^^^ m))
      (fun ds v => ds.length=12 ∧ MInv w0 ds v) := by
  refine (TSim.mapM_range 12 _ (fun _ => 44) (fun _ => 51) (fun _ => 1) (fun _ => 1) (MInv w0)
    (fun pre t hpl ht => tp_mask_one hb hl h14 hpl ht) hw).of_eq rfl ?_ ?_ ?_ ?_ <;> simp [sumTo_const]

end masks
end SigGolfCandidate.T3M.Sign
