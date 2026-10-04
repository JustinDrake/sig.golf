import SigGolfCandidate.T3M.Sign.BaseInv
import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Sign.TopBlocks
import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Sign.Kernels
import SigGolfCandidate.T3M.Sign.LowTree
import SigGolfCandidate.T3M.Search.CounterSearch
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Signature Pieces signLayers counterLimit)
structure Halted0 (u : MachineState) : Prop where
  pc : u.pc = pcOf 542
  x5 : u.getReg .x5 = 1
  x10 : u.getReg .x10 = 0
structure L0Pre (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (root : T3.LayerMessage) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 427
  base : BaseL sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC root.1
  encR : DigAt t (ENC + 48) root.2.2
  pad0 : root.2.1 = 0
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
def L0W (A : Nat) : Prop := ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 3248 ≤ A ∧ A < SIG + 5616)
def L0Post (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => ∃ vals path : List Digest, ps = [(vals, path)] ∧ Halted0 u ∧
      (∀ i < 54, DigAt u (SIG + 2192 + 16 * i) (vals.getD i 0)) ∧
      (∀ j < 12, DigAt u (SIG + 3056 + 16 * j) (path.getD j 0)) ∧ Frame t u L0W
def L0Cost : Nat := counterLimit * 205 + 200000
def L0Spec (sk : SecretKey) (cache : Bytes 131072) : Prop :=
  ∀ (index : Nat) (root : T3.LayerMessage) (t : MachineState), L0Pre sk cache index root t →
    TBSim image sk t L0Cost (signLayers (cacheDec cache) index 1 root) (L0Post t)
def PayPost : Option Signature → MachineState → Prop
  | none, u => Failed u
  | some sig, u => Halted0 u ∧ ∀ k < 351, DigAt u (SIG + 16 * k) ((sigDigests sig).getD k 0)
end SigGolfCandidate.T3M.Sign
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Pieces signLayers)
def L0Post (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => ∃ vals path : List Digest, ps = [(vals, path)] ∧ u.pc = pcOf 540 ∧
      (∀ i < 54, DigAt u (SIG + 2192 + 16 * i) (vals.getD i 0)) ∧
      (∀ j < 12, DigAt u (SIG + 3056 + 16 * j) (path.getD j 0)) ∧ Frame t u L0W
def L0Spec (sk : SecretKey) (cache : Bytes 131072) : Prop :=
  ∀ (index : Nat) (root : T3.LayerMessage) (t : MachineState), L0Pre sk cache index root t →
    TBSim image sk t L0Cost (signLayers (cacheDec cache) index 1 root) (L0Post t)
end SigGolfCandidate.T3M.Sign.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3 (Layer Digest decode dataDigits dataCount chainCount maxDigit)
theorem dataDigits_getD (lay : Layer) (v : Digest) (i : Nat) (hi : i < dataCount lay) :
    (dataDigits lay v).getD i 0 ≤ maxDigit lay i := by
  rw [T3.dataDigits_getD lay v i hi]
  exact T3.Nonbinary.coreDigit_le lay v i
theorem length_dataDigits (lay : Layer) (v : Digest) : (dataDigits lay v).length = dataCount lay := by
  simp [dataDigits]
theorem decode_digits {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ds.length = chainCount lay ∧ ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i :=
  ⟨(T3.decode_length_sum h).1, T3.decode_digit_max h⟩
end SigGolfCandidate.T3M.Sign
end
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
def topSlot (leaf level : Nat) : Nat := 8192 - 2 ^ (13 - level) + (leaf / 2 ^ level ^^^ 1)
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
  (hb : BaseL sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
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
  have fr : ∀ X, X<2^64 → BaseAL X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseAL NeverWL Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseAL NeverWL Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseAL; simp),fr (PRIV+8) (by decide) (by unfold BaseAL; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseAL; simp),fr (PRIV+40) (by decide) (by unfold BaseAL; simp),
      fr (PRIV+48) (by decide) (by unfold BaseAL; simp),fr (PRIV+56) (by decide) (by unfold BaseAL; simp),
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
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signLayers signTop topPath counterSearch counterLimit buildLeaf
  nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION
  LeafArgs LeafW leafRegs n4)
open SphincsSecurity (bytesLE bytesLE_length)
private theorem extractByte_zero_top (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
theorem signLayers_one (cache : Cache) (index : Nat) (root : T3.LayerMessage) :
    signLayers cache index 1 root = (do
      let some (_, digits) ← counterSearch 0 (route index 0).2 (route index 0).1 root 0 counterLimit | pure none
      let part ← signTop cache (route index 0).1 digits
      pure (some [part])) := rfl
theorem route_0 {index : Nat} (h : index < 2 ^ 31) : route index 0 = (index / 2 ^ 19 % 4096, 0) := by
  show (index / 2 ^ 19 % 2 ^ 12, index / 2 ^ (19 + 12)) = _
  rw [Nat.div_eq_of_lt (by omega : index < 2 ^ (19 + 12))]
  rfl
private theorem sumTo_le_mul_top (f : Nat → Nat) (b : Nat) : ∀ n, (∀ j < n, f j ≤ b) → sumTo f n ≤ n * b
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le_mul_top f b n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; rw [Nat.succ_mul]; omega
private theorem sumTo_le_sumTo_top (f g : Nat → Nat) : ∀ n, (∀ j < n, f j ≤ g j) → sumTo f n ≤ sumTo g n
  | 0, _ => le_rfl
  | n + 1, h => by
    have := sumTo_le_sumTo_top f g n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; omega
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2192, dest, 447⟩
theorem tl0_costs (leaf dest : Nat) {ds : List Nat} (hd : ∀ i < 54, ds.getD i 0 ≤ 7) :
    (tl0 leaf ds dest).leafK ≤ (tl0 leaf ds dest).leafC ∧ (tl0 leaf ds dest).leafC ≤ 18674 := by
  have he : ∀ i < 54, (tl0 leaf ds dest).e i ≤ 7 := fun i hi => hd i hi
  have hiK : ∀ i, (tl0 leaf ds dest).iterK i ≤ (tl0 leaf ds dest).iterC i := fun i => by
    unfold LeafArgs.iterK LeafArgs.iterC
    norm_num [tl0, Keygen.rungK, Keygen.rungC, Keygen.headerK]
    omega
  have hiC : ∀ i < 54, (tl0 leaf ds dest).iterC i ≤ 331 := fun i hi => by
    have := he i hi
    have e1 : (tl0 leaf ds dest).iterC i =
        21 + (if i < 51 then 5 else 3) + 1 + (42 * (tl0 leaf ds dest).e i + 10) + 0 := rfl
    rw [e1]; split_ifs <;> omega
  have hpK : ∀ p < 27, (tl0 leaf ds dest).pairK p ≤ (tl0 leaf ds dest).pairC p := fun p _ => by
    have e1 : (tl0 leaf ds dest).pairK p = 19 + (tl0 leaf ds dest).iterK (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterK (2 * p + 1) else 0) := rfl
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiK (2 * p)
    have := hiK (2 * p + 1)
    rw [e1, e2]; split_ifs <;> omega
  have hpC : ∀ p < 27, (tl0 leaf ds dest).pairC p ≤ 691 := fun p hp => by
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiC (2 * p) (by omega)
    have := hiC (2 * p + 1) (by omega)
    rw [e2]; split_ifs <;> omega
  have hs1 := sumTo_le_sumTo_top _ _ 27 hpK
  have hs2 := sumTo_le_mul_top _ 691 27 hpC
  have hn : (tl0 leaf ds dest).n = 54 := rfl
  have hso : (tl0 leaf ds dest).so = true := rfl
  unfold LeafArgs.leafK LeafArgs.leafC
  simp only [hn, hso, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv]
  constructor <;> omega
section top
variable {sk : SecretKey} {cache : Bytes 131072}
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : BaseL sk cache s) (hlay : A.lay = 0)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 54)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 54, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 54, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 54 ≤ 2 ^ 24) (hdigW : ∀ i < 54, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 54 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 54 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  have h4 : n4 A.lay = 51 := by rw [hlay]; rfl
  exact
    { x1 := h1
      x5 := hb.x5
      x8 := by rw [h8, hlay]; rfl
      x9 := h9
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [h26, hn]
      x27 := by rw [h27, h4]
      x31 := h31
      htree := htree
      hleaf := hleaf
      hroute := hroute
      hleafHeight := hleafHeight
      hsteps := hsteps
      p0 := hb.p0
      p8 := hb.p8
      p32 := hb.p32
      p40 := hb.p40
      p48 := hb.p48
      p56 := hb.p56
      z0 := hb.zero _ (by sgo) (by unfold NeverWL; simp)
      z8 := hb.zero _ (by sgo) (by unfold NeverWL; simp)
      z32 := hb.zero _ (by sgo) (by unfold NeverWL; simp)
      z40 := hb.zero _ (by sgo) (by unfold NeverWL; simp)
      ztail := fun _ => ⟨hb.zero _ (by sgo) (by unfold NeverWL; simp), hb.zero _ (by sgo) (by unfold NeverWL; simp)⟩
      hdig := fun i hi => hdig i (by rw [hn] at hi; exact hi)
      hdigb := fun i hi => by rw [hlay]; exact hdigb i (by rw [hn] at hi; exact hi)
      hdigp := by rw [hn]; exact hdigp
      hdigW := fun i hi => hdigW i (by rw [hn] at hi; exact hi)
      hv8 := hv8
      hv := by rw [hn]; exact hv
      hvs := by rw [hn]; exact hvs
      hd8 := hd8
      hd := hd
      hds := hds
      hdv := by rw [hn]; exact hdv }
theorem base_leaf {s t : MachineState} {A : LeafArgs} (hb : BaseL sk cache s) (hlay : A.lay = 0)
    (hf : Frame s t (LeafW A)) (hr : RegsExcept s t leafRegs)
    (hvB : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 54 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 54 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 54 ≤ Search.TOP_DATA) : BaseL sk cache t := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  refine hb.frame hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseAL NeverWL Search.TOP_DATA at hB
  unfold Search.TOP_DATA at hvT
  unfold LeafW at hW
  rw [hn] at hW
  sgo
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 54
  x27 : s.getReg .x27 = BitVec.ofNat 64 51
theorem TopRegs.of {leaf : Nat} {s t : MachineState} {l : List Reg} (h : TopRegs leaf s) (hr : RegsExcept s t l)
    (hl : Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x14 ∉ l ∧ Reg.x26 ∉ l ∧ Reg.x27 ∉ l) : TopRegs leaf t :=
  ⟨by rw [hr.get hl.1, h.x8], by rw [hr.get hl.2.1, h.x9], by rw [hr.get hl.2.2.1, h.x14],
    by rw [hr.get hl.2.2.2.1, h.x26], by rw [hr.get hl.2.2.2.2, h.x27]⟩
theorem zdig_byte {s : MachineState} (hb : BaseL sk cache s) {i : Nat} (hi : i < 54) :
    s.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0 := by
  rw [getByte_eq_word s _ (by sgo), hb.zero _ (by sgo) (by unfold NeverWL; sgo), extractByte_zero_top]
  rfl
theorem frame_l0 {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (hW : ∀ A, W A → L0W A) :
    Frame s t L0W := h.mono (fun A _ hA => hW A hA)
theorem frame_l0_trans {s t u : MachineState} (h1 : Frame s t L0W) (h2 : Frame t u L0W) : Frame s u L0W :=
  (h1.trans h2).mono (fun A _ h => by rcases h with h | h <;> exact h)
theorem leafW_l0 {A : LeafArgs} (hlay : A.lay = 0)
    (hv : A.valp + 16 * 54 ≤ SIG ∨ (SIG + 2192 ≤ A.valp ∧ A.valp + 16 * 54 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2192 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.dest) :
    ∀ X, LeafW A X → L0W X := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  intro X hX
  unfold LeafW at hX
  rw [hn] at hX
  unfold L0W
  constructor <;> sgo
def KeepI (s t : MachineState) (lo hi : Nat) : Prop :=
  ∀ A, A < 2 ^ 64 → lo ≤ A → A < hi → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
theorem KeepI.of_frame {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {lo hi : Nat}
    (hW : ∀ A, lo ≤ A → A < hi → ¬ W A) : KeepI s t lo hi := fun A hA h1 h2 => h.get hA (hW A h1 h2)
theorem KeepI.trans {s t u : MachineState} {lo hi : Nat} (h1 : KeepI s t lo hi) (h2 : KeepI t u lo hi) :
    KeepI s u lo hi := fun A hA a b => (h2 A hA a b).trans (h1 A hA a b)
theorem KeepI.mono {s t : MachineState} {lo hi lo' hi' : Nat} (h : KeepI s t lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : KeepI s t lo' hi' := fun A hA a b => h A hA (by omega) (by omega)
theorem KeepI.digAt {s t : MachineState} {lo hi A : Nat} {d : Digest} (h : KeepI s t lo hi) (hd : DigAt s A d)
    (h1 : lo ≤ A) (h2 : A + 16 ≤ hi) (h3 : A + 16 ≤ 2 ^ 64) : DigAt t A d :=
  ⟨(h A (by omega) h1 (by omega)).trans hd.1, (h (A + 8) (by omega) (by omega) (by omega)).trans hd.2⟩
theorem l0Spec_of (hK : CounterSearchSpec sk) : L0Spec sk cache := by
  intro index root t h
  have hSIG : SIG = 28672 := rfl
  have hidx := h.hidx
  have hl : index / 2 ^ 19 % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  rw [signLayers_one, route_0 hidx]
  obtain ⟨t1, st1, t1pc, t1x1, t1x8, t1x9, t1x26, t1x27, t1x17, t1x18, t1x14, t1r, t1f⟩ :=
    blk427_spec t h.pc index hidx h.idx
  have hcs : CsPre t1 0 0 (index / 2 ^ 19 % 4096) root 441 :=
    { pc := t1pc
      x1 := t1x1
      x5 := by rw [t1r.get (by decide), h.base.x5]
      x8 := t1x8
      x9 := t1x9
      x18 := t1x18
      x17 := t1x17
      x26 := t1x26
      x27 := t1x27
      htree := by norm_num
      hleaf := by omega
      rR := h.encR.frame t1f (by sgo) (fun h => h) (fun h => h)
      hpad := h.pad0
      msg := h.enc.frame t1f (by sgo) (fun h => h) (fun h => h)
      c32 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.c32
      z40 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.base.zero _ (by sgo) (by unfold NeverWL; simp)
      table := h.base.table.frame t1f (fun _ _ h => h) }
  have hc0 : csCost 0 = counterLimit * 205 + 2000 := by unfold csCost; rw [if_pos rfl]
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 50000) (hK t1 0 0 _ root 441 hcs) (fun r u hu => ?_)))
    (by rw [hc0]; unfold L0Cost; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · exact TBSim.mono (TBSim.pure hu) (by omega) (fun _ _ h => h)
  obtain ⟨upc, ux5, ⟨v0, hdec⟩, udig, -, ur, uf, ux25⟩ := hu
  obtain ⟨-, hdb⟩ := decode_digits hdec
  have hd7 : ∀ i < 54, ds.getD i 0 ≤ 7 := fun i hi => by
    have := hdb i hi
    have : maxDigit 0 i ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  have hx25 : (u.getReg .x25).toNat ≤ 126 := ux25
  set leaf := index / 2 ^ 19 % 4096 with hleaf_def
  set dest0 := (u.getReg .x25).toNat with hdest0
  have gu : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x17, .x18, .x26, .x27, .x28] ++ csRegs →
      u.getReg r = t.getReg r := fun r hr => (t1r.trans ur).get hr
  have ftu : Frame t u CsW := (t1f.trans uf).mono (fun A _ h => by
    rcases h with h | h
    · exact h.elim
    · exact h)
  have hbu : BaseL sk cache u := h.base.frame ftu (t1r.trans ur) (by decide) (fun A _ hb hw => by
    unfold BaseAL NeverWL Search.TOP_DATA at hb; unfold CsW at hw; sgo)
  have u14 : u.getReg .x14 = BitVec.ofNat 64 leaf := by rw [ur.get (by decide)]; exact t1x14
  obtain ⟨u1, su1, u1pc, u1x1, u1x31, u1x22, u1x23, u1r, u1f⟩ := blk441_spec u upc
  have g1 : ∀ r, r ∉ [.x1, .x22, .x23, .x31] → u1.getReg r = u.getReg r := fun r hr => u1r.get hr
  have hbu1 : BaseL sk cache u1 := hbu.frame u1f u1r (by decide) (fun _ _ _ h => h)
  have tr1 : TopRegs leaf u1 :=
    ⟨by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x8, by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x9,
      by rw [g1 _ (by decide)]; exact u14, by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x26,
      by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x27⟩
  have hp0 : LeafPreS sk u1 (tl0 leaf ds dest0) :=
    leafPreS_of hbu1 rfl u1x1 tr1.x8 tr1.x9 (by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x18) u1x22 u1x23
      (by rw [g1 _ (by decide)]; show u.getReg .x25 = BitVec.ofNat 64 (u.getReg .x25).toNat
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      tr1.x26 tr1.x27 u1x31 (by show 0 < 2 ^ 32; norm_num) (by show leaf < 2 ^ 32; omega)
      (fun i hi => by
        show u1.getByte (BitVec.ofNat 64 (DIGITS + i)) = _
        rw [u1f.getByte (by sgo) (fun h => h)]; exact udig i hi)
      (fun i hi => ⟨by show ds.getD i 0 < 256; have := hd7 i hi; omega, fun h => by simp [tl0] at h⟩)
      (by show DIGITS + 54 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount, Matrix.cons_val_zero]; sgo)
      (by show (SIG + 2192) % 8 = 0; sgo) (by show SIG + 2192 + 16 * 54 ≤ 2 ^ 24; sgo)
      (Or.inl (by show SIG + 2192 + 16 * 54 ≤ PRIV; sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2192; sgo))
      (by change 0 * 2 ^ 12 + leaf < 2 ^ 31; omega)
      (by change leaf < 4096; omega)
      (fun i hi => by have := hd7 i hi; change ds.getD i 0 ≤ 8; omega)
  obtain ⟨k0le, c0le⟩ := tl0_costs leaf dest0 hd7
  have hL0 := buildLeaf_tsimS subAt_sign sk hp0 u1pc
  dsimp only
  rw [signTop, bind_assoc]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 30000) (TSim.toTBSim hL0 k0le) (fun r0 v0 hv0 => ?_)))
    (by omega) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, -, v0vals, v0len, -, v0r, v0f⟩ := hv0
  have hbv0 : BaseL sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2192 + 16 * 54 ≤ PRIV; sgo))
    (Or.inl (by show SIG + 2192 + 16 * 54 ≤ REGION; sgo)) (by show dest0 + 16 ≤ PRIV; sgo)
    (Or.inl (by show dest0 + 16 ≤ ZDIG; sgo)) (Or.inl (by show SIG + 2192 + 16 * 54 ≤ ZDIG; sgo))
    (by show SIG + 2192 + 16 * 54 ≤ Search.TOP_DATA; unfold Search.TOP_DATA; sgo)
  have trv0 : TopRegs leaf v0 := tr1.of v0r (by decide)
  have fv0 : Frame t v0 L0W := frame_l0_trans (frame_l0_trans (frame_l0_trans (frame_l0 t1f (fun _ h => h.elim))
    (frame_l0 uf (fun A hA => by unfold CsW at hA; unfold L0W; constructor <;> sgo)))
    (frame_l0 u1f (fun _ h => h.elim)))
    (frame_l0 v0f (leafW_l0 rfl (by simp only [tl0]; sgo) (by simp only [tl0]; sgo)))
  show TBSim image sk v0 30000 ((topPath (cacheDec cache) leaf >>= fun path => pure (values, path)) >>=
    fun part => pure (some [part])) (L0Post t)
  simp only [topPath, bind_assoc, pure_bind]
  obtain ⟨v1,s447,v1pc,v1r,v1f⟩ := blk447_spec v0 v0pc
  obtain ⟨w,s1433,wpc,wx22,wx24,wx20,wr,wf⟩ := blk1433_spec v1 v1pc
  have hbw : BaseL sk cache w := (hbv0.frame v1f v1r (by decide) (fun _ _ _ h => h)).frame wf wr
    (by decide) (fun _ _ _ h => h)
  have w14 : w.getReg .x14=BitVec.ofNat 64 leaf := by
    rw [wr.get (by decide),v1r.get (by decide),trv0.x14]
  have hm := tp_masks hbw hl w14 (w:=w)
    ⟨wpc,wx22,by simpa using wx24,wx20,RegsExcept.refl _ _,Frame.refl _ _,DigsAt.nil _ _⟩
  refine TBSim.mono (TBSim.steps (s447.trans s1433)
    (TBSim.bind (W₂:=3) (TSim.toTBSim hm (by norm_num)) (fun path x hx => ?_)))
      (by omega) (fun _ _ h => h)
  obtain ⟨hlen,hx⟩ := hx
  obtain ⟨x1,s1482,x1pc,x1r,x1f⟩ := blk1482_spec x (by simpa [hlen] using hx.pc)
  refine TBSim.mono (TBSim.pure_steps s1482 ?_) (by omega) (fun _ _ h => h)
  have fwx := hx.frame.trans x1f
  have keep : KeepI v0 x1 SIG (SIG+3056) :=
    ((KeepI.of_frame v1f (fun _ _ _ h => h)).trans
      (KeepI.of_frame wf (fun _ _ _ h => h))).trans
      (KeepI.of_frame fwx (fun A h1 h2 hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; sgo
        · exact hA))
  refine ⟨values, path, rfl, x1pc, ?_, ?_, ?_⟩
  · intro i hi
    exact keep.digAt (v0vals i (by rw [v0len]; exact hi)) (by omega) (by omega) (by sgo)
  · intro j hj
    have hd := hx.out j (by rw [hlen]; exact hj)
    exact hd.frame x1f (by sgo) (fun h => h) (fun h => h)
  · exact frame_l0_trans (frame_l0_trans (frame_l0_trans fv0
      (frame_l0 v1f (fun _ h => h.elim))) (frame_l0 wf (fun _ h => h.elim)))
      (frame_l0 fwx (fun A hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; unfold L0W; constructor <;> sgo
        · exact hA.elim))
end top
end SigGolfCandidate.T3M.Sign.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Pieces signLayers counterSearch counterLimit buildTree height chainCount
  target route decode width Cache)
open SigGolfCandidate.T3M.Keygen (LevW n4)
def lstart : Nat → Nat
  | 0 => 137
  | 1 => 203
  | 2 => 253
  | 3 => 302
  | _ => 351
theorem lstart_mono (n : Nat) : lstart n ≤ lstart (n + 1) := by
  rcases n with _ | _ | _ | _ | n <;> simp [lstart]
def LayW (n : Nat) (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 16 * lstart n ≤ A ∧ A < SIG + 5616)
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (layIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (layIdx lay + chainCount lay + j)) (p.2.getD j 0)
def SLPost (t : MachineState) (n : Nat) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = n ∧ (∀ lay : Layer, lay.val < n → PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (LayW n)
theorem SLPost.pre {s t : MachineState} {n : Nat} (hf : Frame s t (fun _ => False)) :
    ∀ r u, SLPost t n r u → SLPost s n r u
  | none, _, h => h
  | some _, _, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (hf.trans h4).mono (fun _ _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)⟩
theorem lay_cases {lay : Layer} (hlay : lay ≠ 0) :
    (lay.val = 1 ∧ layIdx lay = 203 ∧ height lay = 7) ∨ (lay.val = 2 ∧ layIdx lay = 253 ∧ height lay = 6) ∨
      (lay.val = 3 ∧ layIdx lay = 302 ∧ height lay = 6) := by
  fin_cases lay
  · exact absurd rfl hlay
  · left; exact ⟨rfl, rfl, rfl⟩
  · right; left; exact ⟨rfl, rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl, rfl⟩
theorem lay_facts {lay : Layer} (hlay : lay ≠ 0) :
    lstart lay.val = layIdx lay ∧ lstart (lay.val + 1) = layIdx lay + 43 + height lay ∧ 203 ≤ layIdx lay ∧
      layIdx lay + 43 + height lay ≤ 351 := by
  rcases lay_cases hlay with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> simp [lstart]
theorem csW_layW {n A : Nat} (h : CsW A) : LayW n A := by
  have := lstart_mono n
  unfold CsW at h
  unfold LayW
  constructor <;> sgo
theorem btAllW_layW {lay : Layer} (hlay : lay ≠ 0) {tree A : Nat} (h : BtAllW lay tree (SIG + 16 * layIdx lay) A) :
    LayW (lay.val + 1) A := by
  unfold BtAllW BtW LevW at h
  simp only [btLev] at h
  unfold LayW
  obtain ⟨-, hls, -, -⟩ := lay_facts hlay
  rw [hls]
  rcases lay_cases hlay with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> rw [h2, h3] at h <;> rw [h2, h3] <;>
    simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h ⊢ <;> constructor <;> sgo
theorem layW_succ {n A : Nat} (h : LayW n A) : LayW (n + 1) A := by
  have := lstart_mono n
  exact ⟨h.1, fun h2 => h.2 ⟨by omega, h2.2⟩⟩
theorem route_lt {index : Nat} (h : index < 2 ^ 31) (lay : Layer) :
    (route index lay).1 < 2 ^ height lay ∧ (route index lay).2 < 2 ^ 32 := by
  simp only [route]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
theorem route_3 (index : Nat) : route index 3 = (index % 64, index / 64) := by
  show (index / 2 ^ 0 % 2 ^ 6, index / 2 ^ (0 + 6)) = _
  simp
theorem route_2 (index : Nat) : route index 2 = (index / 64 % 64, index / 4096) := by
  show (index / 2 ^ 6 % 2 ^ 6, index / 2 ^ (6 + 6)) = _
  simp
theorem route_1 (index : Nat) : route index 1 = (index / 4096 % 128, index / 2 ^ 19) := by
  show (index / 2 ^ 12 % 2 ^ 7, index / 2 ^ (12 + 7)) = _
  simp
def jalBT (lay : Layer) : Nat := (![0, 426, 411, 396] : Layer → Nat) lay
theorem blkJal_spec {lay : Layer} (hlay : lay ≠ 0) (s : MachineState) (hpc : s.pc = pcOf (jalBT lay)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (jalBT lay + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  fin_cases lay
  · exact absurd rfl hlay
  · exact blk426_spec s hpc
  · exact blk411_spec s hpc
  · exact blk396_spec s hpc
structure LayEntry (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat) (msg : T3.LayerMessage)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 646
  x1 : t.getReg .x1 = pcOf (jalBT lay)
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : t.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x14 : t.getReg .x14 = BitVec.ofNat 64 (route index lay).1
  x15 : t.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : t.getReg .x16 = BitVec.ofNat 64 (SIG + 16 * layIdx lay)
  x17 : t.getReg .x17 = BitVec.ofNat 64 (target lay)
  x18 : t.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : BaseL sk cache t
  hlay : lay ≠ 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC msg.1
  encR : DigAt t (ENC + 48) msg.2.2
  pad0 : msg.2.1 = 0
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
structure LayNext (sk : SecretKey) (cache : Bytes 131072) (ret index : Nat) (root : T3.LayerMessage) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf ret
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : BaseL sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC root.1
  encR : DigAt t (ENC + 48) root.2.2
  pad0 : root.2.1 = 0
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
theorem signLayers_low (cache : Cache) (index : Nat) {lay : Layer} (hlay : lay ≠ 0) (msg : T3.LayerMessage) :
    signLayers cache index (lay.val + 1) msg = (do
      let some (_, digits) ← counterSearch lay (route index lay).2 (route index lay).1 msg 0 counterLimit
        | pure none
      let (levels, values) ← buildTree lay (route index lay).2 (route index lay).1 digits
      let some previous ← signLayers cache index lay.val ((levels.getD (height lay - 1) []).getD 0 0, 0,
        (levels.getD (height lay - 1) []).getD 1 0) | pure none
      pure (some (previous ++ [(values, (List.range (height lay)).map fun j =>
        (levels.getD j []).getD ((route index lay).1 / 2 ^ j ^^^ 1) 0)]))) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals rfl
section layer
variable {sk : SecretKey} {cache : Bytes 131072}
theorem lower_layer (hK : CounterSearchSpec sk) {lay : Layer} {index : Nat} {msg : T3.LayerMessage} {t : MachineState}
    (h : LayEntry sk cache lay index msg t) {W : Nat}
    (hnext : ∀ (root : T3.LayerMessage) v, LayNext sk cache (jalBT lay + 1) index root v →
      TBSim image sk v W (signLayers (cacheDec cache) index lay.val root) (SLPost v lay.val)) :
    TBSim image sk t (csCost lay + (1 + (btCost + W))) (signLayers (cacheDec cache) index (lay.val + 1) msg)
      (SLPost t (lay.val + 1)) := by
  have hlay := h.hlay
  obtain ⟨hli, hls, hl0, hl1⟩ := lay_facts hlay
  have hH := height_low hlay
  have hSIG : SIG = 28672 := rfl
  obtain ⟨hleaf, htree⟩ := route_lt h.hidx lay
  have hcs : CsPre t lay (route index lay).2 (route index lay).1 msg (jalBT lay) :=
    { pc := h.pc
      x1 := h.x1
      x5 := h.base.x5
      x8 := h.x8
      x9 := h.x9
      x18 := h.x18
      x17 := h.x17
      x26 := by rw [h.x26, chainCount_low hlay]
      x27 := by rw [h.x27, n4_low hlay]
      htree := htree
      hleaf := by have : 2 ^ height lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      rR := h.encR
      hpad := h.pad0
      msg := h.enc
      c32 := h.c32
      z40 := h.base.zero _ (by sgo) (by unfold NeverWL; simp)
      table := h.base.table }
  rw [signLayers_low _ _ hlay]
  refine TBSim.bind (hK t lay _ _ msg (jalBT lay) hcs) (fun r u hu => ?_)
  rcases r with _ | ⟨c, ds⟩
  · exact TBSim.mono (TBSim.pure hu) (by omega) (fun _ _ h => h)
  obtain ⟨upc, -, ⟨v0, hdec⟩, udig, uc32, ur, uf, -⟩ := hu
  obtain ⟨-, hdb⟩ := decode_digits hdec
  obtain ⟨u1, st1, u1pc, u1x1, u1r, u1f⟩ := blkJal_spec hlay u upc
  have g1 : ∀ r, r ∉ csRegs ++ [.x1] → u1.getReg r = t.getReg r := fun r hr => (ur.trans u1r).get hr
  have fu1 : Frame t u1 CsW := (uf.trans u1f).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact h.elim)
  have hbt : BtPre sk cache lay (route index lay).2 (route index lay).1 ds (SIG + 16 * layIdx lay) u1 :=
    { x2 := by rw [g1 _ (by decide), h.x2]
      x8 := by rw [g1 _ (by decide), h.x8]
      x9 := by rw [g1 _ (by decide), h.x9]
      x14 := by rw [g1 _ (by decide), h.x14]
      x15 := by rw [g1 _ (by decide), h.x15]
      x16 := by rw [g1 _ (by decide), h.x16]
      x26 := by rw [g1 _ (by decide), h.x26]
      x27 := by rw [g1 _ (by decide), h.x27]
      x31 := by rw [g1 _ (by decide), h.x31]
      base := h.base.frame fu1 (ur.trans u1r) (by decide) (fun A _ hb hw => by
        unfold BaseAL NeverWL Search.TOP_DATA at hb
        unfold CsW at hw
        sgo)
      hlay := hlay
      htree := htree
      hroute := by
        intro l hl
        have hidx := h.hidx
        fin_cases lay <;> norm_num [route, height] at * <;> omega
      hsel := hleaf
      hdb := fun i hi => by
        have := hdb i (by rw [chainCount_low hlay]; exact hi)
        simpa [T3.maxDigit, hlay] using this
      digits := fun i hi => by
        rw [u1f.getByte (by sgo) (fun h => h)]
        exact udig i (by rw [chainCount_low hlay]; exact hi)
      hsb := ⟨by omega, by omega⟩
      hsb8 := by omega }
  refine TBSim.steps st1 (TBSim.bind (buildTree_tbsim hbt u1pc u1x1) (fun lv v hv => ?_))
  obtain ⟨levels, values⟩ := lv
  obtain ⟨vpc, vlen, vvals, vpath, vroot, vrootR, vbase, vr, vf⟩ := hv
  have gv : ∀ r, r ∉ csRegs ++ [.x1] ++ btAllRegs → v.getReg r = t.getReg r := fun r hr =>
    ((ur.trans u1r).trans vr).get hr
  have fuv : Frame u v (fun A => BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A) :=
    (u1f.trans vf).mono (fun A _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)
  have ftv : Frame t v (fun A => CsW A ∨ BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A) :=
    fu1.trans vf
  have nB : ∀ A, (A = IDXV ∨ A = ENC + 32) → ¬ BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A := by
    intro A hA hw
    have := btAllW_layW hlay hw
    unfold BtAllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h6 | h6 <;> rw [h6] at hw <;> simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at hw <;>
      sgo
  have hnx : LayNext sk cache (jalBT lay + 1) index ((levels.getD (height lay - 1) []).getD 0 0, 0,
      (levels.getD (height lay - 1) []).getD 1 0) v :=
    { pc := vpc
      x2 := by rw [gv _ (by decide), h.x2]
      x26 := by rw [gv _ (by decide), h.x26]
      x27 := by rw [gv _ (by decide), h.x27]
      x31 := by rw [gv _ (by decide), h.x31]
      base := vbase
      hidx := h.hidx
      idx := by
        rw [ftv.get (by sgo) (fun hw => by
          rcases hw with hw | hw
          · unfold CsW at hw; sgo
          · exact nB _ (Or.inl rfl) hw)]
        exact h.idx
      enc := vroot
      encR := vrootR
      pad0 := rfl
      c32 := by rw [fuv.get (by sgo) (nB _ (Or.inr rfl))]; exact uc32 }
  refine TBSim.bind (W₂ := 0) (hnext _ v hnx) (fun r w hw => ?_)
  rcases r with _ | previous
  · exact TBSim.pure hw
  obtain ⟨wh, wlen, wpieces, wf⟩ := hw
  refine TBSim.pure ⟨wh, by simp [wlen], fun lay' hlay' => ?_, ?_⟩
  · by_cases hlt : lay'.val < lay.val
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [wlen]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      exact wpieces lay' hlt
    · have heq : lay' = lay := Fin.ext (by omega)
      subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), wlen, Nat.sub_self]
      have nW : ∀ A, SIG + 16 * layIdx lay' ≤ A → A < SIG + 16 * (layIdx lay' + 43 + height lay') →
          ¬ LayW lay'.val A := fun A h1 h2 hw => hw.2 ⟨by omega, by omega⟩
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [chainCount_low hlay] at hi
        have := vvals i (by rw [vlen]; exact hi)
        rw [show SIG + 16 * layIdx lay' + 16 * i = SIG + 16 * (layIdx lay' + i) by ring] at this
        exact this.frame wf (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))
      · rw [chainCount_low hlay]
        have := vpath j (by simp [hj])
        rw [show SIG + 16 * layIdx lay' + 16 * 43 + 16 * j = SIG + 16 * (layIdx lay' + 43 + j) by ring] at this
        exact this.frame wf (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))
  · exact (ftv.trans wf).mono (fun A _ hA => by
      rcases hA with (hA | hA) | hA
      · exact csW_layW hA
      · exact btAllW_layW hlay hA
      · exact layW_succ hA)
theorem entry2 {index : Nat} {root : T3.LayerMessage} {v : MachineState} (h : LayNext sk cache 397 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 2 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk397_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_2]
      x14 := by rw [tx14, route_2]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_2]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by sgo) (fun h => h) (fun h => h)
      encR := h.encR.frame tf (by sgo) (fun h => h) (fun h => h)
      pad0 := h.pad0
      c32 := by rw [tf.get (by sgo) (fun h => h)]; exact h.c32 }
theorem entry1 {index : Nat} {root : T3.LayerMessage} {v : MachineState} (h : LayNext sk cache 412 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 1 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk412_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_1]
      x14 := by rw [tx14, route_1]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_1]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by sgo) (fun h => h) (fun h => h)
      encR := h.encR.frame tf (by sgo) (fun h => h) (fun h => h)
      pad0 := h.pad0
      c32 := by rw [tf.get (by sgo) (fun h => h)]; exact h.c32 }
theorem layer0_link (hL0 : L0Spec sk cache) {index : Nat} {root : T3.LayerMessage} {v : MachineState}
    (h : LayNext sk cache 427 index root v) :
    TBSim image sk v L0Cost (signLayers (cacheDec cache) index 1 root) (SLPost v 1) := by
  refine TBSim.mono (hL0 index root v ⟨h.pc, h.base, h.hidx, h.idx, h.enc, h.encR, h.pad0, h.c32⟩) le_rfl (fun r u hu => ?_)
  rcases r with _ | ps
  · exact hu
  obtain ⟨vals, path, rfl, uh, uv, up, uf⟩ := hu
  refine ⟨uh, rfl, fun lay hlay => ?_, uf.mono (fun A _ hA => hA)⟩
  have h0 : lay = 0 := Fin.ext (by omega)
  subst h0
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := uv i hi
    rw [show SIG + 2192 + 16 * i = SIG + 16 * (layIdx 0 + i) by simp [layIdx]; ring] at this
    exact this
  · have := up j hj
    rw [show SIG + 3056 + 16 * j = SIG + 16 * (layIdx 0 + chainCount 0 + j) by simp [layIdx, chainCount]; ring]
      at this
    exact this
def layW1 : Nat := L0Cost
def layW2 : Nat := 14 + (csCost 1 + (1 + (btCost + layW1)))
def layW3 : Nat := 14 + (csCost 2 + (1 + (btCost + layW2)))
def layersC : Nat := csCost 3 + (1 + (btCost + layW3))
theorem layers_tbsim (hK : CounterSearchSpec sk) (hL0 : L0Spec sk cache) {index : Nat} {root : T3.LayerMessage}
    {t : MachineState} (h : LayEntry sk cache 3 index root t) :
    TBSim image sk t layersC (signLayers (cacheDec cache) index 4 root) (SLPost t 4) := by
  have L1 : ∀ (root : T3.LayerMessage) v, LayNext sk cache (jalBT 1 + 1) index root v →
      TBSim image sk v layW1 (signLayers (cacheDec cache) index (1 : Layer).val root) (SLPost v (1 : Layer).val) :=
    fun root v hv => layer0_link hL0 hv
  have L2 : ∀ (root : T3.LayerMessage) v, LayNext sk cache (jalBT 2 + 1) index root v →
      TBSim image sk v layW2 (signLayers (cacheDec cache) index (2 : Layer).val root) (SLPost v (2 : Layer).val) :=
    fun root v hv => by
      obtain ⟨t1, st, ht1, hf⟩ := entry1 hv
      exact TBSim.steps st (TBSim.mono (lower_layer hK ht1 L1) le_rfl (SLPost.pre hf))
  have L3 : ∀ (root : T3.LayerMessage) v, LayNext sk cache (jalBT 3 + 1) index root v →
      TBSim image sk v layW3 (signLayers (cacheDec cache) index (3 : Layer).val root) (SLPost v (3 : Layer).val) :=
    fun root v hv => by
      obtain ⟨t1, st, ht1, hf⟩ := entry2 hv
      exact TBSim.steps st (TBSim.mono (lower_layer hK ht1 L2) le_rfl (SLPost.pre hf))
  exact lower_layer hK h L3
end layer
end SigGolfCandidate.T3M.Sign.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest signLayers)
theorem counterSearchSpec (sk : BitVec 256) : CounterSearchSpec sk := fun s lay tree leaf msg ret h =>
  (Search.counterSearch_spec Search.kernAt_sign s lay tree leaf msg ret
    ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.rR, h.hpad, h.msg, h.c32,
      h.z40, h.table⟩).mono le_rfl (fun r t ht => by rcases r with _ | _; exacts [⟨ht.pc, ht.x5, ht.x10⟩, ht])
theorem layers_checked {sk : BitVec 256} {cache : Bytes 131072}
    {index : Nat} {root : T3.LayerMessage} {t : MachineState}
    (h : LayEntry sk cache 3 index root t) :
    TBSim image sk t layersC (signLayers (cacheDec cache) index 4 root) (SLPost t 4) := by
  exact layers_tbsim (counterSearchSpec sk) (l0Spec_of (counterSearchSpec sk)) h
end SigGolfCandidate.T3M.Sign.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest signLayers)
theorem entry370 {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    {root : Digest} {s : MachineState} (hp : s.pc = pcOf 370)
    (hb : Base sk cache s) (hi : index < 2 ^ 31)
    (hx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index)
    (hr : DigAt s FOUT root)
    (hc : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32) :
    ∃ t, Steps image s 26 26 t ∧ LayEntry sk cache 3 index (root, 0, 0) t ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  obtain ⟨t, st, tp, t1, m0, m8, t2, t31, t26, t27, t8, t15, t16, t17, t18, t14, t9, tr, tf⟩ := blk370_spec s hp index hi hx
  refine ⟨t, st, ?_, tf⟩
  exact { pc := tp
          x1 := t1
          x2 := t2
          x8 := t8
          x9 := by rw [t9, route_3]
          x14 := by rw [t14, route_3]
          x15 := t15
          x16 := t16
          x17 := t17
          x18 := by rw [t18, route_3]
          x26 := t26
          x27 := t27
          x31 := t31
          base := (hb.frame tf tr (by decide) (fun A _ hA hw => by
            unfold BaseA NeverW Search.TOP_DATA at hA
            sg_omega)).toBaseL
          hlay := by decide
          hidx := hi
          idx := by rw [tf.get (by sg_omega) (by sg_omega)]; exact hx
          enc := ⟨by rw [m0]; exact hr.1, by rw [m8]; exact hr.2⟩
          encR := by
            have hb3 := hb.frame tf tr (by decide) (fun A _ hA hw => by
              unfold BaseA NeverW Search.TOP_DATA at hA
              sg_omega)
            exact ⟨by rw [hb3.zero _ (by sg_omega) (by unfold NeverW; simp)]
                      show (0 : BitVec 64) = BitVec.extractLsb' 0 64 (0 : BitVec 128); decide,
              by rw [hb3.zero _ (by sg_omega) (by unfold NeverW; simp)]
                 show (0 : BitVec 64) = BitVec.extractLsb' 64 64 (0 : BitVec 128); decide⟩
          pad0 := rfl
          c32 := by rw [tf.get (by sg_omega) (by sg_omega)]; exact hc }
theorem layers_from370 {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    {root : Digest} {s : MachineState} (hp : s.pc = pcOf 370)
    (hb : Base sk cache s) (hi : index < 2 ^ 31)
    (hx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index)
    (hr : DigAt s FOUT root)
    (hc : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32) :
    TBSim image sk s (26 + layersC)
      (signLayers (cacheDec cache) index 4 (root, 0, 0)) (SLPost s 4) := by
  obtain ⟨t, st, ht, hf⟩ := entry370 hp hb hi hx hr hc
  refine TBSim.steps st (TBSim.mono (layers_checked ht) le_rfl (fun r u hu => ?_))
  cases r with
  | none => exact hu
  | some ps =>
    obtain ⟨hpc, hlen, hpieces, hframe⟩ := hu
    refine ⟨hpc, hlen, hpieces, (hf.trans hframe).mono ?_⟩
    intro A hA hw; rcases hw with hw | hw; · unfold LayW lstart; constructor <;> sg_omega
    · exact hw
end SigGolfCandidate.T3M.Sign.Boundary
end
