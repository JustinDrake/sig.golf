import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck0
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck1
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck2
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck0
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck1
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck2
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck3
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Routine
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildBridge
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Drv
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChildESem
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region

section







namespace ClaudeWCT.W9.Machine.Expand
theorem routineOK_all (x : Nat) (hx : x < 728) : routineOK x = true := by
  have key : ∀ lo n, (List.range' lo n).all routineOK = true → lo ≤ x → x < lo + n → routineOK x = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : x < 64; · exact key 0 64 routineOK_0 (by omega) h0
  by_cases h64 : x < 128; · exact key 64 64 routineOK_64 (by omega) h64
  by_cases h128 : x < 192; · exact key 128 64 routineOK_128 (by omega) h128
  by_cases h192 : x < 256; · exact key 192 64 routineOK_192 (by omega) h192
  by_cases h256 : x < 320; · exact key 256 64 routineOK_256 (by omega) h256
  by_cases h320 : x < 384; · exact key 320 64 routineOK_320 (by omega) h320
  by_cases h384 : x < 448; · exact key 384 64 routineOK_384 (by omega) h384
  by_cases h448 : x < 512; · exact key 448 64 routineOK_448 (by omega) h448
  by_cases h512 : x < 576; · exact key 512 64 routineOK_512 (by omega) h512
  by_cases h576 : x < 640; · exact key 576 64 routineOK_576 (by omega) h576
  by_cases h640 : x < 704; · exact key 640 64 routineOK_640 (by omega) h640
  exact key 704 24 routineOK_704 (by omega) (by omega)
theorem jtOK_all (x : Nat) (hx : x < 16016) : jtOK x = true := by
  have key : ∀ lo n, (List.range' lo n).all jtOK = true → lo ≤ x → x < lo + n → jtOK x = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : x < 1024; · exact key 0 1024 jtOK_0 (by omega) h0
  by_cases h1024 : x < 2048; · exact key 1024 1024 jtOK_1024 (by omega) h1024
  by_cases h2048 : x < 3072; · exact key 2048 1024 jtOK_2048 (by omega) h2048
  by_cases h3072 : x < 4096; · exact key 3072 1024 jtOK_3072 (by omega) h3072
  by_cases h4096 : x < 5120; · exact key 4096 1024 jtOK_4096 (by omega) h4096
  by_cases h5120 : x < 6144; · exact key 5120 1024 jtOK_5120 (by omega) h5120
  by_cases h6144 : x < 7168; · exact key 6144 1024 jtOK_6144 (by omega) h6144
  by_cases h7168 : x < 8192; · exact key 7168 1024 jtOK_7168 (by omega) h7168
  by_cases h8192 : x < 9216; · exact key 8192 1024 jtOK_8192 (by omega) h8192
  by_cases h9216 : x < 10240; · exact key 9216 1024 jtOK_9216 (by omega) h9216
  by_cases h10240 : x < 11264; · exact key 10240 1024 jtOK_10240 (by omega) h10240
  by_cases h11264 : x < 12288; · exact key 11264 1024 jtOK_11264 (by omega) h11264
  by_cases h12288 : x < 13312; · exact key 12288 1024 jtOK_12288 (by omega) h12288
  by_cases h13312 : x < 14336; · exact key 13312 1024 jtOK_13312 (by omega) h13312
  by_cases h14336 : x < 15360; · exact key 14336 1024 jtOK_14336 (by omega) h14336
  exact key 15360 656 jtOK_15360 (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand
end

section



set_option maxRecDepth 4000
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
def level6 (k index j : Nat) (path : Fin 7 → Digest) (value : Digest) : M Digest :=
  let other := path 6
  let pair := if j / 2 ^ 6 % 2 = 0 then (value, other) else (other, value)
  SigGolfCandidate.T3.nodeHash 11 k index 1 pair.1 pair.2
theorem codewordL_eq (r : Fin 728) (i : Fin 7) : WCT9.digit r i = (codewordL r.val).getD i.val 0 := by
  unfold WCT9.digit WCT9.codeword codewordL
  rw [List.getD_eq_getElem (l := WCT9.compositions 4 7 6) (d := []) (by rw [WCT9.codebook_card]; exact r.isLt)]
theorem mapM_finRange_eq {β : Type} (f : Fin 7 → M β) (g : Nat → M β) (h : ∀ i : Fin 7, f i = g i.val) :
    (List.finRange 7).mapM f = (List.range' 0 7).mapM g := by
  have : f = g ∘ Fin.val := funext h
  rw [this, ← List.mapM_map, Merkle.finRange_map_val, List.range_eq_range']
theorem recoverCoordinate_split (sig : WCT9.Signature) (index : Nat) (N : HashOutput) (k : WCT9.Coord) :
    WCT9.recoverCoordinate sig index N k =
      (chainsFrom index k.val (WCT9.child N k).val (codewordL (WCT9.rank N k).val)
          (fun t => if h : t < 7 then (sig.openings k).values ⟨t, h⟩ else 0) 0 >>= fun ends =>
        (WCT9.leafHash index k.val (WCT9.child N k).val ends >>=
          Merkle.sixLevels k.val index (WCT9.child N k).val (Merkle.finPath (sig.openings k).path)) >>=
        level6 k.val index (WCT9.child N k).val (sig.openings k).path) := by
  unfold WCT9.recoverCoordinate
  simp only
  have hm := mapM_finRange_eq (fun i => WCT9.chain index k.val (WCT9.child N k).val i.val
      (3 - WCT9.digit (WCT9.rank N k) i) (WCT9.digit (WCT9.rank N k) i) ((sig.openings k).values i))
    (fun i => WCT9.chain index k.val (WCT9.child N k).val i (3 - (codewordL (WCT9.rank N k).val).getD i 0)
      ((codewordL (WCT9.rank N k).val).getD i 0) (if h : i < 7 then (sig.openings k).values ⟨i, h⟩ else 0))
    (fun i => by simp only [codewordL_eq, dif_pos i.isLt])
  unfold chainsFrom
  rw [show 7 - 0 = 7 from rfl, ← hm]
  refine bind_congr fun ends => ?_
  rw [bind_assoc]
  refine bind_congr fun root => ?_
  have := Merkle.pathSplit k index (WCT9.child N k).val (sig.openings k).path root (WCT9.child N k).isLt
  rw [this]
  rfl
end ClaudeWCT.W9.Machine.Expand
end

section





namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem dOff_succ (k : Nat) (hk : k < 9) : dOff (k + 1) = dOff k + dLen k + 2 := by
  interval_cases k <;> rfl
theorem disp_spec {im : Image} (hc : NewCodeAt im) (k : Nat) (hk : k < 9) (N : HashOutput) (index : Nat)
    (hidx : index < 2 ^ 31) (s : MachineState) (hpc : s.pc = pcOf (base + dOff k))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (k - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (k - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s (dLen k) (dLen k) t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨k, hk⟩) ∧
      t.getReg .x1 = pcOf (base + dOff k + dLen k) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase k) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * k) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨k, hk⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨k, hk⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * k + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  interval_cases k
  · exact disp_0 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_1 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_2 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_3 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_4 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_5 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_6 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_7 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
  · exact disp_8 hc N index hidx s hpc h22 h29 h24 h2 h8 h28 hN
theorem ret_spec {im : Image} (hc : NewCodeAt im) (k : Nat) (hk : k < 9) (s : MachineState)
    (hpc : s.pc = pcOf (base + dOff k + dLen k)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + dOff k + dLen k + 1) ∧
      t.getReg .x12 = BitVec.ofNat 64 (fslot k) ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  interval_cases k
  · exact ret_0 hc s hpc
  · exact ret_1 hc s hpc
  · exact ret_2 hc s hpc
  · exact ret_3 hc s hpc
  · exact ret_4 hc s hpc
  · exact ret_5 hc s hpc
  · exact ret_6 hc s hpc
  · exact ret_7 hc s hpc
  · exact ret_8 hc s hpc
theorem jt_step {im : Image} (hc : NewCodeAt im) (f : Nat) (hf : f < 16016) (s : MachineState)
    (hpc : s.pc = pcOf (jt0 + f)) :
    Steps im s 1 1 (s.setPC (pcOf (routineEntry.getD (f % 728) 0))) := by
  have h := jtOK_all f hf
  unfold jtOK at h
  split at h
  · rename_i w hw
    have hj : jalTo w (jt0 + f) = some (routineEntry.getD (f % 728) 0) := by simpa using h
    obtain ⟨imm, hd, hoff⟩ := jalTo_sound hj
    exact jal_x0_step (codeAt_one hc hw) hd hoff s hpc
  · cases h
structure FtsIn (sig : WCT9.Signature) (N : HashOutput) (sF : MachineState) : Prop where
  out : OutAt sF 0x60 N
  adm : WCT9.admissible N = true
  placed : Placed N sig sF
  bank : HdrBankOK sF
structure DrvInv (sig : WCT9.Signature) (N : HashOutput) (sF : MachineState) (k : Nat) (roots : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (base + dOff k)
  regs : DRegs (N.toNat % 2 ^ 31) t
  x8 : t.getReg .x8 = BitVec.ofNat 64 (regBase (k - 1))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (k - 1))
  len : roots.length = k
  roots : ∀ k', k' < k → DigAt t (fslot k') (roots.getD k' 0)
  frame : Frame sF t (fun A => (0x840 ≤ A ∧ A < regBase k) ∨ (0x700 ≤ A ∧ A < 0x700 + 16 * (k + 2)))
def coordCost : Nat := 430
theorem level6_eq (k index j : Nat) (path : Fin 7 → Digest) (v : Digest) :
    level6 k index j path v = SigGolfCandidate.T3.shortHash (Merkle.rootIn k index j v 0 (path 6)) := by
  unfold level6 Merkle.rootIn SigGolfCandidate.T3.nodeHash Merkle.bitAt
  have hz : SphincsSecurity.bytesLE 16 (0#128 : BitVec 128) = SigGolfCandidate.T3.zero16 := Verify.bytesLE16_zero
  split <;> simp [Verify.blk4, hz, List.append_assoc]
theorem region_facts {sig : WCT9.Signature} {N : HashOutput} {sF t : MachineState} (hin : FtsIn sig N sF)
    (k : Nat) (hk : k < 9)
    (hfr : ∀ o, o < 1024 → t.getMem (BitVec.ofNat 64 (regBase k + o)) = sF.getMem (BitVec.ofNat 64 (regBase k + o))) :
    (∀ i (h : i < 7), DigAt t (regBase k + offC i + 48) ((sig.openings ⟨k, hk⟩).values ⟨i, h⟩)) ∧
    (∀ i (h : i < 7), DigAt t (regBase k + slotC i) ((sig.openings ⟨k, hk⟩).values ⟨i, h⟩)) ∧
    (∀ i, i < 7 → PadsZ (regBase k) i t) ∧
    (∀ l, l < 7 → DigAt t (regBase k + Merkle.padO l) 0) ∧
    (∀ l (h : l < 7), DigAt t (regBase k + Merkle.sibO l (WCT9.child N ⟨k, hk⟩).val)
      ((sig.openings ⟨k, hk⟩).path ⟨l, h⟩)) := by
  have tr : ∀ o d, o % 8 = 0 → o + 16 ≤ 1024 → DigAt sF (regBase k + o) d → DigAt t (regBase k + o) d :=
    fun o d h8 h16 hd => ⟨(hfr o (by omega)).trans hd.1, by
      rw [show regBase k + o + 8 = regBase k + (o + 8) by omega, hfr (o + 8) (by omega),
        ← show regBase k + o + 8 = regBase k + (o + 8) by omega]; exact hd.2⟩
  have pd := fun o (h8 : o % 8 = 0) (h16 : o + 16 ≤ 1024) d hw => placed_digAt hin.placed k hk o h8 h16 d hw
  refine ⟨fun i h => ?_, fun i h => ?_, fun i h => ?_, fun l h => ?_, fun l h => ?_⟩
  · have hb := offC_bounds i h
    rw [Nat.add_assoc]
    exact tr _ _ (by omega) (by omega) (pd _ (by omega) (by omega) _ (win_chainVal _ _ ⟨i, h⟩))
  · have hb := slotC_bounds i h
    exact tr _ _ (by omega) (by omega) (pd _ (by omega) (by omega) _ (win_leafSlot _ _ ⟨i, h⟩))
  · have hb := offC_bounds i h
    have z0 := tr _ _ (by omega) (by omega) (pd (offC i + 0) (by omega) (by omega) 0
      (by rw [win_chainPad _ _ i h 0 (Or.inl rfl), zeros16]))
    have z32 := tr _ _ (by omega) (by omega) (pd (offC i + 32) (by omega) (by omega) 0
      (by rw [win_chainPad _ _ i h 32 (Or.inr rfl), zeros16]))
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := z0.1; simp only [Nat.add_zero] at this; exact this.trans rfl
    · have := z0.2; simp only [Nat.add_zero] at this; exact this.trans rfl
    · have := z32.1; rw [← Nat.add_assoc] at this; exact this.trans rfl
    · have := z32.2; rw [show regBase k + (offC i + 32) + 8 = regBase k + offC i + 40 by omega] at this
      exact this.trans rfl
  · have := tr _ _ (by unfold Merkle.padO Merkle.blkO; omega) (by unfold Merkle.padO Merkle.blkO; omega)
      (pd (Merkle.padO l) (by unfold Merkle.padO Merkle.blkO; omega) (by unfold Merkle.padO Merkle.blkO; omega) 0
        (by unfold Merkle.padO Merkle.blkO; rw [win_mpad _ _ ⟨l, h⟩, zeros16]))
    exact this
  · have hbit := Merkle.bitAt_lt (WCT9.child N ⟨k, hk⟩).val l
    exact tr _ _ (by unfold Merkle.sibO Merkle.blkO; omega) (by unfold Merkle.sibO Merkle.blkO; omega)
      (pd _ (by unfold Merkle.sibO Merkle.blkO; omega) (by unfold Merkle.sibO Merkle.blkO; omega) _
        (by unfold Merkle.sibO Merkle.blkO Merkle.bitAt; exact win_sib _ _ ⟨l, h⟩))
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000
theorem field_lt_of_adm (N : HashOutput) (k : Nat) (hk : k < 9) (hadm : WCT9.admissible N = true) :
    WCT9.field N ⟨k, hk⟩ < 16016 := by
  have := ((admissible_iff N).mp hadm).2 k (Nat.zero_le _) hk
  exact this
theorem rank_eq_mod (N : HashOutput) (k : Nat) (hk : k < 9) :
    (WCT9.rank N ⟨k, hk⟩).val = WCT9.field N ⟨k, hk⟩ % 728 := rfl
theorem codewordL_le3 (r : Nat) (hr : r < 728) (t : Nat) (ht : t < 7) : (codewordL r).getD t 0 ≤ 3 := by
  have := WCT9.digit_le_three ⟨r, hr⟩ ⟨t, ht⟩
  rwa [codewordL_eq] at this
theorem hw5_bank {s : MachineState} (hb : HdrBankOK s) (k t st : Nat) (hk : k < 9) (ht : t < 7) (hst : st < 3) :
    s.getMem (BitVec.ofNat 64 (HB0 + 2048 + 512 * k - 2048 + (64 * t + 8 * st))) = hw5 k t st := by
  rw [show HB0 + 2048 + 512 * k - 2048 + (64 * t + 8 * st) = HB0 + 512 * k + 64 * t + 8 * st by unfold HB0; omega]
  exact (hb k hk).1 t st ht hst
theorem regBase_bounds (k : Nat) (hk : k < 9) : regBase k % 64 = 0 ∧ 0x840 ≤ regBase k ∧ regBase k + 1024 ≤ 0x2c40 := by
  unfold regBase; omega
theorem chainsWr_range {B : Nat} {z : List Nat} {A : Nat} (h : chainsWr B z 7 A) : B + 464 ≤ A ∧ A < B + 1024 := by
  obtain ⟨t', ht', _, hw⟩ := h
  unfold chainWr offC slotC at hw
  split_ifs at hw <;> omega
theorem childWrites_range {j off : Nat} (h : off ∈ Merkle.childWrites j) : off + 8 ≤ 464 :=
  (Merkle.childWrites_bound h).2
theorem fslot_bounds (k : Nat) (hk : k < 9) : fslot k % 16 = 0 ∧ 0x700 + 16 * (k + 1) ≤ fslot k + 16 ∧
    fslot k + 32 ≤ 0x700 + 16 * (k + 3) ∧ (0 < k → 0x700 + 16 * (k + 1) = fslot k) := by
  unfold fslot; split <;> omega
theorem hdr0_index (tag k index : Nat) (hidx : index < 2 ^ 31) : hdr0 tag k index 0 = hdr0 tag k 0 0 := by
  have h0 : index / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [hdr0, h0, Nat.zero_div]
theorem leafHdr_digAt {w : MachineState} {B k index j : Nat} (hidx : index < 2 ^ 31) (hj : j < 128)
    (h0 : w.getMem (BitVec.ofNat 64 (B + 896)) = BitVec.ofNat 64 (hdr0 6 k 0 0))
    (h1 : w.getMem (BitVec.ofNat 64 (B + 904)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)) :
    DigAt w (B + 896) (WCT9.wctHeader 6 k index 0 j) := by
  rw [WCT9.leaf_header_eq]
  constructor
  · rw [h0, header_lo, if_neg (by decide), hdr0_index _ _ _ hidx]
  · rw [show B + 896 + 8 = B + 904 by omega, h1, header_hi, if_neg (by decide), hdr1_eq _ _ (by omega) (by omega)]
theorem pc_child (j : Nat) : (BitVec.ofNat 64 (17468 + 256 * j)) &&& 18446744073709551614#64 = pcOf (cbE j) := by
  have : BitVec.ofNat 64 (17468 + 256 * j) = pcOf (cbE j) := by
    unfold pcOf cbE cb0; congr 1; ring
  rw [this, not1_eq, pcOf_and_not1]
theorem coord_tb {im : Image} (hc : NewCodeAt im) {sk : BitVec 256} {sig : WCT9.Signature} {N : HashOutput}
    {sF : MachineState} (hin : FtsIn sig N sF) (k : Nat) (hk : k < 9) (roots : List Digest) (t : MachineState)
    (hI : DrvInv sig N sF k roots t) :
    TBSim im sk t coordCost (WCT9.recoverCoordinate sig (N.toNat % 2 ^ 31) N ⟨k, hk⟩)
      (fun root u => DrvInv sig N sF (k + 1) (roots ++ [root]) u) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hj : (WCT9.child N ⟨k, hk⟩).val < 128 := (WCT9.child N ⟨k, hk⟩).isLt
  have hf : WCT9.field N ⟨k, hk⟩ < 16016 := field_lt_of_adm N k hk hin.adm
  have hr : WCT9.field N ⟨k, hk⟩ % 728 < 728 := Nat.mod_lt _ (by decide)
  have hrb := regBase_bounds k hk
  have hfs := fslot_bounds k hk
  set index := N.toNat % 2 ^ 31 with hindex
  set j := (WCT9.child N ⟨k, hk⟩).val with hjdef
  have hlow : ∀ A, A < 0x700 → t.getMem (BitVec.ofNat 64 A) = sF.getMem (BitVec.ofNat 64 A) :=
    fun A hA => hI.frame A (by omega) (by omega)
  have hregk : ∀ o, o < 1024 → t.getMem (BitVec.ofNat 64 (regBase k + o)) =
      sF.getMem (BitVec.ofNat 64 (regBase k + o)) :=
    fun o ho => hI.frame _ (by omega) (by omega)
  have hhigh : ∀ A, 0x3000 ≤ A → A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = sF.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => hI.frame A h2 (by omega)
  have hout : OutAt t 0x60 N := fun i hi => (hlow _ (by omega)).trans (hin.out i hi)
  obtain ⟨t1, s1, p1, x1_1, x8_1, x28_1, x4_1, x23_1, x27_1, x11_1, keep1, f1⟩ :=
    disp_spec hc k hk N index hidx t hI.pc hI.regs.x22 hI.regs.x29 hI.regs.x24 hI.regs.x2 hI.x8 hI.x28 hout
  have s2 := jt_step hc _ hf t1 p1
  set t2 := t1.setPC (pcOf (routineEntry.getD (WCT9.field N ⟨k, hk⟩ % 728) 0)) with ht2
  have m21 : ∀ A, t2.getMem A = t.getMem A := fun A => by
    rw [show t2.getMem A = t1.getMem A from rfl]
    have := f1 A.toNat A.isLt (fun h => h)
    simpa using this
  have r21 : ∀ r, t2.getReg r = t1.getReg r := fun r => rfl
  have hro := routineOK_all _ hr
  unfold routineOK at hro
  obtain ⟨c, hw, hc300⟩ : ∃ c, walk (codewordL (WCT9.field N ⟨k, hk⟩ % 728)) 64 0
      (routineEntry.getD (WCT9.field N ⟨k, hk⟩ % 728) 0) = some c ∧ c ≤ routineCost := by
    revert hro
    cases walk (codewordL (WCT9.field N ⟨k, hk⟩ % 728)) 64 0 (routineEntry.getD (WCT9.field N ⟨k, hk⟩ % 728) 0) with
    | none => simp
    | some c => intro h; exact ⟨c, rfl, by simpa using h⟩
  have hreg2 : ∀ o, o < 1024 → t2.getMem (BitVec.ofNat 64 (regBase k + o)) =
      sF.getMem (BitVec.ofNat 64 (regBase k + o)) := fun o ho => (m21 _).trans (hregk o ho)
  obtain ⟨rv, rl, rp, rmp, rs⟩ := region_facts hin k hk hreg2
  have hpre : RPre (regBase k) (HB0 + 2048 + 512 * k) k index j (codewordL (WCT9.field N ⟨k, hk⟩ % 728))
      (fun t => if h : t < 7 then (sig.openings ⟨k, hk⟩).values ⟨t, h⟩ else 0) t2 := by
    refine ⟨⟨by omega, by omega, by unfold HB0; omega, by unfold HB0; omega, by unfold HB0; omega⟩,
      by unfold HB0; omega, hk, hidx, hj, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun t' st ht hst => ?_, ?_,
      fun t' ht => rp t' ht, fun t' ht => ?_, fun t' ht _ => ?_, fun t' ht => codewordL_le3 _ hr t' ht⟩
    · rw [r21, x8_1]
    · rw [r21, x28_1]
    · rw [r21, x4_1]
    · rw [r21, keep1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hI.regs.x6
    · rw [r21, keep1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hI.regs.x7
    · rw [r21, keep1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hI.regs.x5
    · rw [r21, x11_1]
    · rw [m21, hhigh _ (by unfold HB0; omega) (by unfold HB0; omega)]
      exact hw5_bank hin.bank k t' st hk ht hst
    · rw [m21, hhigh _ (by unfold HB0; omega) (by unfold HB0; omega),
        show HB0 + 2048 + 512 * k - 2048 + 456 = HB0 + 512 * k + 456 by unfold HB0; omega]
      exact (hin.bank k hk).2.2
    · simp only [dif_pos ht]; exact rv t' ht
    · simp only [dif_pos ht]; exact rl t' ht
  have hW := walk_tb (sk := sk) hc hpre 64 0 _ c [] t2 hw (by omega) rfl
    ⟨rfl, hpre.regs, keepC.refl _, Frame.refl _ _, fun t' ht' => absurd ht' (by omega)⟩
  rw [recoverCoordinate_split]
  refine (TBSim.steps (s1.trans s2) (TBSim.bind (W₂ := 102 + (1 + (8 + 0))) hW
    (fun ends w hw' => ?_))).mono (by unfold coordCost routineCost at *; have := Nat.le_trans (le_refl _) hc300; unfold dLen; split <;> omega) (fun _ _ h => h)
  simp only [List.nil_append] at hw'
  have hlen := hw'.len
  have hpath : ∀ l (h : l < 7), Merkle.finPath (sig.openings ⟨k, hk⟩).path l = (sig.openings ⟨k, hk⟩).path ⟨l, h⟩ :=
    fun l h => by simp [Merkle.finPath, h]
  rw [show (⟨k, hk⟩ : WCT9.Coord).val = k from rfl]
  rw [← Merkle.childCanon k index j ends (Merkle.finPath (sig.openings ⟨k, hk⟩).path) hlen]
  have kw : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → r ≠ .x1 → r ≠ .x4 → r ≠ .x8 →
      r ≠ .x16 → r ≠ .x23 → r ≠ .x27 → r ≠ .x28 → w.getReg r = t.getReg r := by
    intro r a b c d e f g h i l m n o
    rw [hw'.keep r a b c d e f, r21, keep1 r g a h i c e l m n o]
  have wfr : ∀ o, o < 1024 → o + 8 ≤ 464 → w.getMem (BitVec.ofNat 64 (regBase k + o)) =
      t2.getMem (BitVec.ofNat 64 (regBase k + o)) := by
    intro o ho h464
    refine hw'.frame _ (by omega) ?_
    rintro (h | h | h)
    · have := chainsWr_range h; omega
    · omega
    · omega
  have hpreC : ChildPreE j (regBase k) k index (Merkle.leafFields k index j ends) (fun _ => 0)
      (Merkle.finPath (sig.openings ⟨k, hk⟩).path) w := by
    refine ⟨?_, by omega, by unfold MEMORY_BYTES; omega, ?_, ?_, hw'.a0, hw'.a1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hw'.pc, r21, x23_1, pc_child]
    · rw [kw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x5
    · rw [hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x8_1]
    · rw [hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x27_1,
        hhigh _ (by unfold HB0; omega) (by unfold HB0; omega), (hin.bank k hk).2.1]
      unfold Merkle.w0n; rw [hdr0_index _ _ _ hidx]
    · rw [kw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x22
    · intro h h1 h7
      have hh : Merkle.heapReg h = .x9 ∨ Merkle.heapReg h = .x13 ∨ Merkle.heapReg h = .x19 ∨
          Merkle.heapReg h = .x20 ∨ Merkle.heapReg h = .x21 ∨ Merkle.heapReg h = .x26 ∨ Merkle.heapReg h = .x30 := by
        unfold Merkle.heapReg; split <;> simp
      rw [kw _ (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)
        (by rcases hh with h | h | h | h | h | h | h <;> rw [h] <;> decide)]
      exact hI.regs.heaps h h1 h7
    · intro i hi
      unfold Merkle.leafFields Merkle.leafO
      by_cases h0 : i = 0
      · subst h0; simp only [if_true, Nat.mul_zero, Nat.add_zero]
        have := hw'.ends 0 (by decide); rwa [show slotC 0 = 880 from rfl] at this
      · by_cases h1 : i = 1
        · subst h1; simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
          exact leafHdr_digAt hidx hj hw'.h0 hw'.h1
        · simp only [h0, h1, if_false]
          have := hw'.ends (i - 1) (by omega)
          rwa [show slotC (i - 1) = 880 + 16 * i by unfold slotC; split <;> omega, ← Nat.add_assoc] at this
    · intro l hl
      have hm := rmp l (by omega)
      have hb : Merkle.padO l + 16 ≤ 464 := by unfold Merkle.padO Merkle.blkO; omega
      exact ⟨(wfr _ (by omega) (by omega)).trans hm.1, by
        rw [Nat.add_assoc, wfr _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.2⟩
    · intro l hl
      have hm := rs l (by omega)
      have hb : Merkle.sibO l j + 16 ≤ 464 := by
        unfold Merkle.sibO Merkle.blkO; have := Merkle.bitAt_lt j l; omega
      rw [hpath l (by omega)]
      exact ⟨(wfr _ (by omega) (by omega)).trans hm.1, by
        rw [Nat.add_assoc, wfr _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.2⟩
  refine TBSim.bind (W₂ := 1 + (8 + 0)) (child_tbE (sk := sk) hj hc (by omega) hpreC) (fun v t3 hpost => ?_)
  have pc3 : t3.pc = pcOf (base + dOff k + dLen k) := by
    rw [hpost.pc, hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x1_1,
      pcOf_and_not1]
  obtain ⟨t4, s4, e4, p4, x12_4, k4, m4⟩ := ret_spec hc k hk t3 pc3
  have h10 : t4.getReg .x10 = BitVec.ofNat 64 (regBase k) := (k4 _ (by decide)).trans hpost.a0
  have h11 : t4.getReg .x11 = BitVec.ofNat 64 64 := (k4 _ (by decide)).trans hpost.a1
  have hpad6 : DigAt w (regBase k + Merkle.padO 6) 0 := by
    have hm := rmp 6 (by decide)
    exact ⟨(wfr _ (by decide) (by decide)).trans hm.1, by
      rw [Nat.add_assoc, wfr _ (by decide) (by decide), ← Nat.add_assoc]; exact hm.2⟩
  have hsib6 : DigAt w (regBase k + Merkle.sibO 6 j) ((sig.openings ⟨k, hk⟩).path ⟨6, by decide⟩) := by
    have hm := rs 6 (by decide)
    have hb : Merkle.sibO 6 j + 16 ≤ 464 := by unfold Merkle.sibO Merkle.blkO; have := Merkle.bitAt_lt j 6; omega
    exact ⟨(wfr _ (by omega) (by omega)).trans hm.1, by
      rw [Nat.add_assoc, wfr _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.2⟩
  have hq := Merkle.rootInput j (regBase k) k index w t3 t4 v 0 ((sig.openings ⟨k, hk⟩).path ⟨6, by decide⟩) hj
    (by omega) (by omega) (by unfold MEMORY_BYTES; omega) hpost hpad6 hsib6 (fun A => m4 A) h10 h11
  have hkall : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 →
      r ≠ .x16 → r ≠ .x23 → r ≠ .x25 → r ≠ .x27 → r ≠ .x28 → t4.getReg r = t.getReg r := by
    intro r a b c d e f g h i l m n o
    rw [k4 r g, hpost.keep r b e f g, kw r b e f g h m a c d i l n o]
  have h5 : t4.getReg .x5 = 0 := by
    rw [hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x5
  have hv : hashArgumentsValid t4 = true :=
    Verify.hashArgs_of t4 (regBase k) 64 (fslot k) h10 h11 x12_4 (by omega) (by decide) (by omega) (by omega)
      (by omega)
  have hb1 : (toQ (SigGolfCandidate.T3.pad64 (Merkle.rootIn k index j v 0
      ((sig.openings ⟨k, hk⟩).path ⟨6, by decide⟩)))).blocks = 1 := by
    unfold Merkle.rootIn; exact Verify.blocks_blk4 _ _ _ _
  rw [level6_eq]
  refine (TBSim.steps s4 (SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (W := 0) (f := fun r => pure r)
    e4 h5 hv hq (fun a => TBSim.pure ?_))).mono (by rw [hb1]) (fun _ _ h => h)
  have x8_4 : t4.getReg .x8 = BitVec.ofNat 64 (regBase k) := by
    rw [k4 _ (by decide), hpost.keep _ (by decide) (by decide) (by decide) (by decide),
      hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x8_1]
  have x28_4 : t4.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * k) := by
    rw [k4 _ (by decide), hpost.keep _ (by decide) (by decide) (by decide) (by decide),
      hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x28_1]
  have F1 : Frame t t2 (fun _ => False) := fun A _ _ => m21 _
  have F3 : Frame t3 t4 (fun _ => False) := fun A _ _ => m4 _
  have FW := Frame.writeHash t4 a (fslot k) x12_4 (by omega)
  have hlowu : ∀ A, A < 0x840 → ¬ (fslot k ≤ A ∧ A < fslot k + 32) →
      (writeHash t4 a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA hn
    rw [FW A (by omega) hn, F3 A (by omega) id,
      hpost.frame A (by omega) (by rintro ⟨off, _, he⟩; omega),
      hw'.frame A (by omega) (by
        rintro (h | h | h)
        · have := chainsWr_range h; omega
        · omega
        · omega), m21]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun k' hk' => ?_, ?_⟩
  · rw [pc_writeHash, p4, pcOf_add4, dOff_succ k hk]; congr 1; omega
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x5
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x22
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x6
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x7
  · intro h h1 h7
    have hh : Merkle.heapReg h = .x9 ∨ Merkle.heapReg h = .x13 ∨ Merkle.heapReg h = .x19 ∨
        Merkle.heapReg h = .x20 ∨ Merkle.heapReg h = .x21 ∨ Merkle.heapReg h = .x26 ∨ Merkle.heapReg h = .x30 := by
      unfold Merkle.heapReg; split <;> simp
    rw [getReg_writeHash]
    rcases hh with hh | hh | hh | hh | hh | hh | hh <;>
    · rw [hh, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← hh]
      exact hI.regs.heaps h h1 h7
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x29
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x24
  · rw [getReg_writeHash, hkall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x2
  · rw [getReg_writeHash, x8_4]; rfl
  · rw [getReg_writeHash, x28_4]; rfl
  · simp [hI.len]
  · rcases Nat.lt_or_ge k' k with h | h
    · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]
      have hD := hI.roots k' h
      have hlt : fslot k' + 16 ≤ fslot k := by unfold fslot; split <;> split <;> omega
      have hfk := fslot_bounds k' (by omega)
      refine ⟨(hlowu _ (by omega) (by omega)).trans hD.1, (hlowu _ (by omega) (by omega)).trans hD.2⟩
    · have : k' = k := by omega
      subst this
      have e := getD_append_len roots (a.extractLsb' 0 128) 0
      rw [hI.len] at e
      rw [e]
      exact DigAt.writeHash_lo t4 a _ x12_4 (by omega)
  · refine (((((hI.frame.trans F1).trans hw'.frame).trans hpost.frame).trans F3).trans FW).mono
      (fun A _ hA => ?_)
    have hrb1 := regBase_bounds k hk
    rcases hA with ((((h | h) | h) | h) | h) | h
    · rcases h with h | h
      · left; unfold regBase at h ⊢; omega
      · right; omega
    · exact h.elim
    · rcases h with h | h | h
      · have := chainsWr_range h; left; unfold regBase at this ⊢; omega
      · left; unfold regBase at h ⊢; omega
      · left; unfold regBase at h ⊢; omega
    · obtain ⟨off, hoff, he⟩ := h
      have := childWrites_range hoff
      left; unfold regBase at he ⊢; omega
    · exact h.elim
    · right; omega
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def forestBytes (index : Nat) (roots : List Digest) : List UInt8 :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 15 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem forestBytes_length (index : Nat) (roots : List Digest) (hlen : roots.length = 9) :
    (forestBytes index roots).length = 160 := by
  have hfl : ((roots.drop 1).flatMap (bytesLE 16)).length = 128 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]
  simp only [forestBytes, List.length_append, bytesLE_length, hfl]
theorem pad64_forest (index : Nat) (roots : List Digest) (hlen : roots.length = 9) :
    pad64 (forestBytes index roots) = forestBytes index roots ++ List.replicate 32 0 := by
  unfold pad64; rw [forestBytes_length index roots hlen]
theorem forest_words (index : Nat) (roots : List Digest) (hlen : roots.length = 9) :
    wordsOf (pad64 (forestBytes index roots)) =
      wordsOf (bytesLE 16 (roots.getD 0 0)) ++
        [BitVec.ofNat 64 (hdr0 15 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        wordsOf ((roots.drop 1).flatMap (bytesLE 16)) ++ [0, 0, 0, 0] := by
  have hfl : ((roots.drop 1).flatMap (bytesLE 16)).length = 128 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]
  rw [pad64_forest index roots hlen, forestBytes,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length, hfl]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_header,
    show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero]
  rfl
theorem forest_blk {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 196)) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (base + 207) ∧ fetch im t = some (.base .ECALL) ∧
      t.getMem (BitVec.ofNat 64 0x710) = BitVec.ofNat 64 3841 ∧ t.getMem (BitVec.ofNat 64 0x718) = s.getReg .x22 ∧
      (∀ i, i < 4 → t.getMem (BitVec.ofNat 64 (0x7a0 + 8 * i)) = 0) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x700 ∧ t.getReg .x11 = BitVec.ofNat 64 192 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x100 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      Frame s t (fun A => A = 0x710 ∨ A = 0x718 ∨ (0x7a0 ≤ A ∧ A < 0x7c0)) := by
  have hs := symRun_sound blk_196 (codeAt_196 hc) s hpc (by simp [blk_196.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, blk_196.res, E.eval, base]
  · rw [(codeAt_207 hc).fetch _ (by simp [Result.toState_pc, blk_196.res, E.eval, base])]; rfl
  · simp only [Result.toState_getMem, blk_196.res]; t3n []
  · simp only [Result.toState_getMem, blk_196.res]; t3n []
  · intro i hi
    interval_cases i <;> (simp only [Result.toState_getMem, blk_196.res]; t3n [])
  · simp [blk_196.res, rv_simp]
  · simp [blk_196.res, rv_simp]
  · simp [blk_196.res, rv_simp]
  · intro r h3 h10 h11 h12; cases r <;> simp_all [blk_196.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [not_or] at hn
    simp only [Result.toState_getMem, blk_196.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem end_blk {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 208)) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 39952 ∧ t.getReg .x5 = 0 ∧
      (∀ r, r ≠ .x5 → r ≠ .x18 → t.getReg r = s.getReg r) ∧ (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_208 (codeAt_208 hc) s hpc (by simp [blk_208.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, blk_208.res, E.eval]
  · simp [blk_208.res, rv_simp]
  · intro r h5 h18; cases r <;> simp_all [blk_208.res, rv_simp] <;> rfl
  · intro A; simp [blk_208.res, rv_simp]
def FtsW (A : Nat) : Prop := (0x840 ≤ A ∧ A < 0x2c40) ∨ (0x700 ≤ A ∧ A < 0x7c0) ∨ (0x100 ≤ A ∧ A < 0x120)
def ftsCost : Nat := 42 + (9 * coordCost + (11 + (24 + 4)))
theorem drvInv_zero {sig : WCT9.Signature} {N : HashOutput} {sF t : MachineState}
    (hpc : t.pc = pcOf (base + 45)) (hr : DRegs (N.toNat % 2 ^ 31) t)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)))
    (h28 : t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1))) (hf : Frame sF t (fun _ => False)) :
    DrvInv sig N sF 0 [] t :=
  ⟨hpc, hr, h8, h28, rfl, fun _ h => absurd h (by omega), hf.mono (fun _ _ h => h.elim)⟩
theorem fts_tb {im : Image} (hc : NewCodeAt im) {sk : BitVec 256} {sig : WCT9.Signature} {N : HashOutput}
    {sF : MachineState} (hin : FtsIn sig N sF) (hpc : sF.pc = pcOf base) (h5 : sF.getReg .x5 = 0) :
    TBSim im sk sF ftsCost (WCT9.recoverFts sig (N.toNat % 2 ^ 31) N)
      (fun root t => t.pc = pcOf 39952 ∧ t.getReg .x5 = 0 ∧ DigAt t 0x100 root ∧ Frame sF t FtsW) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hg : N.toNat / 2 ^ 31 % 2 ^ 12 = 0 := ((admissible_iff N).mp hin.adm).1
  obtain ⟨t0, s0, p0, r0, x8_0, x28_0, f0⟩ := drv_entry hc N sF hpc h5 hin.out hg
  have hI0 : DrvInv sig N sF 0 [] t0 := drvInv_zero (by rw [p0]) r0 x8_0 x28_0 f0
  unfold WCT9.recoverFts
  have hbody : ∀ (i : Fin 9) (pre : List Digest) (t : MachineState), pre.length = i.val →
      DrvInv sig N sF pre.length pre t →
      TBSim im sk t coordCost (WCT9.recoverCoordinate sig (N.toNat % 2 ^ 31) N i)
        (fun d u => DrvInv sig N sF (pre ++ [d]).length (pre ++ [d]) u) := by
    intro i pre t hlen hI
    rw [hlen] at hI
    have h1 := coord_tb (sk := sk) hc hin i.val i.isLt pre t hI
    refine h1.mono (le_refl _) (fun d u h => ?_)
    rw [List.length_append, List.length_singleton, hlen]
    exact h
  have hmap := SigGolfCandidate.T3M.Expand.tb_mapM_finRange (image := im) (sk := sk) 9
    (WCT9.recoverCoordinate sig (N.toNat % 2 ^ 31) N) coordCost
    (fun pre t => DrvInv sig N sF pre.length pre t) hbody hI0
  refine (TBSim.steps s0 (TBSim.bind (W₂ := 11 + (24 + 4)) hmap (fun roots u hu => ?_))).mono
    (by unfold ftsCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hI⟩ := hu
  rw [hlen] at hI
  obtain ⟨t1, s1, p1, e1, m710, m718, mz, h10, h11, h12, k1, f1⟩ := forest_blk hc u (by rw [hI.pc]; rfl)
  have g1 : ∀ A, A < 0x710 ∨ (0x720 ≤ A ∧ A < 0x7a0) →
      t1.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1 A (by omega) (by omega)
  have hr0 : DigAt t1 0x700 (roots.getD 0 0) := by
    have := hI.roots 0 (by decide)
    simp only [fslot, if_true, Nat.add_zero] at this
    exact ⟨(g1 _ (by omega)).trans this.1, (g1 _ (by omega)).trans this.2⟩
  have hrest : DigsAt t1 0x720 (roots.drop 1) := by
    intro c hc'
    simp only [List.length_drop, hlen] at hc'
    have := hI.roots (c + 1) (by omega)
    simp only [fslot, if_neg (show c + 1 ≠ 0 by omega)] at this
    have e : (roots.drop 1).getD c 0 = roots.getD (c + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
    rw [e, show 0x720 + 16 * c = 0x700 + 16 * (c + 1 + 1) by ring]
    exact ⟨(g1 _ (by omega)).trans this.1, (g1 _ (by omega)).trans this.2⟩
  have x22u : u.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31) := hI.regs.x22
  have hw : t1.readWords (BitVec.ofNat 64 0x700) (8 * (2 + 1)) =
      wordsOf (pad64 (forestBytes (N.toNat % 2 ^ 31) roots)) := by
    rw [forest_words _ roots hlen]
    have hd : (roots.drop 1).length = 8 := by simp [hlen]
    have hhd : t1.readWords (BitVec.ofNat 64 (0x700 + 16)) 2 =
        [BitVec.ofNat 64 (hdr0 15 0 (N.toNat % 2 ^ 31) 0), BitVec.ofNat 64 (hdr1 (N.toNat % 2 ^ 31) 0)] := by
      rw [readWords_two, show 0x700 + 16 = 0x710 from rfl, m710, show 0x710 + 8 = 0x718 from rfl, m718, x22u,
        hdr0_index _ _ _ hidx, hdr1_eq _ 0 (by omega) (by decide)]
      simp; rfl
    have hz : t1.readWords (BitVec.ofNat 64 0x7a0) 4 = [0, 0, 0, 0] := by
      rw [show (4 : Nat) = 1 + (1 + (1 + 1)) from rfl, readWords_add, readWords_add, readWords_add,
        readWords_one, readWords_one, readWords_one, readWords_one]
      have z0 := mz 0 (by decide); have z1 := mz 1 (by decide); have z2 := mz 2 (by decide)
      have z3 := mz 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at z0 z1 z2 z3 ⊢
      rw [z0, show 0x7a0 + 8 * 1 = 0x7a0 + 8 by rfl, z1, show 0x7a0 + 8 + 8 * 1 = 0x7a0 + 8 * 2 by rfl, z2,
        show 0x7a0 + 8 * 2 + 8 * 1 = 0x7a0 + 8 * 3 by rfl, z3]; rfl
    have e24 : 8 * (2 + 1) = 2 + (2 + (2 * (roots.drop 1).length + 4)) := by rw [hd]
    rw [e24, readWords_add, readWords_add, readWords_add, hr0.words, hhd, hrest.words,
      show 0x700 + 8 * 2 + 8 * 2 + 8 * (2 * (roots.drop 1).length) = 0x7a0 by rw [hd], hz]
    simp only [List.append_assoc]
  have hq : hashInput t1 = toQ (pad64 (forestBytes (N.toNat % 2 ^ 31) roots)) :=
    hashInput_toQ t1 _ 2 0x700 (by rw [pad64_forest _ roots hlen]; simp [forestBytes_length _ roots hlen])
      h10 (by decide) (by decide) h11 (by decide) hw
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 0x700 192 0x100 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5' : t1.getReg .x5 = 0 := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x5
  have hblk : (toQ (pad64 (forestBytes (N.toNat % 2 ^ 31) roots))).blocks = 3 := by
    rw [blocks_toQ ⟨by rw [pad64_forest _ roots hlen]; simp [forestBytes_length _ roots hlen],
      by rw [pad64_forest _ roots hlen]; simp [forestBytes_length _ roots hlen]⟩,
      pad64_forest _ roots hlen]
    simp [forestBytes_length _ roots hlen]
  have hprog : WCT9.forestPk (N.toNat % 2 ^ 31) roots =
      (shortHash (forestBytes (N.toNat % 2 ^ 31) roots) >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.steps s1 (SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (W := 4) e1 h5' hv hq
    (fun a => ?_))).mono (by rw [hblk]) (fun _ _ h => h)
  have p2 : (writeHash t1 a).pc = pcOf (base + 208) := by rw [pc_writeHash, p1, pcOf_add4]
  obtain ⟨t2, s2, p3, x5_2, k2, m2⟩ := end_blk hc (writeHash t1 a) p2
  have hd := DigAt.writeHash_lo t1 a 0x100 h12 (by decide)
  have fw := Frame.writeHash t1 a 0x100 h12 (by decide)
  refine TBSim.steps s2 (TBSim.pure ⟨p3, x5_2, ⟨(m2 _).trans hd.1, (m2 _).trans hd.2⟩, ?_⟩)
  have F2 : Frame (writeHash t1 a) t2 (fun _ => False) := fun A _ _ => m2 _
  refine ((((hI.frame.trans f1).trans fw).trans F2)).mono (fun A _ h => ?_)
  rcases h with (((h | h) | h) | h) | h
  · left; exact ⟨h.1, by unfold regBase at h; omega⟩
  · right; left; omega
  · right; left; omega
  · right; right; omega
  · exact h.elim
end ClaudeWCT.W9.Machine.Expand
end
