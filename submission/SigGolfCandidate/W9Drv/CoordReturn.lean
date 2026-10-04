import SigGolfCandidate.W9Machine.WctMerkle
import SigGolfCandidate.W9Machine.WctRootGood
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.CodexCheck.Interface
import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctDriverCheck
import SigGolfCandidate.W9Machine.WctJTImageLink
import SigGolfCandidate.W9Drv.Gate

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def CoordinateContract (L : Layout) (b : Budget) (sig : ClaudeWCT.WCT9.Signature)
    (index : Nat) (a : HashOutput) (k : Fin 9) (pre : MachineState → Prop)
    (post : Digest → MachineState → Prop) : Prop :=
  RefinesPiece L b pre post (ClaudeWCT.WCT9.recoverCoordinate sig index a k)
def ForestContract (L : Layout) (b : Budget) (index : Nat) (roots : List Digest)
    (pre : MachineState → Prop) (post : Digest → MachineState → Prop) : Prop :=
  roots.length = 9 → RefinesPiece L b pre post (ClaudeWCT.WCT9.forestPk index roots)
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M shortHash Digest)
open ClaudeWCT.W9.Machine.Merkle
def childRootProg (k index j : Nat) (leaf pads sibs : Nat → Digest) : M Digest := do
  let v ← childProg k index j leaf pads sibs
  shortHash (rootIn k index j v (pads 6) (sibs 6))
theorem child_root_good (k : Fin 9) (j B index : Nat) (leaf pads sibs : Nat → Digest)
    (u : MachineState) (hj : j < 128) (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k.val index leaf pads sibs u)
    (hpad : DigAt u (B + padO 6) (pads 6)) (hsib : DigAt u (B + sibO 6 j) (sibs 6))
    (hret : u.getReg .x1 &&& ~~~1#64 = pcOf (rootPc k))
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs)
    (h : ∀ v t, ChildPost j B k.val index u v t → ∀ ans : BitVec 256,
      GoodQFor Frozen.image (writeHash (rootPrepared k t) ans)
        N C Q A (K (ans.extractLsb' 0 128))) :
    GoodQFor Frozen.image u (N + 47) (C + 111) Q (A + 111)
      (ccM (childRootProg k.val index j leaf pads sibs) K) := by
  have hc := (CodexCheck.frozen_children j hj).1 B k.val index leaf pads sibs u
    (N + 2) (C + 9) (A + 9) Q
    (fun v => ccM (shortHash (rootIn k.val index j v (pads 6) (sibs 6))) K) hidx hu
    (fun v t ht => root_good k j B index u t v (pads 6) (sibs 6) hj hidx
      hu.base8 hu.baseHi ht hpad hsib (ht.pc.trans hret) hu.t0 N C A Q K (h v t ht))
  simpa only [childRootProg, ccM_bind, Nat.add_assoc, GoodQFor, GoodQIm] using hc
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.T3M OracleComp
open SigGolfCandidate.T3 (Digest HashOutput M shortHash)
open ClaudeWCT.W9.Machine.Merkle
theorem rootIn_zero (k index j : Nat) (v sib : Digest) :
    shortHash (rootIn k index j v 0 sib) =
      (let pair := if j / 2 ^ 6 % 2 = 0 then (v, sib) else (sib, v)
       SigGolfCandidate.T3.nodeHash 11 k index 1 pair.1 pair.2) := by
  simp only [rootIn, bitAt, Verify.nodeHash_eq]
  rfl
theorem childRootProg_canon (sig : ClaudeWCT.WCT9.Signature) (index : Nat)
    (a : HashOutput) (k : Fin 9) (ends : List Digest) (hends : ends.length = 7) :
    childRootProg k.val index (ClaudeWCT.WCT9.child a k).val
      (leafFields k.val index (ClaudeWCT.WCT9.child a k).val ends) (fun _ => 0)
      (finPath (sig.openings k).path) =
      (ClaudeWCT.WCT9.leafHash index k.val (ClaudeWCT.WCT9.child a k).val ends >>=
        recoverPath sig index a k) := by
  unfold childRootProg
  rw [childCanon k.val index (ClaudeWCT.WCT9.child a k).val ends
    (finPath (sig.openings k).path) hends, bind_assoc]
  apply congrArg (fun f : Digest → M Digest =>
    ClaudeWCT.WCT9.leafHash index k.val (ClaudeWCT.WCT9.child a k).val ends >>= f)
  funext root
  rw [CodexCheck.recoverPath_split]
  simp only [rootIn_zero, finPath, dif_pos (show 6 < 7 by decide)]
  rfl
end W9Machine
end

section


namespace W9Drv
open OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M shortHash)
open ClaudeWCT.W9.Machine.Merkle
open W9Machine
def coordTail (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M Digest := do
  let leaf ← ClaudeWCT.WCT9.leafHash index k.val j.val ends
  (List.finRange 7).foldlM (fun value level => do
    let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
    let pair := if j.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 11 k.val index (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
      pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val level.val) pair.2) leaf
theorem childRootProg_arbitrary (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (hends : ends.length = 7) :
    childRootProg k.val index j.val (leafFields k.val index j.val ends)
      (ClaudeWCT.W9.T3M.wmpad w k.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val) =
      coordTail w index k j ends := by
  simp only [childRootProg, childProg, coordTail, leafBytes_canon _ _ _ _ hends,
    ClaudeWCT.WCT9.leafHash, bind_assoc]
  apply congrArg (fun f : Digest → M Digest =>
    shortHash (SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++
      SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.wctHeader 6 k.val index 0 j.val) ++
      (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)) >>= f)
  funext leaf
  change _ = (List.finRange 7).foldlM
    (fun value level => childLevelP k.val index j.val
      (ClaudeWCT.W9.T3M.wmpad w k.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val)
      value level.val) leaf
  rw [← List.foldlM_map (f := Fin.val), finRange_map_val]
  rw [show List.range 7 = List.range 6 ++ [6] from List.range_succ (n := 6),
    List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  apply congrArg (fun f : Digest → M Digest =>
    (List.range 6).foldlM (childLevelP k.val index j.val
      (ClaudeWCT.W9.T3M.wmpad w k.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val)) leaf >>= f)
  funext value
  simp only [childLevelP, heapOf,
    show j.val / 2 ^ (6 + 1) = 0 from Nat.div_eq_of_lt j.isLt]
  rfl
theorem wctCoordP_split (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) :
    ClaudeWCT.W9.T3M.wctCoordP w index k j rank =
      (Chain.program w index k j rank >>= coordTail w index k j) := by
  rfl
end W9Drv
end

section

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Merkle W9Machine
theorem coord_core_good (chains : Chain.AllGood)
    (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs) (hu : Chain.Pre w index k j rank u)
    (hnext : ∀ ends entry, Chain.Post w index k j u ends entry →
      ∀ v t, ChildPost j.val (Chain.base k) k.val index entry v t →
      ∀ ans : BitVec 256, GoodQFor Frozen.image (writeHash (rootPrepared k t) ans)
        N C Q A (K (ans.extractLsb' 0 128))) :
    GoodQFor Frozen.image u (N + 136) (C + 200) Q (A + 200)
      (ccM (ClaudeWCT.W9.T3M.wctCoordP w index k j rank) K) := by
  rw [wctCoordP_split, ccM_bind]
  have hc := chains rank w index k j u (N + 47) (C + 111) (A + 111) Q
    (fun ends => ccM (coordTail w index k j ends) K) hu
  apply (show GoodQFor Frozen.image u (N + 136) (C + 200) Q (A + 200)
    (ccM (Chain.program w index k j rank) (fun ends => ccM (coordTail w index k j ends) K))
    from ?_)
  apply (show GoodQFor Frozen.image u ((N + 47) + 89) ((C + 111) + 89) Q
    ((A + 111) + 89) _ from hc ?_)
  intro ends entry hp
  rw [← childRootProg_arbitrary w index k j ends hp.length]
  apply child_root_good k j.val (Chain.base k) index _ _ _ entry j.isLt
    (by have := hu.indexBound; omega) hp.child hp.rootPad hp.rootSibling
    ?_ N C A Q K (hnext ends entry hp)
  rw [hp.keep .x1 (by decide), hu.returnPC]
  fin_cases k <;> decide
end W9Drv
end

section


namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchCode (k : Fin 9) : List (BitVec 32) :=
  [dispatchWords0, dispatchWords1, dispatchWords2, dispatchWords3, dispatchWords4,
    dispatchWords5, dispatchWords6, dispatchWords7, dispatchWords8].getD k.val []
def dispatchBit (k : Fin 9) : Nat := [43,64,85,106,128,149,170,192,213].getD k.val 0
def dispatchLen (k : Fin 9) : Nat := if k.val = 0 then 12 else 14
def dispatchResult (k : Fin 9) : Result :=
  coordDispatch (dispatchPc k.val) (dispatchBit k) (decide (k.val ≠ 0))
theorem dispatch_checked (k : Fin 9) :
    rOK (symRun {} (dispatchCode k) (pcOf (dispatchPc k.val)) (dispatchLen k))
      (dispatchResult k) = true := by
  fin_cases k
  · exact dispatch0_checked
  · exact dispatch1_checked
  · exact dispatch2_checked
  · exact dispatch3_checked
  · exact dispatch4_checked
  · exact dispatch5_checked
  · exact dispatch6_checked
  · exact dispatch7_checked
  · exact dispatch8_checked
theorem dispatch_linked (k : Fin 9) :
    sliceChecked (dispatchPc k.val) (dispatchCode k) = true := by
  fin_cases k
  · exact dispatch0_linked
  · exact dispatch1_linked
  · exact dispatch2_linked
  · exact dispatch3_linked
  · exact dispatch4_linked
  · exact dispatch5_linked
  · exact dispatch6_linked
  · exact dispatch7_linked
  · exact dispatch8_linked
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  rfl
theorem dispatch_steps (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List Digest) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Steps Frozen.image u (dispatchLen k) (dispatchLen k) ((dispatchResult k).toState u) := by
  have hs := symRun_sound (rOK_eq (dispatch_checked k))
    (slice_at _ _ (dispatch_linked k)) u hu.pc
  have hcost : (dispatchResult k).steps = dispatchLen k ∧
      (dispatchResult k).cycles = dispatchLen k := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (dispatchResult k).st.obl
  rw [Oblig.all_iff]
  simp only [dispatchResult, coordDispatch, List.mem_singleton]
  intro o ho
  subst o
  simp only [Oblig.holds, norm_eval, addC_eval]
  fin_cases k <;> simp [addC_eval, E.eval, hu.headerReg, accessValid, rangeValid,
    MEMORY_BYTES]
end W9Drv
end

section

namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.Merkle W9Machine
def chainEntryState (a : HashOutput) (k : Fin 9) (u : MachineState) : MachineState :=
  { (dispatchResult k).toState u with
    pc := pcOf (chainEntries.getD (ClaudeWCT.WCT9.rank a k).val 0) }
theorem dispatch_digest (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List Digest) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    (coordDigest (dispatchBit k)).eval u = a.extractLsb' (64 * (dispatchBit k / 64)) 64 := by
  fin_cases k <;> simp [coordDigest, dispatchBit, E.eval, hu.cached, cachedWord]
  · exact hu.digest 1 (by decide)
  · exact hu.digest 2 (by decide)
  · exact hu.digest 3 (by decide)
theorem coordShift_eval (bit : Nat) (u : MachineState) :
    (coordShift bit).eval u = (coordDigest bit).eval u >>> (bit % 64) := by
  unfold coordShift
  split_ifs with h
  · simp [h]
  · simp only [mkBin_eval, E.eval, BinOp.eval, BitVec.toNat_ofNat]
    congr 1
    omega
theorem dispatch_child (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64)) &&& 127#64 =
      BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  change _ &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.child, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
theorem dispatch_chain_pre (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List Digest) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Chain.Pre w (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k)
      (chainEntryState a k u) := by
  have hm (A : Word) : (chainEntryState a k u).getMem A = u.getMem A := rfl
  have hr (r : Reg) (h : r ∉ [.x1, .x3, .x4, .x8, .x11, .x14, .x16, .x23, .x27, .x28]) :
      (chainEntryState a k u).getReg r = u.getReg r := by
    change ((dispatchResult k).toState u).getReg r = u.getReg r
    apply Keeps.reg (ws := [.x1,.x3,.x4,.x8,.x11,.x14,.x16,.x23,.x27,.x28]) ?_ u h
    intro r hr
    simp only [List.mem_cons, not_or] at hr
    simp only [dispatchResult, coordDispatch]
    split <;> simp [RegFile.get_set_ne, hr, RegFile.init]
  have hload := dispatch_digest pk w a k roots u hu
  refine {
    indexBound := Nat.mod_lt _ (by decide)
    pc := rfl
    baseReg := ?_
    headerReg := ?_
    route := ?_
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x6 (by decide)).trans hu.stepOne
    stepTwo := (hr .x7 (by decide)).trans hu.stepTwo
    hashLen := ?_
    childPC := ?_
    returnPC := ?_
    indexReg := (hr .x22 (by decide)).trans hu.index
    nodeHeader := ?_
    heaps := ?_
    headers := fun t ht d hd => (hm _).trans (hu.bank.chain k t ht d hd)
    leafHeader := (hm _).trans (hu.bank.leaf k)
    witness := hu.coords k (Nat.le_refl _) }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.baseReg, Chain.base]
  · change ((dispatchResult k).toState u).getReg .x28 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.headerReg, Chain.table]
  · change ((dispatchResult k).toState u).getReg .x4 = _
    simp only [dispatchResult, coordDispatch, Result.toState_getReg]
    split <;> simp only [RegFile.get, RegFile.set, mkBin_eval, coordShift_eval, E.eval,
      BinOp.eval]
    all_goals rw [hload]
    all_goals erw [dispatch_child a k, hu.index]
    all_goals
      change (BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val <<< 32) |||
        BitVec.ofNat 64 (idxOf a) = _
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      have hj := (ClaudeWCT.WCT9.child a k).isLt
      have hi : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
      have hor := (Nat.two_pow_add_eq_or_of_lt (i := 32) (by omega : idxOf a < 2 ^ 32)
        (ClaudeWCT.WCT9.child a k).val).symm
      rw [show (ClaudeWCT.WCT9.child a k).val % 2 ^ 64 * 2 ^ 32 % 2 ^ 64 =
        2 ^ 32 * (ClaudeWCT.WCT9.child a k).val by omega,
        Nat.mod_eq_of_lt (by omega : idxOf a < 2 ^ 64), hor]
      unfold hdr1
      omega
  · rfl
  · change ((dispatchResult k).toState u).getReg .x23 = _
    simp only [dispatchResult, coordDispatch, Result.toState_getReg]
    split <;> simp only [RegFile.get, RegFile.set, mkBin_eval, mkAdd_eval,
      coordShift_eval, E.eval, BinOp.eval]
    all_goals rw [hload]
    all_goals erw [dispatch_child a k, hu.childBlock]
    all_goals
      change (BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val <<< 8) +
        BitVec.ofNat 64 0xce800 = _
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq, pcOf, childBase]
      have hj := (ClaudeWCT.WCT9.child a k).isLt
      omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · change ((dispatchResult k).toState u).getReg .x27 = _
    have hb := hu.bank.node k
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, addC_eval, E.eval, hu.headerReg] <;>
      simpa [Chain.table] using hb
  · intro h h1 h7
    exact (hr (heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h1 h7)
end W9Drv
end

section


namespace W9Drv
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem aligned_clear_low (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0
    simp
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0, hj]
theorem field_mask (x : BitVec 64) :
    x &&& 65532#64 = ((x >>> 2) &&& 16383#64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem dispatch_field (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64 + 5)) &&&
      65532#64 = BitVec.ofNat 64 (4 * ClaudeWCT.WCT9.field a k) := by
  rw [field_mask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (_ &&& (2 ^ 14 - 1)) * 4 % 2 ^ 64 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.field, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
theorem dispatch_pc (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List Digest) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    ((dispatchResult k).toState u).pc = pcOf (jtStart + ClaudeWCT.WCT9.field a k) := by
  change (mkBin .and (mkAdd (mkBin .and
    (mkBin .srl (coordDigest (dispatchBit k))
      (.c (BitVec.ofNat 64 (dispatchBit k % 64 + 5)))) (.reg .x2)) (.reg .x24))
      (.c (~~~1#64))).eval u = _
  simp only [mkBin_eval, mkAdd_eval, E.eval, BinOp.eval, hu.mask, hu.jt]
  rw [dispatch_digest pk w a k roots u hu]
  have hshift : (BitVec.ofNat 64 (dispatchBit k % 64 + 5)).toNat % 64 =
      dispatchBit k % 64 + 5 := by fin_cases k <;> decide
  rw [hshift]
  change (((a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>>
    (dispatchBit k % 64 + 5)) &&& 65532#64) + 878592#64) &&& ~~~1#64 = _
  rw [dispatch_field a k]
  rw [ofNat_add_ofNat, aligned_clear_low _ (by omega)]
  congr 1
  unfold jtStart
  omega
theorem codeAt_single (pc : Nat) (words : List (BitVec 32))
    (hb : pc + words.length < 242393)
    (hc : CodeAt Frozen.image (pcOf pc) words) (i : Nat) (hi : i < words.length) :
    CodeAt Frozen.image (pcOf (pc + i)) [words[i]] := by
  have hp : (pcOf pc).toNat = 4096 + 4 * pc := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  have hpi : (pcOf (pc + i)).toNat = 4096 + 4 * (pc + i) := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [hpi]; omega, by rw [hpi]; omega, by rw [hpi]; simp; omega, ?_⟩
  have hpre := hc.2.2.2.drop i
  have hs : [words[i]] <+: words.drop i := by
    rw [List.singleton_prefix_iff_head?_eq_some]
    simp [List.head?_drop, hi]
  have ht := hs.trans hpre
  simpa [hp, hpi, List.drop_drop, Nat.add_comm] using ht
def jtChunk (c : Fin 64) : List (BitVec 32) :=
  [jtWords00, jtWords01, jtWords02, jtWords03, jtWords04, jtWords05, jtWords06, jtWords07, jtWords08, jtWords09, jtWords10, jtWords11, jtWords12, jtWords13, jtWords14, jtWords15, jtWords16, jtWords17, jtWords18, jtWords19, jtWords20, jtWords21, jtWords22, jtWords23, jtWords24, jtWords25, jtWords26, jtWords27, jtWords28, jtWords29, jtWords30, jtWords31, jtWords32, jtWords33, jtWords34, jtWords35, jtWords36, jtWords37, jtWords38, jtWords39, jtWords40, jtWords41, jtWords42, jtWords43, jtWords44, jtWords45, jtWords46, jtWords47, jtWords48, jtWords49, jtWords50, jtWords51, jtWords52, jtWords53, jtWords54, jtWords55, jtWords56, jtWords57, jtWords58, jtWords59, jtWords60, jtWords61, jtWords62, jtWords63].getD c.val []
theorem jtChunk_length (c : Fin 64) : (jtChunk c).length = 256 := by
  fin_cases c <;> rfl
theorem jtChunk_checked (c : Fin 64) : jtCheck (256 * c.val) (jtChunk c) = true := by
  fin_cases c
  · exact jtCheck00
  · exact jtCheck01
  · exact jtCheck02
  · exact jtCheck03
  · exact jtCheck04
  · exact jtCheck05
  · exact jtCheck06
  · exact jtCheck07
  · exact jtCheck08
  · exact jtCheck09
  · exact jtCheck10
  · exact jtCheck11
  · exact jtCheck12
  · exact jtCheck13
  · exact jtCheck14
  · exact jtCheck15
  · exact jtCheck16
  · exact jtCheck17
  · exact jtCheck18
  · exact jtCheck19
  · exact jtCheck20
  · exact jtCheck21
  · exact jtCheck22
  · exact jtCheck23
  · exact jtCheck24
  · exact jtCheck25
  · exact jtCheck26
  · exact jtCheck27
  · exact jtCheck28
  · exact jtCheck29
  · exact jtCheck30
  · exact jtCheck31
  · exact jtCheck32
  · exact jtCheck33
  · exact jtCheck34
  · exact jtCheck35
  · exact jtCheck36
  · exact jtCheck37
  · exact jtCheck38
  · exact jtCheck39
  · exact jtCheck40
  · exact jtCheck41
  · exact jtCheck42
  · exact jtCheck43
  · exact jtCheck44
  · exact jtCheck45
  · exact jtCheck46
  · exact jtCheck47
  · exact jtCheck48
  · exact jtCheck49
  · exact jtCheck50
  · exact jtCheck51
  · exact jtCheck52
  · exact jtCheck53
  · exact jtCheck54
  · exact jtCheck55
  · exact jtCheck56
  · exact jtCheck57
  · exact jtCheck58
  · exact jtCheck59
  · exact jtCheck60
  · exact jtCheck61
  · exact jtCheck62
  · exact jtCheck63
theorem jtChunk_linked (c : Fin 64) :
    CodeAt Frozen.image (pcOf (jtStart + 256 * c.val)) (jtChunk c) := by
  fin_cases c
  · exact jt00_at
  · exact jt01_at
  · exact jt02_at
  · exact jt03_at
  · exact jt04_at
  · exact jt05_at
  · exact jt06_at
  · exact jt07_at
  · exact jt08_at
  · exact jt09_at
  · exact jt10_at
  · exact jt11_at
  · exact jt12_at
  · exact jt13_at
  · exact jt14_at
  · exact jt15_at
  · exact jt16_at
  · exact jt17_at
  · exact jt18_at
  · exact jt19_at
  · exact jt20_at
  · exact jt21_at
  · exact jt22_at
  · exact jt23_at
  · exact jt24_at
  · exact jt25_at
  · exact jt26_at
  · exact jt27_at
  · exact jt28_at
  · exact jt29_at
  · exact jt30_at
  · exact jt31_at
  · exact jt32_at
  · exact jt33_at
  · exact jt34_at
  · exact jt35_at
  · exact jt36_at
  · exact jt37_at
  · exact jt38_at
  · exact jt39_at
  · exact jt40_at
  · exact jt41_at
  · exact jt42_at
  · exact jt43_at
  · exact jt44_at
  · exact jt45_at
  · exact jt46_at
  · exact jt47_at
  · exact jt48_at
  · exact jt49_at
  · exact jt50_at
  · exact jt51_at
  · exact jt52_at
  · exact jt53_at
  · exact jt54_at
  · exact jt55_at
  · exact jt56_at
  · exact jt57_at
  · exact jt58_at
  · exact jt59_at
  · exact jt60_at
  · exact jt61_at
  · exact jt62_at
  · exact jt63_at
theorem jt_steps (field : Fin 16384) (u : MachineState)
    (hu : u.pc = pcOf (jtStart + field.val)) :
    Steps Frozen.image u 1 1 {u with pc := pcOf (jtTarget field.val)} := by
  let c : Fin 64 := ⟨field.val / 256, by omega⟩
  let i : Nat := field.val % 256
  have hi : i < (jtChunk c).length := by rw [jtChunk_length]; exact Nat.mod_lt _ (by decide)
  have he : 256 * c.val + i = field.val := by dsimp [c, i]; omega
  have hcode := codeAt_single (jtStart + 256 * c.val) (jtChunk c)
    (by rw [jtChunk_length]; have := c.isLt; unfold jtStart; omega)
    (jtChunk_linked c) i hi
  have hcheck := jtChunk_checked c
  unfold jtCheck at hcheck
  have hmem : ((jtChunk c)[i], i) ∈ (jtChunk c).zipIdx := by
    have hx := List.getElem_mem (l := (jtChunk c).zipIdx) (n := i) (by simpa using hi)
    simpa using hx
  have hrun := List.all_eq_true.mp hcheck _ hmem
  simp only at hrun
  rw [Nat.add_assoc, he] at hrun
  rw [Nat.add_assoc, he] at hcode
  have hs := symRun_sound (rOK_eq hrun) hcode u hu (by trivial)
  convert hs using 1
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
end W9Drv
end

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.Merkle W9Machine
theorem coord_frame (w : WBytes) (a : HashOutput) (k : Fin 9) (u entry t : MachineState)
    (ends : List Digest) (v : Digest) (ans : BitVec 256)
    (hp : Chain.Post w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : ChildPost (ClaudeWCT.WCT9.child a k).val (Chain.base k) k.val
      (idxOf a) entry v t) :
    Frame u (writeHash (rootPrepared k t) ans) (fun A =>
      (Chain.base k ≤ A ∧ A < Chain.base k + 1024) ∨
      (W9Machine.forestSlot k.val ≤ A ∧ A < W9Machine.forestSlot k.val + 32)) := by
  intro A hA hn
  have hk := k.isLt
  have hf := frame_writeHash4 (rootPrepared k t) ans (W9Machine.forestSlot k.val)
    (coordRoot_dest (rootPc k) k.val t)
    (by unfold W9Machine.forestSlot; split_ifs <;> omega)
  rw [hf A hA (by intro h; exact hn (Or.inr (by rcases h with h | h | h | h <;> omega)))]
  change t.getMem _ = _
  rw [ht.frame A hA (by
    rintro ⟨off, hoff, he⟩
    have hb := childWrites_bound hoff
    exact hn (Or.inl (by omega)))]
  exact hp.frame A hA (by unfold Chain.writes; intro h; exact hn (Or.inl (by omega)))
theorem coord_next (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List Digest) (u entry t : MachineState) (ends : List Digest)
    (v : Digest) (ans : BitVec 256) (hu : CoordPre pk w a k.val roots u)
    (hp : Chain.Post w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : ChildPost (ClaudeWCT.WCT9.child a k).val (Chain.base k) k.val
      (idxOf a) entry v t) :
    CoordPre pk w a (k.val + 1) (roots ++ [ans.extractLsb' 0 128])
      (writeHash (rootPrepared k t) ans) := by
  have hk := k.isLt
  have hc := dispatch_chain_pre pk w a k roots u hu
  have hf := coord_frame w a k u entry t ends v ans hp ht
  have hm (A : Nat) (hA : A < 2 ^ 64)
      (hs : A < 1792 ∨ (1984 ≤ A ∧ A < 2112) ∨ 11328 ≤ A) :
      (writeHash (rootPrepared k t) ans).getMem (BitVec.ofNat 64 A) =
        u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    unfold Chain.base W9Machine.forestSlot
    split_ifs <;> omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      (writeHash (rootPrepared k t) ans).getReg r = (chainEntryState a k u).getReg r := by
    rw [writeHash_getReg, rootPrepared, (coordRoot_keeps (rootPc k) k.val).reg t (x := r)
      (by simp only [List.mem_singleton]; intro hx; exact h (by simp [hx]))]
    rw [ht.keep r (by intro hx; exact h (by simp [hx]))
      (by intro hx; exact h (by simp [hx])) (by intro hx; exact h (by simp [hx]))
      (by intro hx; exact h (by simp [hx]))]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x3,.x4,.x8,.x11,.x14,.x16,.x23,.x27,.x28]) :
      (chainEntryState a k u).getReg r = u.getReg r := by
    change ((dispatchResult k).toState u).getReg r = u.getReg r
    apply Keeps.reg (ws := [.x1,.x3,.x4,.x8,.x11,.x14,.x16,.x23,.x27,.x28]) ?_ u h
    intro r hr
    simp only [List.mem_cons, not_or] at hr
    simp only [dispatchResult, coordDispatch]
    split <;> simp [RegFile.get_set_ne, hr, RegFile.init]
  have hg : Glob baseK w pk (writeHash (rootPrepared k t) ans) := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp [baseK])))
      · exact (hr .x18 (by decide)).trans ((hd .x18 (by decide)).trans (hreg (.x18, 4095) (by simp [baseK])))
    · intro j hj
      rw [hm _ (by unfold WIT; omega) (by unfold WIT; omega)]
      exact hh j hj
    · exact ⟨(hm 160 (by decide) (by omega)).trans hpk.1,
        (hm 168 (by decide) (by omega)).trans hpk.2⟩
    · intro A hA
      have hb : A < 1792 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change ((writeHash (rootPrepared k t) ans).getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · exact hdata.congr (fun A hA hB => hm A (by omega) (Or.inr (Or.inr (by unfold TAB at hA; omega))))
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    index := (hr .x22 (by decide)).trans hc.indexReg
    heaps := ?_
    stepOne := (hr .x6 (by decide)).trans hc.stepOne
    stepTwo := (hr .x7 (by decide)).trans hc.stepTwo
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := by simpa [Chain.base] using (hr .x8 (by decide)).trans hc.baseReg
    headerReg := by simpa [Chain.table, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using (hr .x28 (by decide)).trans hc.headerReg
    roots := ?_
    coords := ?_
    layer := ?_
    cached := ?_ }
  · rw [writeHash_pc]
    change pcOf (rootPc k + 1) + 4 = _
    fin_cases k <;> rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro l t ht d hd
      exact (hm _ (by have := l.isLt; unfold Chain.table; omega)
        (Or.inr (Or.inr (by unfold Chain.table; omega)))).trans (hu.bank.chain l t ht d hd)
    · intro l
      exact (hm _ (by have := l.isLt; unfold Chain.table; omega)
        (Or.inr (Or.inr (by unfold Chain.table; omega)))).trans (hu.bank.node l)
    · intro l
      exact (hm _ (by have := l.isLt; unfold Chain.table; omega)
        (Or.inr (Or.inr (by unfold Chain.table; omega)))).trans (hu.bank.leaf l)
  · intro h h1 h7
    exact (hr (heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h1 h7)
  · intro i hi
    by_cases he : i = k.val
    · subst i
      rw [List.getD_append_right _ _ _ _ (by rw [hu.length]), hu.length, Nat.sub_self]
      exact writeHash_lo (rootPrepared k t) ans (W9Machine.forestSlot k.val)
        (coordRoot_dest (rootPc k) k.val t)
        (by unfold W9Machine.forestSlot; split_ifs <;> omega)
    · rw [List.getD_append _ _ _ _ (by rw [hu.length]; omega)]
      apply DigAt.of_eq (hu.roots i (by omega))
      · apply hf _ (by unfold W9Machine.forestSlot; split_ifs <;> omega)
        unfold Chain.base W9Machine.forestSlot
        split_ifs <;> omega
      · apply hf _ (by unfold W9Machine.forestSlot; split_ifs <;> omega)
        unfold Chain.base W9Machine.forestSlot
        split_ifs <;> omega
  · intro l hl off hoff halign
    unfold OrigW
    rw [hf _ (by have := l.isLt; unfold Chain.base; omega) (by
      have := l.isLt
      unfold Chain.base W9Machine.forestSlot
      split_ifs <;> omega)]
    exact hu.coords l (by omega) off hoff halign
  · exact hu.layer.frame (fun j hj h => hm _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
  · rw [hr .x16 (by decide)]
    have hdig := dispatch_digest pk w a k roots u hu
    have he : (chainEntryState a k u).getReg .x16 = (coordDigest (dispatchBit k)).eval u := by
      fin_cases k <;> rfl
    rw [he, hdig]
    fin_cases k <;> rfl
theorem coord_good (chains : Chain.AllGood) (pk : Digest) (w : WBytes) (a : HashOutput)
    (k : Fin 9) (roots : List Digest) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List Digest) → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a k.val roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, CoordPre pk w a (k.val + 1) (roots ++ [root]) t →
      GoodQFor Frozen.image t N C Q A (K (some (roots ++ [root])))) :
    GoodQFor Frozen.image u (N + (if k.val = 0 then 213 else 215))
      (C + (if k.val = 0 then 213 else 215)) Q (A + (if k.val = 0 then 213 else 215))
      (ccM (ClaudeWCT.W9.T3M.wctStep w a (some roots) k) K) := by
  have ds := dispatch_steps pk w a k roots u hu
  let f : Fin 16384 := ⟨ClaudeWCT.WCT9.field a k, Nat.mod_lt _ (by decide)⟩
  have js := jt_steps f ((dispatchResult k).toState u) (dispatch_pc pk w a k roots u hu)
  by_cases hok : ClaudeWCT.W9.T3M.fieldOk a k = true
  · have hfield : ClaudeWCT.WCT9.field a k < 16016 := by
      exact of_decide_eq_true hok
    have he : jtTarget f.val = chainEntries.getD (ClaudeWCT.WCT9.rank a k).val 0 := by
      simp only [jtTarget, f, if_pos hfield, ClaudeWCT.WCT9.rank]
    rw [he] at js
    change Steps Frozen.image ((dispatchResult k).toState u) 1 1 (chainEntryState a k u) at js
    have core := coord_core_good chains w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (ClaudeWCT.WCT9.rank a k) (chainEntryState a k u) N C A Q
      (fun root => K (some (roots ++ [root]))) (dispatch_chain_pre pk w a k roots u hu)
      (fun ends entry hp v t ht ans => hnext _ _ (coord_next pk w a k roots u entry t ends v ans hu hp ht))
    have full := (core.steps js).steps ds
    simp only [ClaudeWCT.W9.T3M.wctStep, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ccM_bind, ccM_pure]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
  · have hfield : ¬ ClaudeWCT.WCT9.field a k < 16016 := by
      intro hh
      exact hok (show decide (ClaudeWCT.WCT9.field a k < 16016) = true from decide_eq_true hh)
    have he : jtTarget f.val = 24 := by simp only [jtTarget, f, if_neg hfield, jtReject]
    rw [he] at js
    let s : MachineState := { (dispatchResult k).toState u with pc := pcOf 24 }
    have rs := block_steps gReject_checked gReject_linked rfl s (by rfl)
    have rf := block_ecall gReject_checked gReject_linked rfl s rfl
    have rr : GoodQFor Frozen.image (gReject.toState s) 1 1 Q 0 (pure (false, 0)) :=
      GoodQFor.reject rf rfl rfl
    have full := ((rr.steps rs).steps js).steps ds
    dsimp only [gReject] at full
    have hfalse : ClaudeWCT.W9.T3M.fieldOk a k = false := Bool.eq_false_iff.mpr hok
    simp only [ClaudeWCT.W9.T3M.wctStep, hfalse, Bool.not_false, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
end W9Drv
end
