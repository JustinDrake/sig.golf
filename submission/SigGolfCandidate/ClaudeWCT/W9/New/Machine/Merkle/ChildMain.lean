import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs
import SigGolfCandidate.T3M.Verify.Post
import SigGolfCandidate.T3M.Verify.Common
section
namespace ClaudeWCT.W9.Machine.Merkle
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def childLook (j n : Nat) : Option (BitVec 32) :=
  if childBase j ≤ n then (childWords j)[n - childBase j]? else none
def ecIdx (l : Nat) : Nat := [1,9,16,23,30,35,40].getD l 0
def lvlSt (l : Nat) : Nat := ecIdx (l + 1) - ecIdx l - 1
def childRun (j i : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 (childLook j) [] 64 (pcOf (childBase j + i)) dirs (σK []) []
def eX8 (off : Nat) : E := addC (.reg .x8) (BitVec.ofNat 64 off)
def aX8 (off : Nat) : Addr := ⟨some (.reg .x8), BitVec.ofNat 64 off⟩
def p0Res (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x12 (eX8 (curO 0 j)), [], []⟩, pcOf (childBase j + 1), true, 1, 1, [], none⟩
def lvlRegs (j l : Nat) : RegFile :=
  let rf := if l = 0 then RegFile.init.set .x11 (.c 64) else RegFile.init
  let rf := rf.set .x10 (eX8 (blkO l))
  let rf := if l ≤ 3 then rf.set .x3 (.c (BitVec.ofNat 64 (heapOf l j))) else rf
  rf.set .x12 (eX8 (curO (l + 1) j))
def hdr1E (j l : Nat) : E :=
  if l ≤ 3 then .bin (.st .w 4) (.bin (.st .w 0) (.ld (eX8 (blkO l + 24))) (.reg .x22)) (.c (BitVec.ofNat 64 (heapOf l j)))
  else .reg (heapReg (heapOf l j))
def lvlMem (j l : Nat) : SymMem := [(aX8 (blkO l + 24), hdr1E j l), (aX8 (blkO l + 16), .reg .x27)]
def lvlObl (l : Nat) : List Oblig :=
  if l ≤ 3 then
    [.valid (aX8 (blkO l + 28)) 4, .align8 (.reg .x8), .valid (aX8 (blkO l + 24)) 4, .valid (aX8 (blkO l + 16)) 8]
  else [.valid (aX8 (blkO l + 24)) 8, .valid (aX8 (blkO l + 16)) 8]
def lvlRes (j l : Nat) : PRes :=
  ⟨⟨lvlRegs j l, lvlMem j l, lvlObl l⟩, pcOf (childBase j + ecIdx (l + 1)), true, lvlSt l, lvlSt l, [], none⟩
def retE : E := .bin .and (.reg .x1) (.c (~~~1#64))
def p7Res (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x10 (eX8 (blkO 6)), lvlMem j 6, lvlObl 6⟩, 0, false, 4, 4, [], some retE⟩
def childPiecesOK (j : Nat) : Bool :=
  optBeq (childRun j 0 []) (p0Res j) &&
    (List.range 6).all (fun l => optBeq (childRun j (ecIdx l + 1) []) (lvlRes j l)) &&
    optBeq (childRun j (ecIdx 6 + 1) [.jmp]) (p7Res j)
def childPiecesRange (lo n : Nat) : Bool := (List.range' lo n).all childPiecesOK
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
set_option maxRecDepth 100000
theorem childPieces_4 : childPiecesRange 64 16 = true := by decide +kernel
theorem childPieces_5 : childPiecesRange 80 16 = true := by decide +kernel
theorem childPieces_6 : childPiecesRange 96 16 = true := by decide +kernel
theorem childPieces_7 : childPiecesRange 112 16 = true := by decide +kernel
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
set_option maxRecDepth 100000
theorem childPieces_0 : childPiecesRange 0 16 = true := by decide +kernel
theorem childPieces_1 : childPiecesRange 16 16 = true := by decide +kernel
theorem childPieces_2 : childPiecesRange 32 16 = true := by decide +kernel
theorem childPieces_3 : childPiecesRange 48 16 = true := by decide +kernel
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
open SigGolfCandidate.T3M.Verify
theorem childPiecesOK_at (j : Nat) (hj : j < 128) : childPiecesOK j = true := by
  have hall : ∀ lo n, childPiecesRange lo n = true → lo ≤ j → j < lo + n → childPiecesOK j = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 childPieces_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 childPieces_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 childPieces_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 childPieces_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 childPieces_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 childPieces_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 childPieces_6 (by omega) (by omega)
  exact hall 112 16 childPieces_7 (by omega) (by omega)
theorem childRun_p0 (j : Nat) (hj : j < 128) : childRun j 0 [] = some (p0Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem childRun_lvl (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6) :
    childRun j (ecIdx l + 1) [] = some (lvlRes j l) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq (List.all_eq_true.mp h.1.2 l (List.mem_range.mpr hl))
theorem childRun_p7 (j : Nat) (hj : j < 128) : childRun j (ecIdx 6 + 1) [.jmp] = some (p7Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.2
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
variable {im : Image}
theorem GoodQIm.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQIm im s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQIm im s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩
theorem GoodQIm.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps im s k c t) (h : GoodQIm im t N C Q A X) : GoodQIm im s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
    exact ⟨hq, by omega⟩
theorem GoodQIm.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps im s k c t) (h : GoodQIm im t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hA : A + c ≤ A') : GoodQIm im s N' C' Q A' X :=
  (h.steps hst).mono hN hC (fun q => ⟨q, hA⟩)
theorem GoodQIm.query {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, GoodQIm im (writeHash s a) N C Q A (K a)) :
    GoodQIm im s (N + 1) (C + 8 * q.blocks) Q (A + 8 * q.blocks)
      (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩
theorem GoodQIm.shortHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQIm im (writeHash s a) N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQIm im s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (shortHash input >>= f) K) := by
  have := GoodQIm.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem childLook_ok {im : Image} {j : Nat} (h : ChildCodeAt im j) : LookOK im (childLook j) := by
  intro n w hw
  unfold childLook at hw
  split at hw
  · rename_i hle
    have := h (n - childBase j) w hw
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem childRun_sound {im : Image} {j i : Nat} {dirs : List Dir} {r : PRes} (hcode : ChildCodeAt im j)
    (h : childRun j i dirs = some r) (s : MachineState) (hpc : s.pc = pcOf (childBase j + i))
    (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : r.brs = []) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h (childLook_ok hcode) s hpc (by intro p hp; cases hp) hobl
    (by rw [hbr]; intro b hb; cases hb)
theorem aX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (aX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  simp only [aX8, Addr.eval, E.eval, hB, ofNat_add_ofNat]
theorem eX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (eX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  rw [eX8, addC_eval]; simp only [E.eval, hB, ofNat_add_ofNat]
theorem valid_aX8 {s : MachineState} {B off w : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) : (Oblig.valid (aX8 off) w).holds s := by
  simp only [Oblig.holds, aX8_eval hB, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]
  exact ⟨hhi, hal⟩
theorem lvlObl_holds {s : MachineState} {B : Nat} (l : Nat) (hl : l ≤ 6)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0) (hhi : B + 1024 ≤ MEMORY_BYTES) :
    ∀ o ∈ lvlObl l, o.holds s := by
  have hb : blkO l % 64 = 0 ∧ blkO l ≤ 384 := by unfold blkO; omega
  intro o ho
  unfold lvlObl at ho
  split at ho
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact valid_aX8 hB (by omega) (by omega)
    · show ((E.reg .x8).eval s).toNat % 8 = 0
      simp only [E.eval, hB]
      rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]; exact h8
    · exact valid_aX8 hB (by omega) (by omega)
    · exact valid_aX8 hB (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_aX8 hB (by omega) (by omega)
    · exact valid_aX8 hB (by omega) (by omega)
theorem lvlRegs_x12 (j l : Nat) : (lvlRegs j l).get .x12 = eX8 (curO (l + 1) j) := by
  unfold lvlRegs; exact RegFile.get_set_self _ _ (by decide)
theorem lvlRegs_x10 (j l : Nat) : (lvlRegs j l).get .x10 = eX8 (blkO l) := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x11 (j l : Nat) : (lvlRegs j l).get .x11 = if l = 0 then .c 64 else .reg .x11 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x3 (j l : Nat) :
    (lvlRegs j l).get .x3 = if l ≤ 3 then .c (BitVec.ofNat 64 (heapOf l j)) else .reg .x3 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_other (j l : Nat) (r : Reg) (h3 : r ≠ .x3) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h12 : r ≠ .x12) : (lvlRegs j l).get r = RegFile.init.get r := by
  unfold lvlRegs
  simp only
  split_ifs <;> simp only [RegFile.get_set_ne _ _ h3, RegFile.get_set_ne _ _ h10, RegFile.get_set_ne _ _ h11,
    RegFile.get_set_ne _ _ h12]
theorem heapReg_ne (h : Nat) : heapReg h ≠ .x3 ∧ heapReg h ≠ .x10 ∧ heapReg h ≠ .x11 ∧ heapReg h ≠ .x12 := by
  unfold heapReg; split <;> decide
theorem lvlMem_get {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hb : B + 1024 < 2 ^ 64) (j l A : Nat) (hl : l ≤ 6) (hA : A < 2 ^ 64) :
    memEval s (lvlMem j l) (BitVec.ofNat 64 A) =
      if A = B + blkO l + 24 then (hdr1E j l).eval s
      else if A = B + blkO l + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) := by
  have hbl : blkO l ≤ 384 := by unfold blkO; omega
  unfold lvlMem
  rw [memEval_cons, memEval_cons, memEval_nil, aX8_eval hB, aX8_eval hB]
  simp only [← Nat.add_assoc, E.eval]
  simp only [ofNat_inj hA (show B + blkO l + 24 < 2 ^ 64 by omega),
    ofNat_inj hA (show B + blkO l + 16 < 2 ^ 64 by omega)]
theorem hdr1E_eval {s : MachineState} {j l index : Nat} (hj : j < 128) (hl : l ≤ 6) (hidx : index < 2 ^ 32)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hheap : ∀ h, 1 ≤ h → h ≤ 7 → s.getReg (heapReg h) = BitVec.ofNat 64 (index + 2 ^ 32 * h)) :
    (hdr1E j l).eval s = BitVec.ofNat 64 (hdr1 index (heapOf l j)) := by
  unfold hdr1E
  split_ifs with h3
  · simp only [E.eval, BinOp.eval, h22]
    exact merge_sw2 _ _ _
  · have hb : 1 ≤ heapOf l j ∧ heapOf l j ≤ 7 := by
      unfold heapOf
      have : l = 4 ∨ l = 5 ∨ l = 6 := by omega
      rcases this with rfl | rfl | rfl <;> simp <;> omega
    simp only [E.eval]
    rw [hheap _ hb.1 hb.2]
    congr 1
    unfold hdr1
    rw [Nat.mod_eq_of_lt hidx, Nat.mod_eq_of_lt (by omega)]
    ring
theorem frame_writeHash4 (t : MachineState) (a : BitVec 256) (d : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64) :
    Frame t (writeHash t a) (fun A => A = d ∨ A = d + 8 ∨ A = d + 16 ∨ A = d + 24) := by
  intro A hA hn
  simp only [not_or] at hn
  rw [getMem_writeHash t a d A h12 hd hA, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2.1, if_neg hn.2.2.2]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
theorem childWrites_eq (j : Nat) : childWrites j = stagesW j 7 := rfl
theorem mem_stagesW {j m n off : Nat} (hm : m < n) (h : off ∈ stageW j m) : off ∈ stagesW j n :=
  List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, h⟩
theorem bitAt_lt (j l : Nat) : bitAt j l < 2 := Nat.mod_lt _ (by decide)
theorem stagesW_free {j l off : Nat} (hl : l < 6) (h : off ∈ stagesW j (l + 1)) :
    off ≠ padO l ∧ off ≠ padO l + 8 ∧ off ≠ sibO l j ∧ off ≠ sibO l j + 8 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hbl := bitAt_lt j l
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold padO sibO
  by_cases hml : m = l
  · subst hml
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have : m < l := by omega
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem childWrites_free {j off : Nat} (h : off ∈ childWrites j) :
    off ≠ padO 6 ∧ off ≠ padO 6 + 8 ∧ off ≠ sibO 6 j ∧ off ≠ sibO 6 j + 8 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hb6 := bitAt_lt j 6
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold padO sibO
  by_cases hml : m = 6
  · subst hml
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have : m < 6 := by omega
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem childWrites_bound {j off : Nat} (h : off ∈ childWrites j) : off % 8 = 0 ∧ off + 8 ≤ 464 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold curO at ho; unfold blkO at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
end ClaudeWCT.W9.Machine.Merkle
end
section
namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
structure Mid (j B k index : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (childBase j + ecIdx l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  x3 : 4 ≤ l → s.getReg .x3 = BitVec.ofNat 64 (heapOf 3 j)
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + curO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)
def nodeIn (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) : List UInt8 :=
  let pair := if bitAt j l = 0 then (v, sibs l) else (sibs l, v)
  blk4 pair.1 (header 11 k index 0 (heapOf l j)) (pads l) pair.2
theorem childLevelP_eq (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) :
    childLevelP k index j pads sibs v l = shortHash (nodeIn k index j pads sibs v l) := rfl
theorem nodeIn_blocks (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) :
    (toQ (pad64 (nodeIn k index j pads sibs v l))).blocks = 1 := by
  unfold nodeIn; exact blocks_blk4 _ _ _ _
theorem hdr11_lo (k index heap : Nat) :
    (header 11 k index 0 heap).extractLsb' 0 64 = BitVec.ofNat 64 (w0n k index) := by
  rw [header_lo, if_neg (by decide)]; rfl
theorem hdr11_hi (k index heap : Nat) :
    (header 11 k index 0 heap).extractLsb' 64 64 = BitVec.ofNat 64 (hdr1 index heap) := by
  rw [header_hi, if_neg (by decide)]
theorem DigAt.of_eq {X Y : MachineState} {a : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 a) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (a + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y a d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem hashInput_blk4 (t : MachineState) (A : Nat) (a b c d : Digest)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (hA : A % 8 = 0)
    (hA' : A + 64 < 2 ^ 64) (ha : DigAt t A a) (hb : DigAt t (A + 16) b) (hc : DigAt t (A + 32) c)
    (hd : DigAt t (A + 48) d) : hashInput t = toQ (pad64 (blk4 a b c d)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA hA' h11
  rw [wordsOf_blk4, ha.1, ha.2, hb.1, hc.1, hd.1, show A + 24 = A + 16 + 8 by omega, hb.2,
    show A + 40 = A + 32 + 8 by omega, hc.2, show A + 56 = A + 48 + 8 by omega, hd.2]
theorem stagesW_mono {j n n' off : Nat} (h : off ∈ stagesW j n) (hn : n ≤ n') : off ∈ stagesW j n' := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  exact mem_stagesW (by have := List.mem_range.mp hm; omega) ho
theorem lvl_step {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u) (l : Nat) (hl : l < 6) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt l) (lvlSt l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads sibs v l)) ∧
      ∀ a : BitVec 256, Mid j B k index u (l + 1) (a.extractLsb' 0 128) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (childBase j + (ecIdx l + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_lvl j hj l hl) s hpc
    (lvlObl_holds l (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) rfl
  have hreg : ∀ x, ((lvlRes j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((lvlRes j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO l + 24 then (hdr1E j l).eval s
      else if A = B + blkO l + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j l A (by omega) hA)
  generalize ht : (lvlRes j l).toState s = t at hst hec hreg hmem
  have hbl : blkO l + 64 ≤ 384 + 64 := by unfold blkO; omega
  have hb := bitAt_lt j l
  have hb1 := bitAt_lt j (l + 1)
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, lvlRegs_x11]
    split_ifs with h0
    · rfl
    · exact hs.a1 h0
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO (l + 1) j) := by
    rw [hreg, lvlRegs_x12, eX8_eval hx8]
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have hcur : curO (l + 1) j % 8 = 0 ∧ curO (l + 1) j + 32 ≤ 464 := by
    unfold curO blkO; omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO l) 64 (B + curO (l + 1) j) h10 h11 h12 (by unfold blkO; omega) (by decide)
      (by omega) (by omega) (by omega)
  have tS : ∀ o, o ≤ 1024 → o ≠ blkO l + 16 → o ≠ blkO l + 24 →
      t.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho h16 h24
    rw [hmem _ (by omega), if_neg (by omega), if_neg (by omega)]
  have sU : ∀ o, o ≤ 1024 → o ∉ stagesW j (l + 1) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hn
    refine hs.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have : off = o := by omega
    subst this; exact hn hoff
  have hpad : DigAt t (B + blkO l + 32) (pads l) := by
    have hP := hu.padAt l hl
    unfold padO at hP
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hl h
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO l + 32) + 8 = B + (blkO l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l hl
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hl h
    have hsb : sibO l j + 8 ≤ 1024 ∧ (sibO l j = blkO l ∨ sibO l j = blkO l + 48) := by
      unfold sibO blkO; omega
    refine DigAt.of_eq hS ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.1 rfl)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.2 rfl)]
  have hnode : DigAt t (B + curO l j) v := by
    have hcb : curO l j + 8 ≤ 1024 ∧ (curO l j = blkO l ∨ curO l j = blkO l + 48) := by
      unfold curO blkO; omega
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega)]
  have hhdr : DigAt t (B + blkO l + 16) (header 11 k index 0 (heapOf l j)) := by
    constructor
    · rw [hmem _ (by omega), if_neg (by omega), if_pos rfl, hdr11_lo,
        hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
    · rw [show B + blkO l + 16 + 8 = B + blkO l + 24 by omega, hmem _ (by omega), if_pos rfl, hdr11_hi]
      apply hdr1E_eval hj (by omega) hidx
      · rw [hkeep .x22 (by decide) (by decide) (by decide) (by decide)]; exact hu.s6
      · intro h h1 h7
        obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h
        rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7
  have hin : hashInput t = toQ (pad64 (nodeIn k index j pads sibs v l)) := by
    unfold nodeIn
    rcases Nat.lt_or_ge (bitAt j l) 1 with h0 | h1
    · have e0 : bitAt j l = 0 := by omega
      have ec : curO l j = blkO l := by unfold curO; omega
      have es : sibO l j = blkO l + 48 := by unfold sibO; omega
      simp only [e0, if_true]
      rw [ec] at hnode; rw [es, ← Nat.add_assoc] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by unfold blkO; omega) (by omega) hnode hhdr hpad hsib
    · have e1 : bitAt j l = 1 := by omega
      have ec : curO l j = blkO l + 48 := by unfold curO; omega
      have es : sibO l j = blkO l := by unfold sibO; omega
      simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by unfold blkO; omega) (by omega) hsib hhdr hpad hnode
  refine ⟨t, hst, hec rfl, h5, hv, hin, fun a => ?_⟩
  have hpcT : t.pc = pcOf (childBase j + ecIdx (l + 1)) := by
    rw [← ht, PRes.toState_pc (lvlRes j l) s rfl]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · intro h4
    rw [writeHash_getReg, hreg, lvlRegs_x3]
    split_ifs with hl3
    · have : l = 3 := by omega
      subst this; rfl
    · exact hs.x3 (by omega)
  · intro _; rw [writeHash_getReg]; exact h11
  · rw [writeHash_getReg]; exact h12
  · exact DigAt.writeHash_lo t a _ h12 (by omega)
  · have hP : Frame s t (fun A => A = B + blkO l + 24 ∨ A = B + blkO l + 16) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    have hW := frame_writeHash4 t a (B + curO (l + 1) j) h12 (by omega)
    refine ((hs.frame.trans hP).trans hW).mono ?_
    intro A _ hA
    rcases hA with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | (rfl | rfl | rfl | rfl)
    · exact ⟨off, stagesW_mono hoff (by omega), rfl⟩
    · exact ⟨blkO l + 24, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨blkO l + 16, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨curO (l + 1) j + 8, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 16, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 24, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
theorem p7_step {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u 6 v s) :
    ∃ t, Steps im s 4 4 t ∧ ChildPost j B k index u v t := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (childBase j + (ecIdx 6 + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, -⟩ := childRun_sound hcode (childRun_p7 j hj) s hpc
    (lvlObl_holds 6 (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) rfl
  have hreg : ∀ x, ((p7Res j).toState s).getReg x = ((RegFile.init.set .x10 (eX8 (blkO 6))).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((p7Res j).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO 6 + 24 then (hdr1E j 6).eval s
      else if A = B + blkO 6 + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j 6 A (by omega) hA)
  have hpcT : ((p7Res j).toState s).pc = s.getReg .x1 &&& ~~~1#64 := rfl
  generalize ht : (p7Res j).toState s = t at hst hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x10 → t.getReg r = s.getReg r := by
    intro r h10; rw [hreg, RegFile.get_set_ne _ _ h10, RegFile.init_get_eval]
  have hb6 := bitAt_lt j 6
  have hblk6 : blkO 6 = 0 := rfl
  have hheap6 : heapOf 6 j = 1 := by
    unfold heapOf
    rw [show 2 ^ (6 + 1) = 128 by rfl, Nat.div_eq_of_lt hj]; rfl
  refine ⟨t, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcT, hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
  · intro r h3 h10 h11 h12; rw [hother r h10]; exact hkeep r h3 h10 h11 h12
  · rw [hother .x3 (by decide)]; exact hs.x3 (by omega)
  · rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval hx8, hblk6, Nat.add_zero]
  · rw [hother .x11 (by decide)]; exact hs.a1 (by omega)
  · rw [hother .x12 (by decide)]; exact hs.a2
  · have hc : curO 6 j = 0 ∨ curO 6 j = 48 := by unfold curO blkO; omega
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_neg (by rw [hblk6]; omega)]
    · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_neg (by rw [hblk6]; omega)]
  · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_pos (by rw [hblk6]),
      hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
  · rw [hmem _ (by omega), if_pos (by rw [hblk6])]
    rw [← hheap6]
    apply hdr1E_eval hj (by omega) hidx
    · rw [hkeep .x22 (by decide) (by decide) (by decide) (by decide)]; exact hu.s6
    · intro h h1 h7
      obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h
      rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7
  · have hP : Frame s t (fun A => A = B + blkO 6 + 24 ∨ A = B + blkO 6 + 16) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    refine (hs.frame.trans hP).mono ?_
    intro A _ hA
    rw [childWrites_eq]
    rcases hA with ⟨off, hoff, rfl⟩ | (rfl | rfl)
    · exact ⟨off, hoff, rfl⟩
    · exact ⟨blkO 6 + 24, mem_stagesW (m := 6) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨blkO 6 + 16, mem_stagesW (m := 6) (by omega) (by simp [stageW]), by omega⟩
def fuelR : Nat → Nat → Nat
  | _, 0 => 4
  | l, n + 1 => lvlSt l + 1 + fuelR (l + 1) n
def cycR : Nat → Nat → Nat
  | _, 0 => 4
  | l, n + 1 => lvlSt l + 8 + cycR (l + 1) n
theorem fuelR_06 : fuelR 0 6 = 43 := rfl
theorem cycR_06 : cycR 0 6 = 85 := rfl
theorem child_rest {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u) (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, ChildPost j B k index u v t → GoodQIm im t N C Q A (K v)) :
    ∀ n l v s, l + n = 6 → Mid j B k index u l v s →
      GoodQIm im s (N + fuelR l n) (C + cycR l n) Q (A + cycR l n)
        (ccM ((List.range' l n).foldlM (childLevelP k index j pads sibs) v) K) := by
  intro n
  induction n with
  | zero =>
    intro l v s hln hs
    have hl6 : l = 6 := by omega
    subst hl6
    obtain ⟨t, hst, hpost⟩ := p7_step hj hcode hidx hu v s hs
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure, fuelR, cycR]
    exact GoodQIm.steps hst (hK v t hpost)
  | succ m ih =>
    intro l v s hln hs
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step hj hcode hidx hu l (by omega) v s hs
    rw [List.range'_succ, List.foldlM_cons, childLevelP_eq]
    have H : ∀ a : BitVec 256, GoodQIm im (writeHash t a) (N + fuelR (l + 1) m) (C + cycR (l + 1) m) Q
        (A + cycR (l + 1) m)
        (ccM ((fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads sibs) v')
          (a.extractLsb' 0 128)) K) :=
      fun a => ih (l + 1) _ _ (by omega) (hpost a)
    have hg := GoodQIm.shortHash_bind
      (f := fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads sibs) v') hf h5 hv hin H
    rw [nodeIn_blocks] at hg
    simp only [fuelR, cycR]
    exact GoodQIm.steps' hst hg (by omega) (by omega) (by omega)
theorem leafBytes_length (leaf : Nat → Digest) : (leafBytes leaf).length = 128 := by
  simp [leafBytes, List.length_flatMap, bytesLE_length]
theorem leaf_blocks (leaf : Nat → Digest) : (toQ (pad64 (leafBytes leaf))).blocks = 2 := by
  rw [pad64_of_aligned _ (by rw [leafBytes_length]), blocks_toQ (by rw [Aligned, leafBytes_length]; omega),
    leafBytes_length]
theorem child_good (im : Image) (j : Nat) (hj : j < 128) (hcode : ChildCodeAt im j) : ChildGood im j := by
  intro B k index leaf pads sibs u N C A Q K hidx hu hK
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_p0 j hj) u (by rw [hu.pc, Nat.add_zero]) (by intro o ho; cases ho) rfl
  have hreg : ∀ x, ((p0Res j).toState u).getReg x =
      ((RegFile.init.set .x12 (eX8 (curO 0 j))).get x).eval u := fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, ((p0Res j).toState u).getMem A = u.getMem A :=
    fun A => (PRes.toState_getMem _ _ _).trans (memEval_nil _ _)
  have hpcT : ((p0Res j).toState u).pc = pcOf (childBase j + 1) := PRes.toState_pc (p0Res j) u rfl
  generalize ht : (p0Res j).toState u = t at hst hec hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h12; rw [hreg, RegFile.get_set_ne _ _ h12, RegFile.init_get_eval]
  have hb0 := bitAt_lt j 0
  have hc0 : curO 0 j % 8 = 0 ∧ curO 0 j + 32 ≤ 464 := by unfold curO blkO; omega
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + leafO) := (hother .x10 (by decide)).trans hu.a0
  have h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := (hother .x11 (by decide)).trans hu.a1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO 0 j) := by
    rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval hu.s0]
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide)).trans hu.t0
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + leafO) 128 (B + curO 0 j) h10 h11 h12 (by unfold leafO; omega) (by decide)
      (by unfold leafO; omega) (by omega) (by omega)
  have hin : hashInput t = toQ (pad64 (leafBytes leaf)) := by
    rw [pad64_of_aligned _ (by rw [leafBytes_length])]
    apply hashInput_toQ t _ 1 (B + leafO) (leafBytes_length leaf) h10 (by unfold leafO; omega)
      (by unfold leafO; omega) h11 (by norm_num)
    have hD : DigsAt t (B + leafO) ((List.range 8).map leaf) := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      have e : ((List.range 8).map leaf).getD i 0 = leaf i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rw [e]
      exact DigAt.of_eq (hu.leafAt i hi) (hmem _) (hmem _)
    have hw := hD.words
    simp only [List.length_map, List.length_range] at hw
    rw [hw]
    rfl
  have H : ∀ a : BitVec 256, GoodQIm im (writeHash t a) (N + fuelR 0 6) (C + cycR 0 6) Q (A + cycR 0 6)
      (ccM ((fun v => (List.range 6).foldlM (childLevelP k index j pads sibs) v) (a.extractLsb' 0 128)) K) := by
    intro a
    have hmid : Mid j B k index u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, fun h => absurd h (by decide), fun h => absurd rfl h, ?_, ?_, ?_⟩
      · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]; rfl
      · intro r _ _ _ h12'; rw [writeHash_getReg]; exact hother r h12'
      · rw [writeHash_getReg]; exact h12
      · exact DigAt.writeHash_lo t a _ h12 (by omega)
      · have hT : Frame u t (fun _ => False) := fun A _ _ => hmem _
        refine (hT.trans (frame_writeHash4 t a (B + curO 0 j) h12 (by omega))).mono ?_
        intro A _ hA
        rcases hA with h | (rfl | rfl | rfl | rfl)
        · exact absurd h id
        · exact ⟨curO 0 j, mem_stagesW (m := 0) (by omega) (by simp [stageW]), rfl⟩
        · exact ⟨curO 0 j + 8, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 16, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 24, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
    show GoodQIm im (writeHash t a) (N + fuelR 0 6) (C + cycR 0 6) Q (A + cycR 0 6)
      (ccM ((List.range 6).foldlM (childLevelP k index j pads sibs) (a.extractLsb' 0 128)) K)
    rw [List.range_eq_range']
    exact child_rest hj hcode hidx hu K N C A Q hK 6 0 _ _ rfl hmid
  have hg := GoodQIm.shortHash_bind
    (f := fun v => (List.range 6).foldlM (childLevelP k index j pads sibs) v) (hec rfl) h5 hv hin H
  rw [leaf_blocks, fuelR_06, cycR_06] at hg
  exact GoodQIm.steps' hst hg (by simp only [p0Res]; omega) (by simp only [p0Res]; omega)
    (by simp only [p0Res]; omega)
theorem child_refines (im : Image) (j : Nat) (hj : j < 128) (hcode : ChildCodeAt im j) : ChildRefines im j := by
  intro B k index leaf pads sibs P hidx hP u N C A Q K hu hK
  exact child_good im j hj hcode B k index leaf pads sibs u N C A Q K hidx (hP u hu)
    (fun v t hpost => hK v t ⟨u, hu, hpost⟩)
end ClaudeWCT.W9.Machine.Merkle
end
