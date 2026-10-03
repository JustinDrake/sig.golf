import SigGolfCandidate.T3M.Verify.CanonicalRung
import SigGolfCandidate.T3M.Verify.FtsSem

/-! Typed access, direction, and memory frames for the scheduled FTS blocks.
The checked instruction paths quantify over arbitrary registers and memory. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def pendingAddr (p : BlockPlan) (base : Nat) : Nat :=
  match p.leaf with
  | some j => base+48*j
  | none => frame (p.depth+1)

theorem pendingSrc_eval (p : BlockPlan) (s : MachineState) (base : Nat)
    (h19 : s.getReg .x19=BitVec.ofNat 64 base) :
    (pendingSrc p).eval s=BitVec.ofNat 64 (pendingAddr p base) := by
  cases he : p.leaf with
  | none => simp [pendingSrc,pendingAddr,he,E.eval,cE]
  | some j => simp [pendingSrc,pendingAddr,he,leafSrc,rAdd,addC_eval,E.eval,h19,
      BitVec.ofNat_add_ofNat]

theorem pendingAddr_header (p : BlockPlan) (s : MachineState) (base : Nat)
    (h19 : s.getReg .x19=BitVec.ofNat 64 base) (off : Nat) :
    (match p.leaf with
      | some j => leafAddr j off
      | none => (⟨none,BitVec.ofNat 64 (frame (p.depth+1)+off)⟩ : Addr)).eval s=
      BitVec.ofNat 64 (pendingAddr p base+off) := by
  cases he : p.leaf with
  | none => simp [pendingAddr,he,Addr.eval,E.eval]
  | some j => simp [pendingAddr,leafAddr,he,Addr.eval,E.eval,h19,BitVec.ofNat_add_ofNat]
              congr 1 <;> omega

theorem RawRes.pending_src {p : BlockPlan} {side : Nat} {s t : MachineState}
    (h : RawRes (pendingSpec p side) pendingKeep s t) (base : Nat)
    (h19 : s.getReg .x19=BitVec.ofNat 64 base) :
    t.getReg .x10=BitVec.ofNat 64 (pendingAddr p base) := by
  rw [h.regs (.x10,pendingSrc p) (by simp [pendingSpec])]
  exact pendingSrc_eval p s base h19

theorem RawRes.pending_heap {p : BlockPlan} {side : Nat} {s t : MachineState}
    (h : RawRes (pendingSpec p side) pendingKeep s t) (heap : Nat)
    (he : (pendingHeap p).eval s=FtsRev.rv heap) : t.getReg .x23=FtsRev.rv heap := by
  rw [h.regs (.x23,pendingHeap p) (by simp [pendingSpec]),he]

theorem RawRes.pending_pointer {p : BlockPlan} {side : Nat} {s t : MachineState}
    (h : RawRes (pendingSpec p side) pendingKeep s t) (ptr : Nat)
    (h14 : s.getReg .x14=BitVec.ofNat 64 ptr) :
    t.getReg .x14=BitVec.ofNat 64 (ptr+8+80*p.folds) := by
  rw [h.regs (.x14,rAdd .x14 (BitVec.ofNat 64 (8+80*p.folds)))
    (by simp [pendingSpec])]
  simp [rAdd,addC_eval,E.eval,h14,BitVec.ofNat_add_ofNat,Nat.add_assoc]

theorem RawRes.pending_header {p : BlockPlan} {side : Nat} {s t : MachineState}
    (h : RawRes (pendingSpec p side) pendingKeep s t) (base : Nat)
    (h19 : s.getReg .x19=BitVec.ofNat 64 base)
    (hb : pendingAddr p base+24<2^64) :
    t.getMem (BitVec.ofNat 64 (pendingAddr p base+16))=
      s.getReg (if p.leaf.isSome then .x28 else .x27) ∧
    t.getMem (BitVec.ofNat 64 (pendingAddr p base+24))=(pendingHeap p).eval s := by
  have hn : BitVec.ofNat 64 (pendingAddr p base+16)≠
      BitVec.ofNat 64 (pendingAddr p base+24) := by
    intro hh
    have he := congrArg BitVec.toNat hh
    simp only [toNat_ofNat_lt (show pendingAddr p base+16<2^64 by omega),
      toNat_ofNat_lt hb] at he
    omega
  cases hp : p.leaf with
  | none =>
    have ha := pendingAddr_header p s base h19 16
    have hc := pendingAddr_header p s base h19 24
    simp only [hp] at ha hc
    constructor
    · rw [h.mem]; simp [pendingSpec,pendingMem,hp,memEval,ha,hc,hn,E.eval]
    · rw [h.mem]; simp [pendingSpec,pendingMem,hp,memEval,ha,hc]
  | some j =>
    have ha := pendingAddr_header p s base h19 16
    have hc := pendingAddr_header p s base h19 24
    simp only [hp] at ha hc
    constructor
    · rw [h.mem]; simp [pendingSpec,pendingMem,hp,memEval,ha,hc,hn,E.eval]
    · rw [h.mem]; simp [pendingSpec,pendingMem,hp,memEval,ha,hc]

theorem RawRes.pending_frame {p : BlockPlan} {side : Nat} {s t : MachineState}
    (h : RawRes (pendingSpec p side) pendingKeep s t) (base : Nat) (A : Word)
    (h19 : s.getReg .x19=BitVec.ofNat 64 base)
    (ha : A≠BitVec.ofNat 64 (pendingAddr p base+16))
    (hb : A≠BitVec.ofNat 64 (pendingAddr p base+24)) : t.getMem A=s.getMem A := by
  apply h.frame A
  intro v hv
  cases hp : p.leaf with
  | none =>
    simp only [pendingSpec,pendingMem,hp,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · simpa only [pendingAddr,hp,Addr.eval] using hb
    · simpa only [pendingAddr,hp,Addr.eval] using ha
  | some j =>
    simp only [pendingSpec,pendingMem,hp,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · have he := pendingAddr_header p s base h19 24
      simp only [hp] at he
      simpa only [he] using hb
    · have he := pendingAddr_header p s base h19 16
      simp only [hp] at he
      simpa only [he] using ha

theorem pending_br_holds (p : BlockPlan) (s : MachineState) (heap : Nat)
    (he : (pendingHeap p).eval s=FtsRev.rv heap) :
    ∀ b∈(pendingSpec p (heap%2)).brs, b.holds s := by
  intro b hb
  by_cases ha : p.folds=0
  · simp [pendingSpec,ha] at hb
  · simp only [pendingSpec,ha,if_false,List.mem_cons,List.not_mem_nil,or_false] at hb
    subst b
    simp only [Br.holds,E.eval,cE,he,CmpOp.eval]
    exact FtsRev.rv_slt heap

theorem rung_br_holds (p : BlockPlan) (s : MachineState) (heap i : Nat)
    (h23 : s.getReg .x23=FtsRev.rv heap) (hh : heap<2^64) :
    ∀ b∈(rungSpec p i (heap%2) (heap/2%2)).brs, b.holds s := by
  intro b hb
  by_cases ha : i+1=p.folds
  · simp [rungSpec,ha] at hb
  · simp only [rungSpec,ha,if_false,List.mem_cons,List.not_mem_nil,or_false] at hb
    subst b
    have hs : shifted.eval s=FtsRev.rv (heap/2) := by
      simp only [shifted,E.eval,cE,h23]
      exact FtsRev.rv_sll1 heap hh
    have hv : BitVec.slt (FtsRev.rv (heap/2)) (0#64)=decide (heap/2%2=1) :=
      FtsRev.rv_slt (heap/2)
    rcases Nat.mod_two_eq_zero_or_one heap with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one (heap/2) with h2 | h2 <;>
        simp [Br.holds,hs,h0,h2,cE,E.eval,CmpOp.eval,hv]

theorem pending_access (p : BlockPlan) (s : MachineState) (c : Nat) (hc : c<7)
    (hj : ∀ j, p.leaf=some j → j<3)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c))
    (hs : ∀ j, p.leaf=some j → accessValid (s.getReg (slotReg j)) 8=true) :
    ∀ o∈pendingObl p, o.holds s := by
  intro o ho
  cases hp : p.leaf with
  | none => simp [pendingObl,hp] at ho
  | some j =>
    have hj3 := hj j hp
    simp only [pendingObl,hp,List.mem_cons,List.not_mem_nil,or_false] at ho
    have hv : ∀ off, off=16 ∨ off=24 →
        accessValid ((leafAddr j off).eval s) 8=true := by
      intro off hoff
      simp only [leafAddr,Addr.eval,E.eval,h19,BitVec.ofNat_add_ofNat]
      apply accessValid_ofNat
      · unfold WIT; rcases hoff with rfl | rfl <;> omega
      · unfold WIT; rcases hoff with rfl | rfl <;> omega
    rcases ho with rfl | rfl | rfl
    · exact hv 24 (by simp)
    · exact hv 16 (by simp)
    · simpa [Oblig.holds,Addr.eval] using hs j hp

theorem rung_access (p : BlockPlan) (s : MachineState) (P i : Nat)
    (h14 : s.getReg .x14=BitVec.ofNat 64 P+BitVec.ofNat 64 (80*p.folds))
    (hP : P%8=0) (hb : P+80*i+32 ≤ 2^24) :
    ∀ o∈rungObl p i, o.holds s := by
  intro o ho
  simp only [rungObl,List.mem_cons,List.not_mem_nil,or_false] at ho
  have hv : ∀ off, off=16 ∨ off=24 → accessValid ((rungAddr p i off).eval s) 8=true := by
    intro off hoff
    rw [rungAddr_eval p i off s _ h14,BitVec.ofNat_add_ofNat]
    apply accessValid_ofNat
    · rcases hoff with rfl | rfl <;> omega
    · rcases hoff with rfl | rfl <;> omega
  rcases ho with rfl | rfl
  · exact hv 24 (by simp)
  · exact hv 16 (by simp)

#print axioms pending_br_holds
#print axioms rung_br_holds
end SigGolfCandidate.T3M.CanonicalNative
