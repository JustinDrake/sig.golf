import SigGolfCandidate.T3M.Verify.CanonicalChecked
import SigGolfCandidate.T3M.Verify.FtsRev

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

theorem offset_cancel (P A B : Word) : (P+A)+(B-A)=P+B := by
  rw [BitVec.add_assoc,BitVec.add_comm A (B-A),BitVec.sub_add_cancel]

theorem rungAddr_eval (p : BlockPlan) (i off : Nat) (s : MachineState) (P : Word)
    (h14 : s.getReg .x14=P+BitVec.ofNat 64 (80*p.folds)) :
    (rungAddr p i off).eval s=P+BitVec.ofNat 64 (80*i+off) := by
  change s.getReg .x14+(BitVec.ofNat 64 (80*i+off)-BitVec.ofNat 64 (80*p.folds))=_
  rw [h14,offset_cancel]

theorem RawRes.rung_src {p : BlockPlan} {i side out : Nat} {s t : MachineState}
    (h : RawRes (rungSpec p i side out) rungKeep s t) (P : Word)
    (h14 : s.getReg .x14=P+BitVec.ofNat 64 (80*p.folds)) :
    t.getReg .x10=P+BitVec.ofNat 64 (80*i) := by
  have hr := h.regs (.x10,rungSrc p i) (by simp [rungSpec])
  rw [hr]
  simp only [rungSrc,rAdd,addC_eval,E.eval,h14]
  exact offset_cancel _ _ _

theorem RawRes.rung_heap {p : BlockPlan} {i side out : Nat} {s t : MachineState}
    (h : RawRes (rungSpec p i side out) rungKeep s t) (heap : Nat)
    (h23 : s.getReg .x23=FtsRev.rv heap) (hE : heap<2^64) :
    t.getReg .x23=FtsRev.rv (heap/2) := by
  rw [h.regs (.x23,shifted) (by simp [rungSpec])]
  simp only [shifted,E.eval,cE,h23]
  exact FtsRev.rv_sll1 heap hE

theorem rung_offsets_distinct (P : Word) : P+(16#64)≠P+(24#64) := by
  intro h
  have hh := congrArg (fun x : Word => x-P) h
  rw [BitVec.add_comm P (16#64),BitVec.add_sub_cancel,
    BitVec.add_comm P (24#64),BitVec.add_sub_cancel] at hh
  contradiction

theorem RawRes.rung_header {p : BlockPlan} {i side out : Nat} {s t : MachineState}
    (h : RawRes (rungSpec p i side out) rungKeep s t) (P : Word)
    (h14 : s.getReg .x14=P+BitVec.ofNat 64 (80*p.folds)) :
    t.getMem (P+BitVec.ofNat 64 (80*i+16))=s.getReg .x27 ∧
      t.getMem (P+BitVec.ofNat 64 (80*i+24))=shifted.eval s := by
  have ha := rungAddr_eval p i 16 s P h14
  have hb := rungAddr_eval p i 24 s P h14
  have hn : P+BitVec.ofNat 64 (80*i+16)≠P+BitVec.ofNat 64 (80*i+24) := by
    rw [BitVec.ofNat_add,BitVec.ofNat_add]
    simpa only [← BitVec.add_assoc] using rung_offsets_distinct (P+BitVec.ofNat 64 (80*i))
  constructor
  · rw [h.mem]
    simp [rungSpec,rungMem,memEval,ha,hb,hn,E.eval]
  · rw [h.mem]
    simp [rungSpec,rungMem,memEval,ha,hb]

theorem RawRes.rung_frame {p : BlockPlan} {i side out : Nat} {s t : MachineState}
    (h : RawRes (rungSpec p i side out) rungKeep s t) (P A : Word)
    (h14 : s.getReg .x14=P+BitVec.ofNat 64 (80*p.folds))
    (ha : A≠P+BitVec.ofNat 64 (80*i+16))
    (hb : A≠P+BitVec.ofNat 64 (80*i+24)) : t.getMem A=s.getMem A := by
  apply h.frame A
  intro v hv
  simp only [rungSpec,rungMem,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · simpa only [rungAddr_eval p i 24 s P h14] using hb
  · simpa only [rungAddr_eval p i 16 s P h14] using ha

end SigGolfCandidate.T3M.CanonicalNative
