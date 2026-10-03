import SigGolfCandidate.T3M.Verify.CanonicalDispatch
import SigGolfCandidate.T3M.Verify.CanonicalTables

namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.CanonicalGeometry

theorem geometry_small : ∀ d : Fin 128,
    UnOp.eval (.ld .bu 0) (geometryWord d.val)=BitVec.ofNat 64 (8*bitLength d.val) :=
  by decide +kernel

theorem geometry_large : ∀ d : Fin 128,
    UnOp.eval (.ld .hu 4) (geometryWord d.val)=BitVec.ofNat 64 (64*bitLength d.val) :=
  by decide +kernel

theorem geometry_height : ∀ d : Fin 128, bitLength d.val<8 := by decide +kernel

theorem ptrE_eval (s : MachineState) (c j bucket leaf : Nat)
    (h : s.getMem (BitVec.ofNat 64 (0x140+24*c+8*j))=
      BitVec.ofNat 64 (pointer bucket leaf)) :
    (ptrE c j).eval s=BitVec.ofNat 64 (pointer bucket leaf) := h

theorem xorE_eval (s : MachineState) (c i j bucket x y : Nat)
    (hx : x<128) (hy : y<128)
    (hi : (ptrE c i).eval s=BitVec.ofNat 64 (pointer bucket x))
    (hj : (ptrE c j).eval s=BitVec.ofNat 64 (pointer bucket y)) :
    (xorE c i j).eval s=BitVec.ofNat 64 (8*(x ^^^ y)) := by
  change ((ptrE c i).eval s ^^^ (ptrE c j).eval s)=_
  rw [hi,hj,← BitVec.ofNat_xor,pointer_xor bucket x y hx hy]

theorem geomE_eval (s : MachineState) (c i j bucket x y : Nat)
    (ht : TablesOK s) (hx : x<128) (hy : y<128)
    (hi : (ptrE c i).eval s=BitVec.ofNat 64 (pointer bucket x))
    (hj : (ptrE c j).eval s=BitVec.ofNat 64 (pointer bucket y)) :
    (geomE c i j).eval s=geometryWord (x ^^^ y) := by
  have hd := Nat.xor_lt_two_pow (n:=7) hx hy
  change s.getMem ((xorE c i j).eval s+BitVec.ofNat 64 0xfef000)=_
  rw [xorE_eval s c i j bucket x y hx hy hi hj,BitVec.ofNat_add_ofNat,Nat.add_comm]
  exact TablesOK.geometry s ht (x ^^^ y) hd

theorem smallE_eval (s : MachineState) (c bucket x y : Nat)
    (ht : TablesOK s) (hx : x<128) (hy : y<128)
    (hi : (ptrE c 0).eval s=BitVec.ofNat 64 (pointer bucket x))
    (hj : (ptrE c 1).eval s=BitVec.ofNat 64 (pointer bucket y)) :
    (smallE c).eval s=BitVec.ofNat 64 (8*bitLength (x ^^^ y)) := by
  change UnOp.eval (.ld .bu 0) ((geomE c 0 1).eval s)=_
  rw [geomE_eval s c 0 1 bucket x y ht hx hy hi hj]
  exact geometry_small ⟨x ^^^ y,Nat.xor_lt_two_pow (n:=7) hx hy⟩

theorem largeE_eval (s : MachineState) (c bucket y z : Nat)
    (ht : TablesOK s) (hy : y<128) (hz : z<128)
    (hi : (ptrE c 1).eval s=BitVec.ofNat 64 (pointer bucket y))
    (hj : (ptrE c 2).eval s=BitVec.ofNat 64 (pointer bucket z)) :
    (largeE c).eval s=BitVec.ofNat 64 (64*bitLength (y ^^^ z)) := by
  change UnOp.eval (.ld .hu 4) ((geomE c 1 2).eval s)=_
  rw [geomE_eval s c 1 2 bucket y z ht hy hz hi hj]
  exact geometry_large ⟨y ^^^ z,Nat.xor_lt_two_pow (n:=7) hy hz⟩

theorem targetE_eval (s : MachineState) (c bucket x y z : Nat)
    (ht : TablesOK s) (hx : x<128) (hy : y<128) (hz : z<128)
    (h0 : (ptrE c 0).eval s=BitVec.ofNat 64 (pointer bucket x))
    (h1 : (ptrE c 1).eval s=BitVec.ofNat 64 (pointer bucket y))
    (h2 : (ptrE c 2).eval s=BitVec.ofNat 64 (pointer bucket z)) :
    (targetE c).eval s=jumpWord (bitLength (x ^^^ y)) (bitLength (y ^^^ z)) := by
  have hl := geometry_height ⟨x ^^^ y,Nat.xor_lt_two_pow (n:=7) hx hy⟩
  have hr := geometry_height ⟨y ^^^ z,Nat.xor_lt_two_pow (n:=7) hy hz⟩
  change s.getMem (((smallE c).eval s+(largeE c).eval s)+BitVec.ofNat 64 0xfef400)=_
  rw [smallE_eval s c bucket x y ht hx hy h0 h1,
    largeE_eval s c bucket y z ht hy hz h1 h2,
    BitVec.ofNat_add_ofNat,BitVec.ofNat_add_ofNat]
  rw [show 8*bitLength (x ^^^ y)+64*bitLength (y ^^^ z)+0xfef400=
      0xfef400+8*bitLength (x ^^^ y)+64*bitLength (y ^^^ z) by omega]
  exact TablesOK.jump s ht _ _ hl hr

end SigGolfCandidate.T3M.CanonicalNative
