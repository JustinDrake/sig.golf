import SigGolfCandidate.T3M.Verify.CanonicalDispatchSemantics
import SigGolfCandidate.T3M.Verify.CanonicalPlan
import SigGolfCandidate.T3M.Verify.FtsSem

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.CanonicalGeometry

theorem bitLength_lca (x y : Nat) (hne : x≠y) : bitLength (x ^^^ y)=lcaLevel x y := by
  simp [bitLength,lcaLevel,Nat.xor_ne_zero_iff.mpr hne]

theorem geom_start : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x.val≠y.val →
    ((geoms[x.val]!)[y.val]!)=(plan (geomIndex x.val y.val) 0).start := by decide +kernel

theorem jump_start (x y : Nat) (hx : 0<x ∧ x<8) (hy : 0<y ∧ y<8) (hne : x≠y) :
    jumpWord x y=pcOf (plan (geomIndex x y) 0).start := by
  unfold jumpWord
  rw [if_neg (by omega),geom_start ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 hne]

theorem dispatch_access (s : MachineState) (c bucket x y z : Nat)
    (ht : TablesOK s) (hx : x<128) (hy : y<128) (hz : z<128)
    (h0 : (ptrE c 0).eval s=BitVec.ofNat 64 (pointer bucket x))
    (h1 : (ptrE c 1).eval s=BitVec.ofNat 64 (pointer bucket y))
    (h2 : (ptrE c 2).eval s=BitVec.ofNat 64 (pointer bucket z)) :
    ∀ o∈dispatchObl c, o.holds s := by
  have hab := Nat.xor_lt_two_pow (n:=7) hx hy
  have hbc := Nat.xor_lt_two_pow (n:=7) hy hz
  have ha := geometry_height ⟨x ^^^ y,hab⟩
  have hb := geometry_height ⟨y ^^^ z,hbc⟩
  dsimp only at ha hb
  have he01 := xorE_eval s c 0 1 bucket x y hx hy h0 h1
  have he12 := xorE_eval s c 1 2 bucket y z hy hz h1 h2
  have hes := smallE_eval s c bucket x y ht hx hy h0 h1
  have hel := largeE_eval s c bucket y z ht hy hz h1 h2
  intro o ho
  simp only [dispatchObl,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · change accessValid ((smallE c).eval s+(largeE c).eval s+(0xfef400#64)) 8=true
    rw [hes,hel,show (0xfef400#64)=BitVec.ofNat 64 0xfef400 by rfl,
      BitVec.ofNat_add_ofNat,BitVec.ofNat_add_ofNat]
    apply accessValid_ofNat <;> omega
  · change ((xorE c 1 2).eval s).toNat%8=0
    rw [he12,toNat_ofNat_lt (by omega)]
    omega
  · change accessValid ((xorE c 1 2).eval s+(0xfef004#64)) 2=true
    rw [he12,show (0xfef004#64)=BitVec.ofNat 64 0xfef004 by rfl,BitVec.ofNat_add_ofNat]
    apply accessValid_ofNat <;> omega
  · change ((xorE c 0 1).eval s).toNat%8=0
    rw [he01,toNat_ofNat_lt (by omega)]
    omega
  · change accessValid ((xorE c 0 1).eval s+(0xfef000#64)) 1=true
    rw [he01,show (0xfef000#64)=BitVec.ofNat 64 0xfef000 by rfl,BitVec.ofNat_add_ofNat]
    apply accessValid_ofNat <;> omega

/-- A selected sorted triple dispatches to exactly its five-block native plan. -/
theorem dispatch_typed (c bucket x y z : Nat) (s : MachineState)
    (hc : c<7) (hx : x<128) (hy : y<128) (hz : z<128) (hxy : x<y) (hyz : y<z)
    (ht : TablesOK s) (hk : KnownOK (dispatchKnown c) s)
    (hpc : s.pc=pcOf (banks[c]!))
    (h0 : (ptrE c 0).eval s=BitVec.ofNat 64 (pointer bucket x))
    (h1 : (ptrE c 1).eval s=BitVec.ofNat 64 (pointer bucket y))
    (h2 : (ptrE c 2).eval s=BitVec.ofNat 64 (pointer bucket z)) :
    ∃ t, SpecResC [] [] [] (dispatchSpec c) (dispatchKnown c) dispatchKeep s t ∧
      t.pc=pcOf (plan (geomIndex (lcaLevel x y) (lcaLevel y z)) 0).start ∧
      t.getReg .x16=BitVec.ofNat 64 (pointer bucket x) ∧
      t.getReg .x17=BitVec.ofNat 64 (pointer bucket y) ∧
      t.getReg .x18=BitVec.ofNat 64 (pointer bucket z) := by
  have hp01 := lcaLevel_pos x y
  have hp12 := lcaLevel_pos y z
  have hne := lca_ne hxy hyz
  have hA := geometry_height ⟨x ^^^ y,Nat.xor_lt_two_pow (n:=7) hx hy⟩
  have hB := geometry_height ⟨y ^^^ z,Nat.xor_lt_two_pow (n:=7) hy hz⟩
  rw [bitLength_lca x y (by omega)] at hA
  rw [bitLength_lca y z (by omega)] at hB
  have htarget := targetE_eval s c bucket x y z ht hx hy hz h0 h1 h2
  rw [bitLength_lca x y (by omega),bitLength_lca y z (by omega),
    jump_start _ _ ⟨hp01,hA⟩ ⟨hp12,hB⟩ hne] at htarget
  obtain ⟨t,hr⟩ := spec_runC (dispatch_checked ⟨c,hc⟩) s hpc hk
    (by simp [dispatchSpec]) (dispatch_access s c bucket x y z ht hx hy hz h0 h1 h2)
  refine ⟨t,hr,?_,?_,?_,?_⟩
  · rw [hr.spc _ rfl]
    change (targetE c).eval s &&& ~~~(1#64)=_
    rw [htarget]
    exact even_andNot1 _ (by omega)
  · exact (hr.regs (.x16,ptrE c 0) (by simp [dispatchSpec])).trans h0
  · exact (hr.regs (.x17,ptrE c 1) (by simp [dispatchSpec])).trans h1
  · exact (hr.regs (.x18,ptrE c 2) (by simp [dispatchSpec])).trans h2

#print axioms dispatch_typed
end SigGolfCandidate.T3M.CanonicalNative
