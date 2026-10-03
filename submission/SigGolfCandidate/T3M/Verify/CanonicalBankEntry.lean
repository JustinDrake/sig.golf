import SigGolfCandidate.T3M.Verify.CanonicalBankReturn
import SigGolfCandidate.T3M.Verify.CanonicalDispatchTyped

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def entryK (F : FCtx) (c : Nat) : List (Reg × Word) :=
  (bankK F c).filter fun p => p.1≠.x1 ∧ p.1≠.x16 ∧ p.1≠.x17 ∧ p.1≠.x18

structure BankEntry (F : FCtx) (c ptr : Nat) (roots : List Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf banks[c]!
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  known : KnownOK (entryK F c) s
  common : Common F s
  orig : WitF F.w ptr s
  roots : RootsOK roots s

theorem entry_dispatch_known {F c ptr roots s} (h : BankEntry F c ptr roots s) :
    KnownOK (dispatchKnown c) s := by
  intro p hp
  simp only [dispatchKnown,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl <;> apply h.known <;> simp [entryK,bankK,ETAB]

theorem dispatch_entry (F : FCtx) (c ptr : Nat) (roots : List Digest) (s : MachineState)
    (hc : c<7) (hs : BankEntry F c ptr roots s)
    (bucket x y z : Nat) (hx : x<128) (hy : y<128) (hz : z<128) (hxy : x<y) (hyz : y<z)
    (hG0 : F.g (3*c)=128*bucket+x) (hG1 : F.g (3*c+1)=128*bucket+y)
    (hG2 : F.g (3*c+2)=128*bucket+z) :
    ∃ t, Steps fixture s 13 13 t ∧
      BankAt F c (geomIndex (lcaLevel x y) (lcaLevel y z)) 0 ptr [] 0 0 t ∧ RootsOK roots t := by
  have he : ∀ j, j<3 → (ptrE c j).eval s=BitVec.ofNat 64 (TAB+8*F.g (3*c+j)) := by
    intro j hj
    change s.getMem (BitVec.ofNat 64 (0x140+24*c+8*j))=_
    rw [show 0x140+24*c+8*j=ETAB+8*(3*c+j) by unfold ETAB; omega]
    exact hs.common.etab (3*c+j) (by omega)
  obtain ⟨t,hr,hpc,h16,h17,h18⟩ := dispatch_typed c bucket x y z s hc hx hy hz hxy hyz
    hs.common.tables (entry_dispatch_known hs) hs.pc
    (by simpa [hG0,CanonicalGeometry.pointer,TAB] using he 0 (by omega))
    (by simpa [hG1,CanonicalGeometry.pointer,TAB] using he 1 (by omega))
    (by simpa [hG2,CanonicalGeometry.pointer,TAB] using he 2 (by omega))
  have hmem : ∀ A, t.getMem A=s.getMem A := by intro A; rw [hr.mem]; rfl
  have hpres : ∀ r v, (r,v)∈entryK F c → r∈dispatchKeep → t.getReg r=v := by
    intro r v hp hk
    exact (hr.keep r hk).trans (hs.known (r,v) hp)
  have hk : KnownOK (bankK F c) t := by
    intro p hp
    simp only [bankK,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr.regs (.x1,cw (pcOf (banks[c]!+13))) (by simp [dispatchSpec,cw,pcOf])
    · exact hpres .x2 0x1000000 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x5 0 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x8 3 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x9 4 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x13 5 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x11 64 (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x19 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hr.known (.x20,0xfef000) (by simp [dispatchKnown])
    · exact hr.known (.x21,0xfef400) (by simp [dispatchKnown])
    · exact hpres .x22 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hr.known (.x24,BitVec.ofNat 64 (ETAB+24*c)) (by simp [dispatchKnown,ETAB])
    · exact hpres .x25 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x27 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x28 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x29 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · exact hpres .x31 _ (by simp [entryK,bankK]) (by simp [dispatchKeep])
    · simpa [hG0,CanonicalGeometry.pointer,TAB] using h16
    · simpa [hG1,CanonicalGeometry.pointer,TAB] using h17
    · simpa [hG2,CanonicalGeometry.pointer,TAB] using h18
  have hcom : Common F t := hs.common.transport (fun A _ => hmem _)
  have hxl := geometry_height ⟨x ^^^ y,Nat.xor_lt_two_pow (n:=7) hx hy⟩
  have hyl := geometry_height ⟨y ^^^ z,Nat.xor_lt_two_pow (n:=7) hy hz⟩
  rw [bitLength_lca x y (by omega)] at hxl
  rw [bitLength_lca y z (by omega)] at hyl
  have hshape := plan_shape
    ⟨lcaLevel x y,hxl⟩ ⟨lcaLevel y z,hyl⟩
    (lcaLevel_pos _ _) (lcaLevel_pos _ _) (by intro h; exact lca_ne hxy hyz (congrArg Fin.val h))
  have hl := plan_links ⟨_,hshape.1⟩ ⟨0,by decide⟩
  dsimp only at hl
  refine ⟨t,hr.steps,⟨hpc,?_,hk,hcom,?_,?_,?_,?_,by omega,?_⟩,?_⟩
  · rw [hr.keep .x14 (by simp [dispatchKeep])]; exact hs.pointer
  · intro k hk'; simp at hk'
  · simp [inDepth,(hl.2.2.1 rfl).1,(hl.2.2.1 rfl).2]
  · intro hnone; rw [(hl.2.2.1 rfl).1] at hnone; cases hnone
  · intro hnone; rw [(hl.2.2.1 rfl).1] at hnone; cases hnone
  · intro o ho; rw [hmem]; exact hs.orig o ho
  · intro k hk'; exact ⟨(hmem _).trans (hs.roots k hk').1,(hmem _).trans (hs.roots k hk').2⟩

#print axioms dispatch_entry
end SigGolfCandidate.T3M.CanonicalNative
