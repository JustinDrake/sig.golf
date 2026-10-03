import SigGolfCandidate.T3M.Verify.CanonicalBank

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

structure BankReturned (F : FCtx) (c ptr : Nat) (roots : List Digest) (node : Digest)
    (s : MachineState) : Prop where
  pc : s.pc=pcOf (banks[c]!+13)
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  known : KnownOK (bankK F c) s
  common : Common F s
  orig : WitF F.w ptr s
  root : DigAt s (forestSlot c) node
  roots : RootsOK (roots++[node]) s

theorem bank_return (F : FCtx) (c g ptr : Nat) (roots : List Digest) (node : Digest)
    (s : MachineState) (hg : g<42) (hs : BankEnd F c g ptr roots node s) :
    ∃ t, Steps fixture s 1 1 t ∧ BankReturned F c ptr roots node t := by
  obtain ⟨t,hr⟩ := return_run g hg s hs.pc
  have hm : ∀ A, t.getMem A=s.getMem A := by intro A; rw [hr.mem]; rfl
  have hk : KnownOK (bankK F c) t := by
    intro p hp
    rw [hr.keep p.1 (by
      simp only [bankK,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [allKeep])]
    exact hs.known p hp
  refine ⟨t,hr.steps,⟨?_,?_,hk,hs.common.control hr rfl,?_,?_,?_⟩⟩
  · rw [hr.spc _ rfl]
    change s.getReg .x1 &&& ~~~(1#64)=_
    rw [hs.known (.x1,pcOf (banks[c]!+13)) (by simp [bankK])]
    exact even_andNot1 _ (by omega)
  · rw [hr.keep .x14 (by simp [allKeep])]; exact hs.pointer
  · intro o ho; rw [hm]; exact hs.orig o ho
  · exact ⟨(hm _).trans hs.root.1,(hm _).trans hs.root.2⟩
  · intro k hk'; exact ⟨(hm _).trans (hs.roots k hk').1,(hm _).trans (hs.roots k hk').2⟩

theorem bank_body_return_good (F : FCtx) (c g ptr : Nat) (roots : List Digest)
    (s : MachineState) (hc : c<7) (hg : g<42) (hrlen : roots.length=c)
    (hp : 1088 ≤ ptr) (hpx : ptr+4440 ≤ 32168) (hp8 : ptr%8=0)
    (hs : BankAt F c g 0 ptr [] 0 0 s) (hroots : RootsOK roots s)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs) (B A : Nat) (Q : Prop)
    (hK : ∀ node ptr u, BankReturned F c ptr roots node u → GQ u B B Q A (R (node,ptr))) :
    GQ s (B+bankCost g 0 5+1) (B+bankCost g 0 5+1) Q (A+bankCost g 0 5+1)
      (CanonicalPort.Verify.ccM (bankProgram F c g 0 5 ptr [] 0 0) R) := by
  have h := bank_suffix_good F c g roots hc hg hrlen R (B+1) (A+1) Q
    (fun node ptr u hu => by
      obtain ⟨v,hsteps,hv⟩ := bank_return F c g ptr roots node u hg hu
      exact CanonicalPort.Verify.GoodQ.steps hsteps (hK node ptr v hv))
    5 0 ptr [] 0 0 s (by omega) (by omega) hp (by omega) hp8 hs hroots
  convert h using 1 <;> omega

#print axioms bank_body_return_good
end SigGolfCandidate.T3M.CanonicalNative
