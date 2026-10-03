import SigGolfCandidate.T3M.Verify.CanonicalBankTransition

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def bankProgram (F : FCtx) (c g : Nat) : Nat → Nat → Nat → List Digest → Digest → Nat → T3.M (Digest × Nat)
  | _,0,ptr,_,node,_ => pure (node,ptr)
  | j,n+1,ptr,nodes,node,heap =>
    (pendingHash F.w F.idx c node (bankPend F c (plan g j) nodes heap) >>= fun v =>
      foldsP F.w F.idx c ptr (plan g j).folds v (pendHeap (bankPend F c (plan g j) nodes heap)))
    >>= fun p => bankProgram F c g (j+1) n (ptr+8+80*(plan g j).folds)
      (nextNodes (plan g j) nodes p.1) p.1 p.2

def segCost (p : BlockPlan) : Nat := 14+14*p.folds+tailBudget p
def bankCost (g : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | j,n+1 => segCost (plan g j)+bankCost g (j+1) n

structure BankEnd (F : FCtx) (c g ptr : Nat) (roots : List Digest) (node : Digest)
    (s : MachineState) : Prop where
  pc : s.pc=pcOf returns[g]!
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  known : KnownOK (bankK F c) s
  common : Common F s
  orig : WitF F.w ptr s
  root : DigAt s (forestSlot c) node
  roots : RootsOK (roots++[node]) s

theorem roots_append {roots s node} (h : RootsOK roots s)
    (hn : DigAt s (forestSlot roots.length) node) : RootsOK (roots++[node]) s := by
  intro k hk
  by_cases hkn : k<roots.length
  · rw [List.getD_append roots [node] 0 k hkn]; exact h k hkn
  · have hke : k=roots.length := by simp only [List.length_append,List.length_singleton] at hk; omega
    subst k
    rw [List.getD_append_right roots [node] 0 roots.length (by omega)]
    simpa using hn

theorem bank_suffix_good (F : FCtx) (c g : Nat) (roots : List Digest)
    (hc : c<7) (hg : g<42) (hrlen : roots.length=c)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop)
    (hK : ∀ node ptr u, BankEnd F c g ptr roots node u → GQ u B B Q A (R (node,ptr))) :
    ∀ n j ptr nodes node heap s, j+n=5 → 0<n → 1088 ≤ ptr →
      ptr+888*n ≤ 32168 → ptr%8=0 →
      BankAt F c g j ptr nodes node heap s → RootsOK roots s →
      GQ s (B+bankCost g j n) (B+bankCost g j n) Q (A+bankCost g j n)
        (CanonicalPort.Verify.ccM (bankProgram F c g j n ptr nodes node heap) R) := by
  intro n
  induction n with
  | zero => intro j ptr nodes node heap s he hn; omega
  | succ n ih =>
    intro j ptr nodes node heap s heq hn hp hpx hp8 hstate hroots
    have hj : j<5 := by omega
    have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
    dsimp only at hb
    obtain ⟨hmatch,hpend,hheap,hacc⟩ := hstate.pending hc hg hj
    let rk := fun p : Digest × Nat => CanonicalPort.Verify.ccM
      (bankProgram F c g (j+1) n (ptr+8+80*(plan g j).folds)
        (nextNodes (plan g j) nodes p.1) p.1 p.2) R
    have hs := segment_good F c g j ptr s (bankPend F c (plan g j) nodes heap) node s
      hc hg hj hp (by omega) hp8 hheap hmatch hpend hstate.common (FrameMark.refl _ _ _ _) hacc
      rk (B+bankCost g (j+1) n) (A+bankCost g (j+1) n) Q
      (fun nextNode nextHeap t hend hpc hcom hfm hhe => by
        have hrt := hfm.roots hroots hc hg hj hp hrlen
        by_cases hz : n=0
        · subst n
          have hj4 : j=4 := by omega
          subst j
          have hp4 := (plan_links ⟨g,hg⟩ ⟨4,by decide⟩).2.2.2.2 rfl
          dsimp only at hp4
          have hroot : DigAt t (forestSlot c) nextNode := by
            simpa [destA,hp4.1] using hend.node
          have hfinal : BankEnd F c g (ptr+8+80*(plan g 4).folds) roots nextNode t :=
            ⟨by simpa [nextSegment] using hpc,hend.pointer,hfm.bankKnown hstate.known,hcom,
              hend.orig,hroot,roots_append hrt (by simpa [hrlen] using hroot)⟩
          simpa only [rk,bankProgram,CanonicalPort.Verify.ccM_pure,bankCost,Nat.add_zero]
            using hK nextNode _ t hfinal
        · have hj4 : j<4 := by omega
          have hnext := hstate.next hend hpc hcom hfm hhe hc hg hj4 hp
          exact ih (j+1) (ptr+8+80*(plan g j).folds) _ nextNode nextHeap t (by omega)
            (by omega) (by omega) (by omega) (by omega) hnext hrt)
    simp only [bankProgram,CanonicalPort.Verify.ccM_bind]
    simp only [CanonicalPort.Verify.ccM_bind] at hs
    dsimp only [rk] at hs
    convert hs using 1 <;> simp only [bankCost,segCost] <;> omega

#print axioms bank_suffix_good
end SigGolfCandidate.T3M.CanonicalNative
