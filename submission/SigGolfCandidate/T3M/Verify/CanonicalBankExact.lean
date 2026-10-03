import SigGolfCandidate.T3M.Verify.CanonicalBankReturn

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def bankEndPtr (g : Nat) : Nat → Nat → Nat → Nat
  | _,0,ptr => ptr
  | j,n+1,ptr => bankEndPtr g (j+1) n (ptr+8+80*(plan g j).folds)

theorem bank_suffix_good_exact (F : FCtx) (c g : Nat) (roots : List Digest)
    (hc : c<7) (hg : g<42) (hrlen : roots.length=c)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop) :
    ∀ n j ptr nodes node heap s, j+n=5 → 0<n → 1088 ≤ ptr →
      ptr+888*n ≤ 32168 → ptr%8=0 →
      BankAt F c g j ptr nodes node heap s → RootsOK roots s →
      (∀ node u, BankEnd F c g (bankEndPtr g j n ptr) roots node u →
        GQ u B B Q A (R (node,bankEndPtr g j n ptr))) →
      GQ s (B+bankCost g j n) (B+bankCost g j n) Q (A+bankCost g j n)
        (CanonicalPort.Verify.ccM (bankProgram F c g j n ptr nodes node heap) R) := by
  intro n
  induction n with
  | zero => intro j ptr nodes node heap s he hn; omega
  | succ n ih =>
    intro j ptr nodes node heap s heq hn hp hpx hp8 hstate hroots hK
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
          simpa only [rk,bankProgram,CanonicalPort.Verify.ccM_pure,bankCost,bankEndPtr,Nat.add_zero]
            using hK nextNode t (by simpa [bankEndPtr] using hfinal)
        · have hj4 : j<4 := by omega
          have hnext := hstate.next hend hpc hcom hfm hhe hc hg hj4 hp
          exact ih (j+1) (ptr+8+80*(plan g j).folds) _ nextNode nextHeap t (by omega)
            (by omega) (by omega) (by omega) (by omega) hnext hrt (by simpa only [bankEndPtr] using hK))
    simp only [bankProgram,CanonicalPort.Verify.ccM_bind]
    simp only [CanonicalPort.Verify.ccM_bind] at hs
    dsimp only [rk] at hs
    convert hs using 1 <;> simp only [bankCost,segCost] <;> omega


theorem bank_body_return_good_exact (F : FCtx) (c g ptr : Nat) (roots : List Digest)
    (s : MachineState) (hc : c<7) (hg : g<42) (hrlen : roots.length=c)
    (hp : 1088 ≤ ptr) (hpx : ptr+4440 ≤ 32168) (hp8 : ptr%8=0)
    (hs : BankAt F c g 0 ptr [] 0 0 s) (hroots : RootsOK roots s)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs) (B A : Nat) (Q : Prop)
    (hK : ∀ node u, BankReturned F c (bankEndPtr g 0 5 ptr) roots node u →
      GQ u B B Q A (R (node,bankEndPtr g 0 5 ptr))) :
    GQ s (B+bankCost g 0 5+1) (B+bankCost g 0 5+1) Q (A+bankCost g 0 5+1)
      (CanonicalPort.Verify.ccM (bankProgram F c g 0 5 ptr [] 0 0) R) := by
  have h := bank_suffix_good_exact F c g roots hc hg hrlen R (B+1) (A+1) Q
    5 0 ptr [] 0 0 s (by omega) (by omega) hp (by omega) hp8 hs hroots
    (fun node u hu => by
      obtain ⟨v,hsteps,hv⟩ := bank_return F c g (bankEndPtr g 0 5 ptr) roots node u hg hu
      exact CanonicalPort.Verify.GoodQ.steps hsteps (hK node v hv))
  convert h using 1 <;> omega

theorem bank_end_ptr_sum (g : Nat) : ∀ n j ptr,
    bankEndPtr g j n ptr=ptr+8*n+80*((List.range' j n).map fun k => (plan g k).folds).sum := by
  intro n
  induction n with
  | zero => intro j ptr; simp [bankEndPtr]
  | succ n ih => intro j ptr; simp only [bankEndPtr,ih,List.range'_succ,List.map_cons,List.sum_cons]; omega

#print axioms bank_body_return_good_exact
end SigGolfCandidate.T3M.CanonicalNative
