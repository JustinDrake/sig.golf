import SigGolfCandidate.T3M.Verify.CanonicalBank
import SigGolfCandidate.T3M.Witness.CanonicalScheduleRun
import SigGolfCandidate.T3M.Witness.CanonicalGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify

def runOutlines (F : FCtx) (c : Nat) : List (Option Nat × Nat × Nat × Nat) →
    Nat → List Digest → Digest → Nat → T3.M (Digest × Nat)
  | [],ptr,_,node,_ => pure (node,ptr)
  | q::rest,ptr,nodes,node,heap =>
    let p : BlockPlan := ⟨q.1,q.2.1,q.2.2.1,q.2.2.2,0,#[],#[]⟩
    (pendingHash F.w F.idx c node (bankPend F c p nodes heap) >>= fun v =>
      foldsP F.w F.idx c ptr p.folds v (pendHeap (bankPend F c p nodes heap))) >>= fun r =>
      runOutlines F c rest (ptr+8+80*p.folds) (nextNodes p nodes r.1) r.1 r.2

theorem bankProgram_outlines (F : FCtx) (c g : Nat) :
    ∀ n j ptr nodes node heap,
    bankProgram F c g j n ptr nodes node heap=
      runOutlines F c ((List.range' j n).map fun k => outline (plan g k)) ptr nodes node heap := by
  intro n
  induction n with
  | zero => intro j ptr nodes node heap; rfl
  | succ n ih =>
    intro j ptr nodes node heap
    simp only [List.range'_succ,List.map_cons,bankProgram,runOutlines,outline,
      bankPend,nextNodes]
    apply bind_congr
    intro p
    exact ih _ _ _ _ _

theorem plan_outline_list : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x≠y →
    ((List.range' 0 5).map fun k => outline (plan (geomIndex x.val y.val) k))=
      expectedOutline x.val y.val := by decide +kernel

theorem global_slot (F : FCtx) (c k : Nat) (hk : k<3) :
    F.g (3*c+k)=selLeaf (F.sel c) k := by
  simp only [FCtx.g,show (3*c+k)/3=c by omega,show (3*c+k)%3=k by omega]

theorem outlines_source (F : FCtx) (c ptr : Nat)
    (hb : (F.sel c).bucket<16) (h2 : (F.sel c).leaves.getD 2 0<128)
    (h01 : (F.sel c).leaves.getD 0 0<(F.sel c).leaves.getD 1 0)
    (h12 : (F.sel c).leaves.getD 1 0<(F.sel c).leaves.getD 2 0) :
    runOutlines F c
      (expectedOutline (lcaLevel (F.g (3*c)) (F.g (3*c+1)))
        (lcaLevel (F.g (3*c+1)) (F.g (3*c+2)))) ptr [] 0 0=
      CanonicalSchedule.coordProgram F.w F.idx c (F.sel c) ptr := by
  have g0 : F.g (3*c)=selLeaf (F.sel c) 0 := by simpa using global_slot F c 0 (by omega)
  have g1 := global_slot F c 1 (by omega)
  have g2 := global_slot F c 2 (by omega)
  have g01 : F.g (3*c)<F.g (3*c+1) := by rw [g0,g1]; unfold selLeaf; omega
  have g12 : F.g (3*c+1)<F.g (3*c+2) := by rw [g1,g2]; unfold selLeaf; omega
  have px := lcaLevel_pos (F.g (3*c)) (F.g (3*c+1))
  have py := lcaLevel_pos (F.g (3*c+1)) (F.g (3*c+2))
  have lx : lcaLevel (F.g (3*c)) (F.g (3*c+1)) ≤ 7 := by
    apply (div_eq_iff_lca (by omega) 7).mp
    rw [g0,g1]; unfold selLeaf
    rw [bucket_div_eight (by omega),bucket_div_eight (by omega)]
  have ly : lcaLevel (F.g (3*c+1)) (F.g (3*c+2)) ≤ 7 := by
    apply (div_eq_iff_lca (by omega) 7).mp
    rw [g1,g2]; unfold selLeaf
    rw [bucket_div_eight (by omega),bucket_div_eight (by omega)]
  have hne := lca_ne g01 g12
  unfold CanonicalSchedule.coordProgram
  rw [← g0,← g1,← g2]
  dsimp only
  generalize hx : lcaLevel (F.g (3*c)) (F.g (3*c+1))=x at *
  generalize hy : lcaLevel (F.g (3*c+1)) (F.g (3*c+2))=y at *
  by_cases hxy : x<y
  · simp only [expectedOutline,if_pos hxy,runOutlines,bankPend,nextNodes,
      pendHeap,CanonicalSchedule.segmentDigestP,bind_assoc,pure_bind,List.take_nil,
      List.nil_append,List.take_zero,List.take_succ_cons,List.cons_append,List.getD_cons_zero,
      List.getD_nil,segNext,if_true,if_false,show (0:Nat)≠1 by decide,show (2:Nat)≠1 by decide]
    apply bind_congr; intro v0
    apply bind_congr_of_forall_mem_support; intro r0 hr0
    apply bind_congr; intro v1
    apply bind_congr_of_forall_mem_support; intro r1 hr1
    rw [foldsP_support F.w F.idx c _ (x-1) v1 (2048+F.g (3*c+1)) r1 hr1]
    have hxdiv : (2048+F.g (3*c+1))/2^(x-1)/2=(2048+F.g (3*c+1))/2^x := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hxdiv]
    apply bind_congr; intro v2
    apply bind_congr_of_forall_mem_support; intro r2 hr2
    apply bind_congr; intro v3
    apply bind_congr_of_forall_mem_support; intro r3 hr3
    rw [foldsP_support F.w F.idx c _ (y-1) v3 (2048+F.g (3*c+2)) r3 hr3]
    have hydiv : (2048+F.g (3*c+2))/2^(y-1)/2=(2048+F.g (3*c+2))/2^y := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hydiv]
  · simp only [expectedOutline,if_neg hxy,runOutlines,bankPend,nextNodes,
      pendHeap,CanonicalSchedule.segmentDigestP,bind_assoc,pure_bind,List.take_nil,
      List.nil_append,List.take_zero,List.take_succ_cons,List.cons_append,List.getD_cons_zero,
      List.getD_cons_succ,List.getD_nil,segNext,if_true,if_false,
      show (0:Nat)≠1 by decide,show (2:Nat)≠1 by decide]
    apply bind_congr; intro v0
    apply bind_congr_of_forall_mem_support; intro r0 hr0
    apply bind_congr; intro v1
    apply bind_congr_of_forall_mem_support; intro r1 hr1
    apply bind_congr; intro v2
    apply bind_congr_of_forall_mem_support; intro r2 hr2
    rw [foldsP_support F.w F.idx c _ (y-1) v2 (2048+F.g (3*c+2)) r2 hr2]
    have hydiv : (2048+F.g (3*c+2))/2^(y-1)/2=(2048+F.g (3*c+2))/2^y := by
      rw [Nat.div_div_eq_div_mul,← pow_succ]; congr 2; omega
    rw [hydiv]
    apply bind_congr; intro v3
    apply bind_congr_of_forall_mem_support; intro r3 hr3
    rw [foldsP_support F.w F.idx c _ (x-1-y) v3 ((2048+F.g (3*c+2))/2^y) r3 hr3]
    have hxdiv : (2048+F.g (3*c+2))/2^y/2^(x-1-y)/2=(2048+F.g (3*c+2))/2^x := by
      have hmid : (2048+F.g (3*c+2))/2^y/2^(x-1-y)=(2048+F.g (3*c+2))/2^(x-1) := by
        rw [Nat.div_div_eq_div_mul,← pow_add]; congr 2; omega
      rw [hmid,Nat.div_div_eq_div_mul,← pow_succ]
      congr 2; omega
    rw [hxdiv]

theorem bank_program_source (F : FCtx) (c ptr : Nat) (hs : SelOk (F.sel c)) :
    bankProgram F c
      (geomIndex (lcaLevel (F.g (3*c)) (F.g (3*c+1)))
        (lcaLevel (F.g (3*c+1)) (F.g (3*c+2)))) 0 5 ptr [] 0 0=
      CanonicalSchedule.coordProgram F.w F.idx c (F.sel c) ptr := by
  have h01 := hs.s01
  have h12 := hs.s12
  have h2l := hs.l2
  have h0 : F.g (3*c)=selLeaf (F.sel c) 0 := by simpa using global_slot F c 0 (by omega)
  have h1 := global_slot F c 1 (by omega)
  have h2 := global_slot F c 2 (by omega)
  have hx : lcaLevel (F.g (3*c)) (F.g (3*c+1))<8 := by
    rw [h0,h1]; unfold selLeaf
    exact Nat.lt_succ_of_le (lca_le_eight (by omega) (by omega) (by have := hs.s01; omega))
  have hy : lcaLevel (F.g (3*c+1)) (F.g (3*c+2))<8 := by
    rw [h1,h2]; unfold selLeaf
    exact Nat.lt_succ_of_le (lca_le_eight (by omega) hs.l2 (by have := hs.s12; omega))
  rw [bankProgram_outlines,plan_outline_list ⟨_,hx⟩ ⟨_,hy⟩
    (lcaLevel_pos _ _) (lcaLevel_pos _ _)
    (by intro h; have hg01 : F.g (3*c)<F.g (3*c+1) := by rw [h0,h1]; unfold selLeaf; have := hs.s01; omega
        have hg12 : F.g (3*c+1)<F.g (3*c+2) := by rw [h1,h2]; unfold selLeaf; have := hs.s12; omega
        exact lca_ne hg01 hg12 (congrArg Fin.val h))]
  exact outlines_source F c ptr hs.b hs.l2 hs.s01 hs.s12

#print axioms outlines_source
#print axioms bank_program_source
end SigGolfCandidate.T3M.CanonicalNative
