import SigGolfCandidate.T3M.Verify.CanonicalBankBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify

theorem bank_end_geometry (x y ptr : Nat) (hx : 0<x ∧ x<8) (hy : 0<y ∧ y<8) (hne : x≠y) :
    bankEndPtr (geomIndex x y) 0 5 ptr=ptr+40+80*(SideCost.bankShape x y).sum := by
  rw [bank_end_ptr_sum,show List.range' 0 5=List.range 5 by decide,
    plan_folds ⟨x,hx.2⟩ ⟨y,hy.2⟩ hx.1 hy.1 (by intro h; exact hne (congrArg Fin.val h))]

theorem coord_end_shape (coord : Nat) (sel : Selection) (ptr : Nat) :
    segsEnd ptr (coordSchedule coord sel)=ptr+40+80*
      (SideCost.bankShape (lcaLevel (selLeaf sel 0) (selLeaf sel 1))
        (lcaLevel (selLeaf sel 1) (selLeaf sel 2))).sum := by
  unfold coordSchedule SideCost.bankShape
  dsimp only
  split_ifs <;> simp only [segsEnd,segNext,List.sum_cons,List.sum_nil] <;> omega

theorem bank_end_schedule (F : FCtx) (c ptr : Nat) (hs : SelOk (F.sel c)) :
    bankEndPtr (geomOf F c) 0 5 ptr=segsEnd ptr (coordSchedule c (F.sel c)) := by
  have h01 := hs.s01
  have h12 := hs.s12
  have h2l := hs.l2
  have h0 : F.g (3*c)=selLeaf (F.sel c) 0 := by simpa using global_slot F c 0 (by omega)
  have h1 := global_slot F c 1 (by omega)
  have h2 := global_slot F c 2 (by omega)
  have hx : 0<lcaLevel (F.g (3*c)) (F.g (3*c+1)) ∧ lcaLevel (F.g (3*c)) (F.g (3*c+1))<8 := by
    refine ⟨lcaLevel_pos _ _,?_⟩
    rw [h0,h1]; unfold selLeaf
    exact Nat.lt_succ_of_le (lca_le_eight (by omega) (by omega) (by omega))
  have hy : 0<lcaLevel (F.g (3*c+1)) (F.g (3*c+2)) ∧ lcaLevel (F.g (3*c+1)) (F.g (3*c+2))<8 := by
    refine ⟨lcaLevel_pos _ _,?_⟩
    rw [h1,h2]; unfold selLeaf
    exact Nat.lt_succ_of_le (lca_le_eight (by omega) hs.l2 (by omega))
  have hne : lcaLevel (F.g (3*c)) (F.g (3*c+1))≠lcaLevel (F.g (3*c+1)) (F.g (3*c+2)) := by
    apply lca_ne <;> first | (rw [h0,h1]; unfold selLeaf; omega) | (rw [h1,h2]; unfold selLeaf; omega)
  rw [(geometry_context F c hs).2,bank_end_geometry _ _ ptr hx hy hne,coord_end_shape,h0,h1,h2]

theorem bank_end_schedule_global (F : FCtx) (hc : ChosenOk (T3.selections F.a)) (c : Nat) (hc7 : c<7) :
    bankEndPtr (geomOf F c) 0 5 (segPtr (schedule (T3.selections F.a)) (5*c))=
      segPtr (schedule (T3.selections F.a)) (5*(c+1)) := by
  rw [bank_end_schedule F c _ (hc c hc7)]
  have hp := (hdrsOk_of_getD F.w (coordSchedule c (F.sel c))
    (fun i => segPtr (schedule (T3.selections F.a)) (5*c+i))
    (coord_ptrs (T3.selections F.a) hc7)).2
  simpa only [Nat.add_zero,coordSchedule_length,show 5*c+5=5*(c+1) by omega] using hp

theorem bank_program_ptr (F : FCtx) (c g : Nat) : ∀ n j ptr nodes node heap r,
    r∈support (bankProgram F c g j n ptr nodes node heap) → r.2=bankEndPtr g j n ptr := by
  intro n
  induction n with
  | zero => intro j ptr nodes node heap r hr; simp [bankProgram] at hr; subst r; rfl
  | succ n ih =>
    intro j ptr nodes node heap r hr
    simp only [bankProgram,mem_support_bind_iff] at hr
    obtain ⟨p,hp,hr⟩ := hr
    exact ih _ _ _ _ _ r hr

#print axioms bank_end_schedule_global
end SigGolfCandidate.T3M.CanonicalNative
