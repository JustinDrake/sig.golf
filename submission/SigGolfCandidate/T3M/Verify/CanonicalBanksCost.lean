import SigGolfCandidate.T3M.Verify.CanonicalBanksSource
import SigGolfCandidate.T3M.Verify.CanonicalNativeCost

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.T3M.Verify

def nativeShape (g : Nat) : List Nat := (List.range' 0 5).map fun j => (plan g j).folds
def nativeShapes (F : FCtx) (c n : Nat) : List (List Nat) :=
  (List.range' c n).map fun k => nativeShape (geomOf F k)

theorem all_bank_model : ∀ g : Fin 42,
    14+bankCost g.val 0 5+4=CanonicalCost.bankCost (nativeShape g.val) := by decide +kernel
theorem all_bank_model_cap : ∀ g : Fin 42,
    CanonicalCost.bankCost (nativeShape g.val) ≤ CanonicalCost.cap (nativeShape g.val).sum :=
  by decide +kernel

theorem banks_end_sum (F : FCtx) : ∀ n c ptr,
    banksEndPtr F c n ptr=ptr+40*n+80*((nativeShapes F c n).map List.sum).sum := by
  intro n
  induction n with
  | zero => intro c ptr; simp [banksEndPtr,nativeShapes]
  | succ n ih =>
    intro c ptr
    rw [banksEndPtr,ih,bank_end_ptr_sum]
    simp only [nativeShapes,List.range'_succ,List.map_cons,List.sum_cons,nativeShape]
    omega

theorem banks_cost_sum (F : FCtx) (hc : ChosenOk (T3.selections F.a)) : ∀ n c,
    c+n≤7 → 0<n →
    banksCost F c n+4*n=
      ((nativeShapes F c n).map CanonicalCost.bankCost).sum+5*(n-1) := by
  intro n
  induction n with
  | zero => intro c he hn; omega
  | succ n ih =>
    intro c hcn hn
    have hg := (geometry_context F c (hc c (by omega))).1
    by_cases hz : n=0
    · subst n
      simp only [banksCost,if_pos rfl,nativeShapes,List.range'_succ,List.range'_zero,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      simpa using all_bank_model ⟨geomOf F c,hg⟩
    · have hi := ih (c+1) (by omega) (by omega)
      simp only [nativeShapes] at hi
      simp only [banksCost,if_neg hz,nativeShapes,List.range'_succ,List.map_cons,List.sum_cons]
      have he := all_bank_model ⟨geomOf F c,hg⟩
      dsimp only at he
      omega

theorem banks_accepted_cost (F : FCtx) (hc : ChosenOk (T3.selections F.a))
    (hp : banksEndPtr F 0 7 1088≤10568) : 59+banksCost F 0 7≤2322 := by
  have hend := banks_end_sum F 7 0 1088
  have hcost := banks_cost_sum F hc 7 0 (by omega) (by omega)
  have hfold : ((nativeShapes F 0 7).map List.sum).sum≤115 := by omega
  have hb := CanonicalCost.projected_seven_exact (nativeShapes F 0 7)
    (by simp [nativeShapes]) hfold (by
      intro xs hxs
      obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hxs
      have hclt : c<7 := by simpa using hc'
      have hg := (geometry_context F c (hc c hclt)).1
      have hbounds := all_bank_fold_bounds ⟨geomOf F c,hg⟩
      change 10≤(nativeShape (geomOf F c)).sum ∧ (nativeShape (geomOf F c)).sum≤20 at hbounds
      have hcap := all_bank_model_cap ⟨geomOf F c,hg⟩
      dsimp only at hbounds hcap
      exact ⟨hbounds.1,by have := hbounds.2; omega,hcap⟩)
  omega

#print axioms banks_end_sum
#print axioms banks_accepted_cost
end SigGolfCandidate.T3M.CanonicalNative
