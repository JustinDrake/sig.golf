import SigGolfCandidate.T3M.Verify.CanonicalBankSource
import SigGolfCandidate.T3M.Verify.CanonicalBankExact
import SigGolfCandidate.T3M.Verify.CanonicalCaller
import SigGolfCandidate.T3M.Witness.CanonicalNormalizedSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def geomOf (F : FCtx) (c : Nat) : Nat :=
  geomIndex (lcaLevel ((F.sel c).leaves.getD 0 0) ((F.sel c).leaves.getD 1 0))
    (lcaLevel ((F.sel c).leaves.getD 1 0) ((F.sel c).leaves.getD 2 0))

theorem geometry_context (F : FCtx) (c : Nat) (hs : SelOk (F.sel c)) :
    geomOf F c<42 ∧
      geomOf F c=geomIndex (lcaLevel (F.g (3*c)) (F.g (3*c+1)))
        (lcaLevel (F.g (3*c+1)) (F.g (3*c+2))) := by
  have h01 := hs.s01
  have h12 := hs.s12
  have h2l := hs.l2
  have h0 : F.g (3*c)=selLeaf (F.sel c) 0 := by simpa using global_slot F c 0 (by omega)
  have h1 := global_slot F c 1 (by omega)
  have h2 := global_slot F c 2 (by omega)
  have hx : lcaLevel ((F.sel c).leaves.getD 0 0) ((F.sel c).leaves.getD 1 0)<8 := by
    have hh := geometry_height
      ⟨((F.sel c).leaves.getD 0 0) ^^^ ((F.sel c).leaves.getD 1 0),
        Nat.xor_lt_two_pow (n:=7) (by omega) (by omega)⟩
    rw [bitLength_lca ((F.sel c).leaves.getD 0 0) ((F.sel c).leaves.getD 1 0) (by omega)] at hh
    exact hh
  have hy : lcaLevel ((F.sel c).leaves.getD 1 0) ((F.sel c).leaves.getD 2 0)<8 := by
    have hh := geometry_height
      ⟨((F.sel c).leaves.getD 1 0) ^^^ ((F.sel c).leaves.getD 2 0),
        Nat.xor_lt_two_pow (n:=7) (by omega) hs.l2⟩
    rw [bitLength_lca ((F.sel c).leaves.getD 1 0) ((F.sel c).leaves.getD 2 0) (by omega)] at hh
    exact hh
  constructor
  · exact (plan_shape ⟨_,hx⟩ ⟨_,hy⟩ (lcaLevel_pos _ _) (lcaLevel_pos _ _)
      (by intro h; exact lca_ne h01 h12 (congrArg Fin.val h))).1
  · rw [h0,h1,h2]
    unfold geomOf selLeaf
    rw [lca_bucket (by omega) (by omega) (by omega),lca_bucket (by omega) hs.l2 (by omega)]

theorem native_bank_source (F : FCtx) (c : Nat) (hs : SelOk (F.sel c)) (ptr : Nat) :
    bankProgram F c (geomOf F c) 0 5 ptr [] 0 0=
      CanonicalSchedule.coordProgram F.w F.idx c (F.sel c) ptr := by
  rw [(geometry_context F c hs).2]
  exact bank_program_source F c ptr hs

theorem normalized_native_bank (F : FCtx) (c : Nat)
    (hc : ChosenOk (T3.selections F.a)) (hc7 : c<7) :
    ftsCoordP (CanonicalAdapter.normalize (T3.selections F.a) F.w) F.idx c (F.sel c)
      (segPtr (schedule (T3.selections F.a)) (5*c))=
      some <$> bankProgram F c (geomOf F c) 0 5
        (segPtr (schedule (T3.selections F.a)) (5*c)) [] 0 0 := by
  have h := CanonicalSchedule.normalized_coord_exact (T3.selections F.a) F.w F.idx c hc hc7
  change ftsCoordP _ _ _ (F.sel c) _=some <$> CanonicalSchedule.coordProgram _ _ _ (F.sel c) _ at h
  rw [native_bank_source F c (hc c hc7)]
  exact h

theorem dispatched_bank_good (F : FCtx) (c ptr : Nat) (roots : List Digest) (s : MachineState)
    (hc : c<7) (hrlen : roots.length=c) (hs : BankEntry F c ptr roots s)
    (hsel : SelOk (F.sel c)) (hp : 1088 ≤ ptr) (hpx : ptr+4440 ≤ 32168) (hp8 : ptr%8=0)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs) (B A : Nat) (Q : Prop)
    (hK : ∀ node u, BankReturned F c (bankEndPtr (geomOf F c) 0 5 ptr) roots node u →
      GQ u B B Q A (R (node,bankEndPtr (geomOf F c) 0 5 ptr))) :
    GQ s (B+14+bankCost (geomOf F c) 0 5) (B+14+bankCost (geomOf F c) 0 5) Q
      (A+14+bankCost (geomOf F c) 0 5)
      (CanonicalPort.Verify.ccM (bankProgram F c (geomOf F c) 0 5 ptr [] 0 0) R) := by
  have h01 := hsel.s01
  have h12 := hsel.s12
  have h2l := hsel.l2
  obtain ⟨t,hsteps,hstate,hroots⟩ := dispatch_entry F c ptr roots s hc hs (F.sel c).bucket
    ((F.sel c).leaves.getD 0 0) ((F.sel c).leaves.getD 1 0) ((F.sel c).leaves.getD 2 0)
    (by omega) (by omega) hsel.l2 hsel.s01 hsel.s12
    (by simpa [selLeaf,Nat.mul_comm] using global_slot F c 0 (by omega))
    (by simpa [selLeaf,Nat.mul_comm] using global_slot F c 1 (by omega))
    (by simpa [selLeaf,Nat.mul_comm] using global_slot F c 2 (by omega))
  have h := bank_body_return_good_exact F c (geomOf F c) ptr roots t hc
    (geometry_context F c hsel).1 hrlen hp hpx hp8 hstate hroots R B A Q hK
  apply CanonicalPort.Verify.GoodQ.steps' hsteps h <;> first | omega | (intro hQ; exact ⟨hQ,by omega⟩)

#print axioms normalized_native_bank
#print axioms dispatched_bank_good
end SigGolfCandidate.T3M.CanonicalNative
