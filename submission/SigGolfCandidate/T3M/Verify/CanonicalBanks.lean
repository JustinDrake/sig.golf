import SigGolfCandidate.T3M.Verify.CanonicalBankBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

theorem all_bank_fold_bounds : ∀ g : Fin 42,
    10 ≤ ((List.range' 0 5).map fun j => (plan g.val j).folds).sum ∧
      ((List.range' 0 5).map fun j => (plan g.val j).folds).sum ≤ 20 := by decide +kernel

theorem bank_end_bounds (g ptr : Nat) (hg : g<42) :
    ptr ≤ bankEndPtr g 0 5 ptr ∧ bankEndPtr g 0 5 ptr ≤ ptr+1640 ∧
      bankEndPtr g 0 5 ptr%8=ptr%8 := by
  rw [bank_end_ptr_sum]
  have hb := all_bank_fold_bounds ⟨g,hg⟩
  dsimp only at hb
  constructor
  · omega
  constructor
  · omega
  · simp [Nat.add_mod,Nat.mul_mod]

def banksProgram (F : FCtx) : Nat → Nat → Nat → List Digest → T3.M (List Digest × Nat)
  | _,0,ptr,roots => pure (roots,ptr)
  | c,n+1,ptr,roots => bankProgram F c (geomOf F c) 0 5 ptr [] 0 0 >>= fun r =>
    banksProgram F (c+1) n r.2 (roots++[r.1])
def banksEndPtr (F : FCtx) : Nat → Nat → Nat → Nat
  | _,0,ptr => ptr
  | c,n+1,ptr => banksEndPtr F (c+1) n (bankEndPtr (geomOf F c) 0 5 ptr)
def banksCost (F : FCtx) : Nat → Nat → Nat
  | _,0 => 0
  | c,n+1 => 14+bankCost (geomOf F c) 0 5+
    (if n=0 then 0 else 5+banksCost F (c+1) n)

structure BanksEnd (F : FCtx) (ptr : Nat) (roots : List Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf (banks[6]!+13)
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  known : KnownOK (bankK F 6) s
  common : Common F s
  orig : WitF F.w ptr s
  rootsOk : RootsOK roots s
  len : roots.length=7

theorem banks_good (F : FCtx) (hc : ChosenOk (T3.selections F.a))
    (R : List Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop) :
    ∀ n c ptr roots s, c+n=7 → 0<n → roots.length=c → 1088 ≤ ptr →
      ptr ≤ 1088+1640*c → ptr%8=0 → BankEntry F c ptr roots s →
      (∀ out u, BanksEnd F (banksEndPtr F c n ptr) out u →
        GQ u B B Q A (R (out,banksEndPtr F c n ptr))) →
      GQ s (B+banksCost F c n) (B+banksCost F c n) Q (A+banksCost F c n)
        (CanonicalPort.Verify.ccM (banksProgram F c n ptr roots) R) := by
  intro n
  induction n with
  | zero => intro c ptr roots s he hn; omega
  | succ n ih =>
    intro c ptr roots s he hn hlen hp hpx hp8 hs hK
    have hc7 : c<7 := by omega
    have hsel : SelOk (F.sel c) := hc c hc7
    have hg := (geometry_context F c hsel).1
    have hbounds := bank_end_bounds (geomOf F c) ptr hg
    let ptr1 := bankEndPtr (geomOf F c) 0 5 ptr
    let restCost := if n=0 then 0 else 5+banksCost F (c+1) n
    let rk := fun r : Digest × Nat => CanonicalPort.Verify.ccM
      (banksProgram F (c+1) n r.2 (roots++[r.1])) R
    have h := dispatched_bank_good F c ptr roots s hc7 hlen hs hsel hp (by omega) hp8
      rk (B+restCost) (A+restCost) Q (fun node t ht => by
        by_cases hz : n=0
        · subst n
          have hc6 : c=6 := by omega
          have hout : BanksEnd F ptr1 (roots++[node]) t :=
            ⟨by simpa only [hc6] using ht.pc,ht.pointer,
              by simpa only [hc6] using ht.known,ht.common,ht.orig,ht.roots,by simp [hlen,hc6]⟩
          simpa only [rk,banksProgram,CanonicalPort.Verify.ccM_pure,restCost,if_pos rfl,
            Nat.add_zero,banksEndPtr] using hK (roots++[node]) t hout
        · have hc6 : c<6 := by omega
          obtain ⟨u,hsteps,hu⟩ := caller_entry F c ptr1 roots node t hc6 ht
          have hnext := ih (c+1) ptr1 (roots++[node]) u (by omega) (by omega)
            (by simp [hlen]) (by exact hp.trans hbounds.1) (by dsimp only [ptr1]; omega)
            (by exact hbounds.2.2.trans hp8) hu (by simpa only [banksEndPtr] using hK)
          have hs0 := CanonicalPort.Verify.GoodQ.steps hsteps hnext
          dsimp only [rk,restCost]
          rw [if_neg hz]
          convert hs0 using 1 <;> omega)
    simp only [banksProgram,CanonicalPort.Verify.ccM_bind]
    try simp only [CanonicalPort.Verify.ccM_bind] at h
    dsimp only [rk] at h
    convert h using 1 <;> simp only [banksCost,restCost] <;> omega

#print axioms banks_good
end SigGolfCandidate.T3M.CanonicalNative
