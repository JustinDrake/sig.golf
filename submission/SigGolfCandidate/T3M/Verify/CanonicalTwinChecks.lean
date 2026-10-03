import SigGolfCandidate.T3M.Verify.CanonicalGate

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def twinK : List (Reg × Word) := proPost++[(.x2,BitVec.ofNat 64 TAB)]
def twinNKeep : List Reg := [.x16,.x17,.x27,.x28]
def twinLoadSpec : Spec :=
  ⟨[(.x16,nE 0),(.x17,nE 1),(.x27,nE 2),(.x28,nE 3)],[],221960,false,5,[],none,5⟩
def twinBr (k : Nat) (reject : Bool) : Br :=
  ⟨.ne,nE k,.reg (nReg k),reject⟩
def twinPassBrs : List Br := ((List.range 4).map fun k => twinBr k false).reverse
def twinPassSpec : Spec :=
  ⟨[(.x3,nE 3)],[],22,false,9,twinPassBrs,none,9⟩
def twinRejectBrs (k : Nat) : List Br :=
  ([twinBr k true]++((List.range k).map fun j => twinBr j false).reverse)
def twinRejectSpec (k : Nat) : Spec :=
  ⟨[(.x5,SigGolfCandidate.T3M.Verify.cw 1),(.x10,SigGolfCandidate.T3M.Verify.cw 1)],[],221972,true,
    4+2*k,twinRejectBrs k,none,4+2*k⟩
def twinSelE : E :=
  .bin .srl (.bin .sll (.reg .x16) (SigGolfCandidate.T3M.Verify.cw 33)) (SigGolfCandidate.T3M.Verify.cw 33)
def twinSelSpec : Spec := ⟨[(.x22,twinSelE)],[],24,false,2,[],none,2⟩

theorem twin_load_checked :
    specB [] [] [] (runAtC {} twinK [221960] 18 []) twinLoadSpec [] twinK []=true := by decide +kernel
theorem twin_pass_checked :
    specB [] [] [] (runAtC {} twinK [22] 221961 (List.replicate 4 (.br false)))
      twinPassSpec [] twinK twinNKeep=true := by decide +kernel
theorem twin_reject_checked : ∀ k : Fin 4,
    specB [] [] [] (runAtC {} twinK [] 221961
      (List.replicate k.val (.br false)++[.br true])) (twinRejectSpec k.val) [] [] []=true := by
  decide +kernel
theorem twin_sel_checked :
    specB [] [] baseK (runAtC {} selK [24] 22 []) twinSelSpec [] selK twinNKeep=true := by decide +kernel

#print axioms twin_load_checked
#print axioms twin_reject_checked
end SigGolfCandidate.T3M.CanonicalNative
