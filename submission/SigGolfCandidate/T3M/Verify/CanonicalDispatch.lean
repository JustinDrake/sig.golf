import SigGolfCandidate.T3M.Verify.CanonicalSpec
import SigGolfCandidate.T3M.Witness.CanonicalGeometry

/-! Specification of the 13-instruction digest-derived schedule dispatch. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def cw (n : Word) : E := .c n

def dispatchKnown (c : Nat) : List (Reg × Word) :=
  [(.x20,0xfef000),(.x21,0xfef400),(.x24,BitVec.ofNat 64 (0x140+24*c))]

def ptrE (c j : Nat) : E := .ld (cw (BitVec.ofNat 64 (0x140+24*c+8*j)))
def xorE (c i j : Nat) : E := .bin .xor (ptrE c i) (ptrE c j)
def geomE (c i j : Nat) : E := .ld (.bin .add (xorE c i j) (cw 0xfef000))
def smallE (c : Nat) : E := .un (.ld .bu 0) (geomE c 0 1)
def largeE (c : Nat) : E := .un (.ld .hu 4) (geomE c 1 2)
def tableE (c : Nat) : E := .bin .add (.bin .add (smallE c) (largeE c)) (cw 0xfef400)
def targetE (c : Nat) : E := .ld (tableE c)

def dispatchSpec (c : Nat) : Spec :=
  ⟨[(.x1,cw (BitVec.ofNat 64 (0x1000+4*(banks[c]!+13)))),(.x3,targetE c),
    (.x6,smallE c),(.x7,largeE c),(.x16,ptrE c 0),(.x17,ptrE c 1),(.x18,ptrE c 2)],
    [],0,false,13,[],some (.bin .and (targetE c) (cw (~~~1#64))),13⟩

def dispatchObl (c : Nat) : List Oblig :=
  [.valid ⟨some (.bin .add (smallE c) (largeE c)),0xfef400⟩ 8,
    .align8 (xorE c 1 2),.valid ⟨some (xorE c 1 2),0xfef004⟩ 2,
    .align8 (xorE c 0 1),.valid ⟨some (xorE c 0 1),0xfef000⟩ 1]

def dispatchKeep : List Reg :=
  [.x2,.x5,.x8,.x9,.x11,.x13,.x14,.x19,.x22,.x25,.x27,.x28,.x29,.x31]

def dispatchCheck (c : Nat) : Bool :=
  specB [] [] [] (runAtC {} (dispatchKnown c) [] banks[c]! [.jmp])
    (dispatchSpec c) (dispatchObl c) (dispatchKnown c) dispatchKeep

theorem dispatch_checked : ∀ c : Fin 7, dispatchCheck c.val=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalNative
