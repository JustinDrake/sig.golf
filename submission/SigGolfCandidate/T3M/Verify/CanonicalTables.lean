import SigGolfCandidate.T3M.Verify.CanonicalSpec

/-! The new schedule tables and their memory frame. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def bitLength (d : Nat) : Nat := if d=0 then 0 else d.log2+1
def geometryWord (d : Nat) : Word :=
  BitVec.ofNat 64 (8*bitLength d+2^32*(64*bitLength d))
def jumpWord (x y : Nat) : Word :=
  if x=0 ∨ y=0 ∨ x=y then 0 else pcOf ((geoms[x]!)[y]!)

theorem geometry_words : ∀ d : Fin 128,
    bytesToWordLE ((prefixData.drop (8*d.val)).take 8)=geometryWord d.val := by decide +kernel

theorem jump_words : ∀ i : Fin 64,
    bytesToWordLE ((prefixData.drop (1024+8*i.val)).take 8)=
      jumpWord (i.val%8) (i.val/8) := by decide +kernel

theorem prefix_length : prefixData.length=2048 := by decide +kernel

def TablesOK (s : MachineState) : Prop := ∀ k, k<256 →
  s.getMem (BitVec.ofNat 64 (0xfef000+8*k))=
    bytesToWordLE ((prefixData.drop (8*k)).take 8)

theorem TablesOK.geometry (s : MachineState) (h : TablesOK s) (d : Nat) (hd : d<128) :
    s.getMem (BitVec.ofNat 64 (0xfef000+8*d))=geometryWord d := by
  rw [h d (by omega)]
  exact geometry_words ⟨d,hd⟩

theorem TablesOK.jump (s : MachineState) (h : TablesOK s) (x y : Nat)
    (hx : x<8) (hy : y<8) :
    s.getMem (BitVec.ofNat 64 (0xfef400+8*x+64*y))=jumpWord x y := by
  have hi : x+8*y<64 := by omega
  have ht := h (128+x+8*y) (by omega)
  rw [show 0xfef000+8*(128+x+8*y)=0xfef400+8*x+64*y by omega] at ht
  rw [ht,show 8*(128+x+8*y)=1024+8*(x+8*y) by omega]
  have hw := jump_words ⟨x+8*y,hi⟩
  simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_left,show 0<8 by decide,Nat.div_eq_of_lt hx] using hw

theorem SpecResC.tables {allow rel gk sp post keep s t}
    (hr : SpecResC allow rel gk sp post keep s t) (h : TablesOK s)
    (hrel : RelOK rel s) : TablesOK t := by
  intro k hk
  rw [hr.mem,memEval_frame s _ _ (memOKA_data hr.memc s hrel _ (by omega) (by omega))]
  exact h k hk

theorem TablesOK.hash_frame (s : MachineState) (h : TablesOK s) (answer : BitVec 256)
    (d : Nat) (hd : s.getReg .x12=BitVec.ofNat 64 d) (hsafe : d+32 ≤ 2^23) :
    TablesOK (writeHash s answer) := by
  intro k hk
  rw [writeHash_frame s answer d _ hd (by omega) (by omega) (Or.inr (by omega))]
  exact h k hk

end SigGolfCandidate.T3M.CanonicalNative
