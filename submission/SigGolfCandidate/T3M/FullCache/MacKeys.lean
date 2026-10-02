import SigGolfCandidate.T3M.FullCache.MacTag
import SigGolfCandidate.T3M.FullCache.MacPure

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The four little-endian secret-key words at the submitted ABI address. -/
def SkAt (s : MachineState) (sk : BitVec 256) : Prop :=
  ∀ j : Fin 4, s.getMem (BitVec.ofNat 64 (0x80+8*j.val)) = sk.extractLsb' (64*j.val) 64

def PrivAt (s : MachineState) (sk : BitVec 256) (i : Fin 2) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (PRIV+8*j.val)) =
    [sk.extractLsb' 0 64,sk.extractLsb' 64 64,3585,BitVec.ofNat 64 (i.val*2^32),
      sk.extractLsb' 128 64,sk.extractLsb' 192 64,0,0].getD j.val 0

theorem priv_query (s : MachineState) (sk : BitVec 256) (i : Fin 2) (h : PrivAt s sk i)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h11 : s.getReg .x11 = 64) :
    hashInput s = toQ (T3.privateInput sk (.inl (T3.header 14 0 0 0 i.val))) := by
  apply hashInput_toQ s _ 0 PRIV (privateInput_tweak_length _ _) h10 (by decide) (by decide)
    h11 (by decide)
  rw [readWords_eight,wordsOf_privateInput_tweak]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  change s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64 at h0
  change s.getMem (BitVec.ofNat 64 (PRIV+8)) = sk.extractLsb' 64 64 at h1
  change s.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 at h2
  change s.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (i.val*2^32) at h3
  change s.getMem (BitVec.ofNat 64 (PRIV+32)) = sk.extractLsb' 128 64 at h4
  change s.getMem (BitVec.ofNat 64 (PRIV+40)) = sk.extractLsb' 192 64 at h5
  change s.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 at h6
  change s.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 at h7
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  fin_cases i <;> rfl

theorem priv_next {s t : MachineState} {sk : BitVec 256} {a : BitVec 256}
    (hp : PrivAt s sk 0) (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (h24 : t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32)) : PrivAt t sk 1 := by
  intro j
  have hf := Frame.writeHash s a KEYS h12 (by decide)
  have hj := j.isLt
  by_cases he : j.val = 3
  · have ej : j = 3 := Fin.ext he
    subst j
    exact h24
  · rw [hfr.get (by simp [PRIV]; omega) (by simp [PRIV]; omega),
      hf.get (by simp [PRIV]; omega) (by simp [PRIV,KEYS]; omega),hp j]
    fin_cases j <;> first | rfl | exact False.elim (he rfl)

theorem keys_after {s t : MachineState} (a b : BitVec 256)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (ht12 : t.getReg .x12 = BitVec.ofNat 64 (KEYS+32)) : KeysAt (writeHash t b) a b := by
  intro j
  have hj := j.isLt
  have hA : KEYS+8*j.val < 2^64 := by simp [KEYS]; omega
  rw [getMem_writeHash t b (KEYS+32) (KEYS+8*j.val) ht12 (by decide) hA]
  fin_cases j
  all_goals simp only [KEYS, Nat.reduceMul, Nat.reduceAdd, Fin.val_zero, Fin.val_one, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one, Nat.reduceEqDiff, if_true, if_false, Nat.reduceLT, Nat.reduceSub]
  all_goals first
    | rfl
    | (rw [hfr.get (by decide) (by decide), getMem_writeHash s a KEYS _ h12 (by decide) (by decide)]
       simp [KEYS])

end SigGolfCandidate.T3M.FullCache
