import SigGolfCandidate.T3M.Verify.BCCheck
import SigGolfCandidate.T3M.Verify.Words

namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def CounterWord : Prop := ∀ (w : WBytes) (j : Nat),
  LoadKind.wu.fromWord (wword w j) 0 = BitVec.ofNat 64 (wle32 w (8 * j)).toNat
theorem counterWord : CounterWord := fun w j => by
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, wword_toNat, wle32,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, ← Nat.mul_assoc]
set_option maxRecDepth 100000
theorem nCopy_eq : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide
theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay (trPc lay c) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)
def CounterPadBytes : Prop := ∀ (c : BitVec 32) (pad : BitVec 96),
  SphincsSecurity.bytesLE 4 c ++ SphincsSecurity.bytesLE 12 pad =
    SphincsSecurity.bytesLE 16 (pad ++ c)
theorem counterPadBytes : CounterPadBytes := fun c pad => by
  apply readLE_inj (by simp [SphincsSecurity.bytesLE_length])
  simp only [readLE_append, SphincsSecurity.bytesLE_length, readLE_bytesLE, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt c.isLt, Nat.shiftLeft_eq]
  omega
def CounterPadExtract : Prop := ∀ (w : WBytes) (o : Nat),
  (w.extractLsb' (8 * (o + 4)) 96 ++ wle32 w o) = wdig w o
theorem counterPadExtract : CounterPadExtract := fun w o =>
  BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)
end SigGolfCandidate.T3M.BC
