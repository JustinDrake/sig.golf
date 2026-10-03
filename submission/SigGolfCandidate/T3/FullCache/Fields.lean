import SigGolfCandidate.T3.FullCache.Polynomial
import SigGolfCandidate.T3.FullCache.MacDefs

namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal
open SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def macLowWord (key : MacKey) (j : Fin 4) : BitVec 64 :=
  (key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2)) 64
def mkMacKey (lows pads : Fin 4 → BitVec 64) : MacKey := fun i =>
  answerOfWords (lows ⟨2 * i.val, by omega⟩) (pads ⟨2 * i.val, by omega⟩)
    (lows ⟨2 * i.val + 1, by omega⟩) (pads ⟨2 * i.val + 1, by omega⟩)
theorem fin4_cases (j : Fin 4) : ∃ i : Fin 2, j = ⟨2 * i.val, by omega⟩ ∨ j = ⟨2 * i.val + 1, by omega⟩ := by
  refine ⟨⟨j.val / 2, by omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · left; apply Fin.ext; simp only; omega
  · right; apply Fin.ext; simp only; omega
theorem macLowWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) : macLowWord (mkMacKey lows pads) j = lows j := by
  obtain ⟨hA, _, hC, _⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macLowWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero]
    rw [hA]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hC]; congr 1; apply Fin.ext; simp only; omega
theorem macPadWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) : macPadWord (mkMacKey lows pads) j = pads j := by
  obtain ⟨_, hB, _, hD⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macPadWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero, Nat.zero_add]
    rw [hB]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hD]; congr 1; apply Fin.ext; simp only; omega
theorem mkMacKey_words (key : MacKey) : mkMacKey (macLowWord key) (macPadWord key) = key := by
  funext i
  unfold mkMacKey macLowWord macPadWord
  have h0 : (2 * i.val) / 2 = i.val := by omega
  have h1 : (2 * i.val + 1) / 2 = i.val := by omega
  have m0 : (2 * i.val) % 2 = 0 := by omega
  have m1 : (2 * i.val + 1) % 2 = 1 := by omega
  simp only [h0, h1, m0, m1, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Fin.eta]
  exact answerOfWords_extract (key i)
theorem macKeyWord_eq (key : MacKey) (j : Fin 4) : macKeyWord key j = (macLowWord key j).toNat % 2 ^ 61 := by
  unfold macKeyWord macLowWord
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have : (key ⟨j.val / 2, by omega⟩).toNat < 2 ^ 256 := (key ⟨j.val / 2, by omega⟩).isLt
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp only [h, Nat.mul_zero, Nat.mul_one] <;> omega
theorem macKeyWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) :
    macKeyWord (mkMacKey lows pads) j = (lows j).toNat % 2 ^ 61 := by
  rw [macKeyWord_eq, macLowWord_mk]
end SiggolfT3Mac4
