import SigGolfCandidate.W9Machine.WctV3Source
import SigGolfCandidate.W9Machine.WctPackedRuns
import SigGolfCandidate.T3M.Verify.ChainSem

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem chainPrefix_shift (index coord child : Nat) :
    V3.chainPrefix index coord child = ((index <<< 11) ||| coord ||| (child <<< 4)) <<< 16 := by
  have hi : index <<< 27 = (index <<< 11) <<< 16 := by
    simp only [Nat.shiftLeft_eq]; omega
  have hc : child <<< 20 = (child <<< 4) <<< 16 := by
    simp only [Nat.shiftLeft_eq]; omega
  rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib]
  simp only [V3.chainPrefix, hi, hc]
theorem chainPrefix_value (index coord child : Nat) (hk : coord < 9) (hj : child < 128) :
    V3.chainPrefix index coord child = 65536 * (2048 * index + 16 * child + coord) := by
  rw [chainPrefix_shift, Nat.or_assoc, Nat.or_comm coord (child <<< 4),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : coord < 2 ^ 4)]
  have hl : (child <<< 4) + coord < 2 ^ 11 := by
    simp only [Nat.shiftLeft_eq]; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hl]
  simp only [Nat.shiftLeft_eq]
  omega
theorem chainLow_add (index coord child chain digit : Nat) (hc : chain < 7) (hd : digit < 3) :
    V3.chainLow index coord child chain digit =
      V3.chainPrefix index coord child + (128 + 4 * chain + 256 * digit) := by
  have hlo : 128 ||| (chain <<< 2) ||| (digit <<< 8) = 128 + 4 * chain + 256 * digit := by
    interval_cases chain <;> interval_cases digit <;> decide
  unfold V3.chainLow
  rw [hlo, Nat.or_comm, chainPrefix_shift,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : 128 + 4 * chain + 256 * digit < 2 ^ 16)]
theorem packedHeader_eval (s : MachineState) (index coord child chain digit : Nat)
    (hp : s.getReg .x31 = BitVec.ofNat 64 (V3.chainPrefix index coord child))
    (hc : chain < 7) (hd : digit < 3) :
    (packedHeader chain digit).eval s = BitVec.ofNat 64 (V3.chainLow index coord child chain digit) := by
  simp only [packedHeader, addC_eval, E.eval, hp, ofNat_add_ofNat, chainLow_add _ _ _ _ _ hc hd]
theorem packedPos_eval (s : MachineState) (digit : Nat) (hd : digit < 3)
    (h7 : s.getReg .x7 = 1) (h13 : s.getReg .x13 = 2) :
    (packedPos digit).eval s = BitVec.ofNat 64 digit := by
  interval_cases digit <;> simp [packedPos, E.eval, h7, h13]
theorem wct_header_step (k index child t old digit : Nat) (hk : k < 9)
    (hi : index < 2 ^ 31) (hj : child < 128) (ht : t < 7) (ho : old < 3) (hd : digit < 3) :
    StoreKind.merge .b (BitVec.ofNat 64 (V3.chainLow index k child t old)) 1
      (BitVec.ofNat 64 digit) = BitVec.ofNat 64 (V3.chainLow index k child t digit) := by
  have heq : ∀ d, d < 3 → V3.chainLow index k child t d =
      (128 + 4 * t) + 256 * d + 2 ^ 16 * (2048 * index + 16 * child + k) := by
    intro d h
    rw [chainLow_add _ _ _ _ _ ht h, chainPrefix_value _ _ _ hk hj]
    omega
  rw [heq old ho, heq digit hd]
  apply stepByte _ (128 + 4 * t) (2048 * index + 16 * child + k) digit
    (by omega) (by omega) (by omega)
  all_goals
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by omega : 128 + 4 * t + 256 * old + 2 ^ 16 * (2048 * index + 16 * child + k) < 2 ^ 64)]
    omega
end W9Machine
