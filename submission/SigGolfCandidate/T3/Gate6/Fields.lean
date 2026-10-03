import SigGolfCandidate.T3.Gate6.FreshProbability
namespace SigGolfResearch.Gate6
set_option maxHeartbeats 500000

theorem digestRecord_index (output : BitVec 256) :
    (digestRecord output).1.1.val=output.toNat%2^31 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem digestRecord_bucket (output : BitVec 256) (c : Bank) :
    ((digestRecord output).1.2 c).val=output.toNat/2^(31+25*c.val)%16 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem digestRecord_leaf (output : BitVec 256) (c : Bank) (j : Fin 3) :
    ((digestRecord output).2.1 c j).val=
      output.toNat/2^(31+25*c.val)/2^(4+7*j.val)%128 := by
  simp only [digestRecord,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega

theorem digestRecord_gate (output : BitVec 256) :
    (digestRecord output).2.2.1.val=output.toNat/2^246 := by
  have hlt : output.toNat/2^246<2^10 := by
    apply Nat.div_lt_of_lt_mul
    calc output.toNat < 2^256 := output.isLt
      _ = 2^246*2^10 := by norm_num
  simp only [digestRecord,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt hlt

theorem digestRecord_gate_accept (output : BitVec 256) :
    (digestRecord output).2.2.1.val<135 ↔ output.toNat/2^246<135 := by
  rw [digestRecord_gate]

/-- Source-friendly decomposition of the actual acceptance predicate. -/
theorem digest_acceptance_iff (output : BitVec 256) :
    DigestAccepted output ↔ output.toNat/2^246<135 ∧
      (∀ c, Function.Injective ((digestRecord output).2.1 c)) ∧
      (∑ c,childAuth ((digestRecord output).2.1 c))≤87 := by
  change ((digestRecord output).2.2.1.val<135 ∧ _ ∧ _) ↔ _
  rw [digestRecord_gate_accept]

end SigGolfResearch.Gate6
