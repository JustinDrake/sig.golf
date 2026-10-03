import SigGolfCandidate.T3.Proofs

/-! Actual decoded digits respect the mixed radix chain endpoints. -/
namespace SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3 (Layer Digest decode dataDigits dataCount chainCount maxDigit)

theorem dataDigits_getD (lay : Layer) (v : Digest) (i : Nat) (hi : i < dataCount lay) :
    (dataDigits lay v).getD i 0 ≤ maxDigit lay i := by
  rw [T3.dataDigits_getD lay v i hi]
  exact T3.Nonbinary.coreDigit_le lay v i

theorem length_dataDigits (lay : Layer) (v : Digest) : (dataDigits lay v).length = dataCount lay := by
  simp [dataDigits]

/-- Each decoded digit is no larger than its actual radix endpoint. -/
theorem decode_digits {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ds.length = chainCount lay ∧ ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i :=
  ⟨(T3.decode_length_sum h).1, T3.decode_digit_max h⟩
end SigGolfCandidate.T3M.Sign
