import SigGolfCandidate.T3.Core

/-!
# Sign: the digits of a successful encoding

`decode_digits` : a decoded digit list has one digit per chain, each digit at most `2^width - 1`
(the data digits are `width`-bit fields; the lower-layer checksum digit is `< 8`). This is what
`build_leaf`'s precondition (`LeafPre.hdigb`) needs from a successful `counter_search`.
-/

namespace SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3 (Layer Digest decode dataDigits dataCount chainCount width target encodedBits)

theorem dataDigits_getD (lay : Layer) (v : Digest) (i : Nat) (hi : i < dataCount lay) :
    (dataDigits lay v).getD i 0 ≤ 2 ^ width lay i - 1 := by
  simp only [dataDigits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  have := Nat.mod_lt (v.toNat / 2 ^ (if lay = 0 then (if i < 49 then 2 * i else 98 + 3 * (i - 49)) else 3 * i))
    (Nat.two_pow_pos (width lay i))
  omega

theorem length_dataDigits (lay : Layer) (v : Digest) : (dataDigits lay v).length = dataCount lay := by
  simp [dataDigits]

/-- A decoded digit list: one digit per chain, each `≤ 2^width - 1`. -/
theorem decode_digits {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ds.length = chainCount lay ∧ ∀ i < chainCount lay, ds.getD i 0 ≤ 2 ^ width lay i - 1 := by
  unfold decode at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  · cases h
    subst h2
    refine ⟨by rw [length_dataDigits]; rfl, fun i hi => dataDigits_getD 0 v i (by
      have : chainCount 0 = 58 := rfl
      simp only [dataCount, if_true]; omega)⟩
  · cases h
    have hc : chainCount lay = 43 := by
      fin_cases lay
      · exact absurd rfl h2
      all_goals rfl
    have hd : dataCount lay = 42 := by simp [dataCount, h2]
    refine ⟨by rw [List.length_append, length_dataDigits, hd, hc]; rfl, fun i hi => ?_⟩
    rw [hc] at hi
    by_cases hi' : i < 42
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_dataDigits, hd]; exact hi'),
        ← List.getD_eq_getElem?_getD]
      exact dataDigits_getD lay v i (by rw [hd]; exact hi')
    · have hi42 : i = 42 := by omega
      subst hi42
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_dataDigits, hd]),
        length_dataDigits, hd]
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      have hw : width lay 42 = 3 := by simp [width, h2]
      rw [hw]
      omega

end SigGolfCandidate.T3M.Sign
