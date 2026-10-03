import SigGolfCandidate.T3.Nonbinary.Decoder

namespace SigGolfResearch.NonbinaryTop.Decoder
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem parse_succ_isSome (n x : Nat) :
    (parse (n+1) x).isSome ↔ x%128<125 ∧ (parse n (x/128)).isSome := by
  by_cases h : x%128<125
  · cases hp : parse n (x/128) <;> simp [parse,h,hp]
  · simp [parse,h]

theorem parse_isSome_iff (n x : Nat) :
    (parse n x).isSome ↔ x<64*128^n ∧ ∀ j<n,x/128^j%128<125 := by
  induction n generalizing x with
  | zero =>
    by_cases h : x<64 <;> simp [parse,h]
  | succ n ih =>
    rw [parse_succ_isSome,ih]
    have hb : x/128<64*128^n ↔ x<64*128^(n+1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0<128),pow_succ,Nat.mul_assoc]
    constructor
    · rintro ⟨hzero,hbound,hrest⟩
      refine ⟨hb.mp hbound,?_⟩
      intro j hj
      cases j with
      | zero => simpa using hzero
      | succ j =>
        have hh := hrest j (by omega)
        simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh
    · rintro ⟨hbound,hrest⟩
      refine ⟨by simpa using hrest 0 (by omega),hb.mpr hbound,?_⟩
      intro j hj
      have hh := hrest (j+1) (by omega)
      simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh

theorem parse_fields {n x : Nat} {d : (Fin n → Triple5) × Triple4}
    (h : parse n x=some d) :
    (∀ j : Fin n,(rank5 (d.1 j)).val=x/128^j.val%128) ∧
      (rank4 d.2).val=x/128^n := by
  induction n generalizing x with
  | zero =>
    simp only [parse] at h
    split at h
    · cases h
      constructor
      · intro j; exact Fin.elim0 j
      · simp [rank4_digits4]
    · contradiction
  | succ n ih =>
    simp only [parse] at h
    split at h
    · split at h
      · contradiction
      · rename_i ds q hp
        cases h
        obtain ⟨hr,hq⟩ := ih hp
        constructor
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [rank5_digits5]
          · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hr j
        · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hq
    · contradiction

end SigGolfResearch.NonbinaryTop.Decoder
