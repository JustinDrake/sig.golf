import SigGolfCandidate.T3M.Verify.ChainCheckT6

/-! All chain families of the verify image: every `ttab`/`qtab` slot and every shared block. -/

namespace SigGolfCandidate.T3M

theorem triCheck_at (t : Nat) (ht : t < 14) : triCheck t 0 256 = true ∧ triCheck t 256 256 = true := by
  interval_cases t
  exacts [⟨triCheck_0_0, triCheck_0_1⟩,
    ⟨triCheck_1_0, triCheck_1_1⟩,
    ⟨triCheck_2_0, triCheck_2_1⟩,
    ⟨triCheck_3_0, triCheck_3_1⟩,
    ⟨triCheck_4_0, triCheck_4_1⟩,
    ⟨triCheck_5_0, triCheck_5_1⟩,
    ⟨triCheck_6_0, triCheck_6_1⟩,
    ⟨triCheck_7_0, triCheck_7_1⟩,
    ⟨triCheck_8_0, triCheck_8_1⟩,
    ⟨triCheck_9_0, triCheck_9_1⟩,
    ⟨triCheck_10_0, triCheck_10_1⟩,
    ⟨triCheck_11_0, triCheck_11_1⟩,
    ⟨triCheck_12_0, triCheck_12_1⟩,
    ⟨triCheck_13_0, triCheck_13_1⟩]

theorem entCheck_at (t k : Nat) (ht : t < 14) (hk : k < 512) : entCheck t k = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  by_cases h : k < 256
  · exact List.all_eq_true.mp h0.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp h1.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem blkCheck_at (t dB dC : Nat) (ht : t < 14) (hB : dB < 8) (hC : dC < 8) :
    blkCheck t dB dC = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  have e1 : (8 * dB + dC) / 8 = dB := by omega
  have e2 : (8 * dB + dC) % 8 = dC := by omega
  by_cases h : 8 * dB + dC < 32
  · have := List.all_eq_true.mp h0.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this
  · have := List.all_eq_true.mp h1.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this

theorem ckCheck_ok : ckCheck = true := by decide +kernel

end SigGolfCandidate.T3M
