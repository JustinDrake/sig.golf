import SigGolfCandidate.T3M.Verify.LayerRuns

/-! Kernel check of every transition copy of the four layers (`copyCheck`): the transitions, their rejections and
the leaf-pk blocks. -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem ld3Check_ok : ld3Check = true := by decide +kernel
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by decide +kernel

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

end SigGolfCandidate.T3M
