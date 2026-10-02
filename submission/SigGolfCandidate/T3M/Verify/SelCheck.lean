import SigGolfCandidate.T3M.Verify.SelRuns

/-! Kernel checks of the selection code: the setup block and the 7 × (6 accepting + 6 rejecting) sort-tree paths. -/

namespace SigGolfCandidate.T3M.Verify

theorem setupCheck_ok : setupCheck = true := by decide +kernel

theorem selCheck_all : ((List.range 7).all fun c => (List.range 6).all fun p => selCheck1 c p) = true := by
  decide +kernel

theorem selRCheck_all : ((List.range 7).all fun c => (List.range 6).all fun r => selRCheck1 c r) = true := by
  decide +kernel

theorem selCheck_at (c p : Nat) (hc : c < 7) (hp : p < 6) : selCheck1 c p = true := by
  have := List.all_eq_true.mp selCheck_all c (List.mem_range.mpr hc)
  exact List.all_eq_true.mp this p (List.mem_range.mpr hp)

theorem selRCheck_at (c r : Nat) (hc : c < 7) (hr : r < 6) : selRCheck1 c r = true := by
  have := List.all_eq_true.mp selRCheck_all c (List.mem_range.mpr hc)
  exact List.all_eq_true.mp this r (List.mem_range.mpr hr)

end SigGolfCandidate.T3M.Verify
