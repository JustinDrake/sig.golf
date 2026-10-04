import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Code
import SigGolfCandidate.T3M.Verify.Exec
import SigGolfCandidate.T3M.Mem

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def NewCodeAt (im : Image) : Prop :=
  ∀ c, c < 156 → CodeAt im (pcOf (256 * (c + 4))) (expChunks.getD c [])
def expLook (n : Nat) : Option (BitVec 32) :=
  if 1024 ≤ n then (expChunks.getD (n / 256 - 4) [])[n % 256]? else none
set_option maxRecDepth 100000 in
theorem expChunks_length : expChunks.length = 156 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_len_le : ∀ c, c < 156 → (expChunks.getD c []).length ≤ 256 := by decide +kernel
theorem expLook_ok {im : Image} (h : NewCodeAt im) : LookOK im expLook := by
  intro n w hw
  unfold expLook at hw
  split at hw
  · rename_i hn
    have hc : n / 256 - 4 < 156 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by rw [expChunks_length]; omega)] at hw
      simp at hw
    obtain ⟨h1, h2, h3, h4⟩ := h (n / 256 - 4) hc
    have hpc : (pcOf (256 * (n / 256 - 4 + 4))).toNat = 0x1000 + 4 * (256 * (n / 256)) := by
      rw [show n / 256 - 4 + 4 = n / 256 by omega, pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have : expLook n = some w := by unfold expLook; rw [if_pos hn]; exact hw
      have hl := List.getElem?_eq_some_iff.mp hw
      have hlen : (expChunks.getD (n / 256 - 4) []).length ≤ 256 := by
        exact expChunks_len_le _ hc
      omega
    rw [hpc] at h4 h3
    obtain ⟨t, ht⟩ := h4
    have := congrArg (·[n % 256]?) ht
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1, hw,
      List.getElem?_drop] at this
    rw [show 0x1000 + 4 * (256 * (n / 256)) - 0x1000 = 4 * (256 * (n / 256)) by omega,
      show 4 * (256 * (n / 256)) / 4 + n % 256 = n by omega] at this
    exact this.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
