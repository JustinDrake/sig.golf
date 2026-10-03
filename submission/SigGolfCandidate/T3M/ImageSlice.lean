import SigGolfCandidate.Rv.Api
import SigGolfCandidate.T3M.Mem

set_option autoImplicit false
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem codeAt_slice {image : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (image.code.drop b).take code.length = code) :
    CodeAt image (pcOf b) code := by
  simp only [CodeAt, pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4096 + 4 * b < 2 ^ 64 by omega)]
  refine ⟨by omega, by omega, hb, ?_⟩
  rw [show (4096 + 4 * b - 4096) / 4 = b by omega, ← h]; exact List.take_prefix _ _
end SigGolfCandidate.T3M
