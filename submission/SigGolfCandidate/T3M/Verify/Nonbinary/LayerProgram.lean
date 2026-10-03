import SigGolfCandidate.T3M.Verify.LayerLower
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3.Proofs

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem nctx_block (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - 0x800 = chainBlock 0 i := by
  change 15768 - 1664 + 64 * (53 - i) - 2048 = 11288 + 64 * 12 + 64 * (54 - 1 - i)
  omega

theorem nctx_chain_eq (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) (hi : i < 54) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i) =
      chainP 0 (route index 0).2 (route index 0).1 i ((dataDigits 0 v).getD i 0)
        (maxDigit 0 i - (dataDigits 0 v).getD i 0) (wchainPads w 0 i).1 (wchainPads w 0 i).2 (wvalue w 0 i) := by
  have hm : NCtx.topMax i = maxDigit 0 i := by
    simp [NCtx.topMax, Nonbinary.mx, maxDigit, show (i / 3 < 17) ↔ i < 51 by omega]
  dsimp only
  rw [T3.dataDigits_getD 0 v i hi, hm]
  unfold NCtx.pad0 NCtx.pad1 NCtx.val
  rw [nctx_block]
  rfl

/-- The checked chain context hashes exactly Core's padded source chains. -/
theorem nctx_mapM_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    let c := nctxOf w index v p
    (List.finRange 54).mapM (fun i => chainP 0 c.tree c.leaf i.val (c.dig i.val)
      (NCtx.topMax i.val - c.dig i.val) (c.pad0 i.val) (c.pad1 i.val) (c.val i.val)) =
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold chainsP
  apply congrArg (fun f => (List.finRange 54).mapM f)
  funext i
  exact nctx_chain_eq w index v p i.val i.isLt

end SigGolfCandidate.T3M
