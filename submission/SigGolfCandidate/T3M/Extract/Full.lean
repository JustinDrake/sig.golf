import SigGolfCandidate.T3M.Extract.VerifyP
import SigGolfCandidate.T3M.Extract.Fts

/-! # Unconditional padded structural extraction of `verifyP` (PEX-L ∘ PEX-F)

`verifyP_extract_full`: PEX-L's `verifyP_extract_normal` with PEX-F's `FtsExtract.ftsExtractSpecN_holds`
discharging `FtsExtractSpecN FtsExtract.FtsShaped`. -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityExtraction
open Correctness (Answers)

theorem ftsExtractSpecN_FtsShaped : FtsExtractSpecN FtsExtract.FtsShaped :=
  fun answers N w hS hrun => FtsExtract.ftsExtractSpecN_holds answers N w hS hrun

/-- **Padded structural extraction of the byte verifier** (unconditional). Under an answers table, an accepting
byte verification against the honest public key (`honestRoot answers 0 0 = (eval keygen).1`, `keygen_pk`) has
its digest query, an honestly shaped stream, and: a header-preserving hit at a bounded position among its actual
queries (`HitIn`; the position is a parse of the actual input, `hitIn_posOf`), or a WOTS/encoding divergence below
honest layers, or all four layers honest and the FTS part honest-shaped (`FtsExtract.FtsShaped`). -/
theorem verifyP_extract_full (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N w)) :=
  verifyP_extract_normal ftsExtractSpecN_FtsShaped answers m pk w hpk hv

end SigGolfCandidate.T3M.Extract
