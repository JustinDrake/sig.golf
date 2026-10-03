import SigGolfCandidate.T3M.Witness.Honest

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec
open SigGolfCandidate.T3 (M Message Digest Signature Cache Witness keygen sign expand verify)
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgramCore message
    pure (accepted && result)) true
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  T3.Cost.countBlocks (sign keys.2 message)
def jointCounts {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ))
    (expander : κ → σ → M ω) : M (Nat × Nat) := do
  let keys ← initial
  let signed ← T3.Cost.countBlocks (signer keys)
  match signed.1 with
  | none => pure (signed.2, 0)
  | some sig =>
      let expanded ← T3.Cost.countBlocks (expander keys sig)
      pure (signed.2, expanded.2)
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
end SigGolfCandidate.T3M.Final
