import SigGolfCandidate.T3M.Witness.Honest

/-!
# The source programs of CLOSURE's statements (verbatim copies)

CLOSURE's base-T3 closure (`t3/closure` fe2b0d1, appended to `T3/BPORS.lean`) proves its completeness and
budget theorems about `Completeness.everyMessageProgram`, `BudgetClosure.honestSignCount` and
`ExpansionClosure.honestJointCounts`. The definitions below are the same text (over W's
`honestProgramCore`, itself the text of `Completeness.honestProgram`), so `SourceFacts` can be stated
before CLOSURE is merged, and discharged from CLOSURE's theorems by unfolding (`Discharge`).
-/

namespace SigGolfCandidate.T3M.CanonicalFinal
open OracleComp OracleSpec
open SigGolfCandidate.T3 (M Message Digest Signature Cache Witness keygen sign expand verify)

/-- Every message against one oracle: CLOSURE's `Completeness.everyMessageProgram`. -/
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgramCore message
    pure (accepted && result)) true

/-- Key generation, then the counted signing phase: CLOSURE's `BudgetClosure.honestSignCount`. -/
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  T3.Cost.countBlocks (sign keys.2 message)

/-- CLOSURE's `ExpansionClosure.jointCounts`: both phase charges in one oracle, expansion charged only
when reached. -/
def jointCounts {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ))
    (expander : κ → σ → M ω) : M (Nat × Nat) := do
  let keys ← initial
  let signed ← T3.Cost.countBlocks (signer keys)
  match signed.1 with
  | none => pure (signed.2, 0)
  | some sig =>
      let expanded ← T3.Cost.countBlocks (expander keys sig)
      pure (signed.2, expanded.2)

/-- CLOSURE's `ExpansionClosure.honestJointCounts`. -/
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)

end SigGolfCandidate.T3M.CanonicalFinal
