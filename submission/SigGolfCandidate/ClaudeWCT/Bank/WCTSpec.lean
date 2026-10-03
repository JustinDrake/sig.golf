import SigGolfCandidate.ClaudeWCT.Bank.Spec
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.WCT9 (Coord Child Rank child rank digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WProposal := Fin (2 ^ 31) × (Coord → Child × Rank)
def outIdx (x : HashOutput) : Fin (2 ^ 31) := ⟨x.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def proposal (x : HashOutput) : WProposal := (outIdx x, fun k => (child x k, rank x k))
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 7) : Prop :=
  ∃ x ∈ X, outIdx x = outIdx N ∧ child x k = child N k ∧ digit (rank N k) t ≤ digit (rank x k) t
def Covered (X : List HashOutput) (N : HashOutput) : Prop := ∀ k t, SlotCovered X N k t
def SlotCoveredP (W : List WProposal) (N : HashOutput) (k : Coord) (t : Fin 7) : Prop :=
  ∃ p ∈ W, p.1 = outIdx N ∧ (p.2 k).1 = child N k ∧ digit (rank N k) t ≤ digit (p.2 k).2 t
def CoveredP (W : List WProposal) (N : HashOutput) : Prop := ∀ k t, SlotCoveredP W N k t
theorem slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 7) :
    SlotCovered X N k t ↔ SlotCoveredP (X.map proposal) N k t := by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    exact ⟨proposal x, List.mem_map_of_mem hx, h1, h2, h3⟩
  · rintro ⟨p, hp, h1, h2, h3⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact ⟨x, hx, h1, h2, h3⟩
theorem covered_iff (X : List HashOutput) (N : HashOutput) : Covered X N ↔ CoveredP (X.map proposal) N :=
  forall_congr' fun k => forall_congr' fun t => slotCovered_iff X N k t
theorem coveredP_append (W V : List WProposal) (N : HashOutput) (h : CoveredP W N) : CoveredP (W ++ V) N := by
  intro k t
  obtain ⟨p, hp, h1, h2, h3⟩ := h k t
  exact ⟨p, List.mem_append_left V hp, h1, h2, h3⟩
noncomputable def scoreP (W : List WProposal) (N : HashOutput) : ENNReal :=
  if WCT9.admissible N = true ∧ CoveredP W N then 1 else 0
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal := scoreP (X.map proposal) N
noncomputable def price (W : List WProposal) : ENNReal := 2 ^ 128 * BPORS.finiteAverage (fun N => scoreP W N)
theorem one_le_score (X : List HashOutput) (N : HashOutput) (hadm : WCT9.admissible N = true)
    (hcov : Covered X N) : 1 ≤ score X N := by
  unfold score scoreP
  rw [if_pos ⟨hadm, (covered_iff X N).mp hcov⟩]
theorem scoreP_append_mono (W V : List WProposal) (N : HashOutput) : scoreP W N ≤ scoreP (W ++ V) N := by
  unfold scoreP
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, coveredP_append W V N h1.2⟩ h2
  · exact bot_le
  · exact le_rfl
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  rw [List.map_append]
  exact scoreP_append_mono _ _ N
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = price (X.map proposal) / 2 ^ 128 := by
  unfold price score
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
theorem admissible_zero : WCT9.admissible 0 = true := by decide
def AcceptedProposalUniform : Prop :=
  ∀ g : WProposal → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if WCT9.admissible x = true then g (proposal x) else 0) =
      BPORS.finiteAverage g *
        Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def AcceptanceBound : Prop :=
  Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 64
def ExcessBound (horizon : Nat) (rate : ENNReal) : Prop :=
  uniformWordAverage horizon (fun W : List WProposal => price W - CaseC.theta) ≤ rate
noncomputable def wctSpec (hacc : AcceptedProposalUniform) (hle : AcceptanceBound) (horizon : Nat) (rate : ENNReal)
    (hexc : ExcessBound horizon rate) : FtsBankSpec WProposal where
  admissible := WCT9.admissible
  exists_admissible := ⟨0, admissible_zero⟩
  acceptance_le := hle
  proposal := proposal
  accepted_proposal := hacc
  score := score
  covered := Covered
  one_le_score := one_le_score
  score_append_mono := score_append_mono
  price := price
  average_score := average_score
  horizon := horizon
  excessRate := rate
  excess_le := hexc
end ClaudeWCT.Bank.WCT
