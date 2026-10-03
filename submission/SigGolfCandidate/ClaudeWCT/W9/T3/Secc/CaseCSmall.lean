import SigGolfCandidate.T3.Secc.CaseCFull
import SigGolfCandidate.T3.Secc.CaseCSplit
import SigGolfCandidate.T3.Secc.CaseCCore
import SigGolfCandidate.T3.Secc.WotsSmallContract
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCFull

section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFullBound : DecidableEq T3.Cache := Classical.decEq _
def FullEvent (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) (A : Correctness.Answers) : Prop :=
  y.1 = true ∧ countOf y.2 ≤ q ∧ PinnedC adversary FullQ ((y.1, ([], y.2)), A)
noncomputable def fullWeight (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) : ENNReal :=
  Pr[fun t => FullEvent adversary q y (SeccLaw.completeWith (lazyOf y.2) t) |
    (PMF.uniformOfFintype SeccLaw.CompletionTables)]
theorem pmf_probEvent_bind {α β : Type} (p : PMF α) (K : α → PMF β) (F : β → Prop) :
    Pr[F | p.bind K] = expectedValue p (fun a => Pr[F | K a]) := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  rfl
theorem pmf_probEvent_map {α β : Type} (p : PMF α) (f : α → β) (F : β → Prop) :
    Pr[F | p.map f] = Pr[fun a => F (f a) | p] := by
  rw [← PMF.monad_map_eq_map, probEvent_map]
  rfl
theorem pmf_probEvent_mono {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hF : F x
  · simp [hF, h x hF]
  · simp [hF]
theorem pmf_probEvent_eq_zero {α : Type} (p : PMF α) {F : α → Prop} (h : ∀ x, ¬F x) : Pr[F | p] = 0 := by
  simp only [probEvent_eq_tsum_ite]
  simp [h]
theorem fullWeight_le_one (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) :
    fullWeight adversary q y ≤ 1 := probEvent_le_one
theorem completed_full_eq (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] =
      expectedValue (bankExperiment adversary q) (fun b => fullWeight adversary q (b.1, b.2.2)) := by
  unfold SeccLaw.completedExperiment
  rw [pmf_probEvent_bind]
  have hinner : ∀ r : PaddedGame.TraceResult,
      Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 |
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map
          (fun t => (r, SeccLaw.completeWith r.2.2.base.source.2 t))] = fullWeight adversary q (r.1, r.2.2) := by
    intro r
    rw [pmf_probEvent_map]
    rfl
  simp_rw [hinner]
  have h1 := expectedValue_pmf_map (PaddedGame.tracedExperiment adversary q hq)
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) (fullWeight adversary q)
  have h2 := expectedValue_pmf_map (bankExperiment adversary q)
    (fun b : Bool × BankState => (b.1, b.2.2)) (fullWeight adversary q)
  rw [← h1, ← h2]
  have ht := bank_traced adversary q hq
  rw [PMF.monad_map_eq_map, PMF.monad_map_eq_map] at ht
  rw [ht]
theorem full_bound_births (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | SeccLaw.completedExperiment adversary q hq] ≤
      (theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths IsDigestInput adversary q hq +
        (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  calc
    _ ≤ Pr[fun z => FullEvent adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] := by
      apply pmf_probEvent_mono
      intro z hz
      exact ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = expectedValue (bankExperiment adversary q) (fun b => fullWeight adversary q (b.1, b.2.2)) :=
      completed_full_eq adversary q hq
    _ ≤ expectedValue (bankExperiment adversary q) (fun b => potential q b.2) := by
      apply pmf_expectedValue_mono
      intro b hb
      by_cases hex : ∃ t, FullEvent adversary q (b.1, b.2.2) (SeccLaw.completeWith (lazyOf b.2.2) t)
      · obtain ⟨t, ht⟩ := hex
        have hA : Agrees (SeccLaw.completeWith (lazyOf b.2.2) t) (lazyOf b.2.2) :=
          fun input answer hk => SeccLaw.completeWith_agrees _ t input answer hk
        exact (fullWeight_le_one adversary q _).trans
          (full_potential adversary q hq b hb [] _ hA ht.2.1 ht.2.2)
      · push Not at hex
        have h0 : fullWeight adversary q (b.1, b.2.2) = 0 := by
          unfold fullWeight
          exact pmf_probEvent_eq_zero _ hex
        rw [h0]
        exact bot_le
    _ ≤ _ := bank_potential_le adversary q hq
end SigGolfCandidate.T3.Security.CaseC
end

section




namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def NearBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | SeccLaw.completedExperiment adversary q hq] ≤
      Wots.nearTerm q
theorem pmf_probEvent_mono_support {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]
theorem pmf_probEvent_or_le {α : Type} (p : PMF α) (F G : α → Prop) :
    Pr[fun x => F x ∨ G x | p] ≤ Pr[F | p] + Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hF : F x <;> by_cases hG : G x <;> simp [hF, hG]
theorem publicClass_digest : (fun _ => CreationGame.publicClass IsDigestInput) = Wots.digestClass := by
  funext z input
  apply propext
  rcases input with (coin | x) | priv
  · exact ⟨fun h => h.elim, fun ⟨_, _, _, h⟩ => by cases h⟩
  · constructor
    · rintro ⟨rho, m, ctr, rfl⟩
      exact ⟨rho, m, ctr, rfl⟩
    · rintro ⟨rho, m, ctr, h⟩
      cases h
      exact ⟨rho, m, ctr, rfl⟩
  · exact ⟨fun h => h.elim, fun ⟨_, _, _, h⟩ => by cases h⟩
theorem full_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
        ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 := by
  refine (full_bound_births adversary q hq).trans (add_le_add ?_ ?_)
  · apply mul_le_mul'
    · apply ENNReal.div_le_div_right
      exact theta_add_sixteenth_le_one.trans le_self_add
    · rw [← publicClass_digest]
      exact CreationGame.expectedBirths_le_shared IsDigestInput adversary q hq
  · rw [SeccClosing.excessRate_def]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast (by unfold Wots.signRatio; omega : q ≤ Wots.signRatio * q)
theorem caseC_small_bound (hnear : NearBound) : Wots.CaseCSmallBound := by
  intro adversary q hq h1 hsplit
  set P := SeccLaw.completedExperiment adversary q hq
  calc
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ Wots.CaseCFreshPinned adversary z | P] ≤
        Pr[fun z => (QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z) ∨
          ((QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z) ∨
            (QueryRecorded.CleanWin q z.1 ∧ BPair.PairGuess adversary z)) | P] := by
      apply pmf_probEvent_mono_support
      intro z hz hzC
      rcases caseC_three_way adversary q hq z hz hzC.1 hzC.2 with h | h | h
      · exact Or.inl ⟨hzC.1, h⟩
      · exact Or.inr (Or.inl ⟨hzC.1, h⟩)
      · exact Or.inr (Or.inr ⟨hzC.1, h⟩)
    _ ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | P] +
        (Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | P] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ BPair.PairGuess adversary z | P]) :=
      (pmf_probEvent_or_le _ _ _).trans (add_le_add le_rfl (pmf_probEvent_or_le _ _ _))
    _ ≤ ((1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
          ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128) +
        (Wots.nearTerm q + BPair.pairTerm q) :=
      add_le_add (full_bound adversary q hq)
        (add_le_add (hnear adversary q hq h1 hsplit) (BPair.pair_guess_bound adversary q hq))
    _ ≤ _ := by
      rw [← add_assoc]
      exact le_self_add
end SigGolfCandidate.T3.Security.CaseC
end

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (theta IsDigestInput countOf lazyOf Agrees pmf_probEvent_bind
  pmf_probEvent_map pmf_probEvent_mono pmf_probEvent_eq_zero pmf_expectedValue_mono expectedValue_pmf_map)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open ClaudeWCT.Bank.WCT (ExcessBound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def FullEvent (X : CaseCExtraction) (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State)
    (A : Correctness.Answers) : Prop :=
  y.1 = true ∧ countOf y.2 ≤ q ∧ PinnedC X adversary FullQ ((y.1, ([], y.2)), A)
noncomputable def fullWeight (X : CaseCExtraction) (adversary : AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) : ENNReal :=
  Pr[fun t => FullEvent X adversary q y (SeccLaw.completeWith (lazyOf y.2) t) |
    (PMF.uniformOfFintype SeccLaw.CompletionTables)]
theorem fullWeight_le_one (X : CaseCExtraction) (adversary : AdversaryP) (q : Nat) (y : Bool × QueryRecorded.State) :
    fullWeight X adversary q y ≤ 1 := probEvent_le_one
theorem completed_full_eq (X : CaseCExtraction) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => FullEvent X adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] =
      expectedValue (bankExperiment adversary q) (fun b => fullWeight X adversary q (b.1, b.2.2)) := by
  unfold SeccLaw.completedExperiment
  rw [pmf_probEvent_bind]
  have hinner : ∀ r : PaddedGame.TraceResult,
      Pr[fun z => FullEvent X adversary q (z.1.1, z.1.2.2) z.2 |
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map
          (fun t => (r, SeccLaw.completeWith r.2.2.base.source.2 t))] = fullWeight X adversary q (r.1, r.2.2) := by
    intro r
    rw [pmf_probEvent_map]
    rfl
  simp_rw [hinner]
  have h1 := expectedValue_pmf_map (PaddedGame.tracedExperiment adversary q hq)
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) (fullWeight X adversary q)
  have h2 := expectedValue_pmf_map (bankExperiment adversary q)
    (fun b : Bool × BankState => (b.1, b.2.2)) (fullWeight X adversary q)
  rw [← h1, ← h2]
  have ht := bank_traced adversary q hq
  rw [PMF.monad_map_eq_map, PMF.monad_map_eq_map] at ht
  rw [ht]
theorem full_bound_births (X : CaseCExtraction) (rate : ENNReal) (hexc : ExcessBound horizon rate)
    (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary FullQ z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths IsDigestInput adversary q hq +
        (q : ENNReal) * rate / 2 ^ 128 := by
  calc
    _ ≤ Pr[fun z => FullEvent X adversary q (z.1.1, z.1.2.2) z.2 | SeccLaw.completedExperiment adversary q hq] := by
      apply pmf_probEvent_mono
      intro z hz
      exact ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = expectedValue (bankExperiment adversary q) (fun b => fullWeight X adversary q (b.1, b.2.2)) :=
      completed_full_eq X adversary q hq
    _ ≤ expectedValue (bankExperiment adversary q) (fun b => potential q b.2) := by
      apply pmf_expectedValue_mono
      intro b hb
      by_cases hex : ∃ t, FullEvent X adversary q (b.1, b.2.2) (SeccLaw.completeWith (lazyOf b.2.2) t)
      · obtain ⟨t, ht⟩ := hex
        have hA : Agrees (SeccLaw.completeWith (lazyOf b.2.2) t) (lazyOf b.2.2) :=
          fun input answer hk => SeccLaw.completeWith_agrees _ t input answer hk
        exact (fullWeight_le_one X adversary q _).trans
          (full_potential X adversary q hq b hb [] _ hA ht.2.1 ht.2.2)
      · push Not at hex
        have h0 : fullWeight X adversary q (b.1, b.2.2) = 0 := by
          unfold fullWeight
          exact pmf_probEvent_eq_zero _ hex
        rw [h0]
        exact bot_le
    _ ≤ _ := bank_potential_le rate hexc adversary q hq
end ClaudeWCT.W9.T3.Security.CaseC
end

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (theta IsDigestInput pmf_probEvent_mono_support pmf_probEvent_or_le
  publicClass_digest theta_add_sixteenth_le_one)
open ClaudeWCT.W9.T3M (WBytes)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open ClaudeWCT.Bank.WCT (ExcessBound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem full_bound (X : CaseCExtraction) (hexc : ExcessBound horizon (11324 / 100000000))
    (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary FullQ z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
        ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 := by
  refine (full_bound_births X _ hexc adversary q hq).trans (add_le_add ?_ ?_)
  · apply mul_le_mul'
    · apply ENNReal.div_le_div_right
      exact theta_add_sixteenth_le_one.trans le_self_add
    · rw [← publicClass_digest]
      exact CreationGame.expectedBirths_le_shared IsDigestInput adversary q hq
  · rw [SeccClosing.excessRate_def]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast (by unfold Wots.signRatio; omega : q ≤ Wots.signRatio * q)
def NearBound (X : CaseCExtraction)
    (NearQ : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop)
    (nearTerm : Nat → ENNReal) : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary NearQ z |
        SeccLaw.completedExperiment adversary q hq] ≤ nearTerm q
structure CaseCSplitInterface (X : CaseCExtraction) where
  CaseCFreshPinned : AdversaryP → PaddedGame.TraceResult × Correctness.Answers → Prop
  NearQ : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop
  PairGuess : AdversaryP → PaddedGame.TraceResult × Correctness.Answers → Prop
  pairTerm : Nat → ENNReal
  three_way : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (z : PaddedGame.TraceResult × Correctness.Answers),
    z ∈ (SeccLaw.completedExperiment adversary q hq).support → QueryRecorded.CleanWin q z.1 →
    CaseCFreshPinned adversary z →
    PinnedC X adversary FullQ z ∨ PinnedC X adversary NearQ z ∨ PairGuess adversary z
  pair_guess_bound : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127),
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PairGuess adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      pairTerm q
def CaseCSmallBound (CaseCFreshPinned : AdversaryP → PaddedGame.TraceResult × Correctness.Answers → Prop)
    (nearTerm pairTerm : Nat → ENNReal) : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
        ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700
theorem caseC_small_bound (X : CaseCExtraction) (Y : CaseCSplitInterface X) (nearTerm : Nat → ENNReal)
    (hexc : ExcessBound horizon (11324 / 100000000)) (hnear : NearBound X Y.NearQ nearTerm) :
    CaseCSmallBound Y.CaseCFreshPinned nearTerm Y.pairTerm := by
  intro adversary q hq h1 hsplit
  set P := SeccLaw.completedExperiment adversary q hq
  calc
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ Y.CaseCFreshPinned adversary z | P] ≤
        Pr[fun z => (QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary FullQ z) ∨
          ((QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary Y.NearQ z) ∨
            (QueryRecorded.CleanWin q z.1 ∧ Y.PairGuess adversary z)) | P] := by
      apply pmf_probEvent_mono_support
      intro z hz hzC
      rcases Y.three_way adversary q hq z hz hzC.1 hzC.2 with h | h | h
      · exact Or.inl ⟨hzC.1, h⟩
      · exact Or.inr (Or.inl ⟨hzC.1, h⟩)
      · exact Or.inr (Or.inr ⟨hzC.1, h⟩)
    _ ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary FullQ z | P] +
        (Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC X adversary Y.NearQ z | P] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ Y.PairGuess adversary z | P]) :=
      (pmf_probEvent_or_le _ _ _).trans (add_le_add le_rfl (pmf_probEvent_or_le _ _ _))
    _ ≤ ((1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
          ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128) +
        (nearTerm q + Y.pairTerm q) :=
      add_le_add (full_bound X hexc adversary q hq)
        (add_le_add (hnear adversary q hq h1 hsplit) (Y.pair_guess_bound adversary q hq))
    _ ≤ _ := by
      rw [← add_assoc]
      exact le_self_add
end ClaudeWCT.W9.T3.Security.CaseC
end
