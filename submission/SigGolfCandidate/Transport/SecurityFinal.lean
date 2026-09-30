import SigGolfCandidate.Transport.SecurityProof

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec OracleComp.EvalDist Bridge

set_option allowUnsafeReducibility true in
attribute [local reducible] adversary submission sizes program input output Legacy.Input Legacy.Output
  SigGolf.Input SigGolf.Output

noncomputable def legacyGame (s : Legacy.Submission) (A : Legacy.Adversary s.sizes) (n : Nat) :
    OracleComp SigGolf.World Legacy.AttackResult := do
  let sk ← liftM Legacy.sampleSecretKey
  let kg ← liftM (s.run .keygen sk)
  let some (pk, cache) := kg.value | return ⟨false, kg.hashCalls⟩
  s.interact A sk pk n (A.initial pk cache) { hashCalls := kg.hashCalls }

theorem native_game_count (s : Legacy.Submission) (h : s.Admissible)
    (A : SigGolf.Adversary (sizes s.sizes)) :
    countFrom SigGolf.hashCost ((submission s).game A) 0 = (do
      let sk ← (liftM Legacy.sampleSecretKey : OracleComp SigGolf.World _)
      let kg ← (liftM (s.run .keygen sk) : OracleComp SigGolf.World _)
      let some (pk, cache) := kg.value | return (false, kg.hashCalls)
      countedTail s sk pk (A pk cache) [] kg.hashCalls) := by
  unfold SigGolf.Submission.game
  rw [countFrom_bind, countFrom_liftM_unif _ (fun _ => rfl), bind_map_left]
  apply bind_congr
  intro sk
  rw [countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl), native_run_count s h .keygen sk]
  simp only [liftM_map, bind_map_left, runResult, output, Nat.zero_add]
  apply bind_congr
  intro kg
  cases hk : kg.value with
  | none => simp [countFrom_pure]
  | some key =>
    rcases key with ⟨pk, cache⟩
    simp only [Option.map_some, output]
    simp only [countedTail, nativeTail, nativeRun, nativeImpl, SigGolf.Submission.interact, List.nil_append, QueryImpl.add_eq_hAdd]
    congr 1
    apply bind_congr
    rintro ⟨final, log⟩
    cases final <;> rfl

theorem game_rel (s : Legacy.Submission) (h : s.Admissible)
    (A : SigGolf.Adversary (sizes s.sizes)) :
    Rel (legacyGame s (adversary A) (rounds A))
      (countFrom SigGolf.hashCost ((submission s).game A) 0) WinRel := by
  rw [native_game_count s h]
  unfold legacyGame
  apply Rel.bind_eq
  intro sk
  apply Rel.bind_eq
  intro kg
  cases hk : kg.value with
  | none =>
    apply rel_false
    simp
  | some key =>
    rcases key with ⟨pk, cache⟩
    exact interaction_rel s h sk pk A (rounds A) (A pk cache) [] kg.hashCalls
      (depth_le_rounds A pk cache) (by simp [SigGolf.SigningLog.WithinLifetime])

theorem security (s : Legacy.Submission) (h : s.Admissible)
    (hs : s.Secure) : (submission s).Security := by
  intro A Q hQ
  have he := probEvent_countFrom_eq (roImpl SigGolf.Query (BitVec 256)) SigGolf.hashCost
    ((submission s).game A) ∅ (fun p => p.1 = true ∧ p.2 ≤ Q)
  have hp := Rel.probEvent_le_rev (roImpl SigGolf.Query (BitVec 256)) (game_rel s h A)
    (fun r => r.won = true ∧ r.hashCalls ≤ Q) (fun p => p.1 = true ∧ p.2 ≤ Q)
    (fun r p hr hp => by
      obtain ⟨hw, hc⟩ := hr hp.1
      exact ⟨hw, by simpa only [hc] using hp.2⟩) ∅
  calc
    _ = Pr[fun p : Bool × Nat => p.1 = true ∧ p.2 ≤ Q |
        (simulateQ (roImpl SigGolf.Query (BitVec 256))
          (countFrom SigGolf.hashCost ((submission s).game A) 0)).run' ∅] := he.symm
    _ ≤ Pr[fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q |
        (simulateQ (roImpl SigGolf.Query (BitVec 256))
          (legacyGame s (adversary A) (rounds A))).run' ∅] := hp
    _ ≤ _ := hs (adversary A) (rounds A) Q hQ

end SigGolfCandidate.Transport
