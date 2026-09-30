import SigGolfCandidate.Transport.Security

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec OracleComp.EvalDist Bridge

set_option allowUnsafeReducibility true in
attribute [local reducible] adversary submission sizes program input output Legacy.Input Legacy.Output
  SigGolf.Input SigGolf.Output

theorem interaction_rel (s : Legacy.Submission) (h : s.Admissible)
    (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (A : SigGolf.Adversary (sizes s.sizes))
    (n : Nat) (a : AdversaryState s.sizes)
    (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat)
    (hn : depth a ≤ n) (hl : log.WithinLifetime) :
    Rel (s.interact (adversary A) sk pk n a (transcript log c))
      (countedTail s sk pk a log c) WinRel := by
  induction n generalizing a log c with
  | zero =>
    cases a using OracleComp.casesOn <;> simp [depth, OracleComp.recOn] at hn
  | succ n ih =>
    cases a using OracleComp.casesOn with
    | pure f =>
      simp only [← OracleComp.pure_def (spec := NativeSpec s.sizes)]
      cases f with
      | none =>
        rw [old_none, countedTail_none]
        apply rel_false
        simp
      | some f =>
        rw [countedTail_some s h sk pk f log c hl]
        change Rel (liftM (s.checkForgery pk (transcript log c) (forgery f)) : OracleComp SigGolf.World _)
          ((fun r => (r.won, r.hashCalls)) <$>
            (liftM (s.checkForgery pk (transcript log c) (forgery f)) : OracleComp SigGolf.World _)) WinRel
        simpa only [id_map] using
          (Rel.of_map (R := WinRel)
            (liftM (s.checkForgery pk (transcript log c) (forgery f)) : OracleComp SigGolf.World _)
            id (fun r => (r.won, r.hashCalls)) (fun r hr => ⟨hr, rfl⟩))
    | queryBind t k =>
      have hkdepth (u) : depth (k u) ≤ n := by
        have := depth_lt t k u
        omega
      rcases t with (coin | hash) | req
      · change Rel _ (countedTail s sk pk
          (((NativeSpec s.sizes).query (.inl (.inl coin)) : OracleComp (NativeSpec s.sizes) _) >>= k) log c) _
        rw [countedTail_world]
        simp only [Legacy.Submission.interact, adversary, adversaryStep, SigGolf.hashCost, Nat.add_zero]
        apply Rel.bind_eq
        intro u
        exact ih (k u) log c (hkdepth u) hl
      · change Rel _ (countedTail s sk pk
          (((NativeSpec s.sizes).query (.inl (.inr hash)) : OracleComp (NativeSpec s.sizes) _) >>= k) log c) _
        rw [countedTail_world]
        simp only [Legacy.Submission.interact, adversary, adversaryStep, SigGolf.hashCost]
        apply Rel.bind_eq
        intro u
        exact ih (k u) log (c + 1) (hkdepth u) hl
      · change Rel _ (countedTail s sk pk
          (((NativeSpec s.sizes).query (.inr req) : OracleComp (NativeSpec s.sizes) _) >>= k) log c) _
        rw [countedTail_sign s h]
        simp only [Legacy.Submission.interact, adversary, adversaryStep, Legacy.Submission.signingOracle]
        by_cases hk : log.length < SigGolf.LIFETIME
        · have hk' : (transcript log c).signingRequests < Legacy.LIFETIME := hk
          rw [if_pos hk']
          apply Rel.bind_eq
          intro r
          rw [← transcript_record]
          let log' : SigGolf.SigningLog (sizes s.sizes) := log ++ [⟨req, r.value⟩]
          have hl' : log'.WithinLifetime := by
            simp only [log', SigGolf.SigningLog.WithinLifetime, List.length_append, List.length_singleton]
            omega
          have ht := ih (k r.value) log' (c + r.hashCalls) (hkdepth r.value) hl'
          simpa only [adversary, log'] using ht
        · have hk' : ¬(transcript log c).signingRequests < Legacy.LIFETIME := hk
          rw [if_neg hk']
          apply rel_false
          simp only [map_bind]
          apply bind_congr
          intro r
          apply countedTail_over_lifetime
          simp only [List.length_append, List.length_singleton]
          omega

end SigGolfCandidate.Transport
