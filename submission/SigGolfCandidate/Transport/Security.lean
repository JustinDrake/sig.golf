import SigGolfCandidate.Transport.Game
import SigGolfCandidate.Transport.Transcript

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec OracleComp.EvalDist Bridge

set_option allowUnsafeReducibility true in
attribute [local reducible] submission sizes program input output Legacy.Input Legacy.Output
  SigGolf.Input SigGolf.Output

def countedTail (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (a : AdversaryState s.sizes) (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat) :=
  countFrom SigGolf.hashCost (nativeTail s sk pk a log) c

def WinRel (old : Legacy.AttackResult) (new : Bool × Nat) : Prop :=
  new.1 = true → old.won = true ∧ old.hashCalls = new.2

theorem countedTail_none (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat) :
    countedTail s sk pk (pure none) log c = pure (false, c) := by
  simp [countedTail, nativeTail, countFrom_pure]

theorem countedTail_some (s : Legacy.Submission) (h : s.Admissible)
    (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (f : SigGolf.Forgery (sizes s.sizes)) (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat)
    (hl : log.WithinLifetime) :
    countedTail s sk pk (pure (some f)) log c =
      (fun r => (r.won, r.hashCalls)) <$>
        (liftM (s.checkForgery pk (transcript log c) (forgery f)) : OracleComp SigGolf.World _) := by
  unfold countedTail nativeTail
  simp only [nativeRun_pure, pure_bind, List.append_nil]
  rw [countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl), checkForgery_count s h]
  simp [liftM_map, bind_map_left, countFrom_pure, hl]

theorem countedTail_world (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (t : SigGolf.World.Domain) (k : SigGolf.World.Range t → AdversaryState s.sizes)
    (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat) :
    countedTail s sk pk (((NativeSpec s.sizes).query (.inl t) : OracleComp (NativeSpec s.sizes) _) >>= k) log c =
      (SigGolf.World.query t : OracleComp SigGolf.World _) >>= fun u =>
        countedTail s sk pk (k u) log (c + SigGolf.hashCost t) := by
  rw [countedTail, nativeTail_world, countFrom_query_bind]
  rfl

theorem countedTail_sign (s : Legacy.Submission) (h : s.Admissible)
    (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (req : SigGolf.SigningRequest (sizes s.sizes))
    (k : Option (SigGolf.Bytes (sizes s.sizes).signature) → AdversaryState s.sizes)
    (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat) :
    countedTail s sk pk (((NativeSpec s.sizes).query (.inr req) : OracleComp (NativeSpec s.sizes) _) >>= k) log c =
      (liftM (s.run .sign (sk, req.cache, req.message)) : OracleComp SigGolf.World _) >>= fun r =>
        countedTail s sk pk (k r.value) (log ++ [⟨req, r.value⟩]) (c + r.hashCalls) := by
  rw [countedTail, nativeTail_sign, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl),
    native_run_count s h .sign (sk, req.cache, req.message)]
  simp [liftM_map, bind_map_left, countedTail, runResult, output]

theorem countedTail_over_lifetime (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (a : AdversaryState s.sizes) (log : SigGolf.SigningLog (sizes s.sizes)) (c : Nat)
    (hl : SigGolf.LIFETIME < log.length) :
    (fun p => (false, p.2)) <$> countedTail s sk pk a log c = countedTail s sk pk a log c := by
  unfold countedTail
  have he := countFrom_map SigGolf.hashCost (nativeTail s sk pk a log) (fun _ : Bool => false) c
  rw [nativeTail_over_lifetime s sk pk a log hl] at he
  exact he.symm

lemma rel_false (q : OracleComp SigGolf.World (Bool × Nat)) (c : Nat)
    (hq : (fun p => (false, p.2)) <$> q = q) :
    Rel (pure (⟨false, c⟩ : Legacy.AttackResult)) q WinRel := by
  rw [← hq]
  refine ⟨(fun p => ⟨(⟨false, c⟩, (false, p.2)), by simp [WinRel]⟩) <$> q, ?_, ?_⟩
  · simpa only [Functor.map_map, Function.comp_def] using (Ext.leaf (⟨false, c⟩ : Legacy.AttackResult) q)
  · simp only [Functor.map_map, Function.comp_def]

theorem old_none (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (a : SigGolf.Adversary (sizes s.sizes)) (n : Nat) (T : Legacy.Transcript s.sizes) :
    s.interact (adversary a) sk pk n (pure none) T = pure ⟨false, T.hashCalls⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Legacy.Submission.interact, adversary, adversaryStep, OracleComp.pure_def] using ih

lemma Rel.probEvent_le_rev {ι σ α β : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    {R : α → β → Prop} {p : OracleComp spec α} {q : OracleComp spec β} (h : Rel p q R)
    (E₁ : α → Prop) (E₂ : β → Prop) (hE : ∀ a b, R a b → E₂ b → E₁ a) (st : σ) :
    Pr[E₂ | (simulateQ impl q).run' st] ≤ Pr[E₁ | (simulateQ impl p).run' st] := by
  obtain ⟨J, h1, h2⟩ := h
  rw [h1.probEvent_eq impl E₁ st, ← h2]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, probEvent_map]
  exact probEvent_mono fun z _ hz => hE _ _ z.1.2 hz

end SigGolfCandidate.Transport
