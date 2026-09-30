import SigGolfCandidate.Transport.Adversary
import SigGolfCandidate.Transport.Counting

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec Bridge

set_option allowUnsafeReducibility true in
attribute [local reducible] submission sizes

abbrev NativeSpec (sz : Legacy.Sizes) := SigGolf.World + SigGolf.SigningSpec (sizes sz)

def nativeImpl (s : Legacy.Submission) (sk : SigGolf.SecretKey) :
    QueryImpl (NativeSpec s.sizes)
      (WriterT (SigGolf.SigningLog (sizes s.sizes)) (OracleComp SigGolf.World)) :=
  QueryImpl.add (QueryImpl.ofLift SigGolf.World
    (WriterT (SigGolf.SigningLog (sizes s.sizes)) (OracleComp SigGolf.World)))
    ((submission s).signingOracle sk)

def nativeRun (s : Legacy.Submission) (sk : SigGolf.SecretKey) {α : Type}
    (a : OracleComp (NativeSpec s.sizes) α) :
    OracleComp SigGolf.World (α × SigGolf.SigningLog (sizes s.sizes)) :=
  (simulateQ (nativeImpl s sk) a).run

@[simp] theorem nativeRun_pure (s : Legacy.Submission) (sk : SigGolf.SecretKey) {α : Type} (a : α) :
    nativeRun s sk (pure a) = pure (a, []) := rfl

theorem nativeRun_world (s : Legacy.Submission) (sk : SigGolf.SecretKey) {α : Type}
    (t : SigGolf.World.Domain) (k : SigGolf.World.Range t → OracleComp (NativeSpec s.sizes) α) :
    nativeRun s sk (((NativeSpec s.sizes).query (.inl t) : OracleComp (NativeSpec s.sizes) _) >>= k) =
      (SigGolf.World.query t : OracleComp SigGolf.World _) >>= fun u => nativeRun s sk (k u) := by
  simp only [nativeRun, nativeImpl, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : (nativeImpl s sk (.inl t)).run =
      (fun a => (a, [])) <$> (SigGolf.World.query t : OracleComp SigGolf.World _) := rfl
  dsimp only [nativeImpl] at e
  rw [e, bind_map_left]
  simp

theorem nativeRun_sign (s : Legacy.Submission) (sk : SigGolf.SecretKey) {α : Type}
    (req : SigGolf.SigningRequest (sizes s.sizes))
    (k : Option (SigGolf.Bytes (sizes s.sizes).signature) → OracleComp (NativeSpec s.sizes) α) :
    nativeRun s sk (((NativeSpec s.sizes).query (.inr req) : OracleComp (NativeSpec s.sizes) _) >>= k) =
      (liftM ((submission s).run .sign (sk, req.cache, req.message)) : OracleComp SigGolf.World _) >>= fun r =>
        (fun p => (p.1, [⟨req, r.output⟩] ++ p.2)) <$> nativeRun s sk (k r.output) := by
  simp [nativeRun, nativeImpl, SigGolf.Submission.signingOracle, WriterT.run_bind, QueryImpl.add,
    bind_assoc]

/-- The exact native game after key generation, with an existing signing-log prefix. -/
def nativeTail (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (a : AdversaryState s.sizes) (log : SigGolf.SigningLog (sizes s.sizes)) :
    OracleComp SigGolf.World Bool := do
  let (final, extra) ← nativeRun s sk a
  let some f := final | return false
  let forged ← liftM ((submission s).checkForgery pk (log ++ extra) f)
  return decide ((log ++ extra).WithinLifetime) && forged

theorem nativeTail_world (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (t : SigGolf.World.Domain) (k : SigGolf.World.Range t → AdversaryState s.sizes)
    (log : SigGolf.SigningLog (sizes s.sizes)) :
    nativeTail s sk pk (((NativeSpec s.sizes).query (.inl t) : OracleComp (NativeSpec s.sizes) _) >>= k) log =
      (SigGolf.World.query t : OracleComp SigGolf.World _) >>= fun u => nativeTail s sk pk (k u) log := by
  unfold nativeTail
  rw [nativeRun_world]
  simp only [bind_assoc]

theorem nativeTail_sign (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (req : SigGolf.SigningRequest (sizes s.sizes))
    (k : Option (SigGolf.Bytes (sizes s.sizes).signature) → AdversaryState s.sizes)
    (log : SigGolf.SigningLog (sizes s.sizes)) :
    nativeTail s sk pk (((NativeSpec s.sizes).query (.inr req) : OracleComp (NativeSpec s.sizes) _) >>= k) log =
      (liftM ((submission s).run .sign (sk, req.cache, req.message)) : OracleComp SigGolf.World _) >>= fun r =>
        nativeTail s sk pk (k r.output) (log ++ [⟨req, r.output⟩]) := by
  unfold nativeTail
  rw [nativeRun_sign]
  simp [bind_assoc, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem nativeTail_over_lifetime (s : Legacy.Submission) (sk : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (a : AdversaryState s.sizes) (log : SigGolf.SigningLog (sizes s.sizes))
    (hl : SigGolf.LIFETIME < log.length) :
    (fun _ => false) <$> nativeTail s sk pk a log = nativeTail s sk pk a log := by
  unfold nativeTail
  simp only [map_bind]
  apply bind_congr
  rintro ⟨final, extra⟩
  cases final with
  | none => rfl
  | some f =>
    have hn : ¬(log ++ extra).WithinLifetime := by
      simp only [SigGolf.SigningLog.WithinLifetime, List.length_append]
      omega
    simp only [hn, decide_false, Bool.false_and, map_bind, map_pure]

end SigGolfCandidate.Transport
