import SigGolfCandidate.Transport

set_option backward.isDefEq.respectTransparency false

namespace SigGolfCandidate.Transport
open OracleComp OracleSpec

abbrev AdversaryState (sz : Legacy.Sizes) :=
  OracleComp (SigGolf.World + SigGolf.SigningSpec (sizes sz)) (Option (SigGolf.Forgery (sizes sz)))

def forgery {sz : Legacy.Sizes} : SigGolf.Forgery (sizes sz) → Legacy.Forgery sz
  | .witness m w => .witness m w
  | .signature m sig => .signature m sig

/-- A native finite oracle computation, viewed as the old interactive state machine. -/
def adversaryStep (sz : Legacy.Sizes) : AdversaryState sz → Legacy.Action sz (AdversaryState sz)
  | .pure none => .step (.pure none)
  | .pure (some f) => .submit (forgery f)
  | .queryBind (.inl (.inl n)) k => .sample n k
  | .queryBind (.inl (.inr q)) k => .hash q k
  | .queryBind (.inr req) k => .sign ⟨req.message, req.cache⟩ k

def adversary {sz : Legacy.Sizes} (a : SigGolf.Adversary (sizes sz)) : Legacy.Adversary sz :=
  ⟨AdversaryState sz, a, adversaryStep sz⟩

instance adversaryRangeFintype (sz : Legacy.Sizes)
    (t : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Domain) :
    Fintype ((SigGolf.World + SigGolf.SigningSpec (sizes sz)).Range t) := by
  rcases t with (n | q) | r <;> dsimp <;> infer_instance

/-- All response types are finite, so every native adversary has a finite maximum depth. -/
noncomputable def depth {sz : Legacy.Sizes} (a : AdversaryState sz) : Nat :=
  a.recOn (fun _ => 1) (fun _ _ ih => 1 + Finset.univ.sup ih)

@[simp] theorem depth_pure {sz : Legacy.Sizes} (f : Option (SigGolf.Forgery (sizes sz))) :
    depth (sz := sz) (.pure f) = 1 := rfl

theorem depth_query {sz : Legacy.Sizes}
    (t : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Domain)
    (k : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Range t → AdversaryState sz) :
    depth (.queryBind t k) = 1 + Finset.univ.sup (fun u => depth (k u)) := rfl

theorem depth_lt {sz : Legacy.Sizes}
    (t : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Domain)
    (k : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Range t → AdversaryState sz)
    (u : (SigGolf.World + SigGolf.SigningSpec (sizes sz)).Range t) :
    depth (k u) < depth (.queryBind t k) := by
  rw [depth_query]
  have := Finset.le_sup (f := fun u => depth (k u)) (Finset.mem_univ u)
  omega

noncomputable def rounds {sz : Legacy.Sizes} (a : SigGolf.Adversary (sizes sz)) : Nat :=
  Finset.univ.sup fun pk => Finset.univ.sup fun cache => depth (a pk cache)

theorem depth_le_rounds {sz : Legacy.Sizes} (a : SigGolf.Adversary (sizes sz))
    (pk : SigGolf.PublicKey) (cache : SigGolf.Bytes (sizes sz).cache) :
    depth (a pk cache) ≤ rounds a := by
  exact (Finset.le_sup (f := fun cache => depth (a pk cache)) (Finset.mem_univ cache)).trans
    (Finset.le_sup (f := fun pk => Finset.univ.sup fun cache => depth (a pk cache)) (Finset.mem_univ pk))

end SigGolfCandidate.Transport
