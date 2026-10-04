import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsStructuralFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTwoEdge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingMatch
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportCount
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportShort
import SigGolfCandidate.T3.Secc.WotsSmallContract
import SigGolfCandidate.T3.Secc.WotsClasses

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem posOf_chainRow (a : ChainAddr) (s : Nat) (v : Digest) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 4096) (hc : a.chain < 64) (hs : s < 8) :
    Extract.posOf (chainRow a s v) = some (.chain a.key.lay a.key.tree a.key.leaf a.chain s) :=
  Extract.posOf_eq ⟨htree, hleaf, hc, hs⟩
    (show Extract.hdrBlock (chainRow a s v) =
        bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) from
      SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_chainRow a s v)
end SmallA
open SigGolfCandidate.T3.Security.Wots.SmallA (chainRow_ne_digest sourceChain_bounds)
namespace SmallA
theorem chainRow_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : BitVec 96) : chainRow a s v ≠ encRow L m c pad := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h1 : ClaudeWCT.W9.T3M.Extract.hdrBlock (chainRow a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_chainRow a s v
  rw [h1, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hb)
theorem encRow_ne_digest (L : LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : BitVec 96) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (header 12 0 0 0 c'.toNat) :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  exact SigGolfCandidate.T3.Security.Wots.Mask.header_ne_of_tag (by decide) (bytesLE_injective hb)
end SmallA
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRow_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRow_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
    have h7 := Mask.depth_le_seven T a
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change OtherChainRow T (chainRow a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
def NonChainPos : Extract.Pos → Prop
  | .chain _ _ _ _ _ => False
  | _ => True
def FtsPos : Extract.Pos → Prop
  | .wctChain _ _ _ _ _ => True
  | .wctLeaf _ _ _ => True
  | .wctNode _ _ _ _ => True
  | .forest _ => True
  | _ => False
theorem FtsPos.nonChain {p : Extract.Pos} (h : FtsPos p) : NonChainPos p := by
  cases p <;> first | exact h.elim | trivial
theorem otherQuery_of_nonChain (T : Answers) {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p)
    (hb : p.Bounded) (hsrc : WotsExtract.PosSource p) (hp : NonChainPos p) :
    OtherQuery T (.inl (.inr x)) := by
  refine ⟨p, hpos, hb, hsrc, ?_⟩
  cases p <;> first | exact hp.elim | trivial
theorem ftsRow_not_prefixRow (T : Answers) {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p)
    (hp : FtsPos p) : ¬PrefixRow T (.inl (.inr x)) := by
  rintro ⟨a, ha, s, v, hs, rfl⟩
  obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
  have h7 := Mask.depth_le_seven T a
  rw [SmallA.posOf_chainRow a s v htree hleaf hc (by omega)] at hpos
  cases hpos
  exact hp
theorem ftsRow_not_encodingRow (T : Answers) {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) :
    ¬EncodingRow T (.inl (.inr x)) := by
  rintro ⟨L, m, c, pad, -, rfl⟩
  have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _
  rw [hnone] at hpos
  cases hpos
theorem ftsRow_not_digest {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) :
    ¬IsDigestQuery (.inl (.inr x)) := by
  rintro ⟨rho, m, c, he⟩
  have hx : x = pad64 (digestInput rho m c) := by injection he with h; injection h
  rw [hx, Structural.posOf_digest] at hpos
  cases hpos
theorem fts_tags_disjoint {tag : Nat} (h : tag = 5 ∨ tag = 6 ∨ tag = 11 ∨ tag = 15) :
    tag % 256 ≠ 1 ∧ tag % 256 ≠ 4 ∧ tag % 256 ≠ 12 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent PrefixRow := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [PrefixRow, PrefixRowAt, hdepth]
  · exact Iff.rfl
theorem shortCongruent_otherQuery : ShortCongruent OtherQuery := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  have hcls : ∀ x p, StructuralClass A x p ↔ StructuralClass T x p := by
    intro x p
    cases p <;> simp only [StructuralClass, OtherChainRow, hdepth]
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [OtherQuery, OtherInput, hcls]
  · exact Iff.rfl
noncomputable def refExpect (adversary : AdversaryP) (q : Nat) (f : RefSample → Nat) : ENNReal :=
  ∑' s, referenceExperiment adversary q s * (f s : ENNReal)
theorem prefixClassCount_eq (s : RefSample) : prefixClassCount s = refCount PrefixRow s := rfl
theorem otherCount_eq (s : RefSample) : otherCount s = refCount OtherQuery s := rfl
theorem reference_class_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    refExpect adversary q prefixClassCount + refExpect adversary q encodingCount + refExpect adversary q otherCount +
      SeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow shortCongruent_otherQuery prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input => prefixRow_digest_disjoint z.2 input)
    (fun z input => encodingRow_digest_disjoint z.2 input) (fun z input => otherQuery_digest_disjoint z.2 input)
end ClaudeWCT.W9.T3.Security.Wots
