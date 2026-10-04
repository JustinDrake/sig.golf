import SigGolfCandidate.T3.Secc.WotsSmallContract
import SigGolfCandidate.T3.Secc.WotsTwoEdge
import SigGolfCandidate.T3.Secc.WotsEncodingMatch
import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.T3.Secc.WotsTransportCount

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRow (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRow a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  chainInput_header _ _ _ _ _ _
theorem hdrBlock_encodingRow (L : LeafAddr) (m : Digest) (c : BitVec 32) :
    Extract.hdrBlock (encodingRow L m c) = bytesLE 16 (header 4 L.lay.val L.tree 0 L.leaf) := by
  unfold encodingRow encodingInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem hdrBlock_digest (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = bytesLE 16 (header 12 0 0 0 c.toNat) := by
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem chainRow_ne_encodingRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : Digest) (c : BitVec 32) :
    chainRow a s v ≠ encodingRow L m c := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRow, hdrBlock_encodingRow] at hb
  exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hb)
theorem chainRow_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRow a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRow, hdrBlock_digest] at hb
  exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hb)
theorem encodingRow_ne_digest (L : LeafAddr) (m : Digest) (c : BitVec 32) (rho : Digest) (m' : Message)
    (c' : BitVec 32) : encodingRow L m c ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_encodingRow, hdrBlock_digest] at hb
  exact Mask.header_ne_of_tag (by decide) (bytesLE_injective hb)
theorem posOf_chainRow (a : ChainAddr) (s : Nat) (v : Digest) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 4096) (hc : a.chain < 64) (hs : s < 8) :
    Extract.posOf (chainRow a s v) = some (.chain a.key.lay a.key.tree a.key.leaf a.chain s) :=
  Extract.posOf_eq ⟨htree, hleaf, hc, hs⟩ (by rw [hdrBlock_chainRow]; rfl)
theorem sourceChain_bounds {a : ChainAddr} (ha : WotsExtract.SourceChain a) :
    a.key.tree < 2 ^ 31 ∧ a.key.leaf < 4096 ∧ a.chain < 64 := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega)
  have hcc := Mask.chainCount_le a.key.lay
  refine ⟨by omega, by omega, by omega⟩
end SmallA
open SmallA
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, hx⟩ := hE
    exact chainRow_ne_encodingRow a s v L m c hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRow_ne_digest a s v rho m c hx.symm
theorem encodingRow_digest_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', hx⟩ := hE
  exact encodingRow_ne_digest L m' c' rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encodingRow L m c) = none := Structural.posOf_encoding _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
    have h7 := Mask.depth_le_seven T a
    have hrow := posOf_chainRow a s v htree hleaf hc (by omega)
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
theorem shortCongruent_prefixRow : ShortCongruent PrefixRow := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [PrefixRow, PrefixRowAt, hdepth]
  · exact Iff.rfl
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
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
theorem encodingCount_eq (s : RefSample) : encodingCount s = refCount EncodingRow s := rfl
theorem otherCount_eq (s : RefSample) : otherCount s = refCount OtherQuery s := rfl
theorem reference_class_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    refExpect adversary q prefixClassCount + refExpect adversary q encodingCount + refExpect adversary q otherCount +
      SeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow shortCongruent_otherQuery prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input => prefixRow_digest_disjoint z.2 input)
    (fun z input => encodingRow_digest_disjoint z.2 input) (fun z input => otherQuery_digest_disjoint z.2 input)
end SigGolfCandidate.T3.Security.Wots
