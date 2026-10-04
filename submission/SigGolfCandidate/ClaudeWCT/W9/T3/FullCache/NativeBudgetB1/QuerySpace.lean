import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.PairRows
import SigGolfCandidate.T3.FullCache.NativeBudget

section


namespace ClaudeWCT.W9.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial digestTrial_injective
  digestTrial_length V_publicSearch public_randomOracle)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def digestDecode (answer : HashOutput) : Option HashOutput :=
  if ClaudeWCT.WCT9.admissible answer then some answer else none
theorem digestDecode_eq_none_iff (value : HashOutput) :
    digestDecode value = none ↔ ClaudeWCT.WCT9.admissible value = false := by
  simp [digestDecode]
theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter, ClaudeWCT.WCT9.digestSearch rho message counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (digestTrial rho message) digestDecode
        (fun c output => pure (BitVec.ofNat 32 c, output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.digestSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        digest, publicHash, bind_assoc, pure_bind, digestTrial, digestDecode]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem digestSearch_failure (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass digestDecode ^ fuel := by
  rw [digestSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh
theorem V_digestSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (rho : Digest) (message : Message)
    (hstep : z * (SphincsSecurity.Completeness.failMass digestDecode * b +
      (1 - SphincsSecurity.Completeness.failMass digestDecode)) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    V secret z (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ b := by
  rw [digestSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh
end ClaudeWCT.W9.T3.Sampling
end

section

namespace ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling (digestTrial)
open SigGolfCandidate.T3.QuerySpace (DigestFamily digestTrial_coordinates)
open ClaudeWCT.W9.T3.PairRows (pairTrial pairTrial_coordinates pairTrial_ne_digestTrial pairTrial_length)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev EncodingFamilyBC := Layer × Fin (2 ^ 31) × Fin 4096 × Digest × Digest
theorem encodingFamilyBC_card : Fintype.card EncodingFamilyBC = 2 ^ 301 := by
  set_option exponentiation.threshold 512 in
  norm_num [EncodingFamilyBC, Layer, Fintype.card_prod, Fintype.card_bitVec]
abbrev EncodingKeyBC := EncodingFamilyBC × Fin (2 ^ 22)
abbrev DigestKey := DigestFamily × Fin (2 ^ 21)
abbrev SearchKey := EncodingKeyBC ⊕ DigestKey
def encodingQueryBC (key : EncodingKeyBC) : HashInput :=
  pairTrial key.1.1 key.1.2.1 key.1.2.2.1 key.1.2.2.2.1 key.1.2.2.2.2 key.2
def digestQuery (key : DigestKey) : HashInput := digestTrial key.1.1 key.1.2 key.2
def searchQuery : SearchKey → HashInput := Sum.elim encodingQueryBC digestQuery
theorem encodingQueryBC_injective : Function.Injective encodingQueryBC := by
  rintro ⟨⟨lay, tree, leaf, left, right⟩, counter⟩ ⟨⟨lay', tree', leaf', left', right'⟩, counter'⟩ he
  obtain ⟨a, b, c, d, e, f⟩ := pairTrial_coordinates
    (by have := tree.isLt; omega) (by have := tree'.isLt; omega)
    (by have := leaf.isLt; omega) (by have := leaf'.isLt; omega)
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have b := Fin.ext b
  have c := Fin.ext c
  have f := Fin.ext f
  cases a; cases b; cases c; cases d; cases e; cases f; rfl
theorem digestQuery_injective : Function.Injective digestQuery := by
  rintro ⟨⟨rho, msg⟩, counter⟩ ⟨⟨rho', msg'⟩, counter'⟩ he
  obtain ⟨a, b, c⟩ := digestTrial_coordinates
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have c := Fin.ext c
  cases a; cases b; cases c; rfl
theorem searchQuery_injective : Function.Injective searchQuery := by
  intro left right he
  cases left with
  | inl l =>
    cases right with
    | inl r => exact congrArg Sum.inl (encodingQueryBC_injective he)
    | inr r => exact False.elim (pairTrial_ne_digestTrial _ _ _ _ _ _ _ _ _ he)
  | inr l =>
    cases right with
    | inl r => exact False.elim (pairTrial_ne_digestTrial _ _ _ _ _ _ _ _ _ he.symm)
    | inr r => exact congrArg Sum.inr (digestQuery_injective he)
theorem searchQuery_length (key : SearchKey) : (searchQuery key).length = 64 := by
  cases key with
  | inl key => exact pairTrial_length _ _ _ _ _ _
  | inr key => exact SigGolfCandidate.T3.Sampling.digestTrial_length _ _ _
end ClaudeWCT.W9.T3.QuerySpace
end
