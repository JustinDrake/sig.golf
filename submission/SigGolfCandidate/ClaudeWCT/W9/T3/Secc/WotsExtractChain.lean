import SigGolfCandidate.T3.Secc.WotsExtractChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layer
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.ExtractSrc

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry chainRow low SeenRow encodingRow entriesOf)
open SigGolfCandidate.T3M (chainP chainInputP)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono height_le' chainCount_le'
  width_le' chainP_join chainP_frontier chainP_row chain_seen)
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem structuralHitSrc_mono {answers : Answers} {trace trace' : List Entry} (h : StructuralHitSrc answers trace)
    (hsub : ∀ e ∈ trace, e ∈ trace') : StructuralHitSrc answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hs, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hs, hc, hh⟩
theorem otherChainRow_intro {answers : Answers} {input : HashInput} {a : ChainAddr} {step : Nat}
    (hpos : Extract.posOf input = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
    (h : (∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step) : OtherChainRow answers input :=
  ⟨a, step, hpos, h⟩
theorem structuralHit_intro {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : HashHit answers (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : StructuralClass answers actual pos) : StructuralHitSrc answers (entriesOf answers qs) :=
  ⟨pos, actual, _, mem_entriesOf hq,
    Extract.posOf_key_eq hb (by rw [hsame, Extract.hdrBlock_honestInput, Extract.Pos.canonicalHeader_eq hb]),
    hb, hsrc, hclass, hhit⟩
theorem chain_bounded {a : ChainAddr} {step : Nat} (hsrc : SourceChain a)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain) :
    (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).Bounded := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := hsrc
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' _)
  have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (width_le' _ _)
  have hcc := chainCount_le' a.key.lay
  refine ⟨by omega, by omega, by omega, by omega⟩
theorem structuralHit_chain {answers : Answers} {qs : List Spec.Domain} (a : ChainAddr) (step : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (v : Digest)
    (hq : (.inl (.inr (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) : Spec.Domain) ∈ qs)
    (hsrc : SourceChain a) (hstep : step + 1 < 2 ^ width a.key.lay a.chain)
    (hhit : HashHit answers (Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
      (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v))
    (hclass : ¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ step) : StructuralHitSrc answers (entriesOf answers qs) := by
  have hb := chain_bounded hsrc hstep
  have hhdr : Extract.canonicalHeader (Extract.hdrBlock
      (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) =
      bytesLE 16 (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).hdr := by
    rw [← pad64_chainInputP, Extract.hdrBlock_chainInputP, Extract.canonicalHeader_chainHeaderP]
    exact Extract.Pos.canonicalHeader_eq
      (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb
  have hpos := Extract.posOf_key_eq (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb hhdr
  refine ⟨_, _, _, mem_entriesOf hq, hpos, hb, ⟨hsrc.1.1, hsrc.1.2, hsrc.2, hstep⟩, ?_, hhit⟩
  refine otherChainRow_intro hpos ?_
  rcases hclass with hpad | hdepth
  · refine Or.inl fun value he => hpad ?_
    rw [chainRow, chainInput_eq_zero _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2] at he
    have hh := chainInputP_headerPad_eq he
    obtain ⟨h0, _, h1, _⟩ := chainInputP_fields he
    exact ⟨h0, h1, hh⟩
  · exact Or.inr hdepth
theorem chain_cases (answers : Answers) (a : ChainAddr) (start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest)
    (qs : List Spec.Domain)
    (hsub : ∀ q ∈ queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value),
      q ∈ qs)
    (hsrc : SourceChain a) (hcount : start + count < 2 ^ width a.key.lay a.chain)
    (hdepth : depth answers a ≤ start + count)
    (reaches : evalWithAnswerFn answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) =
      honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + count)) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
      ((depth answers a ≤ start →
          value = honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
            (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) start ∧
          (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∧
        (start < depth answers a →
          ContactAt answers (entriesOf answers qs) a ∧
            (start + 2 ≤ depth answers a → TwoEdgeAt answers (entriesOf answers qs) a))) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have ht := hsrc.1.1
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' a.key.lay)
  have hl : a.key.leaf < 4096 := lt_of_lt_of_le hsrc.1.2 hh
  have hi : a.chain < 64 := lt_of_lt_of_le hsrc.2 (by have := chainCount_le' a.key.lay; omega)
  have hc8 : start + count ≤ 8 := by
    have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by decide) (width_le' a.key.lay a.chain)
    omega
  have hit : ∀ step, step < count →
      .inl (.inr (pad64 (pathInput answers
        (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) →
      HashHit answers
        (pad64 (chainInput a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
            (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))))
        (pad64 (pathInput answers
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step)) →
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ start + step) → False := by
    intro step hstep hq hhit hclass
    apply hS
    simp only [pathInput, chainPathInput, pad64_chainInputP] at hq hhit
    exact structuralHit_chain a (start + step) pad0 pad1 headerPad _ (hsub _ hq) hsrc (by omega) hhit hclass
  constructor
  · intro hle
    rcases chainP_extract answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches with
      ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
    · exact ⟨hval, hpads⟩
    · exact (hit step hstep hq hhit (Or.inr (by omega))).elim
  · intro hlt
    rcases chainP_frontier answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches (depth answers a) hlt hdepth with
      ⟨step, hstep, hq, hhit, hclass⟩ | ⟨h0, h1, hh, hval⟩
    · exact (hit step hstep hq hhit hclass).elim
    · subst h0 h1 hh
      obtain ⟨⟨x, hx⟩, htwo⟩ := chain_seen answers a start count value _ qs ht hl hi hc8 hsub (depth answers a) hlt hdepth hval
      exact ⟨⟨by omega, x, hx⟩, fun h2 => ⟨by omega, htwo h2⟩⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
