import SigGolfCandidate.T3.Secc.WotsTransportShort
import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
theorem forestPk_respects (index : Nat) (roots : List Digest) (hlen : roots.length ≤ 200) :
    ShortRespects (ClaudeWCT.WCT9.forestPk index roots) :=
  ClaudeWCT.WCT9.Wots.Ref.forestPk_respects index roots hlen
theorem signForest_respects (index : Nat) (output : HashOutput) :
    ShortRespects (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.Ref.signForest_respects index output
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem honestForest_short (index : Nat) : Extract.honestForest A index = Extract.honestForest T index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq))
theorem ftsLevels_short (index coord : Nat) (hc : coord < 9) :
    Extract.ftsLevels A index coord = Extract.ftsLevels T index coord := by
  unfold Extract.ftsLevels
  have h1 := Extract.ftsNodes_eq A index ⟨coord, hc⟩
  have h2 := Extract.ftsNodes_eq T index ⟨coord, hc⟩
  have h3 := ClaudeWCT.WCT9.Wots.coordNodes_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩
  rw [show Extract.ftsNodes A index coord = Extract.ftsNodes T index coord from h1.trans (h3.trans h2.symm)]
theorem ftsRootsHonest_short (index : Nat) : Extract.ftsRootsHonest A index = Extract.ftsRootsHonest T index := by
  rw [Extract.ftsRootsHonest_eq, Extract.ftsRootsHonest_eq]
  exact congrArg List.ofFn (funext fun coord => ClaudeWCT.WCT9.Wots.coordinateRoot_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) coord)
theorem wctValue_short (index coord child chain step : Nat) (hc : coord < 9) (hch : child < 128) (ht : chain < 7)
    (hs : step ≤ 3) :
    Extract.wctValue A index coord child chain step = Extract.wctValue T index coord child chain step :=
  ClaudeWCT.WCT9.Wots.ftsChainValue_congr (index := index) (T := A) (T' := T)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩ ⟨child, hch⟩ ⟨chain, ht⟩ step hs
theorem wctEnds_short (index coord child : Nat) (hc : coord < 9) (hch : child < 128) :
    Extract.wctEnds A index coord child = Extract.wctEnds T index coord child := by
  unfold Extract.wctEnds
  exact congrArg List.ofFn (funext fun t => wctValue_short hAT index coord child t.val 3 hc hch t.isLt le_rfl)
theorem leafMsg_short (L : LeafAddr) : leafMsg A L = leafMsg T L := by
  unfold leafMsg
  split_ifs
  · unfold Extract.honestRoot
    rw [builtTree_short hAT]
  · exact honestForest_short hAT _
theorem referenceSearch_short (L : LeafAddr) : referenceSearch A L = referenceSearch T L := by
  unfold referenceSearch
  rw [leafMsg_short hAT]
  exact counterSearch_respects _ _ _ _ _ _ A T hAT
theorem referenceDigits_short (L : LeafAddr) : referenceDigits A L = referenceDigits T L := by
  unfold referenceDigits
  rw [referenceSearch_short hAT]
theorem depth_short (a : ChainAddr) : depth A a = depth T a := by
  unfold depth
  rw [referenceDigits_short hAT]
theorem frontierValue_short (a : ChainAddr) : frontierValue A a = frontierValue T a := by
  unfold frontierValue
  rw [depth_short hAT, leafSeed_short hAT]
  exact honestChainValue_short hAT _ _ _ _ _ _
theorem referenceInput_short (L : LeafAddr) : referenceInput A L = referenceInput T L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, leafMsg_short hAT]
theorem honestInput_short (position : Extract.Pos) (hb : position.Bounded) :
    Extract.honestInput A position = Extract.honestInput T position := by
  cases position with
  | chain lay tree leaf i step =>
      simp only [Extract.honestInput]
      rw [leafSeed_short hAT, honestChainValue_short hAT]
  | leaf lay tree leaf =>
      simp only [Extract.honestInput]
      rw [List.map_congr_left (fun i _ => leafEnd_short hAT lay tree leaf i)]
  | node lay tree level node =>
      simp only [Extract.honestInput]
      rw [builtTree_short hAT]
  | forest index =>
      simp only [Extract.honestInput]
      rw [ftsRootsHonest_short hAT]
  | wctChain index coord child t step =>
      obtain ⟨-, hc, hch, ht, hs⟩ := hb
      simp only [Extract.honestInput]
      rw [wctValue_short hAT index coord child t step hc hch ht (by omega)]
  | wctLeaf index coord child =>
      obtain ⟨-, hc, hch⟩ := hb
      simp only [Extract.honestInput]
      rw [wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level nd =>
      obtain ⟨-, hc, -, -⟩ := hb
      simp only [Extract.honestInput]
      rw [ftsLevels_short hAT index coord hc]
end objects
theorem honestInput_length (answers : Answers) (position : Extract.Pos) :
    (Extract.honestInput answers position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step =>
      apply short_of_le
      rw [chainInput_length]; omega
  | leaf lay tree leaf =>
      apply short_of_le
      simp only [Extract.leafInput, Extract.listInput_length', List.length_drop, List.length_map, List.length_range]
      have := chainCount_le lay
      omega
  | node lay tree level node =>
      apply short_of_le
      simp [nodeInputP]
  | forest index =>
      apply short_of_le
      rw [Extract.forestInput, Extract.listInput_length']
      simp only [List.length_drop, Extract.ftsRootsHonest_length]
      omega
  | wctChain index coord child t step =>
      apply short_of_le
      rw [ClaudeWCT.WCT9.chainInput_length]; omega
  | wctLeaf index coord child =>
      apply short_of_le
      simp only [Extract.wctLeafInput, Extract.listInput_length', List.length_drop, Extract.wctEnds,
        List.length_ofFn]
      omega
  | wctNode index coord level node =>
      apply short_of_le
      simp [nodeInputP]
theorem WotsPrimitive.transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : WotsPrimitive A trace) : WotsPrimitive T trace := by
  have hdepth : depth A = depth T := funext (depth_short hAT)
  have hfront : frontierValue A = frontierValue T := funext (frontierValue_short hAT)
  have hrefi : referenceInput A = referenceInput T := funext (referenceInput_short hAT)
  have hrefd : referenceDigits A = referenceDigits T := funext (referenceDigits_short hAT)
  rcases h with ⟨L, hL⟩ | hS | ⟨a, ha⟩ | ⟨a, b, hab, ha, hb⟩ | ⟨a, ha, hc⟩
  · refine Or.inl ⟨L, ?_⟩
    simpa only [EncodingMatchAt, hrefi, hrefd] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hclass, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, ?_, ?_⟩
    · cases position <;> simpa only [StructuralClass, OtherChainRow, hdepth] using hclass
    · rw [← honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem,
        ← hAT.public _ (honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, ?_⟩))
    simpa only [TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, ?_, ?_⟩)))
    · simpa only [ContactAt, hdepth, hfront] using ha
    · simpa only [ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ?_, ?_⟩)))
    · simpa only [MarkerAt, hrefi, hrefd] using ha
    · simpa only [ContactAt, hdepth, hfront] using hc
end ClaudeWCT.W9.T3.Security.Wots.Ref
