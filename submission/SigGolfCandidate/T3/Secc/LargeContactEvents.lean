import SigGolfCandidate.T3.Secc.LargeContactChain
import SigGolfCandidate.T3.Secc.LargeContactWalk

/-!
# LR-34 (LR-5, 3/3a): W's events on the verifier's queries are not clear

`AllClear A K qs`: every public query of `qs` is `Clear` for the knowledge `K` (what a contact-free monitor leaves).
Each source-sized W event among the verifier's entries contradicts `AllClear` for the final knowledge:

* `contactAt_false` — `ContactAt a` (W): the row at the step below the frontier either carries the hidden child
  (never known: `frontier_child_unknown`) or hits the frontier label;
* `structuralHitSrc_false` — a structural hit is a hit;
* `encodingMatch_route_false` — an encoding match at a route leaf is an encoding hit (route leaves are G's
  presampled leaves, `CanonEncoding.route_source`);
* `wotsPrimitiveRoute_false` — all five events.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Every public query of a list is clear. -/
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → Clear A K X (A (.inl (.inr X)))

/-! ## Chain rows -/

theorem slotValue_block4_three (a b c d : Digest) : slotValue (block4 a b c d) 3 = d := by
  unfold slotValue block4
  have ha := bytesLE_length 16 a
  have hb := bytesLE_length 16 b
  have hc := bytesLE_length 16 c
  have hd := bytesLE_length 16 d
  rw [show 16 * 3 = (bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c).length by simp [ha, hb, hc]]
  rw [List.drop_left]
  rw [show (bytesLE 16 d).take 16 = bytesLE 16 d from List.take_of_length_le (by rw [hd])]
  exact Correctness.readDigest_bytesLE d

theorem chainRow_block4 (a : Wots.ChainAddr) (s : Nat) (v : Digest) :
    Wots.chainRow a s v = block4 0 (header 1 a.key.lay.val a.key.tree (s + 256 * a.chain) a.key.leaf) 0 v := by
  unfold Wots.chainRow
  rw [chainInput_eq_zero, chainInputP_eq_block4]

theorem slotValue_chainRow (a : Wots.ChainAddr) (s : Nat) (v : Digest) : slotValue (Wots.chainRow a s v) 3 = v := by
  rw [chainRow_block4, slotValue_block4_three]

theorem chainCount_le58 (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide

/-- The G address of a source-sized W chain address. -/
def gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : ChainGraph.Address :=
  ⟨a.key.lay, ⟨a.key.tree, ha.1.1⟩,
    ⟨a.key.leaf, lt_of_lt_of_le ha.1.2 (by
      calc 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
        _ = 4096 := by norm_num)⟩,
    ⟨a.chain, lt_of_lt_of_le ha.2 (chainCount_le58 _)⟩⟩

theorem wotsAddr_gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : wotsAddr (gAddr a ha) = a := rfl

theorem posOf_chainRow (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (s : Nat) (hs : s < 7) (v : Digest) :
    Extract.posOf (Wots.chainRow a s v) = some (CanonGraph.Node.chain (gAddr a ha, ⟨s, hs⟩)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  unfold Wots.chainRow
  rw [chainInput_eq_zero, ← pad64_chainInputP, Extract.hdrBlock_chainInputP]
  rfl

theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRow (wotsAddr p.1) p.2.val (honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [chainInput_eq_zero, pad64_chainInputP, ← chainInput_eq_zero]
  rfl

theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    honestValue A (.inl (.chain p)) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  rw [← honestChainValue_succ, eval_shortHash]
  rfl

theorem honestChainValue_zero' (A : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue A lay tree leaf i seed 0 = seed := by
  simp [honestChainValue, chain]

theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    honestValue A (chainChild p) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, honestChainValue_zero']
    rfl
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega

theorem childSlots_chain (p : ChainGraph.Point) : childSlots (.chain p) = [(chainChild p, 3)] := rfl

/-- **W's `ContactAt` on the verifier's queries is a contact.** -/
theorem contactAt_false (A : Answers) (published : T3.Cache) (qs : List Spec.Domain) (a : Wots.ChainAddr)
    (ha : WotsExtract.SourceChain a) (hc : Wots.ContactAt A (Wots.entriesOf A qs) a)
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  obtain ⟨hd, value, answer, hmem, hlow⟩ := hc
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hd7 : Wots.depth A a ≤ 7 := by
    have := WotsExtract.depth_le A a ha.2
    have hw : maxDigit a.key.lay a.chain ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  set s := Wots.depth A a - 1 with hsdef
  have hs7 : s < 7 := by omega
  let p : ChainGraph.Point := (gAddr a ha, ⟨s, hs7⟩)
  have hpos := posOf_chainRow a ha s hs7 value
  obtain ⟨hhit, hsingle, -⟩ := hclear _ hq
  have hcv : honestValue A (chainChild p) = honestChainValue A a.key.lay a.key.tree a.key.leaf a.chain
      (leafSeed A a.key.lay a.key.tree a.key.leaf a.chain) s := honestValue_chainChild A p
  by_cases hv : value = honestValue A (chainChild p)
  · have hk := hsingle (.chain p) hpos (chainChild p) 3 (childSlots_chain p) (by rw [slotValue_chainRow]; exact hv)
    exact frontier_child_unknown A published (gAddr a ha) ⟨s, hs7⟩ (by
      change s + 1 = Wots.depth A (wotsAddr (gAddr a ha))
      rw [wotsAddr_gAddr]; omega) hk
  · apply hhit (.chain p) hpos
    refine ⟨fun heq => hv ?_, ?_⟩
    · have := congrArg (fun X => slotValue X 3) heq
      simp only [slotValue_chainRow] at this
      rw [this, honestInput_chainNode, slotValue_chainRow, hcv]
      rfl
    · rw [hans]
      change Wots.low answer = _
      rw [hlow, honestValue_chainNode]
      unfold Wots.frontierValue
      congr 1
      change Wots.depth A a = s + 1
      omega

/-- **W's structural hit on the verifier's queries is a hit.** -/
theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : WotsExtract.StructuralHitSrc A (Wots.entriesOf A qs)) (hclear : AllClear A K qs) : False := by
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, -, hne, hlow⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hsp : CanonGraph.SourcePos position := by
    cases position with
    | chain lay tree leaf i step =>
        obtain ⟨h1, h2, h3, h4⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 (chainCount_le58 lay), ?_⟩
        · calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
            _ = 4096 := by norm_num
        · have hw : 2 ^ width lay i ≤ 8 := by unfold width; split_ifs <;> norm_num
          omega
    | leaf lay tree leaf =>
        obtain ⟨h1, h2⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
          _ = 4096 := by norm_num
    | node lay tree level nd => exact hsrc
    | forest index => exact hsrc
    | ftsLeaf index coord leaf => exact hsrc
    | ftsNode index coord level nd => exact hsrc
  obtain ⟨N, rfl⟩ := CanonGraph.exists_toPos hsp
  exact (hclear _ hq).1 N hpos ⟨hne, hlow⟩

/-- **W's encoding match at a route leaf on the verifier's queries is an encoding hit.** -/
theorem encodingMatch_route_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (lay : Layer)
    (h : Wots.EncodingMatchAt A (Wots.entriesOf A qs) (WotsExtract.routeLeaf index lay))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m, ctr, answer, hmem, hne, hdec⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  obtain ⟨L, hL⟩ := CanonEncoding.route_source index hidx lay
  have hL' : L.toWots = WotsExtract.routeLeaf index lay := hL
  refine (hclear _ hq).2.2 L m ctr (by rw [hL']) ⟨?_, ?_⟩
  · rw [hL']; exact hne
  · have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL'
    rw [hans, hL', hlay]; exact hdec

/-- **Every route-sized W event on the verifier's queries contradicts a contact-free run.** -/
theorem wotsPrimitiveRoute_false (A : Answers) (published : T3.Cache) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (h : WotsExtract.WotsPrimitiveRoute index A (Wots.entriesOf A qs))
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, -, -, h, -⟩ | ⟨a, ha, -, h⟩
  · exact encodingMatch_route_false A _ qs index hidx lay h hclear
  · exact structuralHitSrc_false A _ qs h hclear
  · obtain ⟨hd, start, middle, -, hrow⟩ := h
    exact contactAt_false A published qs a ha ⟨by omega, middle, hrow⟩ hclear
  · exact contactAt_false A published qs a ha h hclear
  · exact contactAt_false A published qs a ha h hclear

end SigGolfCandidate.T3.Security.LargeCoupling
