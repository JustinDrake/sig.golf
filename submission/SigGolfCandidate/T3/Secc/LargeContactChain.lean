import SigGolfCandidate.T3.Secc.LargeContactMonitor
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactChain : DecidableEq T3.Cache := Classical.decEq _
theorem known_secret {D : Coord → Prop} {s : CanonGraph.SecretIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem known_chain_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ p : ChainGraph.Point, c = .inl (.chain p) →
      (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) := by
  induction h with
  | base hc =>
      intro p hp
      subst hp
      exact Or.inl ⟨p.2, le_rfl, hc⟩
  | @node N hall ih =>
      intro p hp
      simp only [Sum.inl.injEq] at hp
      subst hp
      have hmem : (chainChild p, 3) ∈ childSlots (.chain p) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      unfold chainChild at hk hih
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0] at hk
        exact Or.inr (known_secret hk)
      · rw [if_neg h0] at hih
        rcases hih (ChainGraph.predecessor p) rfl with ⟨s, hs, hd⟩ | hd
        · refine Or.inl ⟨s, ?_, hd⟩
          simp only [ChainGraph.predecessor] at hs
          omega
        · exact Or.inr hd
theorem known_chain {D : Coord → Prop} {p : ChainGraph.Point} (h : Known D (.inl (.chain p))) :
    (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) :=
  known_chain_aux h p rfl
def wotsAddr (a : ChainGraph.Address) : Wots.ChainAddr := ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩
theorem chainItem_chain {L : CanonGraph.LeafPos} {i d : Nat} {p : ChainGraph.Point}
    (h : chainItem L i d = .inl (.chain p)) :
    p.1 = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d ≠ 0 ∧ p.2.val = (d - 1) % 7 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    cases h
  · rw [if_neg hd] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.chain.injEq] at h
    subst h
    exact ⟨rfl, hd, rfl⟩
theorem chainItem_seed {L : CanonGraph.LeafPos} {i d : Nat} {a : ChainGraph.Address}
    (h : chainItem L i d = .inr (.inl a)) : a = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d = 0 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h.symm, hd⟩
  · rw [if_neg hd] at h
    cases h
def NotChain (c : Coord) : Prop := (∀ p, c ≠ .inl (.chain p)) ∧ (∀ a, c ≠ .inr (.inl a))
theorem treeChild_not_chain {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) : NotChain d := by
  unfold treeChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 4096
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsChild_not_chain {index : Fin (2^31)} {coord : Fin 7} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) : NotChain d := by
  unfold ftsChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 2048
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsItems_not_chain (index : Fin (2^31)) (chosen : List Selection) (c : Coord)
    (hc : c ∈ ftsItems index chosen) : NotChain c := by
  unfold ftsItems ftsOpened ftsProof at hc
  simp only [List.mem_flatMap, List.mem_range, List.mem_append, List.mem_filterMap] at hc
  obtain ⟨coord, _, hc⟩ := hc
  rcases hc with ⟨leaf, _, hl⟩ | ⟨pr, _, hp⟩ | ⟨j, _, hj⟩
  · split_ifs at hl with h
    simp only [Option.some.injEq] at hl
    subst hl
    exact ⟨fun p => by simp, fun a => by simp⟩
  · exact ftsChild_not_chain hp
  · exact ftsChild_not_chain hj
theorem keygen_not_chain (c : Coord) (hc : c ∈ keygenDisclosed) : NotChain c := by
  unfold keygenDisclosed at hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨_, _, _, _, h⟩ := hc
  exact treeChild_not_chain h
theorem layerItems_chain (A : Answers) (index : Fin (2^31)) (c : Coord)
    (hc : c ∈ layerItems (Wots.referenceDigits A) index) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      have hfin : (CanonGraph.fin58 i).val = i := Nat.mod_eq_of_lt hi58
      have hdepth : ∀ a : ChainGraph.Address,
          a = ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ →
          Wots.depth A (wotsAddr a) = (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 := by
        intro a ha
        subst ha
        simp only [Wots.depth, wotsAddr, hfin, routeAddr]
      constructor
      · intro p hp
        obtain ⟨h1, hd, h2⟩ := chainItem_chain hp
        rw [hdepth p.1 h1, h2]
        have hle : (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
          WotsExtract.depth_le A ⟨routeAddr index.val lay, i⟩ hi
        have hw : maxDigit lay i ≤ 7 := by
          unfold maxDigit; split_ifs <;> norm_num
        omega
      · intro a ha
        obtain ⟨h1, hd⟩ := chainItem_seed ha
        rw [hdepth a h1, hd]
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      have := treeChild_not_chain hj
      exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
    · cases hc
theorem signDisclosed_chain (A : Answers) (published : T3.Cache) (request : Security.Request) (c : Coord)
    (hc : c ∈ signDisclosed A published request) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold signDisclosed at hc
  split_ifs at hc with hcache
  · split at hc
    · split_ifs at hc with hok
      · unfold signItems signItemsWith at hc
        rcases List.mem_append.mp hc with hc | hc
        · have := ftsItems_not_chain _ _ c hc
          exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
        · exact layerItems_chain A _ c hc
      · cases hc
    · cases hc
  · cases hc
def Disclosed (A : Answers) (published : T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
theorem frontier_child_unknown (A : Answers) (published : T3.Cache) (a : ChainGraph.Address) (s : Fin 7)
    (hs : s.val + 1 = Wots.depth A (wotsAddr a)) :
    ¬Known (Disclosed A published) (chainChild (a, s)) := by
  intro hk
  unfold chainChild at hk
  by_cases h0 : s.val = 0
  · rw [if_pos h0] at hk
    rcases known_secret hk with hd | ⟨request, hd⟩
    · exact (keygen_not_chain _ hd).2 a rfl
    · have := (signDisclosed_chain A published request _ hd).2 a rfl
      omega
  · rw [if_neg h0] at hk
    rcases known_chain hk with ⟨t, ht, hd⟩ | hd
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).1 _ rfl
      · have := (signDisclosed_chain A published request _ hd).1 _ rfl
        simp only [ChainGraph.predecessor] at ht this
        omega
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).2 _ rfl
      · have := (signDisclosed_chain A published request _ hd).2 _ rfl
        simp only [ChainGraph.predecessor] at this
        omega
end SigGolfCandidate.T3.Security.LargeCoupling
