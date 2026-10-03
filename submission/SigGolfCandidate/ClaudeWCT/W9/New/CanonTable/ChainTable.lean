import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.GuessV2.WorldHash

namespace ClaudeWCT.W9.CanonTable
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs
open ClaudeWCT.W9.T3.Security.CanonGraph
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem chainAddr_eq : Guess.ChainAddr = WctAddr := rfl
theorem gCoord_eq : Guess.GCoord = WctPoint := rfl
theorem cell_wctChain (secrets : Secrets) (labels : Labels) (p : WctPoint) :
    cell secrets (.wctChain p) labels = Guess.probeInput p.1 p.2 (wctValueL secrets labels p.1 p.2.val) := rfl
theorem probeInput_hdr (a : WctAddr) (p : Fin 3) (c : Digest) :
    Extract.hdrBlock (Guess.probeInput a p c) = bytesLE 16 (Node.toPos (.wctChain (a, p))).hdr :=
  Extract.hdrBlock_wctChainInput _ _ _ _ _ _
theorem probeInput_inj {a a' : WctAddr} {p p' : Fin 3} {c c' : Digest}
    (h : Guess.probeInput a p c = Guess.probeInput a' p' c') : a = a' ∧ p = p' ∧ c = c' := by
  have hh := probeInput_hdr a p c
  rw [h, probeInput_hdr] at hh
  have hn : (Node.wctChain (a', p') : Node) = .wctChain (a, p) :=
    toPos_injective (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _) (bytesLE_injective hh))
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn
  refine ⟨rfl, rfl, ?_⟩
  unfold Guess.probeInput at h
  rw [Extract.wctChainInput_block4, Extract.wctChainInput_block4] at h
  exact (block4_injective h).2.2.2
theorem decodeProbe_probe (a : WctAddr) (p : Fin 3) (c : Digest) :
    Guess.decodeProbe (Guess.probeInput a p c) = some ((a, p), c) := by
  have h : ∃ q : Guess.GCoord × Digest, Guess.probeInput a p c = Guess.probeInput q.1.1 q.1.2 q.2 :=
    ⟨((a, p), c), rfl⟩
  delta Guess.decodeProbe
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := probeInput_inj (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext (Prod.ext h1 h2) h3)
theorem decodeProbe_none {x : HashInput} (h : Guess.decodeProbe x = none) (a : WctAddr) (p : Fin 3) (c : Digest) :
    x ≠ Guess.probeInput a p c := by
  intro hx
  rw [hx, decodeProbe_probe] at h
  cases h
theorem probeInput_mem (a : WctAddr) (p : Fin 3) (c : Digest) : Guess.probeInput a p c ∈ canonInputs := by
  have h := cell_mem (fun _ => c) (.wctChain (a, p)) (fun _ => ChainGraph.joinOutput c 0)
  have hv : wctValueL (fun _ => c) (fun _ => ChainGraph.joinOutput c 0) a p.val = c := by
    unfold wctValueL
    split_ifs
    · rfl
    · exact ChainGraph.joinOutput_low _ _
  rw [cell_wctChain, hv] at h
  exact h
theorem cell_ne_probe (secrets : Secrets) (labels : Labels) (node : Node) (hnode : ∀ q, node ≠ .wctChain q)
    (a : WctAddr) (p : Fin 3) (c : Digest) : cell secrets node labels ≠ Guess.probeInput a p c := by
  intro he
  have h1 := hdrBlock_cell secrets node labels
  rw [he, probeInput_hdr] at h1
  exact hnode (a, p) (toPos_injective (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _)
    (bytesLE_injective h1))).symm
def Hidden (node : Node) : Prop := ∃ a : WctAddr, ∃ q : Fin 3, q.val < 2 ∧ node = .wctChain (a, q)
theorem treeLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold treeLabel
  split_ifs with hzero hc
  · rw [hn _ (fun _ => Node.noConfusion)]
  · rfl
  · cases treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem ftsLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [hn _ (fun _ => Node.noConfusion)]
  · rfl
  · cases ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem cell_outer (secrets secrets' : Secrets) (labels labels' : Labels)
    (hs : ∀ a, secrets (.inl a) = secrets' (.inl a)) (hl : ∀ node, ¬Hidden node → labels node = labels' node)
    (node : Node) (hnode : ∀ q, node ≠ .wctChain q) :
    cell secrets node labels = cell secrets' node labels' := by
  have hseeds : seedsOf secrets = seedsOf secrets' := funext hs
  have hchain : chainLabels labels = chainLabels labels' :=
    funext fun point => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)
  cases node with
  | chain p =>
      change ChainGraph.input (seedsOf secrets) p (chainLabels labels) =
        ChainGraph.input (seedsOf secrets') p (chainLabels labels')
      rw [hseeds, hchain]
  | leaf L =>
      have hends : (List.range (chainCount L.lay)).map (endLabel secrets labels L) =
          (List.range (chainCount L.lay)).map (endLabel secrets' labels' L) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel
        rw [hseeds, hchain]
      simp only [cell, hends]
  | node n =>
      simp only [cell, treeLabel_outer labels labels' hl]
  | wctChain p => exact absurd rfl (hnode p)
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 7 => wctEndLabel labels (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 7 => wctEndLabel labels' (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [hl _ (fun ⟨a, q, hq, he⟩ => by
          simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact absurd hq (by decide))]
      simp only [cell, hends]
  | wctNode n =>
      simp only [cell, ftsLabel_outer labels labels' hl]
  | forest index =>
      simp only [cell, ftsLabel_outer labels labels' hl]
def stepNode (c : WctAddr × Fin 2) : Node := .wctChain (c.1, ⟨c.2.val, by omega⟩)
def shiftCoord (c : WctAddr × Fin 2) : WctPoint := (c.1, ⟨c.2.val + 1, by omega⟩)
theorem stepNode_injective : Function.Injective stepNode := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  simp only [stepNode, Node.wctChain.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [Fin.ext h]
theorem inr_injective : Function.Injective (Sum.inr : WctAddr → SecretIndex) := Sum.inr_injective
noncomputable def worldSecrets (secrets : Secrets) (g : WctPoint → Digest) : Secrets :=
  Function.extend Sum.inr (fun a => g (a, 0)) secrets
noncomputable def worldLow (low : LowLabels) (g : WctPoint → Digest) : LowLabels :=
  Function.extend stepNode (fun c => g (shiftCoord c)) low
structure Omega (U : Finset HashInput) where
  secrets : Secrets
  other : OtherHalves
  low : LowLabels
  high : LowLabels
  residual : U → HashOutput
variable {U : Finset HashInput} (hU : canonInputs ⊆ U)
noncomputable def worldLabels (ω : Omega U) (g : WctPoint → Digest) : Labels :=
  joinLabels (worldLow ω.low g) ω.high
noncomputable def worldAnswers (ω : Omega U) (g : WctPoint → Digest) : Answers :=
  eagerAnswers (privateEquiv.symm (worldSecrets ω.secrets g, ω.other)) U
    (programmed U hU (worldSecrets ω.secrets g) (worldLabels ω g) ω.residual)
theorem worldSecrets_inr (secrets : Secrets) (g : WctPoint → Digest) (a : WctAddr) :
    worldSecrets secrets g (.inr a) = g (a, 0) :=
  inr_injective.extend_apply _ _ a
theorem worldSecrets_inl (secrets : Secrets) (g : WctPoint → Digest) (a : ChainGraph.Address) :
    worldSecrets secrets g (.inl a) = secrets (.inl a) := by
  unfold worldSecrets
  rw [Function.extend_apply']
  rintro ⟨b, hb⟩
  cases hb
theorem worldLabels_step (ω : Omega U) (g : WctPoint → Digest) (a : WctAddr) (q : Fin 3) (hq : q.val < 2) :
    worldLabels ω g (.wctChain (a, q)) = ChainGraph.joinOutput (g (a, ⟨q.val + 1, by omega⟩)) (ω.high (.wctChain (a, q))) := by
  have hs : stepNode (a, ⟨q.val, hq⟩) = .wctChain (a, q) := rfl
  unfold worldLabels joinLabels worldLow
  rw [← hs, stepNode_injective.extend_apply]
  rfl
theorem worldLabels_outer (ω : Omega U) (g : WctPoint → Digest) (node : Node) (hnode : ¬Hidden node) :
    worldLabels ω g node = joinLabels ω.low ω.high node := by
  unfold worldLabels joinLabels worldLow
  rw [Function.extend_apply']
  rintro ⟨⟨a, q⟩, hc⟩
  exact hnode ⟨a, ⟨q.val, by omega⟩, q.isLt, hc.symm⟩
theorem not_hidden_top (a : WctAddr) : ¬Hidden (.wctChain (a, 2)) := by
  rintro ⟨b, q, hq, he⟩
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact absurd hq (by decide)
theorem worldValueL (ω : Omega U) (g : WctPoint → Digest) (p : WctPoint) :
    wctValueL (worldSecrets ω.secrets g) (worldLabels ω g) p.1 p.2.val = g p := by
  obtain ⟨a, ⟨s, hs⟩⟩ := p
  show wctValueL (worldSecrets ω.secrets g) (worldLabels ω g) a s = g (a, ⟨s, hs⟩)
  unfold wctValueL
  split_ifs with h0
  · subst h0
    exact worldSecrets_inr _ _ a
  · have hq : (s - 1) % 3 < 2 := by omega
    rw [worldLabels_step ω g a ⟨(s - 1) % 3, Nat.mod_lt _ (by decide)⟩ hq, ChainGraph.joinOutput_low]
    have he : (⟨(s - 1) % 3 + 1, by omega⟩ : Fin 3) = ⟨s, hs⟩ := Fin.ext (by simp only; omega)
    rw [he]
theorem worldAnswers_public (ω : Omega U) (g : WctPoint → Digest) (x : HashInput) (hx : x ∈ U) :
    worldAnswers hU ω g (.inl (.inr x)) =
      programmed U hU (worldSecrets ω.secrets g) (worldLabels ω g) ω.residual ⟨x, hx⟩ :=
  eagerAnswers_mem _ U _ ⟨x, hx⟩
theorem programmed_outer (ω : Omega U) (g : WctPoint → Digest) (x : HashInput) (hx : x ∈ U)
    (hprobe : Guess.decodeProbe x = none) :
    programmed U hU (worldSecrets ω.secrets g) (worldLabels ω g) ω.residual ⟨x, hx⟩ =
      programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual ⟨x, hx⟩ := by
  have hnot : ∀ (secrets : Secrets) (labels : Labels) (q : WctPoint), x ≠ cell secrets (.wctChain q) labels :=
    fun secrets labels q he => decodeProbe_none hprobe q.1 q.2 _ (he.trans (cell_wctChain secrets labels q))
  have hs : ∀ a, worldSecrets ω.secrets g (.inl a) = ω.secrets (.inl a) := worldSecrets_inl ω.secrets g
  have hl : ∀ node, ¬Hidden node → worldLabels ω g node = joinLabels ω.low ω.high node :=
    worldLabels_outer ω g
  have hcell : ∀ node, (∀ q, node ≠ .wctChain q) →
      cell (worldSecrets ω.secrets g) node (worldLabels ω g) = cell ω.secrets node (joinLabels ω.low ω.high) :=
    cell_outer _ _ _ _ hs hl
  by_cases hex : ∃ node, x = cell ω.secrets node (joinLabels ω.low ω.high)
  · obtain ⟨node, hnode⟩ := hex
    have hq : ∀ q, node ≠ .wctChain q := by
      rintro q rfl
      exact hnot _ _ q hnode
    have h1 : (⟨x, hx⟩ : U) = cellIn U hU (worldSecrets ω.secrets g) node (worldLabels ω g) :=
      Subtype.ext (hnode.trans (hcell node hq).symm)
    have h2 : (⟨x, hx⟩ : U) = cellIn U hU ω.secrets node (joinLabels ω.low ω.high) := Subtype.ext hnode
    rw [h1, programmed_at, ← h1, h2, programmed_at]
    exact hl node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  · push Not at hex
    rw [programmed_other U hU _ _ _ _ (fun node he => ?_), programmed_other U hU _ _ _ _ (fun node he => hex node he)]
    by_cases hq : ∀ q, node ≠ .wctChain q
    · exact hex node (he.trans (hcell node hq))
    · push Not at hq
      obtain ⟨q, rfl⟩ := hq
      exact hnot _ _ q he
noncomputable def chainTable (ω : Omega U) : Guess.ChainTable where
  answers := worldAnswers hU ω
  step a p v := ChainGraph.joinOutput v (ω.high (.wctChain (a, p)))
  top a := joinLabels ω.low ω.high (.wctChain (a, 2))
  miss x := SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x
  answers_probe := by
    intro g a p c
    have hmem : Guess.probeInput a p c ∈ U := hU (probeInput_mem a p c)
    rw [worldAnswers_public hU ω g _ hmem]
    unfold Guess.probeAnswer
    by_cases hc : g (a, p) = c
    · rw [if_pos hc]
      have hx : (⟨Guess.probeInput a p c, hmem⟩ : U) =
          cellIn U hU (worldSecrets ω.secrets g) (.wctChain (a, p)) (worldLabels ω g) := by
        apply Subtype.ext
        change Guess.probeInput a p c = cell _ (.wctChain (a, p)) _
        rw [cell_wctChain]
        exact congrArg _ ((worldValueL ω g (a, p)).trans hc).symm
      rw [hx, programmed_at]
      unfold Guess.succPos
      split_ifs with hp
      · simp only
        exact worldLabels_step ω g a p (by omega)
      · simp only
        have hp2 : p = 2 := Fin.ext (by have := p.isLt; omega)
        subst hp2
        exact worldLabels_outer ω g _ (not_hidden_top a)
    · rw [if_neg hc]
      rw [programmed_other U hU _ _ _ _ (fun node he => ?_)]
      · exact (SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U ω.residual _ hmem rfl).symm
      · by_cases hq : ∀ q, node ≠ .wctChain q
        · exact cell_ne_probe _ _ node hq a p c he.symm
        · push Not at hq
          obtain ⟨q, rfl⟩ := hq
          change Guess.probeInput a p c = cell _ (.wctChain q) _ at he
          rw [cell_wctChain, worldValueL] at he
          obtain ⟨h1, h2, h3⟩ := probeInput_inj he
          subst h1 h2
          exact hc h3.symm
  answers_public := by
    intro g g' x hx
    by_cases hU' : x ∈ U
    · rw [worldAnswers_public hU ω g x hU', worldAnswers_public hU ω g' x hU',
        programmed_outer hU ω g x hU' hx, programmed_outer hU ω g' x hU' hx]
    · change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x
      unfold SphincsSecurity.Concrete.finiteHashAnswer
      rw [dif_neg hU', dif_neg hU']
  step_low a p v := ChainGraph.joinOutput_low _ _
  seed := by
    intro g a
    have h1 : Guess.seedOf (worldAnswers hU ω g) a = wctSeedOf (worldAnswers hU ω g) a := by
      unfold Guess.seedOf wctSeedOf
      by_cases h : a.2.2.2.val % 2 = 0
      · rw [if_pos h]
      · rw [if_neg h]
    rw [h1]
    change secretsOf (worldAnswers hU ω g) (.inr a) = _
    unfold worldAnswers
    rw [secretsOf_eager, privateSecrets_symm, worldSecrets_inr]
theorem worldAnswers_agrees (ω : Omega U) (g : WctPoint → Digest) :
    Agrees (worldAnswers hU ω g) (worldLabels ω g) :=
  eager_programmed_agrees U hU _ _ _ _
def trueHidden (ω : Omega U) : WctPoint → Digest :=
  fun p => if h : p.2.val = 0 then ω.secrets (.inr p.1) else ω.low (.wctChain (p.1, ⟨p.2.val - 1, by omega⟩))
theorem worldSecrets_true (ω : Omega U) : worldSecrets ω.secrets (trueHidden ω) = ω.secrets := by
  funext i
  cases i with
  | inl a => exact worldSecrets_inl _ _ a
  | inr a => rw [worldSecrets_inr]; rfl
theorem worldLow_true (ω : Omega U) : worldLow ω.low (trueHidden ω) = ω.low := by
  funext node
  unfold worldLow
  by_cases hn : ∃ c, stepNode c = node
  · obtain ⟨⟨a, q⟩, rfl⟩ := hn
    rw [stepNode_injective.extend_apply]
    unfold trueHidden shiftCoord
    simp only
    rw [dif_neg (by omega)]
    rfl
  · rw [Function.extend_apply' _ _ _ hn]
theorem worldAnswers_true (ω : Omega U) :
    worldAnswers hU ω (trueHidden ω) =
      eagerAnswers (privateEquiv.symm (ω.secrets, ω.other)) U
        (programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual) := by
  unfold worldAnswers worldLabels
  rw [worldSecrets_true, worldLow_true]
theorem chainTable_answers (ω : Omega U) : (chainTable hU ω).answers = worldAnswers hU ω := rfl
end ClaudeWCT.W9.CanonTable
