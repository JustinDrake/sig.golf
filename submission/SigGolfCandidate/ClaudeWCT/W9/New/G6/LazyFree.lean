import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyDefs
import SigGolfCandidate.T3.Secc.PairGuessLazyFree

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep NotDN)
open SphincsSecurity.Concrete
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem ftsQuery_dn {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) : NotDN q := by
  rcases q with (n | x) | (tweak | other)
  · exact h.elim
  · obtain ⟨tag, lay, position, idx, htag, hx⟩ := (show WCT9.FtsInput index x from h).hdrBlock
    exact SigGolfCandidate.T3.Security.BPair.not_digest_of_hdr hx (by rcases htag with rfl | rfl | rfl | rfl <;> decide)
  · trivial
  · exact h.elim
theorem allQ_mono {P Q : SigGolfCandidate.T3.Spec.Domain → Prop} {α : Type} {program : M α}
    (h : AllQueriesSatisfy program P) (hPQ : ∀ q, P q → Q q) : AllQueriesSatisfy program Q := by
  induction program using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind i next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hi, fun a => ih a (hn a)⟩
theorem dn_of_fts {index : Nat} {α : Type} {program : M α} (h : AllQueriesSatisfy program (WCT9.FtsQuery index)) :
    AllQueriesSatisfy program NotDN :=
  allQ_mono h fun _ hq => ftsQuery_dn hq
theorem signForest_dn (index : Nat) (output : HashOutput) : AllQueriesSatisfy (WCT9.signForest index output) NotDN :=
  dn_of_fts (WCT9.signForest_queries index output)
theorem cell_not_digest (s : CanonGraph.Secrets) (node : CanonGraph.Node) (labels : CanonGraph.Labels) :
    CanonGraph.cell s node labels ∉ digestInputs := by
  have h := CanonGraph.hdrBlock_cell s node labels
  cases node <;> simp only [CanonGraph.Node.toPos, ClaudeWCT.W9.T3M.Extract.Pos.hdr] at h <;>
    exact SigGolfCandidate.T3.Security.BPair.not_digest_of_hdr h (by decide)
def nonceHalf (m : Message) : ChainGraph.HalfCoordinate := (.inr (.inl m), 0)
theorem nonceHalf_not_secret (m : Message) : nonceHalf m ∉ Set.range CanonGraph.secretCoordinate := by
  rintro ⟨i, hi⟩
  have h1 := congrArg Prod.fst hi
  cases i with
  | inl a => cases h1
  | inr f => cases h1
def nonceOther (m : Message) : CanonGraph.OtherHalf := ⟨nonceHalf m, nonceHalf_not_secret m⟩
theorem nonceOther_injective : Function.Injective nonceOther := by
  intro m m' h
  have h1 := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) h
  change (Sum.inr (Sum.inl m) : Coordinate) = Sum.inr (Sum.inl m') at h1
  exact Sum.inl.inj (Sum.inr.inj h1)
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable def digestOf (ω : CanonTable.Omega U) : digestInputs → HashOutput :=
  fun x => finiteHashAnswer ∅ U ω.residual x.val
def nonceOf (ω : CanonTable.Omega U) : Message → Digest := fun m => ω.other (nonceOther m)
theorem answers_digest (ω : CanonTable.Omega U) (g : WctPoint → Digest) (x : HashInput) (hx : x ∈ digestInputs) :
    wA hU ω g (.inl (.inr x)) = rowVal (digestOf ω) x := by
  rw [rowVal, dif_pos hx]
  change finiteHashAnswer ∅ U (CanonGraph.programmed U hU (CanonTable.worldSecrets ω.secrets g)
    (CanonTable.worldLabels ω g) ω.residual) x = finiteHashAnswer ∅ U ω.residual x
  by_cases hxU : x ∈ U
  · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
    apply CanonGraph.programmed_other
    intro node he
    exact cell_not_digest _ node _ (by rw [← he]; exact hx)
  · simp only [finiteHashAnswer, dif_neg hxU]
theorem eval_nonce (ω : CanonTable.Omega U) (g : WctPoint → Digest) (m : Message) :
    evalWithAnswerFn (wA hU ω g) (privateNonce m) = nonceOf ω m := by
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (CanonGraph.privateEquiv.symm (CanonTable.worldSecrets ω.secrets g, ω.other) (.inr (.inl m))).extractLsb'
    0 128 = _
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low]
  exact splitEquiv_symm_other _ _ (nonceHalf m) (nonceHalf_not_secret m)
end Table
section Rest
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_g6LazyFree : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def SameRest (ω₁ ω₂ : CanonTable.Omega U) : Prop :=
  ω₁.secrets = ω₂.secrets ∧ ω₁.low = ω₂.low ∧ ω₁.high = ω₂.high ∧
    (∀ x : U, x.val ∉ digestInputs → ω₁.residual x = ω₂.residual x) ∧
    (∀ h : CanonGraph.OtherHalf, (∀ m, h ≠ nonceOther m) → ω₁.other h = ω₂.other h)
theorem programmed_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest) (x : U)
    (hx : x.val ∉ digestInputs) :
    CanonGraph.programmed U hU (CanonTable.worldSecrets ω₁.secrets g) (CanonTable.worldLabels ω₁ g) ω₁.residual x =
      CanonGraph.programmed U hU (CanonTable.worldSecrets ω₂.secrets g) (CanonTable.worldLabels ω₂ g)
        ω₂.residual x := by
  have hs : CanonTable.worldSecrets ω₁.secrets g = CanonTable.worldSecrets ω₂.secrets g := by rw [h.1]
  have hl : CanonTable.worldLabels ω₁ g = CanonTable.worldLabels ω₂ g := by
    unfold CanonTable.worldLabels
    rw [h.2.1, h.2.2.1]
  rw [hs, hl]
  by_cases hc : ∃ node, x.val = CanonGraph.cell (CanonTable.worldSecrets ω₂.secrets g) node (CanonTable.worldLabels ω₂ g)
  · obtain ⟨node, hnode⟩ := hc
    have hx' : x = CanonGraph.cellIn U hU (CanonTable.worldSecrets ω₂.secrets g) node (CanonTable.worldLabels ω₂ g) :=
      Subtype.ext hnode
    rw [hx', CanonGraph.programmed_at, CanonGraph.programmed_at]
  · have hn : ∀ node, x.val ≠ CanonGraph.cell (CanonTable.worldSecrets ω₂.secrets g) node
        (CanonTable.worldLabels ω₂ g) := fun node he => hc ⟨node, he⟩
    rw [CanonGraph.programmed_other U hU _ _ _ _ hn, CanonGraph.programmed_other U hU _ _ _ _ hn]
    exact h.2.2.2.1 x hx
theorem private_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest) (c : Coordinate)
    (hc : ∀ m, c ≠ .inr (.inl m)) :
    CanonGraph.privateEquiv.symm (CanonTable.worldSecrets ω₁.secrets g, ω₁.other) c =
      CanonGraph.privateEquiv.symm (CanonTable.worldSecrets ω₂.secrets g, ω₂.other) c := by
  have hhalf : ∀ k : Fin 2, CanonGraph.splitEquiv.symm (CanonTable.worldSecrets ω₁.secrets g, ω₁.other) (c, k) =
      CanonGraph.splitEquiv.symm (CanonTable.worldSecrets ω₂.secrets g, ω₂.other) (c, k) := by
    intro k
    by_cases hr : (c, k) ∈ Set.range CanonGraph.secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret, h.1]
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
      apply h.2.2.2.2
      intro m he
      have := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) he
      exact hc m this
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem answers_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest)
    (q : SigGolfCandidate.T3.Spec.Domain) (hq : NotDN q) : wA hU ω₁ g q = wA hU ω₂ g q := by
  rcases q with (n | x) | c
  · rfl
  · change finiteHashAnswer ∅ U (CanonGraph.programmed U hU (CanonTable.worldSecrets ω₁.secrets g)
        (CanonTable.worldLabels ω₁ g) ω₁.residual) x =
      finiteHashAnswer ∅ U (CanonGraph.programmed U hU (CanonTable.worldSecrets ω₂.secrets g)
        (CanonTable.worldLabels ω₂ g) ω₂.residual) x
    by_cases hxU : x ∈ U
    · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
      exact programmed_sameRest hU h g ⟨x, hxU⟩ hq
    · simp only [finiteHashAnswer, dif_neg hxU]
  · apply private_sameRest h g c
    rintro m rfl
    exact hq
theorem eval_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest) {α : Type}
    {program : M α} (hp : AllQueriesSatisfy program NotDN) :
    evalWithAnswerFn (wA hU ω₁ g) program = evalWithAnswerFn (wA hU ω₂ g) program :=
  eval_congr_allowed hp (answers_sameRest hU h g)
theorem residual_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (x : HashInput) (hx : x ∉ digestInputs) :
    finiteHashAnswer ∅ U ω₁.residual x = finiteHashAnswer ∅ U ω₂.residual x := by
  by_cases hxU : x ∈ U
  · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
    exact h.2.2.2.1 ⟨x, hxU⟩ hx
  · simp only [finiteHashAnswer, dif_neg hxU]
theorem probeInput_not_digest (a : Guess.ChainAddr) (p : Fin 3) (c : Digest) :
    Guess.probeInput a p c ∉ digestInputs := by
  have hx := CanonTable.probeInput_hdr a p c
  simp only [CanonGraph.Node.toPos, ClaudeWCT.W9.T3M.Extract.Pos.hdr] at hx
  exact SigGolfCandidate.T3.Security.BPair.not_digest_of_hdr hx (by decide)
theorem hashL_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) : hashL hU ω₁ = hashL hU ω₂ := by
  funext x
  unfold hashL
  cases hd : Guess.decodeProbe x with
  | some q =>
      have hx := Guess.eq_of_decodeProbe hd
      have hnd : x ∉ digestInputs := by rw [hx]; exact probeInput_not_digest _ _ _
      have hstep : (CanonTable.chainTable hU ω₁).step = (CanonTable.chainTable hU ω₂).step := by
        funext a p v
        change ChainGraph.joinOutput v (ω₁.high (.wctChain (a, p))) = ChainGraph.joinOutput v (ω₂.high (.wctChain (a, p)))
        rw [h.2.2.1]
      have htop : (CanonTable.chainTable hU ω₁).top = (CanonTable.chainTable hU ω₂).top := by
        funext a
        change CanonGraph.joinLabels ω₁.low ω₁.high (.wctChain (a, 2)) = CanonGraph.joinLabels ω₂.low ω₂.high (.wctChain (a, 2))
        rw [h.2.1, h.2.2.1]
      have hmiss : (CanonTable.chainTable hU ω₁).miss x = (CanonTable.chainTable hU ω₂).miss x :=
        residual_sameRest h x hnd
      simp only [hstep, htop, hmiss]
  | none =>
      by_cases hx : x ∈ digestInputs
      · simp only [if_pos hx]
      · simp only [if_neg hx]
        exact congrArg _ (answers_sameRest hU h 0 (.inl (.inr x)) hx)
theorem honestForest_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest)
    (index : Nat) : WCT9.honestForest (wA hU ω₁ g) index = WCT9.honestForest (wA hU ω₂ g) index := by
  rw [← WCT9.signForest_root _ index 0, ← WCT9.signForest_root _ index 0,
    eval_sameRest hU h g (signForest_dn _ _)]
theorem expectedOpening_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest)
    (index : Nat) (output : HashOutput) (k : WCT9.Coord) :
    WCT9.expectedOpening (wA hU ω₁ g) index output k = WCT9.expectedOpening (wA hU ω₂ g) index output k := by
  rw [← WCT9.signForest_openings, ← WCT9.signForest_openings, eval_sameRest hU h g (signForest_dn _ _)]
theorem assembleWith_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (g : WctPoint → Digest)
    (core : Digest × HashOutput × List Pieces) :
    assembleWith (wA hU ω₁ g) core = assembleWith (wA hU ω₂ g) core := by
  unfold assembleWith
  exact congrArg (fun l => WCT9.assembledSignature core.1 l core.2.2)
    (congrArg List.ofFn (funext fun k => expectedOpening_sameRest hU h g _ _ k))
theorem signerLayersW_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) :
    signerLayersW hU ω₁ = signerLayersW hU ω₂ := by
  funext request output
  unfold signerLayersW
  rw [honestForest_sameRest hU h, eval_sameRest hU h _ (SigGolfCandidate.T3.Security.BPair.signLayers_dn _ _ _ _)]
theorem finishL_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) : finishL hU ω₁ = finishL hU ω₂ := by
  funext request rho found
  rcases found with _ | ⟨c, output⟩
  · rfl
  · simp only [finishL, signerLayersW_sameRest hU h, assembleWith_sameRest hU h]
theorem signL_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) : signL hU ω₁ = signL hU ω₂ := by
  funext published request
  unfold signL
  simp only [finishL_sameRest hU h]
theorem interactionL_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂)
    (published : SigGolfCandidate.T3.Cache) {α : Type} :
    (interactionL hU ω₁ published : OracleComp LazyPrivate.Interaction α → _) = interactionL hU ω₂ published := by
  unfold interactionL
  simp only [hashL_sameRest hU h, signL_sameRest hU h]
theorem programL_sameRest {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) {β : Type} :
    (programL hU ω₁ : M β → _) = programL hU ω₂ := by
  unfold programL
  simp only [hashL_sameRest hU h]
theorem worldGameL_congr {ω₁ ω₂ : CanonTable.Omega U} (h : SameRest ω₁ ω₂) (adversary : AdversaryP) :
    worldGameCore hU ω₁ adversary = worldGameCore hU ω₂ adversary := by
  unfold worldGameCore
  rw [eval_sameRest hU h _ SigGolfCandidate.T3.Security.BPair.keygen_dn]
  simp only [interactionL_sameRest hU h, programL_sameRest hU h]
end Rest
end ClaudeWCT.W9.T3.Security.WPair
