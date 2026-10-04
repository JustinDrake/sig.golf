import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsExtractVerify
namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def ShortQuery : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr input) => input.length ≤ SeccLaw.maxInputLength
  | .inr _ => True
def ShortAgree (A T : Answers) : Prop := ∀ query, ShortQuery query → A query = T query
theorem ShortAgree.symm {A T : Answers} (h : ShortAgree A T) : ShortAgree T A :=
  fun query hq => (h query hq).symm
theorem ShortAgree.public {A T : Answers} (h : ShortAgree A T) (input : HashInput)
    (hinput : input.length ≤ SeccLaw.maxInputLength) : A (.inl (.inr input)) = T (.inl (.inr input)) :=
  h _ hinput
theorem ShortAgree.priv {A T : Answers} (h : ShortAgree A T) (coordinate : Coordinate) :
    A (.inr coordinate) = T (.inr coordinate) := h _ trivial
def ShortRespects {α : Type} (program : M α) : Prop :=
  ∀ A T : Answers, ShortAgree A T → evalWithAnswerFn A program = evalWithAnswerFn T program
theorem ShortRespects.pure' {α : Type} (x : α) : ShortRespects (pure x : M α) := fun _ _ _ => rfl
theorem ShortRespects.bind {α β : Type} {p : M α} {f : α → M β} (hp : ShortRespects p)
    (hf : ∀ x, ShortRespects (f x)) : ShortRespects (p >>= f) := by
  intro A T h
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hp A T h]
  exact hf _ A T h
theorem ShortRespects.map {α β : Type} {p : M α} (f : α → β) (hp : ShortRespects p) :
    ShortRespects (f <$> p) := by
  intro A T h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map, hp A T h]
theorem ShortRespects.shortHash (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (T3.shortHash input) := by
  intro A T hAT
  rw [eval_shortHash, eval_shortHash, hAT.public _ h]
theorem ShortRespects.privatePair (tag lay tree position index : Nat) :
    ShortRespects (T3.privatePair tag lay tree position index) := by
  intro A T hAT
  unfold T3.privatePair T3.privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [show evalWithAnswerFn A (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      A (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query A _,
    show evalWithAnswerFn T (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      T (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query T _,
    hAT.priv]
theorem ShortRespects.foldlM {β γ : Type} (l : List β) (f : γ → β → M γ)
    (hf : ∀ x ∈ l, ∀ s, ShortRespects (f s x)) : ∀ init, ShortRespects (l.foldlM f init) := by
  induction l with
  | nil => intro init; exact ShortRespects.pure' init
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons]
      exact ShortRespects.bind (hf x List.mem_cons_self init)
        fun s => ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s) s
theorem ShortRespects.mapM {α β : Type} (l : List α) (f : α → M β) (hf : ∀ x ∈ l, ShortRespects (f x)) :
    ShortRespects (l.mapM f) := by
  intro A T h
  rw [Correctness.eval_mapM, Correctness.eval_mapM]
  exact List.map_congr_left fun x hx => hf x hx A T h
theorem pad64_length_le (input : HashInput) : (pad64 input).length ≤ input.length + 63 := by
  rw [Cost.pad64_length]
  omega
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by
  fin_cases lay <;> decide
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    (chainInput lay tree leaf i step value).length = 64 := by
  simp [chainInput, zero16, bytesLE_length]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (Extract.listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [Extract.listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem short_of_le (input : HashInput) (h : input.length ≤ 4033) :
    (pad64 input).length ≤ SeccLaw.maxInputLength := by
  have := pad64_length_le input
  unfold SeccLaw.maxInputLength
  omega
theorem chain_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (chain lay tree leaf i start count value) := by
  unfold chain
  exact ShortRespects.foldlM _ _ (fun step _ v => ShortRespects.shortHash _
    (short_of_le _ (by rw [chainInput_length]; omega))) value
theorem leafHash_respects (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    ShortRespects (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply ShortRespects.shortHash
  apply short_of_le
  simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop]
  omega
theorem nodeHash_respects (tag lay tree heap : Nat) (left right : Digest) :
    ShortRespects (nodeHash tag lay tree heap left right) := by
  unfold nodeHash
  apply ShortRespects.shortHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildLevel_respects (tag lay tree h level : Nat) (nodes : List Digest) :
    ShortRespects (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel
  exact ShortRespects.mapM _ _ fun i _ => nodeHash_respects _ _ _ _ _ _
theorem buildLevels_respects (tag lay tree h : Nat) (leaves : List Digest) :
    ShortRespects (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact ShortRespects.foldlM _ _ (fun level _ levels =>
    ShortRespects.bind (buildLevel_respects _ _ _ _ _ _) fun _ => ShortRespects.pure' _) _
theorem ftsLeaf_respects (index coord leaf : Nat) (secret : Digest) :
    ShortRespects (ftsLeaf index coord leaf secret) := by
  unfold ftsLeaf
  apply ShortRespects.shortHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildFts_respects (index coord : Nat) : ShortRespects (buildFts index coord) := by
  unfold buildFts
  refine ShortRespects.bind (ShortRespects.foldlM _ _ (fun pair _ state => ?_) _) fun state =>
    ShortRespects.bind (buildLevels_respects _ _ _ _ _) fun _ => ShortRespects.pure' _
  refine ShortRespects.bind (ShortRespects.privatePair _ _ _ _ _) fun seeds => ?_
  rcases seeds with ⟨left, right⟩
  exact ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ =>
    ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ => ShortRespects.pure' _
theorem forestPk_respects (index : Nat) (roots : List Digest) (hlen : roots.length ≤ 200) :
    ShortRespects (forestPk index roots) := by
  unfold forestPk
  apply ShortRespects.shortHash
  apply short_of_le
  simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop]
  omega
theorem counterSearch_respects (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter fuel : Nat) :
    ShortRespects (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold counterSearch
      refine ShortRespects.bind (ShortRespects.shortHash _ (short_of_le _ ?_)) fun answer => ?_
      · simp [encodingInput, bytesLE_length]
      · cases decode lay answer with
        | none => exact ih _
        | some digits => exact ShortRespects.pure' _
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem leafSeed_short (lay : Layer) (tree leaf i : Nat) : leafSeed A lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  rw [ShortRespects.privatePair 0 lay.val tree (i / 2) leaf A T hAT]
theorem chainValue_short (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    evalWithAnswerFn A (chain lay tree leaf i start count value) =
      evalWithAnswerFn T (chain lay tree leaf i start count value) :=
  chain_respects lay tree leaf i start count value A T hAT
theorem honestChainValue_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValue A lay tree leaf i seed step = honestChainValue T lay tree leaf i seed step :=
  chainValue_short hAT lay tree leaf i 0 step seed
theorem leafEnd_short (lay : Layer) (tree leaf i : Nat) : leafEnd A lay tree leaf i = leafEnd T lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_short hAT]
  exact chainValue_short hAT _ _ _ _ _ _ _
theorem leafRoot_short (lay : Layer) (tree leaf : Nat) : leafRoot A lay tree leaf = leafRoot T lay tree leaf := by
  unfold leafRoot
  rw [List.map_congr_left (fun i _ => leafEnd_short hAT lay tree leaf i)]
  apply leafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem builtTree_short (lay : Layer) (tree : Nat) : builtTree A lay tree = builtTree T lay tree := by
  unfold builtTree
  rw [List.map_congr_left (fun leaf _ => leafRoot_short hAT lay tree leaf)]
  exact buildLevels_respects _ _ _ _ _ A T hAT
theorem honestRoot_short (lay : Layer) (tree : Nat) : Extract.honestRoot A lay tree = Extract.honestRoot T lay tree := by
  unfold Extract.honestRoot
  rw [builtTree_short hAT]
theorem honestPair_short (lay : Layer) (tree : Nat) : Extract.honestPair A lay tree = Extract.honestPair T lay tree := by
  unfold Extract.honestPair
  rw [builtTree_short hAT]
theorem buildFts_short (index coord : Nat) :
    evalWithAnswerFn A (buildFts index coord) = evalWithAnswerFn T (buildFts index coord) :=
  buildFts_respects index coord A T hAT
theorem honestForest_short (index : Nat) : Extract.honestForest A index = Extract.honestForest T index := by
  rw [WotsExtract.honestForest_eq_built, WotsExtract.honestForest_eq_built]
  simp only [buildFts_short hAT]
  apply forestPk_respects
  · simp only [List.length_map, List.length_range]; omega
  · exact hAT
theorem builtSecret_short (index : Nat) : FtsExtract.builtSecret A index = FtsExtract.builtSecret T index := by
  funext c g
  simp only [FtsExtract.builtSecret, buildFts_short hAT]
theorem out_short (input : HashInput) (h : input.length ≤ SeccLaw.maxInputLength) :
    FtsExtract.out A input = FtsExtract.out T input := by
  unfold FtsExtract.out
  rw [hAT.public input h]
theorem honL_short (index coord : Nat) (secret : Nat → Digest) (level node : Nat) :
    FtsExtract.honL A index coord secret level node = FtsExtract.honL T index coord secret level node := by
  induction level generalizing node with
  | zero =>
      simp only [FtsExtract.honL]
      exact out_short hAT _ (by simp [ftsLeafInputP, SeccLaw.maxInputLength])
  | succ level ih =>
      simp only [FtsExtract.honL]
      rw [ih, ih]
      exact out_short hAT _ (by simp [nodeInputP, SeccLaw.maxInputLength])
theorem honInputL_short (index coord : Nat) (secret : Nat → Digest) (level node : Nat) :
    FtsExtract.honInputL A index coord secret level node = FtsExtract.honInputL T index coord secret level node := by
  cases level with
  | zero => rfl
  | succ level =>
      simp only [FtsExtract.honInputL]
      rw [honL_short hAT, honL_short hAT]
theorem leafMsg_short (L : LeafAddr) : leafMsg A L = leafMsg T L := by
  unfold leafMsg
  split_ifs
  · exact honestPair_short hAT _ _
  · rw [honestForest_short hAT _]
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
      rw [FtsExtract.honestInput_forest, FtsExtract.honestInput_forest]
      simp only [buildFts_short hAT]
  | ftsLeaf index coord leaf =>
      rw [FtsExtract.honestInput_ftsLeaf, FtsExtract.honestInput_ftsLeaf, builtSecret_short hAT]
      rfl
  | ftsNode index coord level node =>
      obtain ⟨-, -, hl, hn⟩ := hb
      have hn' : node < 2 ^ (11 - (level + 1)) := by
        have : 11 - level - 1 = 11 - (level + 1) := by omega
        rwa [this] at hn
      rw [FtsExtract.honestInput_ftsNode A index coord level node hl hn',
        FtsExtract.honestInput_ftsNode T index coord level node hl hn', builtSecret_short hAT,
        honInputL_short hAT]
end objects
theorem honestInput_length (answers : Answers) (position : Extract.Pos) :
    (Extract.honestInput answers position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step =>
      apply short_of_le
      rw [chainInput_length]; omega
  | leaf lay tree leaf =>
      apply short_of_le
      simp only [Extract.leafInput, listInput_length, List.length_drop, List.length_map, List.length_range]
      have := chainCount_le lay
      omega
  | node lay tree level node =>
      apply short_of_le
      simp [nodeInputP]
  | forest index =>
      rw [FtsExtract.honestInput_forest]
      apply short_of_le
      rw [Extract.forestInput, listInput_length]
      simp only [List.length_drop, List.length_map, List.length_range]
      omega
  | ftsLeaf index coord leaf =>
      apply short_of_le
      simp [ftsLeafInputP]
  | ftsNode index coord level node =>
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
end SigGolfCandidate.T3.Security.Wots.Ref
