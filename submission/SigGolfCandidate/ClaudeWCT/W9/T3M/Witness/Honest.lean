import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Encode
import SigGolfCandidate.T3M.Witness.Normal
import SigGolfCandidate.T3M.Witness.Shaped
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.T3M.Witness.Roundtrip
import SigGolfCandidate.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness

section




namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wrho wdc wle32 wvalue wpath wchainPads wmerklePad wchainHeaderPad chainP layerP
  nodeHashP recoverLayerP chainP_zero_route nodeHashP_zero bytesLE_zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
@[simp] theorem Pads.zero_wctChain (k : WCT9.Coord) (t : Fin 7) : (0 : Pads).wctChain k t = (0, 0) := rfl
@[simp] theorem Pads.zero_wctChainHigh (k : WCT9.Coord) (t : Fin 7) : (0 : Pads).wctChainHigh k t = 0 := rfl
@[simp] theorem Pads.zero_wctMerkle (k : WCT9.Coord) (l : Fin 7) : (0 : Pads).wctMerkle k l = 0 := rfl
@[simp] theorem Pads.zero_chain' (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle' (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl
@[simp] theorem Pads.zero_chainHeader (lay : Layer) (i : Fin (chainCount lay)) :
    (0 : Pads).chainHeader lay i = 0 := rfl
@[simp] theorem Pads.zero_bc (lay : Layer) : (0 : Pads).bc lay = 0 := rfl
@[simp] theorem Pads.zero_toT3 : (0 : Pads).toT3 = 0 := rfl
theorem wctChainInputP_zero (index coord child t step : Nat) (value : Digest) :
    wctChainInputP index coord child t step 0 0 0 value = WCT9.chainInput index coord child t step value := by
  simp only [wctChainInputP, WCT9.chainInput, WCT9.ftsChainHeader, bytesLE_zero16]
@[simp] theorem wctChainP_zero (index coord child t start count : Nat) (value : Digest) :
    wctChainP index coord child t start count 0 0 0 value = WCT9.chain index coord child t start count value := by
  simp only [wctChainP, WCT9.chain, wctChainInputP_zero]
@[simp] theorem wctNodeHashP_zero (coord index heap : Nat) (left right : Digest) :
    wctNodeHashP coord index heap left 0 right = WCT9.wctNodeHash coord index heap left right := by
  simp only [wctNodeHashP, WCT9.wctNodeHash, nodeHashP_zero]
theorem recoverCoordinateP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord) :
    recoverCoordinateP sig 0 index output coord = WCT9.recoverCoordinate sig index output coord := by
  simp only [recoverCoordinateP, WCT9.recoverCoordinate, Pads.zero_wctChain, Pads.zero_wctChainHigh,
    Pads.zero_wctMerkle, wctChainP_zero, wctNodeHashP_zero]
theorem recoverFtsP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) :
    recoverFtsP sig 0 index output = WCT9.recoverFts sig index output := by
  unfold recoverFtsP WCT9.recoverFts
  rw [show recoverCoordinateP sig 0 index output = WCT9.recoverCoordinate sig index output from
    funext (recoverCoordinateP_zero sig index output)]
theorem layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    layerEncodingInputP lay tree leaf msg counter 0 = WCT9.layerEncodingInput lay tree leaf msg counter := by
  cases msg <;> rfl
theorem recoverLayerPairP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hindex : index < 2 ^ 31) :
    recoverLayerPairP sig 0 index lay digits = WCT9.recoverLayerPair sig index lay digits := by
  simp only [recoverLayerPairP, WCT9.recoverLayerPair, Pads.zero_chain', Pads.zero_chainHeader,
    chainP_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', nodeHashP_zero]
theorem verifyLayersBCP_zero (w : WCT9.Witness) (index : Nat) (hindex : index < 2 ^ 31) : ∀ n msg,
    verifyLayersBCP w 0 index n msg = WCT9.verifyLayersBC w index n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, layerEncodingInputP_zero, Pads.zero_toT3,
        SigGolfCandidate.T3M.recoverLayerP_zero _ _ _ _ hindex, recoverLayerPairP_zero _ _ _ _ hindex, ih]
      rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : WCT9.Witness) :
    verifyPads m pk w 0 = WCT9.Rev3.verify m pk w := by
  unfold verifyPads verifyPadsTail WCT9.Rev3.verify WCT9.verifyWith
  simp only [recoverFtsP_zero, verifyLayersBCP_zero _ _ (Nat.mod_lt _ (by decide))]
  rfl
theorem layerP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) :
    layerP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayerP (WCT9.toT3Signature (witDecP N w).signature) (padDecP N w).toT3 (N.toNat % 2 ^ 31) lay
        digits := by
  unfold layerP recoverLayerP
  simp only [Pads.toT3, padDecP, witDecP, WCT9.toT3Signature, hlay, or_true, if_true]
theorem layerPairP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerPairP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayerPairP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) lay digits := by
  unfold layerPairP recoverLayerPairP
  have hm : ∀ j : Fin (height lay - 1),
      (padDecP N w).merkle lay (Fin.castLE (Nat.sub_le _ _) j) = wmerklePad w lay j.val := by
    intro j
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (Or.inl (by omega))]
  simp only [hm]
  rfl
theorem layersBC_dec (N : HashOutput) (w : WBytes) : ∀ n msg,
    layersBC w (N.toNat % 2 ^ 31) n msg =
      verifyLayersBCP (witDecP N w) (padDecP N w) (N.toNat % 2 ^ 31) n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      unfold layersBC verifyLayersBCP
      by_cases hn : n = 0
      · subst n
        simp only [if_true, layerP_dec N w (Fin.ofNat 4 0) _ rfl]
        rfl
      · simp only [hn, if_false, layerPairP_dec N w, ih]
        rfl
theorem wctStep_none (w : WBytes) (N : HashOutput) (coord : WCT9.Coord) : wctStep w N none coord = pure none := rfl
theorem foldlM_wctStep_none (w : WBytes) (N : HashOutput) :
    ∀ l : List WCT9.Coord, l.foldlM (wctStep w N) none = pure none
  | [] => rfl
  | k :: ks => by rw [List.foldlM_cons, wctStep_none, pure_bind, foldlM_wctStep_none w N ks]
theorem wctCoordP_dec (N : HashOutput) (w : WBytes) (index : Nat) (coord : WCT9.Coord) :
    wctCoordP w index coord (WCT9.child N coord) (WCT9.rank N coord) =
      recoverCoordinateP (witDecP N w).signature (padDecP N w) index N coord := by
  unfold wctCoordP recoverCoordinateP
  have hm : ∀ level : Fin 6, (padDecP N w).wctMerkle coord level.castSucc = wmpad w coord.val level.val := by
    intro level
    simp only [padDecP, Fin.val_castSucc]
    rw [if_pos level.isLt]
  simp only [hm]
  rfl
theorem foldlM_wctStep_ok (w : WBytes) (N : HashOutput) (hok : ∀ k, fieldOk N k = true) :
    ∀ (l : List WCT9.Coord) (acc : List (Digest × Digest)),
      l.foldlM (wctStep w N) (some acc) =
        (fun rs => some (acc ++ rs)) <$>
          l.mapM (fun k => wctCoordP w (N.toNat % 2 ^ 31) k (WCT9.child N k) (WCT9.rank N k))
  | [], acc => by simp
  | k :: ks, acc => by
      rw [List.foldlM_cons, List.mapM_cons]
      have hs : wctStep w N (some acc) k =
          (fun pair => some (acc ++ [pair])) <$>
            wctCoordP w (N.toNat % 2 ^ 31) k (WCT9.child N k) (WCT9.rank N k) := by
        simp only [wctStep, hok k, Bool.not_true, Bool.false_eq_true, if_false, map_eq_bind_pure_comp]
        rfl
      rw [hs, bind_map_left, map_bind]
      congr 1; funext pair
      rw [foldlM_wctStep_ok w N hok ks (acc ++ [pair]), map_eq_bind_pure_comp, map_eq_bind_pure_comp,
        bind_assoc]
      congr 1; funext a
      simp only [Function.comp, pure_bind, List.append_assoc, List.singleton_append]
theorem fieldOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) (k : WCT9.Coord) :
    fieldOk N k = true := by
  have := ((WCT9.admissible_iff N).1 h).2 k
  exact decide_eq_true this
theorem gateOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) : gateOk N = true := by
  have := ((WCT9.admissible_iff N).1 h).1
  simp only [gateOk, decide_eq_true_eq]; exact this
theorem admissible_of_ok {N : HashOutput} (hg : gateOk N = true) (hf : ∀ k, fieldOk N k = true) :
    WCT9.admissible N = true := by
  rw [WCT9.admissible_iff]
  refine ⟨by simpa [gateOk] using hg, fun k => ?_⟩
  have := hf k
  exact of_decide_eq_true this
theorem wctP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    wctP w N = some <$> recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N := by
  unfold wctP recoverFtsP
  rw [foldlM_wctStep_ok w N (fieldOk_of_admissible h) _ [], bind_map_left, map_bind]
  simp only [List.nil_append]
  rw [show (fun k => wctCoordP w (N.toNat % 2 ^ 31) k (WCT9.child N k) (WCT9.rank N k)) =
    recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N from
      funext fun k => wctCoordP_dec N w _ k]
theorem foldlM_wctStep_bad (w : WBytes) (N : HashOutput) :
    ∀ (l : List WCT9.Coord) (st : Option (List (Digest × Digest))),
    (∃ k ∈ l, fieldOk N k = false) → ∀ r ∈ support (l.foldlM (wctStep w N) st), r = none := by
  intro l
  induction l with
  | nil => intro st h; obtain ⟨k, hk, -⟩ := h; simp at hk
  | cons k ks ih =>
      intro st h r hr
      rw [List.foldlM_cons, mem_support_bind_iff] at hr
      obtain ⟨s, hs, hr⟩ := hr
      by_cases hk : fieldOk N k = false
      · have h0 : wctStep w N st k = pure none := by
          rcases st with _ | roots
          · rfl
          · simp only [wctStep, hk, Bool.not_false, if_true]
        rw [h0] at hs
        simp only [support_pure, Set.mem_singleton_iff] at hs
        subst hs
        rw [foldlM_wctStep_none] at hr
        simpa using hr
      · obtain ⟨k', hk', hbad⟩ := h
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact absurd hbad hk
        · exact ih s ⟨k', hk', hbad⟩ r hr
theorem wctP_bad (w : WBytes) (N : HashOutput) (h : ∃ k, fieldOk N k = false) :
    ∀ r ∈ support (wctP w N), r = none := by
  intro r hr
  unfold wctP at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨s, hs, hr⟩ := hr
  obtain ⟨k, hk⟩ := h
  have := foldlM_wctStep_bad w N _ _ ⟨k, List.mem_finRange k, hk⟩ s hs
  subst this
  simpa using hr
theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  have hg := gateOk_of_admissible h
  have ha : WCT9.admissible N = true := h
  simp only [hg, ha, Bool.not_true, Bool.false_eq_true, if_false]
  rw [wctP_shaped N w h, bind_map_left]
  refine bind_congr (fun root => ?_)
  dsimp only
  rw [layersBC_dec]
  rfl
theorem rejectTail_false (w : WBytes) (N : HashOutput) : ∀ b ∈ support (rejectTail w N), b = false := by
  intro b hb
  unfold rejectTail at hb
  split at hb
  · simpa using hb
  · rw [support_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    rfl
theorem verifyP_normal (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w =
      if (wdc w).toNat ≥ WCT9.digestAttemptLimit then pure false else (do
        let N ← digest (wrho w) m (wdc w)
        if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N) := by
  rw [verifyP_eq_tail]
  unfold digestP
  split_ifs with h
  · simp
  · rw [bind_map_left]
    refine bind_congr (fun N => ?_)
    dsimp only
    split_ifs with hS
    · exact verifyTailP_shaped pk N w hS
    · unfold verifyTailP rejectTail
      by_cases hg : gateOk N = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, if_false]
        have hbad : ∃ k, fieldOk N k = false := by
          by_contra hall
          push Not at hall
          exact hS (admissible_of_ok hg fun k => by simpa using hall k)
        rw [map_eq_bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro r hr
        rw [wctP_bad w N hbad r hr]
        rfl
      · simp [hg]
end ClaudeWCT.W9.T3M
end

section


namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wle32 wrho wdc wvalue wpath wchainPads wmerklePad wchainHeaderPad sibOff zeros
  layerBytes layerBytes_length layerBytes_merkle layerBytes_chain merkleBlock chainBlock
  window window_append_left window_append_right window_flatMap_const window_full window_zeros readDigest_zeros
  readLE_bytesLE_32 extract_readLE layerBase rhoOff dcOff)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem headerBytes_length (w : WCT9.Witness) : (headerBytes w).length = 64 := by
  simp [headerBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem merkleBytes_length (c : Nat) (op : WCT9.Opening) : (merkleBytes c op).length = 448 := by
  unfold merkleBytes
  rw [List.length_flatMap]
  have h1 : ∀ l : Fin 7, (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (op.path l)).length = 64 := by
    intro l; split <;> simp [zeros, bytesLE_length]
  simp only [h1, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem chainBytes_length (op : WCT9.Opening) : (chainBytes op).length = 384 := by
  simp [chainBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length (op : WCT9.Opening) : (leafBytes op).length = 128 := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem regionBytes_length (c : Nat) (op : WCT9.Opening) : (regionBytes c op).length = 1024 := by
  simp only [regionBytes, List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length, zeros,
    List.length_replicate]
theorem wctBytes_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytes N sig).length = 9216 := by
  unfold wctBytes
  rw [List.length_flatMap]
  simp only [regionBytes_length, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem bcTopBlock_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (bcTopBlock lay leaf ls ctr).length = 64 := by
  unfold bcTopBlock; split <;> simp [zeros, bytesLE_length]
theorem height_pos' (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem layerBytesBC_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (layerBytesBC lay leaf ls ctr).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytesBC
  rw [List.length_append, bcTopBlock_length, List.length_drop, layerBytes_length]
  have := height_pos' lay
  have : 64 ≤ 64 * (height lay + chainCount lay) := by nlinarith
  omega
theorem layerRegion_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegion N w lay).length = 64 * (height lay + chainCount lay) := by
  unfold layerRegion; split
  · exact layerBytes_length _ _ _
  · exact layerBytesBC_length _ _ _ _
theorem witList_length_eq (N : HashOutput) (w : WCT9.Witness) : (witList N w).length = 24264 := by
  unfold witList
  simp only [List.length_append, headerBytes_length, wctBytes_length, zeros, List.length_replicate,
    List.length_flatMap, layerRegion_length]
  simp [List.finRange, height, chainCount]
theorem wdig_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (window (witList N w) off 16) := by
  unfold wdig witEnc readDigest window
  exact extract_readLE (witList N w) 24264 (by rw [witList_length_eq]) off 16
theorem wle32_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (window (witList N w) off 4)) := by
  unfold wle32 witEnc window
  exact extract_readLE (witList N w) 24264 (by rw [witList_length_eq]) off 4
section header
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 64) :
    window (witList N w) off n = window (headerBytes w) off n := by
  have hA : (headerBytes w ++ wctBytes N w.signature ++ zeros 1288).length = 10568 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, zeros, List.length_replicate]
  have hB : (headerBytes w ++ wctBytes N w.signature).length = 9280 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length]
  unfold witList
  rw [window_append_left _ _ _ _ (by rw [hA]; omega), window_append_left _ _ _ _ (by rw [hB]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
theorem wrho_witEnc : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
    Correctness.readDigest_bytesLE]
theorem wdc_witEnc : wdc (witEnc N w) = w.digestCounter := by
  unfold wdc dcOff
  rw [wle32_witEnc, win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_right _ _ _ _ (by simp [bytesLE_length]), bytesLE_length, Nat.sub_self,
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wctr3_witEnc : SigGolfCandidate.T3M.wle32 (witEnc N w) 32 = w.counters 3 := by
  rw [wle32_witEnc, win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - (bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12).length = 0 by
      simp [bytesLE_length, zeros],
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wpad3_witEnc : (witEnc N w).extractLsb' (8 * 36) 96 = 0 := by
  have h := extract_readLE (witList N w) 24264 (by rw [witList_length_eq]) 36 12
  unfold witEnc
  rw [show (96 : Nat) = 8 * 12 from rfl, h, show ((witList N w).drop 36).take 12 = window (witList N w) 36 12 from rfl,
    win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 36 - (bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3)).length
      = 0 by simp [bytesLE_length, zeros],
    window_zeros _ _ _ (by omega)]
  rfl
end header
theorem layer_prefix (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (((List.finRange 4).take lay.val).map fun l => (layerRegion N w l).length).sum = layerBase lay - 10568 := by
  simp only [layerRegion_length]
  fin_cases lay <;> simp [List.finRange, layerBase, height, chainCount]
theorem win_layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 64 * (height lay + chainCount lay)) :
    window (witList N w) (layerBase lay + j) m = window (layerRegion N w lay) j m := by
  have hb : 10568 ≤ layerBase lay := by fin_cases lay <;> simp [layerBase]
  have hA : (headerBytes w ++ wctBytes N w.signature ++ zeros 1288).length = 10568 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, zeros, List.length_replicate]
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := SigGolfCandidate.T3M.window_flatMap (List.finRange 4) (layerRegion N w) lay.val (by simp) j m
    (by rw [hlen, layerRegion_length]; omega)
  rw [layer_prefix N w lay, hlen] at key
  unfold witList
  rw [window_append_right _ _ _ _ (by rw [hA]; omega), hA,
    show layerBase lay + j - 10568 = (layerBase lay - 10568) + j by omega, key]
theorem layerRegion_tail (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat) (hj : 64 ≤ j) :
    window (layerRegion N w lay) j m =
      window (layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) j m := by
  unfold layerRegion
  split
  · rfl
  · unfold layerBytesBC
    rw [window_append_right _ _ _ _ (by rw [bcTopBlock_length]; exact hj), bcTopBlock_length]
    unfold window
    rw [List.drop_drop]
    congr 2
    omega
theorem layerRegion_top (N : HashOutput) (w : WCT9.Witness) (j m : Nat) :
    window (layerRegion N w 0) j m =
      window (layerBytes 0 (route (N.toNat % 2 ^ 31) 0).1 (w.signature.layers 0)) j m := by
  unfold layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
theorem win_layer (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 64 * (height lay + chainCount lay)) (hj : 64 ≤ j ∨ lay.val = 0) :
    window (witList N w) (layerBase lay + j) m =
      window (layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) j m := by
  rw [win_layerRegion N w lay j m hjm]
  rcases hj with hj | hj
  · exact layerRegion_tail N w lay j m hj
  · have hl : lay = 0 := Fin.ext hj
    subst hl
    exact layerRegion_top N w j m
section t3
variable (N : HashOutput) (w : WCT9.Witness)
theorem layerBase_ge (lay : Layer) : 10568 ≤ layerBase lay := by
  fin_cases lay <;> simp [layerBase]
theorem wvalue_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc N w) lay i.val = (w.signature.layers lay).values i := by
  have hi := i.isLt
  have hh := height_pos' lay
  unfold wvalue chainBlock
  rw [wdig_witEnc, show layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val) + 48
      = layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 48) by omega,
    win_layer _ _ _ _ _ (by omega) (Or.inl (by omega)), layerBytes_chain _ _ _ _ _ (by omega),
    window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wchainPads_witEnc (lay : Layer) (i : Fin (chainCount lay)) : wchainPads (witEnc N w) lay i.val = (0, 0) := by
  have hi := i.isLt
  have hh := height_pos' lay
  unfold wchainPads chainBlock
  rw [wdig_witEnc, wdig_witEnc,
    show layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val)
      = layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 0) by omega,
    show layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 0) + 32
      = layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 32) by omega,
    win_layer _ _ _ _ _ (by omega) (Or.inl (by omega)), win_layer _ _ _ _ _ (by omega) (Or.inl (by omega)),
    layerBytes_chain _ _ _ _ _ (by omega), layerBytes_chain _ _ _ _ _ (by omega),
    window_append_left _ _ _ _ (by simp [zeros]), window_append_left _ _ _ _ (by simp [zeros]),
    window_zeros _ _ _ (by omega), window_zeros _ _ _ (by omega), readDigest_zeros]
theorem wchainHeaderPad_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wchainHeaderPad (witEnc N w) lay i.val = 0 := by
  have hi := i.isLt
  have hh := height_pos' lay
  unfold wchainHeaderPad chainBlock
  rw [wdig_witEnc, show layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val) + 16
      = layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 16) by omega,
    win_layer _ _ _ _ _ (by omega) (Or.inl (by omega)), layerBytes_chain _ _ _ _ _ (by omega),
    window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), readDigest_zeros]
  rfl
theorem win_bcTop (lay : Layer) (hlay : lay.val ≠ 0) (o m : Nat) (hom : o + m ≤ 64) :
    window (witList N w) (layerBase lay + o) m =
      window (bcTopBlock lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
        (w.counters (Fin.ofNat 4 (lay.val - 1)))) o m := by
  have hh := height_pos' lay
  rw [win_layerRegion N w lay o m (by nlinarith)]
  unfold layerRegion layerBytesBC
  rw [if_neg hlay, window_append_left _ _ _ _ (by rw [bcTopBlock_length]; exact hom)]
theorem wpath_witEnc (lay : Layer) (j : Fin (height lay)) :
    wpath (witEnc N w) lay (route (N.toNat % 2 ^ 31) lay).1 j.val = (w.signature.layers lay).path j := by
  have hj := j.isLt
  have hh := height_pos' lay
  have hs : sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2) ≤ 48 := by unfold sibOff; split <;> omega
  unfold wpath merkleBlock
  rw [wdig_witEnc, show layerBase lay + 64 * (height lay - 1 - j.val) +
      sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2)
    = layerBase lay + (64 * (height lay - 1 - j.val) +
      sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2)) by omega]
  by_cases htop : j.val + 1 < height lay ∨ lay.val = 0
  · rw [win_layer _ _ _ _ _ (by omega) (htop.imp (fun h => by omega) id),
      layerBytes_merkle _ _ _ _ _ (by omega)]
    unfold sibOff
    split
    · rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
        Correctness.readDigest_bytesLE]
    · rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
        window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
  · push Not at htop
    obtain ⟨hj1, hlay0⟩ := htop
    have hjv : j.val = height lay - 1 := by omega
    have hjt : j = WCT9.topLevel lay := Fin.ext hjv
    rw [show 64 * (height lay - 1 - j.val) = 0 by omega, Nat.zero_add,
      win_bcTop N w lay hlay0 _ _ (by omega), hjv]
    unfold bcTopBlock sibOff
    rw [← hjt]
    by_cases hb : (route (N.toNat % 2 ^ 31) lay).1 / 2 ^ (height lay - 1) % 2 = 1
    · rw [if_pos hb, if_pos hb, window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (bytesLE_length _ _),
        Correctness.readDigest_bytesLE]
    · rw [if_neg hb, if_neg hb, window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
        show 48 - (zeros 32 ++ bytesLE 4 (w.counters (Fin.ofNat 4 (lay.val - 1))) ++ zeros 12).length = 0 by
          simp [bytesLE_length, zeros],
        window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wmerklePad_witEnc (lay : Layer) (j : Fin (height lay)) (hj : j.val + 1 < height lay ∨ lay.val = 0) :
    wmerklePad (witEnc N w) lay j.val = 0 := by
  have hjl := j.isLt
  have hh := height_pos' lay
  unfold wmerklePad merkleBlock
  rw [wdig_witEnc, show layerBase lay + 64 * (height lay - 1 - j.val) + 32
      = layerBase lay + (64 * (height lay - 1 - j.val) + 32) by omega,
    win_layer _ _ _ _ _ (by omega) (hj.imp (fun h => by omega) id),
    layerBytes_merkle _ _ _ _ _ (by omega)]
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length]),
      readDigest_zeros]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega), readDigest_zeros]
theorem bcCounterOff_upper (lay : Layer) (h : lay.val < 3) :
    bcCounterOff lay = layerBase (Fin.ofNat 4 (lay.val + 1)) + 32 := by
  fin_cases lay <;> first | rfl | (exfalso; simp at h)
theorem wbcCtr_witEnc (lay : Layer) : wbcCtr (witEnc N w) lay = w.counters lay := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wctr3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (Fin.ofNat 4 (lay.val + 1) : Layer).val = lay.val + 1 := Nat.mod_eq_of_lt (by omega)
    unfold wbcCtr
    rw [bcCounterOff_upper lay hlt, wle32_witEnc,
      win_bcTop N w _ (by rw [hv]; omega) 32 4 (by omega)]
    have hc : (Fin.ofNat 4 ((Fin.ofNat 4 (lay.val + 1) : Layer).val - 1) : Layer) = lay := by
      apply Fin.ext; rw [hv]; simp [Fin.val_ofNat]
    rw [hc]
    unfold bcTopBlock
    split
    · rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
        show 32 - (bytesLE 16 _ ++ zeros 16).length = 0 by simp [bytesLE_length, zeros],
        window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
    · rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_right _ _ _ _ (by simp [zeros]), show 32 - (zeros 32).length = 0 by simp [zeros],
        window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wbcPad_witEnc (lay : Layer) : wbcPad (witEnc N w) lay = 0 := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wpad3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (Fin.ofNat 4 (lay.val + 1) : Layer).val = lay.val + 1 := Nat.mod_eq_of_lt (by omega)
    unfold wbcPad witEnc
    rw [bcCounterOff_upper lay hlt, show (96 : Nat) = 8 * 12 from rfl,
      extract_readLE (witList N w) 24264 (by rw [witList_length_eq]) _ 12,
      show ((witList N w).drop (layerBase (Fin.ofNat 4 (lay.val + 1)) + 32 + 4)).take 12 =
        window (witList N w) (layerBase (Fin.ofNat 4 (lay.val + 1)) + 36) 12 from rfl,
      win_bcTop N w _ (by rw [hv]; omega) 36 12 (by omega)]
    unfold bcTopBlock
    split
    · rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
        show 36 - (bytesLE 16 _ ++ zeros 16 ++ bytesLE 4 _).length = 0 by simp [bytesLE_length, zeros],
        window_zeros _ _ _ (by omega)]
      rfl
    · rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
        window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
        show 36 - (zeros 32 ++ bytesLE 4 _).length = 0 by simp [bytesLE_length, zeros],
        window_zeros _ _ _ (by omega)]
      rfl
end t3
theorem win_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o n : Nat) (h : o + n ≤ 1024) :
    window (witList N w) (regionBase k.val + o) n =
      window (regionBytes (WCT9.child N k).val (w.signature.openings k)) o n := by
  have hk := k.isLt
  unfold witList
  rw [window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, zeros, List.length_replicate, regionBase]
      omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length, regionBase]; omega),
    window_append_right _ _ _ _ (by simp only [headerBytes_length, regionBase]; omega),
    headerBytes_length, show regionBase k.val + o - 64 = 1024 * k.val + o by unfold regionBase; omega]
  unfold wctBytes
  rw [window_flatMap_const _ _ 1024 (fun _ => regionBytes_length _ _) k.val (by simp [hk]) o n h]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
theorem wdig_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o : Nat) (h : o + 16 ≤ 1024) :
    wdig (witEnc N w) (regionBase k.val + o) =
      readDigest (window (regionBytes (WCT9.child N k).val (w.signature.openings k)) o 16) := by
  rw [wdig_witEnc, win_region N w k o 16 h]
section region
variable (c : Nat) (op : WCT9.Opening)
theorem region_merkle (o n : Nat) (h : o + n ≤ 448) :
    window (regionBytes c op) o n = window (merkleBytes c op) o n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length]; omega)]
theorem region_chain (o n : Nat) (h0 : 448 ≤ o) (h : o + n ≤ 832) :
    window (regionBytes c op) o n = window (chainBytes op) (o - 448) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length]; omega), merkleBytes_length]
theorem region_prefix (o n : Nat) (h0 : 832 ≤ o) (h : o + n ≤ 880) :
    window (regionBytes c op) o n = zeros n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length]
  exact window_zeros _ _ _ (by omega)
theorem region_leaf (o n : Nat) (h0 : 880 ≤ o) (h : o + n ≤ 1008) :
    window (regionBytes c op) o n = window (leafBytes op) (o - 880) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, zeros, List.length_replicate]
theorem merkleBytes_window (l : Fin 7) (o : Nat) (ho : o + 16 ≤ 64) :
    window (merkleBytes c op) (64 * (6 - l.val) + o) 16 =
      window (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (op.path l)) o 16 := by
  have hl := l.isLt
  unfold merkleBytes
  rw [window_flatMap_const _ _ 64 (fun j => by split <;> simp [zeros, bytesLE_length]) (6 - l.val)
    (by simp; omega) o 16 ho]
  have hj : ((List.finRange 7).reverse[6 - l.val]'(by simp; omega)) = l := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem chainBytes_window (i : Fin 6) (o : Nat) (ho : o + 16 ≤ 64) :
    window (chainBytes op) (64 * (5 - i.val) + o) 16 = window (zeros 48 ++ bytesLE 16 (op.values i.succ)) o 16 := by
  have hi := i.isLt
  unfold chainBytes
  rw [window_flatMap_const _ _ 64 (fun j => by simp [zeros, bytesLE_length]) (5 - i.val) (by simp; omega) o 16 ho]
  have hj : ((List.finRange 6).reverse[5 - i.val]'(by simp; omega)) = i := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem leafBytes_window_zero : window (leafBytes op) 0 16 = bytesLE 16 (op.values 0) := by
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem leafBytes_window_succ (i : Fin 6) : window (leafBytes op) (32 + 16 * i.val) 16 = bytesLE 16 (op.values i.succ) := by
  have hi := i.isLt
  unfold leafBytes
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 + 16 * i.val - (bytesLE 16 (op.values 0) ++ zeros 16).length = 16 * i.val + 0 by
      simp [bytesLE_length, zeros],
    window_flatMap_const _ _ 16 (fun j => bytesLE_length _ _) i.val (by simp [hi]) 0 16 le_rfl,
    window_full _ _ (bytesLE_length _ _)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
end region
section fields
variable (N : HashOutput) (w : WCT9.Witness)
theorem wopen_witEnc (k : WCT9.Coord) (t : Fin 7) :
    wopen (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  unfold wopen wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (832 - 64 * 0) + 48 = regionBase k.val + 880 by omega,
      wdig_region N w k _ (by omega), region_leaf _ _ _ _ le_rfl (by omega), Nat.sub_self,
      leafBytes_window_zero, Correctness.readDigest_bytesLE]
    rfl
  · have hi : i < 6 := by omega
    dsimp only
    rw [show regionBase k.val + (832 - 64 * (i + 1)) + 48 = regionBase k.val + (448 + (64 * (5 - i) + 48)) by
        omega, wdig_region N w k _ (by omega), region_chain _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (5 - i) + 48) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + 48 by simp,
      chainBytes_window _ _ _ (by omega), window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _),
      Correctness.readDigest_bytesLE]
    rfl
theorem wleaf_witEnc (k : WCT9.Coord) (t : Fin 7) :
    wleaf (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  rcases t with ⟨_ | i, ht⟩
  · rw [show (⟨0, ht⟩ : Fin 7).val = 0 from rfl, wleaf_zero]
    exact wopen_witEnc N w k ⟨0, ht⟩
  · have hi : i < 6 := by omega
    unfold wleaf wctLeafSlot
    dsimp only
    rw [if_neg (by omega), show regionBase k.val + (896 + 16 * (i + 1)) = regionBase k.val + (880 + (32 + 16 * i)) by
        omega, wdig_region N w k _ (by omega), region_leaf _ _ _ _ (by omega) (by omega),
      show 880 + (32 + 16 * i) - 880 = 32 + 16 * (⟨i, hi⟩ : Fin 6).val by simp,
      leafBytes_window_succ, Correctness.readDigest_bytesLE]
    rfl
theorem wreveal_witEnc (k : WCT9.Coord) (t : Fin 7) (d : Nat) :
    wreveal (witEnc N w) k.val t.val d = (w.signature.openings k).values t := by
  unfold wreveal
  split
  · exact wleaf_witEnc N w k t
  · exact wopen_witEnc N w k t
theorem wcpads_witEnc (k : WCT9.Coord) (t : Fin 7) : wcpads (witEnc N w) k.val t.val = (0, 0) := by
  unfold wcpads wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (832 - 64 * 0) = regionBase k.val + 832 by omega,
      show regionBase k.val + 832 + 32 = regionBase k.val + 864 by omega,
      wdig_region N w k _ (by omega), wdig_region N w k _ (by omega),
      region_prefix _ _ _ _ le_rfl (by omega), region_prefix _ _ _ _ (by omega) (by omega), readDigest_zeros]
  · have hi : i < 6 := by omega
    dsimp only
    rw [show regionBase k.val + (832 - 64 * (i + 1)) = regionBase k.val + (448 + (64 * (5 - i) + 0)) by omega,
      show regionBase k.val + (448 + (64 * (5 - i) + 0)) + 32 = regionBase k.val + (448 + (64 * (5 - i) + 32)) by
        omega,
      wdig_region N w k _ (by omega), wdig_region N w k _ (by omega),
      region_chain _ _ _ _ (by omega) (by omega), region_chain _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (5 - i) + 0) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + 0 by simp,
      show 448 + (64 * (5 - i) + 32) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + 32 by simp,
      chainBytes_window _ _ _ (by omega), chainBytes_window _ _ _ (by omega),
      window_append_left _ _ _ _ (by simp [zeros]), window_append_left _ _ _ _ (by simp [zeros]),
      window_zeros _ _ _ (by omega), window_zeros _ _ _ (by omega), readDigest_zeros]
theorem wcHeaderPad_witEnc (k : WCT9.Coord) (t : Fin 7) : wcHeaderPad (witEnc N w) k.val t.val = 0 := by
  unfold wcHeaderPad wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (832 - 64 * 0) + 16 = regionBase k.val + 848 by omega,
      wdig_region N w k _ (by omega), region_prefix _ _ _ _ (by omega) (by omega), readDigest_zeros]
    rfl
  · have hi : i < 6 := by omega
    dsimp only
    rw [show regionBase k.val + (832 - 64 * (i + 1)) + 16 = regionBase k.val + (448 + (64 * (5 - i) + 16)) by omega,
      wdig_region N w k _ (by omega), region_chain _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (5 - i) + 16) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + 16 by simp,
      chainBytes_window _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]),
      window_zeros _ _ _ (by omega), readDigest_zeros]
    rfl
theorem wsib_witEnc (k : WCT9.Coord) (l : Fin 7) :
    wsib (witEnc N w) k.val (WCT9.child N k).val l.val = (w.signature.openings k).path l := by
  have hl := l.isLt
  have hs : sibOff ((WCT9.child N k).val / 2 ^ l.val % 2) ≤ 48 := by unfold sibOff; split <;> omega
  unfold wsib wctMerkleBlock
  rw [show regionBase k.val + 64 * (6 - l.val) + sibOff ((WCT9.child N k).val / 2 ^ l.val % 2) =
      regionBase k.val + (64 * (6 - l.val) + sibOff ((WCT9.child N k).val / 2 ^ l.val % 2)) by omega,
    wdig_region N w k _ (by omega), region_merkle _ _ _ _ (by omega), merkleBytes_window _ _ _ _ (by omega)]
  unfold sibOff
  split
  · rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
      Correctness.readDigest_bytesLE]
  · rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wmpad_witEnc (k : WCT9.Coord) (l : Fin 7) : wmpad (witEnc N w) k.val l.val = 0 := by
  have hl := l.isLt
  unfold wmpad wctMerkleBlock
  rw [show regionBase k.val + 64 * (6 - l.val) + 32 = regionBase k.val + (64 * (6 - l.val) + 32) by omega,
    wdig_region N w k _ (by omega), region_merkle _ _ _ _ (by omega), merkleBytes_window _ _ _ _ (by omega)]
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length]),
      readDigest_zeros]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega),
      readDigest_zeros]
end fields
theorem witDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : witDecP N (witEnc N w) = w := by
  obtain ⟨⟨rho, openings, layers⟩, dc, ctr⟩ := w
  unfold witDecP
  simp only [WCT9.Witness.mk.injEq, WCT9.Signature.mk.injEq]
  refine ⟨⟨wrho_witEnc N _, funext fun k => ?_, funext fun lay => ?_⟩, wdc_witEnc N _,
    funext fun lay => wbcCtr_witEnc N _ lay⟩
  · have hv := fun t => wreveal_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k t
      (WCT9.digit (WCT9.rank N k) t)
    have hp := fun l => wsib_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k l
    simp only at hv hp
    rcases ho : openings k with ⟨vals, path⟩
    rw [ho] at hv hp
    simp only [WCT9.Opening.mk.injEq]
    exact ⟨funext hv, funext hp⟩
  · exact SigGolfCandidate.T3M.LayerSignature.ext' (funext fun i => wvalue_witEnc N _ lay i)
      (funext fun j => wpath_witEnc N _ lay j)
theorem padDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : padDecP N (witEnc N w) = 0 := by
  unfold padDecP
  show Pads.mk _ _ _ _ _ _ _ = Pads.mk _ _ _ _ _ _ _
  congr 1
  · funext k t; exact wcpads_witEnc N w k t
  · funext k t; exact wcHeaderPad_witEnc N w k t
  · funext k l; split
    · exact wmpad_witEnc N w k l
    · rfl
  · funext lay i; exact wchainPads_witEnc N w lay i
  · funext lay j; split
    · rename_i h; exact wmerklePad_witEnc N w lay j h
    · rfl
  · funext lay i; exact wchainHeaderPad_witEnc N w lay i
  · funext lay; exact wbcPad_witEnc N w lay
end ClaudeWCT.W9.T3M
end

section



namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wdig wrho wdc eval_countCalls_bind_congr eval_countCalls_fst eval_map)
set_option linter.unusedSimpArgs false
def honestProgramCore (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← WCT9.Rev3.expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => WCT9.Rev3.verify message keys.1 witness
def honestProgramB (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let wb ← expandB message keys.1 sig
    match wb with
    | none => pure false
    | some wb => verifyP message keys.1 wb
def ExpandEqExpandN : Prop := ∀ (m : Message) (pk : Digest) (σ : WCT9.Signature),
  WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ
def VerifyPWitEncEval : Prop := ∀ (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness),
  evalWithAnswerFn answers (expandN m pk σ) = some (N, w) →
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w))
def HonestBEval : Prop := ∀ (answers : Correctness.Answers) (m : Message),
  evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m)
theorem expand_eq_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ := by
  unfold WCT9.Rev3.expand WCT9.expandWith expandN
  rw [map_bind]; congr 1; funext r
  rcases r with _ | ⟨counter, output⟩
  · simp
  · simp only
    rw [map_bind]; congr 1; funext root
    rw [map_bind]; congr 1; funext r
    rcases r with _ | ⟨root, counters⟩
    · simp
    · simp only
      split <;> simp
theorem expandEqExpandN_holds : ExpandEqExpandN := expand_eq_expandN
structure ExpandFacts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) : Prop where
  sig : w.signature = σ
  dc : w.digestCounter.toNat < WCT9.digestAttemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : WCT9.admissible N = true
theorem expandN_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ExpandFacts answers m pk σ N w := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (WCT9.expandLayersBC σ (output.toNat % 2 ^ 31) 4
          (.forest (evalWithAnswerFn answers (WCT9.recoverFts σ (output.toNat % 2 ^ 31) output)))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨_, hcounter, houtput, hadm⟩ := WCT9.digestSearch_some_good answers σ.rho m
              WCT9.digestAttemptLimit 0 counter output (by unfold WCT9.digestAttemptLimit; norm_num) hd
            exact ⟨rfl, by simpa using hcounter, houtput, hadm⟩
theorem verifyP_witEnc_eval (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w)) := by
  have F := expandN_facts answers m pk σ N w he
  have hv : verifyP m pk (witEnc N w) =
      digest w.signature.rho m w.digestCounter >>= verifyTailP pk (witEnc N w) := by
    rw [verifyP_eq_tail]
    unfold digestP
    rw [wdc_witEnc, wrho_witEnc, if_neg (by have := F.dc; omega), bind_map_left]
  have hw : WCT9.Rev3.verify m pk w =
      digest w.signature.rho m w.digestCounter >>= fun N' => verifyPadsTail pk N' w 0 := by
    rw [← verifyPads_zero]
    unfold verifyPads
    rw [if_neg (by have := F.dc; omega)]
  rw [hv, hw]
  apply eval_countCalls_bind_congr
  rw [F.sig, F.digest, verifyTailP_shaped pk N _ F.adm, witDecP_witEnc, padDecP_witEnc]
theorem verifyPWitEncEval_holds : VerifyPWitEncEval := verifyP_witEnc_eval
theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    evalWithAnswerFn answers (expandB m pk σ) =
      (evalWithAnswerFn answers (expandN m pk σ)).map (fun x => witEnc x.1 x.2) := by
  unfold expandB; rw [eval_map]
theorem honestB_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m) := by
  unfold honestProgramB honestProgramCore
  simp only [evalWithAnswerFn_bind]
  cases hs : evalWithAnswerFn answers (WCT9.Rev3.sign (evalWithAnswerFn answers WCT9.Rev3.keygen).2 m) with
  | none => rfl
  | some sig =>
      simp only []
      rw [expand_eq_expandN, evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_map, eval_expandB]
      cases hx : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers WCT9.Rev3.keygen).1 sig) with
      | none => rfl
      | some x =>
          obtain ⟨N, w⟩ := x
          simp only [Option.map_some]
          have := verifyP_witEnc_eval answers m _ sig N w hx
          have h1 := congrArg Prod.fst this
          rwa [eval_countCalls_fst, eval_countCalls_fst] at h1
theorem honestBEval_holds : HonestBEval := honestB_eval
end ClaudeWCT.W9.T3M
end
