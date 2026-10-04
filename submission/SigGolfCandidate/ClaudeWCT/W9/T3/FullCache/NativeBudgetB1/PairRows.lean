import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.FullCache.NativeBudget

namespace ClaudeWCT.W9.T3.PairRows
open OracleComp OracleSpec ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial V_publicSearch public_randomOracle
  encodingDecode)
open SigGolfCandidate.T3.Freshness (Avoids HasTag avoids_pure avoids_bind preserves avoids_shortHash_of_ne)
open ClaudeWCT.WCT9 (LayerMsg layerEncodingInput pairEncodingInputP layerCounterSearch)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) : HashInput :=
  pairEncodingInputP lay tree leaf left right (BitVec.ofNat 32 counter) 0
def layerTrial (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) : HashInput :=
  pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
def msgLeft : LayerMsg → Digest
  | .forest root => root
  | .pair left _ => left
def msgRight : LayerMsg → Digest
  | .forest _ => 0
  | .pair _ right => right
theorem pairTrial_length (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    (pairTrial lay tree leaf left right counter).length = 64 := by
  simp [pairTrial, pairEncodingInputP, bytesLE_length]
theorem pad64_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    pad64 (pairTrial lay tree leaf left right counter) = pairTrial lay tree leaf left right counter := by
  simp [pad64, pairTrial_length]
theorem layerTrial_eq (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    layerTrial lay tree leaf msg counter = pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter := by
  cases msg with
  | forest root =>
      have h12 : bytesLE 12 (0 : BitVec 96) = List.replicate 12 0 := by decide
      have h16 : bytesLE 16 (0 : Digest) = List.replicate 16 0 := by decide
      simp only [layerTrial, pairTrial, layerEncodingInput, encodingInput, pairEncodingInputP, msgLeft,
        msgRight, pad64, List.length_append, bytesLE_length, h12, h16, List.append_assoc,
        List.replicate_append_replicate]
  | pair left right =>
      exact pad64_pairTrial lay tree leaf left right counter
theorem layerTrial_length (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    (layerTrial lay tree leaf msg counter).length = 64 := by
  rw [layerTrial_eq, pairTrial_length]
theorem pairTrial_coordinates {lay lay' : Layer} {tree tree' leaf leaf' : Nat} {left left' right right' : Digest}
    {counter counter' : Nat} (ht : tree < 2 ^ 40) (ht' : tree' < 2 ^ 40) (hl : leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ 32) (hc : counter < 2 ^ 32) (hc' : counter' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right counter = pairTrial lay' tree' leaf' left' right' counter') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ left = left' ∧ right = right' ∧ counter = counter' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, hR⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨hL, hH⟩ := List.append_inj he (by simp [bytesLE_length])
  have hH := header_injective (by decide : 4 < 256) (by have := lay.isLt; omega) ht (by decide : 0 < 2 ^ 32) hl
    (by decide : 4 < 256) (by have := lay'.isLt; omega) ht' (by decide : 0 < 2 ^ 32) hl' (bytesLE_injective hH)
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hC
  exact ⟨Fin.ext hH.2.1, hH.2.2.1, hH.2.2.2.2, bytesLE_injective hL, bytesLE_injective hR, hC⟩
theorem pairTrial_injective (lay : Layer) (tree leaf : Nat) (left right : Digest) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right c = pairTrial lay tree leaf left right c') : c = c' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨-, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] using hC
theorem layerTrial_injective (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : layerTrial lay tree leaf msg c = layerTrial lay tree leaf msg c') : c = c' := by
  rw [layerTrial_eq, layerTrial_eq] at he
  exact pairTrial_injective lay tree leaf _ _ hc hc' he
@[simp] theorem queryHeader_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    SigGolfCandidate.T3.QuerySpace.queryHeader (pairTrial lay tree leaf left right counter) =
      bytesLE 16 (header 4 lay.val tree 0 leaf) := by
  simp [SigGolfCandidate.T3.QuerySpace.queryHeader, pairTrial, pairEncodingInputP, List.append_assoc,
    bytesLE_length]
theorem hasTag_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    HasTag 4 (pairTrial lay tree leaf left right counter) :=
  ⟨lay.val, tree, 0, leaf, queryHeader_pairTrial ..⟩
theorem pairTrial_ne_of_layer {lay other : Layer} (hne : lay ≠ other) (tree leaf : Nat) (left right : Digest)
    (counter : Nat) (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    pairTrial lay tree leaf left right counter ≠ pairTrial other tree' leaf' left' right' counter' := by
  intro he
  have hh := congrArg SigGolfCandidate.T3.QuerySpace.queryHeader he
  simp only [queryHeader_pairTrial] at hh
  apply SigGolfCandidate.T3.QuerySpace.header_ne_of_layer _ (bytesLE_injective hh)
  have h1 : lay.val < 256 := by have := lay.isLt; omega
  have h2 : other.val < 256 := by have := other.isLt; omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  exact fun h => hne (Fin.ext h)
theorem pairTrial_ne_digestTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat)
    (rho : Digest) (message : Message) (ctr : Nat) :
    pairTrial lay tree leaf left right counter ≠ digestTrial rho message ctr :=
  SigGolfCandidate.T3.Freshness.tagged_ne (hasTag_pairTrial ..)
    (SigGolfCandidate.T3.Freshness.hasTag_digest ..) (by decide)
theorem layerCounterSearch_public (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, layerCounterSearch lay tree leaf msg counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (layerTrial lay tree leaf msg) (encodingDecode lay)
        (fun c digits => pure (BitVec.ofNat 32 c, digits)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.layerCounterSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        shortHash, publicHash, bind_assoc, pure_bind, layerTrial, encodingDecode]
      apply bind_congr
      intro answer
      cases hd : decode lay (answer.extractLsb' 0 128) <;>
        simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem V_layerCounterSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (hstep : z * (SphincsSecurity.Completeness.failMass (encodingDecode lay) * b +
      (1 - SphincsSecurity.Completeness.failMass (encodingDecode lay))) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    V secret z (layerCounterSearch lay tree leaf msg counter fuel) cache ≤ b := by
  rw [layerCounterSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => layerTrial_length lay tree leaf msg c)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    hstep fuel counter hlimit cache hfresh
theorem layerCounterSearch_failure (secret : BitVec 256) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (layerCounterSearch lay tree leaf msg counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass (encodingDecode lay) ^ fuel := by
  rw [layerCounterSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    fuel counter hlimit cache hfresh
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, Cost.CBound (Cost.CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [Cost.CounterResult])
  | succ fuel ih =>
      intro counter
      unfold ClaudeWCT.WCT9.layerCounterSearch
      refine (Cost.bound_shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) 1
        (by cases msg <;> simp [layerEncodingInput, encodingInput, pairEncodingInputP, bytesLE_length])
        (by rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
              layerTrial lay tree leaf msg counter from rfl, layerTrial_length])).bind'
        (l := fuel) (fun answer _ => ?_) (by omega)
      cases hd : decode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, Cost.validDigits_decode hd⟩
theorem layerCounterSearch_none_iff (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (msg : LayerMsg) :
    ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = none ↔
      ∀ offset, offset < fuel → decode lay (evalWithAnswerFn answers
        (shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (counter + offset))))) = none := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [ClaudeWCT.WCT9.layerCounterSearch]
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind]
      cases hd : decode lay (evalWithAnswerFn answers
        (shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd, ih]
          constructor
          · intro hall offset hoff
            cases offset with
            | zero => simpa using hd
            | succ offset =>
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall offset (by omega)
          · intro hall offset hoff
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall (offset + 1) (by omega)
      | some digits =>
          simp only [hd, evalWithAnswerFn_pure, reduceCtorEq, false_iff]
          intro hall
          have := hall 0 (by omega)
          simp only [Nat.add_zero, hd, reduceCtorEq] at this
theorem eval_shortHash_layer (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) :
    evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))) =
      (answers (.inl (.inr (pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter)))).extractLsb' 0 128 := by
  rw [SigGolfCandidate.T3.Presampling.eval_shortHash, ← layerTrial_eq]
  rfl
theorem layerCounterSearch_forest_eval (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (root : Digest) : ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.forest root) counter fuel) =
        evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.pair root 0) counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      have hs : evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf (.forest root)
            (BitVec.ofNat 32 counter))) =
          evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf (.pair root 0)
            (BitVec.ofNat 32 counter))) := by
        rw [eval_shortHash_layer, eval_shortHash_layer]
        rfl
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind, hs]
      cases hd : decode lay (evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf
        (.pair root 0) (BitVec.ofNat 32 counter)))) <;> simp only [hd, ih]
def PairFreshBelow (n : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer, lay.val < n → ∀ tree leaf left right c, c < 2 ^ 32 →
    cache (pairTrial lay tree leaf left right c) = none
def AllSearchesFreshBC (cache : RCache) : Prop :=
  (∀ rho message c, c < 2 ^ 32 → cache (digestTrial rho message c) = none) ∧ PairFreshBelow 4 cache
@[simp] theorem allSearchesFreshBC_empty : AllSearchesFreshBC ∅ := by
  constructor
  · intro rho message c hc; rfl
  · intro lay hl tree leaf left right c hc; rfl
theorem PairFreshBelow.layerTrial {n : Nat} {cache : RCache} (h : PairFreshBelow n cache) (lay : Layer)
    (hl : lay.val < n) (tree leaf : Nat) (msg : LayerMsg) (c : Nat) (hc : c < 2 ^ 32) :
    cache (layerTrial lay tree leaf msg c) = none := by
  rw [layerTrial_eq]
  exact h lay hl tree leaf _ _ c hc
theorem PairFreshBelow.mono {n m : Nat} {cache : RCache} (h : PairFreshBelow n cache) (hm : m ≤ n) :
    PairFreshBelow m cache :=
  fun lay hl => h lay (by omega)
theorem avoids_layerCounterSearch (secret : BitVec 256) {lay other : Layer} (hne : lay ≠ other)
    (tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    Avoids secret (pairTrial other tree' leaf' left' right' counter')
      (layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.layerCounterSearch
      apply avoids_bind
      · apply avoids_shortHash_of_ne
        rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
          layerTrial lay tree leaf msg counter from rfl, layerTrial_eq]
        exact pairTrial_ne_of_layer hne tree leaf _ _ counter tree' leaf' left' right' counter'
      · intro answer
        split
        · exact ih _
        · exact avoids_pure _ _ _
theorem preserves_pairBelow {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, HasTag 4 target → Avoids secret target program)
    (n : Nat) (cache : RCache) (hc : PairFreshBelow n cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : PairFreshBelow n result.2 := by
  intro lay hl tree leaf left right c hlt
  rw [preserves secret _ program (h _ (hasTag_pairTrial ..)) cache result hr]
  exact hc lay hl tree leaf left right c hlt
theorem preserves_allSearchesBC {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, HasTag 4 target ∨ HasTag 12 target → Avoids secret target program)
    (cache : RCache) (hc : AllSearchesFreshBC cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : AllSearchesFreshBC result.2 := by
  constructor
  · intro rho message c hlt
    rw [preserves secret _ program (h _ (Or.inr (SigGolfCandidate.T3.Freshness.hasTag_digest ..))) cache result hr]
    exact hc.1 rho message c hlt
  · exact preserves_pairBelow secret program (fun target ht => h target (Or.inl ht)) 4 cache hc.2 result hr
theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : HasTag 4 target)
    (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.digestSearch
      refine avoids_bind (SigGolfCandidate.T3.Freshness.avoids_digest_encoding secret target ht rho message _) ?_
      intro output
      split
      · exact avoids_pure _ _ _
      · exact ih _
theorem digestSearch_preserves_pairBelow (secret : BitVec 256) (rho : Digest) (message : Message)
    (counter fuel : Nat) (cache : RCache) (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache)) :
    PairFreshBelow 4 result.2 :=
  preserves_pairBelow secret _ (fun target ht => avoids_digestSearch_encoding secret target ht rho message _ _)
    4 cache hc.2 result hr
theorem privateMac_preserves_fresh (secret : BitVec 256) (region : Region) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateMac region) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateMac secret target ht region) cache hc result hr
theorem privateNonce_preserves_fresh (secret : BitVec 256) (message : Message) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateNonce message) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateNonce secret target ht message) cache hc result hr
theorem keygen_fresh_from_empty_bc (secret : BitVec 256) (result : (Digest × Cache) × RCache)
    (hr : result ∈ support (roRun secret keygen ∅)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret keygen
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_keygen secret target ht) ∅
    allSearchesFreshBC_empty result hr
end ClaudeWCT.W9.T3.PairRows
