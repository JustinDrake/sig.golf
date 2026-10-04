import SigGolfCandidate.ClaudeWCT.WCT9.Queries

namespace ClaudeWCT.WCT9.Cost
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_buildChild (index coord selected : Nat) (word : Rank) (hcoord : coord < 9)
    (hsel : selected < 128) :
    CBound (fun result : Digest × List Digest => result.2.length = 7) 27 (buildChild index coord selected word) :=
  cbound_of_ftsBound (ftsBound_buildChild index coord selected word hcoord hsel)
theorem bound_buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    CBound (fun _ => True) 3582 (buildCoordinate index coord selected word) :=
  cbound_of_ftsBound (ftsBound_buildCoordinate index coord selected word)
theorem bound_forestPk (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    CBound (fun _ => True) 5 (WCT9.forestPk index pairs) :=
  cbound_of_ftsBound (ftsBound_forestPk index pairs hlen)
theorem bound_forestRows (index : Nat) (output : HashOutput) :
    CBound (fun state : List Opening × List (Digest × Digest) => state.1.length = 9 ∧ state.2.length = 9) 32238
      (forestRows index output) :=
  cbound_of_ftsBound (ftsBound_forestRows index output)
theorem bound_signForest (index : Nat) (output : HashOutput) :
    CBound (fun result : List Opening × Digest => result.1.length = 9) 32243 (signForest index output) :=
  cbound_of_ftsBound (ftsBound_signForest index output)
theorem bound_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord) :
    CBound (fun _ => True) 14 (recoverCoordinate sig index output coord) :=
  cbound_of_ftsBound (ftsBound_recoverCoordinate index sig output coord)
theorem bound_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    CBound (fun _ => True) 131 (recoverFts sig index output) :=
  cbound_of_ftsBound (ftsBound_recoverFts index sig output)
theorem signForest_blocks : 9 * (128 * (4 + 21 + 2) + 126) + 5 = 32243 := by norm_num
theorem verifyFts_blocks : 9 * (6 + 2 + 6) + 5 + 1 = 132 := by norm_num
def DigestResult (out : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ counter output, out = some (counter, output) → admissible output = true
theorem bound_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, CBound DigestResult fuel (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [DigestResult])
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      refine (bound_digest rho message (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun output _ => ?_) (by omega)
      split
      · rename_i hgood
        refine .pure (some (BitVec.ofNat 32 counter, output)) fuel ?_
        intro other value hv
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
        exact hgood
      · exact ih (counter + 1)
theorem bound_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : BitVec 32) :
    CBound (fun _ => True) 1 (shortHash (layerEncodingInput lay tree leaf msg counter)) := by
  cases msg <;> apply bound_shortHash <;>
    simp [layerEncodingInput, encodingInput, pairEncodingInputP, pad64_length, SphincsSecurity.bytesLE_length]
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, CBound (CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [CounterResult])
  | succ fuel ih =>
      intro counter
      unfold layerCounterSearch
      refine (bound_layerEncoding lay tree leaf msg (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun answer _ => ?_) (by omega)
      cases hd : decode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, validDigits_decode hd⟩
theorem bound_signLayersBC (cache : Cache) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + layerFixedCost n) (signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero =>
      intro msg
      exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold signLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg counterLimit 0).bind'
        (l := n * counterLimit + layerFixedCost (n + 1)) (fun out hout => ?_)
        (by simp only [Nat.add_mul, Nat.one_mul]; omega)
      cases out with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hout counter digits rfl
          dsimp only
          by_cases hn : n = 0
          · subst n
            simp only [ite_true]
            refine (bound_signTop cache _ digits hd.1 hd.2.1).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCost])
          · simp only [hn, ite_false]
            refine (bound_buildTree (Fin.ofNat 4 n) _ _ digits hd.2.2).bind'
              (l := n * counterLimit + layerFixedCost n) (fun result _ => ?_)
              (by simp only [layerFixedCost, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun previous _ => ?_) (by omega)
            cases previous <;> exact .pure _ 0 trivial
def recoverLayerPairCost (lay : Layer) : Nat := capacity lay - target lay + leafHashCost lay + (height lay - 1)
theorem recoverLayerPairCost_succ (lay : Layer) : recoverLayerPairCost lay + 1 = recoverLayerCost lay := by
  have : 1 ≤ height lay := by fin_cases lay <;> decide
  unfold recoverLayerPairCost recoverLayerCost
  omega
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerPairCost lay) (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_leafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerPairCost]
    omega
def recoveryLayersCostBC : Nat → Nat
  | 0 => 0
  | n + 1 => (if n = 0 then recoverLayerCost (Fin.ofNat 4 n) else recoverLayerPairCost (Fin.ofNat 4 n)) +
      recoveryLayersCostBC n
theorem recoveryLayersCostBC_add : recoveryLayersCostBC 4 + 3 = recoveryLayersCost 4 := by
  have h1 := recoverLayerPairCost_succ (Fin.ofNat 4 1)
  have h2 := recoverLayerPairCost_succ (Fin.ofNat 4 2)
  have h3 := recoverLayerPairCost_succ (Fin.ofNat 4 3)
  simp only [recoveryLayersCostBC, recoveryLayersCost, if_true, show (3 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (1 : Nat) ≠ 0 by decide, if_false]
  omega
theorem recoveryLayersCostBC_four_le : recoveryLayersCostBC 4 ≤ 481 := by
  have h := recoveryLayersCostBC_add
  have h4 := recoveryLayersCost_four
  omega
theorem bound_verifyLayersBC (w : Witness) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n + recoveryLayersCostBC n) (verifyLayersBC w index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold verifyLayersBC
      dsimp only
      split
      · exact .pure _ _ trivial
      · refine (bound_layerEncoding _ _ _ msg _).bind'
          (l := recoveryLayersCostBC (n + 1) + n) (fun answer _ => ?_) (by simp only [recoveryLayersCostBC]; omega)
        cases hd : decode (Fin.ofNat 4 n) answer with
        | none => exact .pure _ _ trivial
        | some digits =>
            dsimp only
            by_cases hn : n = 0
            · subst n
              simp only [ite_true]
              rw [map_eq_bind_pure_comp]
              refine (bound_recoverLayer _ index (Fin.ofNat 4 0) digits
                (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2).bind'
                (l := 0) (fun value _ => .pure _ 0 trivial) (by simp [recoveryLayersCostBC])
            · simp only [hn, ite_false]
              exact (bound_recoverLayerPair w.signature index (Fin.ofNat 4 n) digits
                (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2).bind'
                (l := n + recoveryLayersCostBC n) (fun pair _ => ih _)
                (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
theorem bound_expandLayersBC (sig : Signature) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + recoveryLayersCostBC n) (expandLayersBC sig index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold expandLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) _ _ msg counterLimit 0).bind'
        (l := recoveryLayersCostBC (n + 1) + n * counterLimit)
        (fun found hf => ?_) (by simp only [recoveryLayersCostBC, Nat.add_mul, Nat.one_mul]; omega)
      cases found with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hf counter digits rfl
          dsimp only
          by_cases hn : n = 0
          · subst n
            simp only [ite_true]
            refine (bound_recoverLayer _ index (Fin.ofNat 4 0) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := 0) (fun value _ => .pure _ 0 trivial) (by simp [recoveryLayersCostBC])
          · simp only [hn, ite_false]
            refine (bound_recoverLayerPair sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := n * counterLimit + recoveryLayersCostBC n) (fun value _ => ?_)
              (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun result _ => ?_) (by omega)
            cases result <;> exact .pure _ 0 trivial
theorem bound_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118167 + limit + 4 * counterLimit) (signPayloadWith limit cache message) := by
  rw [signPayloadWith_eq]
  refine (bound_privateNonce message).bind' (l := 118165 + limit + 4 * counterLimit)
    (fun rho _ => ?_) (by omega)
  refine (bound_digestSearch rho message limit 0).bind' (l := 118165 + 4 * counterLimit)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_signForest _ output).bind' (l := 85922 + 4 * counterLimit)
        (fun forest _ => ?_) (by omega)
      refine (bound_signLayersBC cache _ 4 (.forest forest.2)).bind' (l := 0) (fun layers _ => ?_)
        (by rw [layerFixedCost_four]; omega)
      cases layers <;> exact .pure _ 0 trivial
theorem bound_signWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118169 + limit + 4 * counterLimit) (signWith limit cache message) := by
  unfold signWith
  refine (bound_privateMac cache.region).bind' (l := 118167 + limit + 4 * counterLimit)
    (fun tag _ => ?_) (by omega)
  split
  · exact .pure _ _ trivial
  · exact bound_signPayloadWith limit cache message
theorem bound_verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 617 (verifyWith limit message pk w) := by
  unfold verifyWith
  split
  · exact .pure _ _ trivial
  · refine (bound_digest w.signature.rho message w.digestCounter).bind' (l := 616)
      (fun output _ => ?_) (by decide)
    dsimp only
    split
    · exact .pure _ _ trivial
    · refine (bound_recoverFts w.signature _ output).bind' (l := 485) (fun root _ => ?_) (by decide)
      refine (bound_verifyLayersBC w _ 4 (.forest root)).bind' (l := 0) (fun r _ => ?_)
        (by have := recoveryLayersCostBC_four_le; omega)
      cases r <;> exact .pure _ 0 trivial
theorem bound_expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 612) (expandWith limit message pk sig) := by
  unfold expandWith
  refine (bound_digestSearch sig.rho message limit 0).bind' (l := 4 * counterLimit + 612)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts sig _ output).bind' (l := 4 * counterLimit + 481)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayersBC sig _ 4 (.forest root)).bind' (l := 0)
        (fun layers _ => ?_) (by have := recoveryLayersCostBC_four_le; omega)
      cases layers with
      | none => exact .pure _ 0 trivial
      | some pair =>
          obtain ⟨root, counters⟩ := pair
          dsimp only
          split <;> exact .pure _ 0 trivial
theorem bound_signPayload (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118167 + digestAttemptLimit + 4 * counterLimit) (Rev3.signPayload cache message) :=
  bound_signPayloadWith digestAttemptLimit cache message
theorem bound_sign (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118169 + digestAttemptLimit + 4 * counterLimit) (Rev3.sign cache message) :=
  bound_signWith digestAttemptLimit cache message
theorem bound_expand (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (digestAttemptLimit + 4 * counterLimit + 612) (Rev3.expand message pk sig) :=
  bound_expandWith digestAttemptLimit message pk sig
theorem bound_verify (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 617 (Rev3.verify message pk w) :=
  bound_verifyWith digestAttemptLimit message pk w
theorem sign_compression_ceiling (secret : BitVec 256) (cache : Cache) (message : Message) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.sign cache message))),
      result.2 ≤ 18992537 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_sign cache message).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit])
theorem expand_compression_ceiling (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.expand message pk sig))),
      result.2 ≤ 18874980 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_expand message pk sig).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit])
theorem verify_compression_bound (secret : BitVec 256) (message : Message) (pk : Digest) (w : Witness) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.verify message pk w))), result.2 ≤ 617 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  exact (bound_verify message pk w).count_support result (realize_support_subset secret _ hr) |>.2
end ClaudeWCT.WCT9.Cost
