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
    CBound (fun _ => True) 3583 (buildCoordinate index coord selected word) :=
  cbound_of_ftsBound (ftsBound_buildCoordinate index coord selected word)
theorem bound_forestPk (index : Nat) (roots : List Digest) (hlen : roots.length = 9) :
    CBound (fun _ => True) 3 (WCT9.forestPk index roots) :=
  cbound_of_ftsBound (ftsBound_forestPk index roots hlen)
theorem bound_forestRows (index : Nat) (output : HashOutput) :
    CBound (fun state : List Opening × List Digest => state.1.length = 9 ∧ state.2.length = 9) 32247
      (forestRows index output) :=
  cbound_of_ftsBound (ftsBound_forestRows index output)
theorem bound_signForest (index : Nat) (output : HashOutput) :
    CBound (fun result : List Opening × Digest => result.1.length = 9) 32250 (signForest index output) :=
  cbound_of_ftsBound (ftsBound_signForest index output)
theorem bound_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord) :
    CBound (fun _ => True) 15 (recoverCoordinate sig index output coord) :=
  cbound_of_ftsBound (ftsBound_recoverCoordinate index sig output coord)
theorem bound_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    CBound (fun _ => True) 138 (recoverFts sig index output) :=
  cbound_of_ftsBound (ftsBound_recoverFts index sig output)
theorem signForest_blocks : 9 * (128 * (4 + 21 + 2) + 127) + 3 = 32250 := by norm_num
theorem verifyFts_blocks : 9 * (6 + 2 + 7) + 3 + 1 = 139 := by norm_num
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
theorem bound_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118174 + limit + 4 * counterLimit) (signPayloadWith limit cache message) := by
  rw [signPayloadWith_eq]
  refine (bound_privateNonce message).bind' (l := 118172 + limit + 4 * counterLimit)
    (fun rho _ => ?_) (by omega)
  refine (bound_digestSearch rho message limit 0).bind' (l := 118172 + 4 * counterLimit)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_signForest _ output).bind' (l := 85922 + 4 * counterLimit)
        (fun forest _ => ?_) (by omega)
      refine (bound_signLayers cache _ 4 (forest.2, 0, 0)).bind' (l := 0) (fun layers _ => ?_)
        (by rw [layerFixedCost_four]; omega)
      cases layers <;> exact .pure _ 0 trivial
theorem bound_signWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118176 + limit + 4 * counterLimit) (signWith limit cache message) := by
  unfold signWith
  refine (bound_privateMac cache.region).bind' (l := 118174 + limit + 4 * counterLimit)
    (fun tag _ => ?_) (by omega)
  split
  · exact .pure _ _ trivial
  · exact bound_signPayloadWith limit cache message
theorem bound_verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 627 (verifyWith limit message pk w) := by
  unfold verifyWith
  split
  · exact .pure _ _ trivial
  · refine (bound_digest w.signature.rho message w.digestCounter).bind' (l := 626)
      (fun output _ => ?_) (by decide)
    dsimp only
    split
    · exact .pure _ _ trivial
    · refine (bound_recoverFts w.signature _ output).bind' (l := 488) (fun root _ => ?_) (by decide)
      refine (bound_verifyLayers (toT3Witness w) _ 4 (root, 0, 0)).bind' (l := 0) (fun r _ => ?_)
        (by rw [recoveryLayersCost_four]; omega)
      cases r <;> exact .pure _ 0 trivial
theorem bound_expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 622) (expandWith limit message pk sig) := by
  unfold expandWith
  refine (bound_digestSearch sig.rho message limit 0).bind' (l := 4 * counterLimit + 622)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts sig _ output).bind' (l := 4 * counterLimit + 484)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayers (toT3Signature sig) _ 4 (root, 0, 0)).bind' (l := 0)
        (fun layers _ => ?_) (by rw [recoveryLayersCost_four]; omega)
      cases layers with
      | none => exact .pure _ 0 trivial
      | some pair =>
          obtain ⟨root, counters⟩ := pair
          dsimp only
          split <;> exact .pure _ 0 trivial
theorem bound_signPayload (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118174 + digestAttemptLimit + 4 * counterLimit) (Rev3.signPayload cache message) :=
  bound_signPayloadWith digestAttemptLimit cache message
theorem bound_sign (cache : Cache) (message : Message) :
    CBound (fun _ => True) (118176 + digestAttemptLimit + 4 * counterLimit) (Rev3.sign cache message) :=
  bound_signWith digestAttemptLimit cache message
theorem bound_expand (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (digestAttemptLimit + 4 * counterLimit + 622) (Rev3.expand message pk sig) :=
  bound_expandWith digestAttemptLimit message pk sig
theorem bound_verify (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 627 (Rev3.verify message pk w) :=
  bound_verifyWith digestAttemptLimit message pk w
theorem sign_compression_ceiling (secret : BitVec 256) (cache : Cache) (message : Message) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.sign cache message))),
      result.2 ≤ 18992544 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_sign cache message).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit])
theorem expand_compression_ceiling (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.expand message pk sig))),
      result.2 ≤ 18874990 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_expand message pk sig).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit])
theorem verify_compression_bound (secret : BitVec 256) (message : Message) (pk : Digest) (w : Witness) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.verify message pk w))), result.2 ≤ 627 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  exact (bound_verify message pk w).count_support result (realize_support_subset secret _ hr) |>.2
end ClaudeWCT.WCT9.Cost
