import SigGolfCandidate.T3.Secc.WotsEncodingCongr
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraph
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
section Programs
theorem respects_forestPk (index : Nat) (roots : List Digest) :
    Respects Enc.NonEnc (ClaudeWCT.WCT9.forestPk index roots) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_forestPk index roots
theorem respects_signForest (index : Nat) (output : HashOutput) :
    Respects Enc.NonEnc (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_signForest index output
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects Enc.NonEnc (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_digestSearch rho message
end Programs
section RespAt
variable {T : Answers} {S : Spec.Domain → Prop}
end RespAt
def Reached (T : Answers) (L : LeafAddr) (input : HashInput) : Prop :=
  ∃ c < counterLimit, input = encodingRow L (leafMsg T L) (BitVec.ofNat 32 c) ∧
    ∀ c' < c, decode L.lay (low (T (.inl (.inr (encodingRow L (leafMsg T L) (BitVec.ofNat 32 c')))))) = none
def leafOf (L : CanonGraph.LeafPos) : LeafAddr := ⟨L.lay, L.tree.val, L.leaf.val⟩
def HonestQ (T : Answers) : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input ∨ ∃ L : CanonGraph.LeafPos, Reached T (leafOf L) input
  | _ => True
theorem honestQ_of_nonEnc {T : Answers} {q : Spec.Domain} (h : Enc.NonEnc q) : HonestQ T q := by
  rcases q with (coin | input) | coordinate
  · trivial
  · exact Or.inl h
  · trivial
theorem respAt_referenceSearch (T : Answers) (S : Spec.Domain → Prop) (L : LeafAddr)
    (hS : ∀ input, Reached T L input → S (.inl (.inr input))) :
    RespAt T S (counterSearch L.lay L.tree L.leaf (leafMsg T L) 0 counterLimit) := by
  apply respAt_counterSearch
  intro c hc hprev
  apply hS
  refine ⟨c, hc, ?_, fun c' hc' => ?_⟩
  · simp only [encodingRow, Nat.zero_add]
  · have := hprev c' hc'
    rw [Nat.zero_add] at this
    exact this
def routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : CanonGraph.LeafPos :=
  ⟨lay, ⟨(route index lay).2, lt_of_le_of_lt (Nat.div_le_self _ _) hindex⟩,
    ⟨(route index lay).1, lt_of_lt_of_le (route_leaf_bound index lay)
      (by calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
            _ = 4096 := by norm_num)⟩⟩
theorem leafOf_routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    leafOf (routePos index hindex lay) = routeLeaf index lay := rfl
theorem respAt_routeSearch (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    RespAt T (HonestQ T) (counterSearch lay (route index lay).2 (route index lay).1
      (leafMsg T (routeLeaf index lay)) 0 counterLimit) :=
  respAt_referenceSearch T (HonestQ T) (routeLeaf index lay)
    (fun input h => Or.inr ⟨routePos index hindex lay, h⟩)
theorem respAt_signLayers (T : Answers) (cache : T3.Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg T (routeLeaf index (Fin.ofNat 4 m))) →
      RespAt T (HonestQ T) (signLayers cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; exact RespAt.pure' _
  | succ n ih =>
      intro hn msg hmsg
      simp only [signLayers]
      refine RespAt.bind ?_ ?_
      · rw [hmsg n rfl]
        exact respAt_routeSearch T index hindex _
      · cases hs : evalWithAnswerFn T (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
        | none => exact RespAt.pure' _
        | some found =>
            obtain ⟨counter, digits⟩ := found
            have hd := (Correctness.counterSearch_some T _ _ _ msg counterLimit 0 counter digits
              (by decide) hs).2.2
            have hvalid := Cost.validDigits_decode hd
            dsimp only
            split_ifs with hn0
            · exact RespAt.bind (RespAt.of_respects (respects_signTop _ _ _) fun _ h => honestQ_of_nonEnc h)
                (RespAt.pure' _)
            · refine RespAt.bind (RespAt.of_respects (respects_buildTree _ _ _ _)
                fun _ h => honestQ_of_nonEnc h) ?_
              rw [Correctness.eval_buildTree_result T _ _ _ digits hvalid (route_leaf_bound index _)]
              dsimp only
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              refine RespAt.bind (ih (by omega) _ (fun m' hm' => ?_)) ?_
              · obtain rfl : m = m' := by omega
                exact Mask.signedMsg_succ T index m (by omega)
              · cases evalWithAnswerFn T (signLayers cache index (m + 1) _) <;> exact RespAt.pure' _
theorem respAt_signPayload (T : Answers) (cache : T3.Cache) (message : Message) :
    RespAt T (HonestQ T) (signPayload cache message) := by
  change RespAt T (HonestQ T) (ClaudeWCT.WCT9.Rev3.signPayload cache message)
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine RespAt.bind (RespAt.of_respects (respects_privateNonce message) fun _ h => honestQ_of_nonEnc h) ?_
  refine RespAt.bind (RespAt.of_respects (respects_digestSearch _ _ _ _) fun _ h => honestQ_of_nonEnc h) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact RespAt.pure' _
  · dsimp only
    refine RespAt.bind (RespAt.of_respects (respects_signForest _ _) fun _ h => honestQ_of_nonEnc h) ?_
    refine RespAt.bind (respAt_signLayers T cache _ (Nat.mod_lt _ (by decide)) 4 le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [ClaudeWCT.WCT9.signForest_root]
      exact (congrArg (fun x => ((x, 0, 0) : Digest × BitVec 96 × Digest))
        (Extract.honestForest_eq_wct9 T _).symm).trans (Mask.signedMsg_top T _)
    · generalize evalWithAnswerFn T (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
      rcases pieces with _ | pieces <;> exact RespAt.pure' _
theorem respAt_sign (T : Answers) (published : T3.Cache) (request : Request) :
    RespAt T (HonestQ T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine RespAt.bind (RespAt.of_respects (respects_privateMac _) fun _ h => honestQ_of_nonEnc h) ?_
  split
  · exact respAt_signPayload T _ _
  · exact RespAt.pure' _
theorem respAt_keygen (T : Answers) : RespAt T (HonestQ T) keygen :=
  RespAt.of_respects respects_keygen fun _ h => honestQ_of_nonEnc h
end Enc
open ClaudeWCT.W9.T3.Security.Wots.Enc
theorem keygenCharge_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) :
    keygenCharge T' = keygenCharge T := by
  unfold keygenCharge
  rw [(respAt_keygen T).queried_eq h]
theorem signCharge_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (published : T3.Cache)
    (request : Request) : signCharge T' published request = signCharge T published request := by
  unfold signCharge
  rw [(respAt_sign T published request).queried_eq h]
theorem offlineSign_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (published : T3.Cache)
    (request : Request) : offlineSign T' published request = offlineSign T published request := by
  unfold offlineSign
  rw [signCharge_congr h, (respAt_sign T published request).eval_eq h]
theorem offlineImpl_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (published : T3.Cache) :
    offlineImpl T' published = offlineImpl T published := by
  unfold offlineImpl
  have hs : offlineSign T' published = offlineSign T published := funext (offlineSign_congr h published)
  rw [hs]
theorem offlineGame_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (adversary : Final.AdversaryP) :
    offlineGame T' adversary = offlineGame T adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_congr h, (respAt_keygen T).eval_eq h, offlineImpl_congr h]
theorem referenceGame_congr_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q)
    (adversary : Final.AdversaryP) (q : Nat) : referenceGame T' adversary q = referenceGame T adversary q := by
  unfold referenceGame
  rw [offlineGame_congr h]
theorem honestForest_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (index : Nat) :
    Extract.honestForest T' index = Extract.honestForest T index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.Enc.honestForest_congr h index
theorem leafMsg_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (L : LeafAddr) :
    leafMsg T' L = leafMsg T L := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [builtTree_congr_nonEnc h]
  · rw [honestForest_congr_nonEnc h _]
theorem nonEnc_of_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) : ∀ q, Enc.NonEnc q → T' q = T q :=
  fun q hq => h q (honestQ_of_nonEnc hq)
theorem referenceSearch_congr_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q)
    (L : CanonGraph.LeafPos) : referenceSearch T' (leafOf L) = referenceSearch T (leafOf L) := by
  unfold referenceSearch
  rw [leafMsg_congr_nonEnc (nonEnc_of_honest h)]
  exact (respAt_referenceSearch T (HonestQ T) (leafOf L) (fun input hr => Or.inr ⟨L, hr⟩)).eval_eq h
theorem referenceDigits_congr_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q)
    (L : CanonGraph.LeafPos) : referenceDigits T' (leafOf L) = referenceDigits T (leafOf L) := by
  unfold referenceDigits
  rw [referenceSearch_congr_honest h]
theorem referenceInput_congr_honest {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q)
    (L : CanonGraph.LeafPos) : referenceInput T' (leafOf L) = referenceInput T (leafOf L) := by
  unfold referenceInput
  rw [referenceSearch_congr_honest h, leafMsg_congr_nonEnc (nonEnc_of_honest h)]
end ClaudeWCT.W9.T3.Security.Wots
