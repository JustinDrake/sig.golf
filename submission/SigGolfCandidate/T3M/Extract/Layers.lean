import SigGolfCandidate.T3M.Extract.Layer

/-! # The hypertree walk of the byte verifier (stream PEX-L; T3 + E8)

`layersP_walk`: `layersP w index 4 (root, 0, 0)` reaching the honest public key, walked top-down from layer 0:
* a header-preserving hit among its actual queries, or
* a **divergence** at some layer `lay` (`Diverge`): every layer above is `Good` (signs its honest message, honest
  shape), layer `lay` is honest-shaped for the digits of a message different from its honest message (the WOTS /
  encoding event SEC charges with the backwards-chain analysis), or
* every layer `Good` and the bottom message is the honest `(forest pk, 0, 0)`.
E8: a layer below the top hands the layer above the pair `(L, P, R)` (`layerNextP`), and the honest message of an
upper layer is the honest pair of the tree below (`honestPair`), so the walk binds the signed pair: an equal pair
makes the lower tree's level-`h-1` node and its sibling honest (`layerPairP_extract`). -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Layer `lay` signs `msg`: its witness counter is in range and the encoding answer decodes to `digits`. -/
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : LayerMessage) (digits : List Nat) :
    Prop :=
  (wctr w lay).toNat < counterLimit ∧
    decode lay (evalWithAnswerFn answers
      (shortHash (encodingInput lay (route index lay).2 (route index lay).1 msg (wctr w lay)))) = some digits

/-- The encoding query of layer `lay` on `msg`, as queried. -/
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : LayerMessage) : Spec.Domain :=
  .inl (.inr (pad64 (encodingInput lay (route index lay).2 (route index lay).1 msg (wctr w lay))))

/-- Layer `lay` signs its honest message and its bytes are honest-shaped for the decoded digits. -/
def Good (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∃ digits, Frame answers w index lay (honestMsg answers index lay) digits ∧ LayerShaped answers w index lay digits

/-- Layer `lay` signs a message other than its honest one, with honest-shaped bytes for that message's digits;
the encoding query is among `qs`. -/
def Diverge (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (qs : List Spec.Domain) : Prop :=
  ∃ msg digits, msg ≠ honestMsg answers index lay ∧ Frame answers w index lay msg digits ∧
    LayerShaped answers w index lay digits ∧ encodingQuery w index lay msg ∈ qs

theorem Diverge.mono {answers : Answers} {w : WBytes} {index : Nat} {lay : Layer} {qs qs' : List Spec.Domain}
    (h : Diverge answers w index lay qs) (hsub : ∀ q ∈ qs, q ∈ qs') : Diverge answers w index lay qs' := by
  obtain ⟨msg, digits, hne, hf, hs, hq⟩ := h
  exact ⟨msg, digits, hne, hf, hs, hsub _ hq⟩

/-- The value expected at the output of the first `n` evaluated layers of the top-down walk: the honest pk (as
`(pk, 0, 0)`) for `n = 0`, else the honest message of layer `n - 1`. -/
noncomputable def walkTarget (answers : Answers) (index : Nat) : Nat → LayerMessage
  | 0 => (honestRoot answers 0 (route index 0).2, 0, 0)
  | n + 1 => if h : n < 4 then honestMsg answers index ⟨n, h⟩ else 0

/-- Below the top, the walk target is the honest pair of the layer's tree. -/
theorem walkTarget_pair (answers : Answers) (index n : Nat) (hn : n < 4) (h0 : n ≠ 0) :
    walkTarget answers index n = honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
  rcases n with _ | k
  · exact absurd rfl h0
  · have hk : k < 4 := by omega
    have hk3 : k < 3 := by omega
    have hl : (⟨k + 1, by omega⟩ : Layer) = Fin.ofNat 4 (k + 1) := Fin.ext (by simp [Fin.val_ofNat]; omega)
    simp only [walkTarget, dif_pos hk, honestMsg, dif_pos hk3, hl]

theorem layerNextP_zero (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerNextP w index 0 lay digits = (fun value => (value, 0, 0)) <$> layerP w index lay digits := by
  rw [layerNextP, if_pos rfl]

theorem layerNextP_ne (w : WBytes) (index n : Nat) (lay : Layer) (digits : List Nat) (h : n ≠ 0) :
    layerNextP w index n lay digits = layerPairP w index lay digits := by
  rw [layerNextP, if_neg h]

theorem layersP_succ_eq (w : WBytes) (index n : Nat) (root : LayerMessage) :
    layersP w index (n + 1) root =
      if (wctr w (Fin.ofNat 4 n)).toNat ≥ counterLimit then pure none else
      (shortHash (encodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          root (wctr w (Fin.ofNat 4 n))) >>= fun answer =>
        match decode (Fin.ofNat 4 n) answer with
        | some digits => layerNextP w index n (Fin.ofNat 4 n) digits >>= fun next => layersP w index n next
        | _ => pure none) := by
  conv_lhs => unfold layersP
  rfl

/-- One evaluated layer of `layersP`. -/
theorem layersP_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (root : LayerMessage) (out : Digest)
    (h : evalWithAnswerFn answers (layersP w index (n + 1) root) = some out) :
    ∃ digits, Frame answers w index (Fin.ofNat 4 n) root digits ∧
      evalWithAnswerFn answers
        (layersP w index n (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits))) = some out ∧
      encodingQuery w index (Fin.ofNat 4 n) root ∈ queried answers (layersP w index (n + 1) root) ∧
      (∀ q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits),
        q ∈ queried answers (layersP w index (n + 1) root)) ∧
      (∀ q ∈ queried answers
          (layersP w index n (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits))),
        q ∈ queried answers (layersP w index (n + 1) root)) := by
  rw [layersP_succ_eq] at h ⊢
  by_cases hc : (wctr w (Fin.ofNat 4 n)).toNat ≥ counterLimit
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  rw [evalWithAnswerFn_bind] at h
  rw [queried_bind]
  generalize hans : evalWithAnswerFn answers (shortHash (encodingInput (Fin.ofNat 4 n)
    (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 root (wctr w (Fin.ofNat 4 n)))) = answer at h ⊢
  cases hd : decode (Fin.ofNat 4 n) answer with
  | none => rw [hd] at h; simp at h
  | some digits =>
      rw [hd] at h
      simp only at h ⊢
      rw [evalWithAnswerFn_bind] at h
      refine ⟨digits, ⟨by omega, by rw [hans]; exact hd⟩, h, ?_, ?_, ?_⟩
      · apply List.mem_append_left
        rw [queried_shortHash]; exact List.mem_singleton_self _
      · intro q hq
        apply List.mem_append_right
        rw [queried_bind]; exact List.mem_append_left _ hq
      · intro q hq
        apply List.mem_append_right
        rw [queried_bind]; exact List.mem_append_right _ hq

/-- **The Merkle part of one layer's handover** reaching the walk target (the honest root at the top, the honest
root children below it): a node hit among the handover's queries, or honest Merkle bytes, the honest leaf pk, and
the leaf pk's queries among the handover's. -/
theorem layerNextP_merkle (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (digits : List Nat)
    (hv : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    NodeHitIn answers (queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ∨
      (MerkleShaped answers w index (Fin.ofNat 4 n) ∧
        evalWithAnswerFn answers (layerLeafP w index (Fin.ofNat 4 n) digits) =
          treeValue (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2) 0
            (route index (Fin.ofNat 4 n)).1 ∧
        ∀ q ∈ queried answers (layerLeafP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) := by
  by_cases h0 : n = 0
  · subst h0
    have hq : queried answers (layerNextP w index 0 (Fin.ofNat 4 0) digits) =
        queried answers (layerP w index (Fin.ofNat 4 0) digits) := by
      rw [layerNextP_zero, map_eq_bind_pure_comp, queried_bind]
      simp
    have hr : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
        honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
      have h1 := congrArg Prod.fst hv
      rw [layerNextP_zero, evalWithAnswerFn_map] at h1
      exact h1
    rw [hq]
    rcases layerP_merkle answers w index (Fin.ofNat 4 0) digits hr with hn | ⟨hm, hv0⟩
    · exact Or.inl hn
    · refine Or.inr ⟨hm, hv0, fun q hq' => ?_⟩
      rw [layerP_eq_hashPath, queried_bind]
      exact List.mem_append_left _ hq'
  · have hq : layerNextP w index n (Fin.ofNat 4 n) digits = layerPairP w index (Fin.ofNat 4 n) digits :=
      layerNextP_ne w index n (Fin.ofNat 4 n) digits h0
    rw [hq] at hv ⊢
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
      intro h; apply h0; have := congrArg Fin.val h; simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using this
    rw [walkTarget_pair answers index n hn h0] at hv
    rcases layerPairP_merkle answers w index (Fin.ofNat 4 n) hlay digits hv with hn' | ⟨hm, hv0⟩
    · exact Or.inl hn'
    · refine Or.inr ⟨hm, hv0, fun q hq' => ?_⟩
      rw [layerPairP_eq_hashPath, queried_bind]
      exact List.mem_append_left _ hq'

/-- One layer's handover reaching the walk target: a hit among its queries or honest-shaped bytes. -/
theorem layerNextP_extract (answers : Answers) (w : WBytes) (index n : Nat) (hn : n < 4) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits (Fin.ofNat 4 n) digits)
    (hv : evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    HitIn answers (queried answers (layerNextP w index n (Fin.ofNat 4 n) digits)) ∨
      LayerShaped answers w index (Fin.ofNat 4 n) digits := by
  rcases layerNextP_merkle answers w index n hn digits hv with hnode | ⟨hm, hv0, hsub⟩
  · exact Or.inl (hnode.hitIn (route_tree_bound index _ hidx) (route_leaf_bound index _))
  rcases leafChains_extract answers w index (Fin.ofNat 4 n) digits hidx hvalid hv0 with hh | hc
  · exact Or.inl (hh.mono hsub)
  · exact Or.inr ⟨hm, hc⟩

/-- The walk's induction hypothesis at position `n` read as "the handover of layer `n` reaches `walkTarget n`". -/
theorem next_target (answers : Answers) (w : WBytes) (index n : Nat) (digits : List Nat)
    (hv : if n = 0 then (evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits)).1 =
        (walkTarget answers index 0).1
      else evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n) :
    evalWithAnswerFn answers (layerNextP w index n (Fin.ofNat 4 n) digits) = walkTarget answers index n := by
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl] at hv
    rw [layerNextP_zero, evalWithAnswerFn_map] at hv ⊢
    simp only [walkTarget] at hv ⊢
    rw [hv]
  · rw [if_neg h0] at hv
    exact hv

/-- **The top-down hypertree walk** over the first `n` evaluated layers (`n ≤ 4`). -/
theorem layersP_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : LayerMessage,
    evalWithAnswerFn answers (layersP w index n root) = some (walkTarget answers index 0).1 →
    HitIn answers (queried answers (layersP w index n root)) ∨
    (∃ lay : Layer, lay.val < n ∧ Diverge answers w index lay (queried answers (layersP w index n root)) ∧
      ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
    ((∀ l : Layer, l.val < n → Good answers w index l) ∧
      (if n = 0 then root.1 = (walkTarget answers index 0).1 else root = walkTarget answers index n))
  | 0, _, root, h => by
      right; right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_walk answers w index hidx n (by omega) _ hrest with hhit | ⟨lay, hlay, hdiv, hgood⟩ | ⟨hgood, hv⟩
      · exact Or.inl (hhit.mono hqR)
      · exact Or.inr (Or.inl ⟨lay, by omega, hdiv.mono hqR, hgood⟩)
      · have hv' := next_target answers w index n digits hv
        rcases layerNextP_extract answers w index n (by omega) digits hidx
            (Cost.validDigits_decode hframe.2) hv' with hhit | hshape
        · exact Or.inl (hhit.mono hqL)
        · have hmsg : honestMsg answers index (Fin.ofNat 4 n) = walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [walkTarget, dif_pos (show n < 4 by omega), hl]
          by_cases heq : root = honestMsg answers index (Fin.ofNat 4 n)
          · right; right
            refine ⟨fun l hl => ?_, by simpa only [Nat.succ_ne_zero, if_false] using heq.trans hmsg⟩
            by_cases hle : l.val < n
            · exact hgood l hle
            · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
              subst hl
              exact ⟨digits, heq ▸ hframe, hshape⟩
          · right; left
            exact ⟨Fin.ofNat 4 n, by omega, ⟨root, digits, heq, hframe, hshape, henc⟩,
              fun l hl => hgood l (by omega)⟩

end SigGolfCandidate.T3M.Extract
