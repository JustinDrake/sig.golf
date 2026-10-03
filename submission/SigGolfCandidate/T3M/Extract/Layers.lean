import SigGolfCandidate.T3M.Extract.Layer

/-! # The hypertree walk of the byte verifier (stream PEX-L)

`layersP_walk`: `layersP w index 4 root` reaching the honest public key, walked top-down from layer 0:
* a header-preserving hit among its actual queries, or
* a **divergence** at some layer `lay` (`Diverge`): every layer above is `Good` (signs its honest message, honest
  shape), layer `lay` is honest-shaped for the digits of a message different from its honest message (the WOTS /
  encoding event SEC charges with the backwards-chain analysis), or
* every layer `Good` and `root` is the honest forest pk (`honestMsg … 3 = honestForest`). -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Layer `lay` signs `msg`: its witness counter is in range and the encoding answer decodes to `digits`. -/
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : Digest) (digits : List Nat) : Prop :=
  (wctr w lay).toNat < counterLimit ∧
    decode lay (evalWithAnswerFn answers
      (shortHash (encodingInput lay (route index lay).2 (route index lay).1 msg (wctr w lay)))) = some digits

/-- The encoding query of layer `lay` on `msg`, as queried. -/
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : Digest) : Spec.Domain :=
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

/-- The value expected at the output of the first `n` evaluated layers of the top-down walk: the honest pk for
`n = 0`, else the honest message of layer `n - 1`. -/
noncomputable def walkTarget (answers : Answers) (index : Nat) : Nat → Digest
  | 0 => honestRoot answers 0 (route index 0).2
  | n + 1 => if h : n < 4 then honestMsg answers index ⟨n, h⟩ else 0

theorem walkTarget_root (answers : Answers) (index n : Nat) (hn : n < 4) :
    walkTarget answers index n = honestRoot answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
  rcases n with _ | k
  · rfl
  · have hk : k < 4 := by omega
    have hk3 : k < 3 := by omega
    have hl : (⟨k + 1, by omega⟩ : Layer) = Fin.ofNat 4 (k + 1) := Fin.ext (by simp [Fin.val_ofNat]; omega)
    simp only [walkTarget, dif_pos hk, honestMsg, dif_pos hk3, hl]

theorem layersP_succ_eq (w : WBytes) (index n : Nat) (root : Digest) :
    layersP w index (n + 1) root =
      if (wctr w (Fin.ofNat 4 n)).toNat ≥ counterLimit then pure none else
      (shortHash (encodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          root (wctr w (Fin.ofNat 4 n))) >>= fun answer =>
        match decode (Fin.ofNat 4 n) answer with
        | some digits => layerP w index (Fin.ofNat 4 n) digits >>= fun value => layersP w index n value
        | _ => pure none) := by
  conv_lhs => unfold layersP
  rfl

/-- One evaluated layer of `layersP`. -/
theorem layersP_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (root : Digest) (out : Digest)
    (h : evalWithAnswerFn answers (layersP w index (n + 1) root) = some out) :
    ∃ digits, Frame answers w index (Fin.ofNat 4 n) root digits ∧
      evalWithAnswerFn answers
        (layersP w index n (evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 n) digits))) = some out ∧
      encodingQuery w index (Fin.ofNat 4 n) root ∈ queried answers (layersP w index (n + 1) root) ∧
      (∀ q ∈ queried answers (layerP w index (Fin.ofNat 4 n) digits),
        q ∈ queried answers (layersP w index (n + 1) root)) ∧
      (∀ q ∈ queried answers
          (layersP w index n (evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 n) digits))),
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

/-- **The top-down hypertree walk** over the first `n` evaluated layers (`n ≤ 4`). -/
theorem layersP_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : Digest,
    evalWithAnswerFn answers (layersP w index n root) = some (walkTarget answers index 0) →
    HitIn answers (queried answers (layersP w index n root)) ∨
    (∃ lay : Layer, lay.val < n ∧ Diverge answers w index lay (queried answers (layersP w index n root)) ∧
      ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
    ((∀ l : Layer, l.val < n → Good answers w index l) ∧ root = walkTarget answers index n)
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
      · rw [walkTarget_root answers index n (by omega)] at hv
        rcases layerP_extract answers w index (Fin.ofNat 4 n) digits hidx
            (Cost.validDigits_decode hframe.2) hv with hhit | hshape
        · exact Or.inl (hhit.mono hqL)
        · have hmsg : honestMsg answers index (Fin.ofNat 4 n) = walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [walkTarget, dif_pos (show n < 4 by omega), hl]
          by_cases heq : root = honestMsg answers index (Fin.ofNat 4 n)
          · right; right
            refine ⟨fun l hl => ?_, heq.trans hmsg⟩
            by_cases hle : l.val < n
            · exact hgood l hle
            · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
              subst hl
              exact ⟨digits, heq ▸ hframe, hshape⟩
          · right; left
            exact ⟨Fin.ofNat 4 n, by omega, ⟨root, digits, heq, hframe, hshape, henc⟩,
              fun l hl => hgood l (by omega)⟩

end SigGolfCandidate.T3M.Extract
