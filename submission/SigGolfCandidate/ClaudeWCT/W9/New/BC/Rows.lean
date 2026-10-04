import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Leaf
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs

namespace ClaudeWCT.W9.T3M.BC
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    layerEncodingInputP lay tree leaf msg counter 0 = WCT9.layerEncodingInput lay tree leaf msg counter := by
  cases msg <;> rfl
theorem layerEncodingInputP_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    layerEncodingInputP lay tree leaf (.forest root) counter pad = encodingInput lay tree leaf root counter := rfl
theorem layerEncodingInputP_pair (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    layerEncodingInputP lay tree leaf (.pair l r) counter pad = WCT9.pairEncodingInputP lay tree leaf l r counter pad :=
  rfl
theorem layerEncodingInputP_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) :
    (layerEncodingInputP lay tree leaf msg counter pad).length = match msg with | .forest _ => 36 | .pair _ _ => 64 := by
  cases msg <;> simp [layerEncodingInputP, encodingInput, WCT9.pairEncodingInputP, bytesLE_length]
theorem layerEncodingRow_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) : (pad64 (layerEncodingInputP lay tree leaf msg counter pad)).length = 64 := by
  cases msg <;> simp [layerEncodingInputP, encodingInput, WCT9.pairEncodingInputP, bytesLE_length, pad64]
theorem pad64_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    pad64 (WCT9.pairEncodingInputP lay tree leaf l r counter pad) = WCT9.pairEncodingInputP lay tree leaf l r counter pad := by
  simp [pad64, WCT9.pairEncodingInputP, bytesLE_length]
theorem layerEncodingInputP_split (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) :
    ∃ first rest : HashInput, first.length = 16 ∧
      layerEncodingInputP lay tree leaf msg counter pad =
        first ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++ (bytesLE 4 counter ++ rest) := by
  cases msg with
  | forest root =>
      exact ⟨bytesLE 16 root, [], bytesLE_length _ _, by simp [layerEncodingInputP, encodingInput]⟩
  | pair l r =>
      refine ⟨bytesLE 16 l, bytesLE 12 pad ++ bytesLE 16 r, bytesLE_length _ _, ?_⟩
      simp only [layerEncodingInputP, WCT9.pairEncodingInputP, List.append_assoc]
theorem hdrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) :
    Extract.hdrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad)) =
      bytesLE 16 (header 4 lay.val tree 0 leaf) := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad
  have hl : 32 ≤ (layerEncodingInputP lay tree leaf msg counter pad).length := by
    rw [layerEncodingInputP_length]; cases msg <;> simp
  rw [Extract.hdrBlock_pad64 _ hl, he]
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' hf, List.take_left' (bytesLE_length _ _)]
theorem hdrBlock_layerEncodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.hdrBlock (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) =
      bytesLE 16 (header 4 lay.val tree 0 leaf) := by
  rw [← layerEncodingInputP_zero]
  exact hdrBlock_layerEncodingInputP lay tree leaf msg counter 0
def ctrBlock (input : HashInput) : HashInput := (input.drop 32).take 4
theorem ctrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) :
    ctrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad)) = bytesLE 4 counter := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad
  unfold ctrBlock pad64
  rw [he]
  have h32 : (first ++ bytesLE 16 (header 4 lay.val tree 0 leaf)).length = 32 := by
    simp [hf, bytesLE_length]
  rw [List.append_assoc (first ++ _) (bytesLE 4 counter ++ rest), List.drop_left' h32, List.append_assoc,
    List.take_left' (bytesLE_length _ _)]
theorem layerEncodingRow_coords {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (ht : tree < 2 ^ 40) (hl : leaf < 2 ^ 32) (ht' : tree' < 2 ^ 40) (hl' : leaf' < 2 ^ 32)
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad) = pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ c = c' := by
  have hh := congrArg Extract.hdrBlock h
  rw [hdrBlock_layerEncodingInputP, hdrBlock_layerEncodingInputP] at hh
  have hc := congrArg ctrBlock h
  rw [ctrBlock_layerEncodingInputP, ctrBlock_layerEncodingInputP] at hc
  have hu := lay.isLt
  have hu' := lay'.isLt
  obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) (by omega) ht (by norm_num) hl
    (by decide) (by omega) ht' (by norm_num) hl' (bytesLE_injective hh)
  exact ⟨Fin.ext e1, e2, e3, bytesLE_injective hc⟩
theorem layerEncodingRow_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (ht : tree < 2 ^ 40) (hl : leaf < 2 ^ 32) (ht' : tree' < 2 ^ 40) (hl' : leaf' < 2 ^ 32)
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay' msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad) = pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ msg = msg' ∧ c = c' ∧
      (∀ l r, msg = .pair l r → pad = pad') := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := layerEncodingRow_coords ht hl ht' hl' h
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases msg with
  | forest root =>
      cases msg' with
      | forest root' =>
          have he := Sampling.pad64_inj_of_length (by simp [layerEncodingInputP, encodingInput, bytesLE_length]) h
          simp only [layerEncodingInputP, encodingInput] at he
          obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
          obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
          exact ⟨by rw [bytesLE_injective he], rfl, fun _ _ h => by cases h⟩
      | pair l r =>
          change lay.val = 3 at hf
          change lay.val < 3 at hf'
          omega
  | pair l r =>
      cases msg' with
      | forest root' =>
          change lay.val < 3 at hf
          change lay.val = 3 at hf'
          omega
      | pair l' r' =>
          simp only [layerEncodingInputP, pad64_pairEncodingInputP] at h
          obtain ⟨-, -, -, e1, e2, -, e3⟩ := WCT9.pairEncodingInputP_injective ht hl ht hl h
          subst e1 e2
          exact ⟨rfl, rfl, fun _ _ _ => e3⟩
theorem layerEncodingRow_injective_leaf {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad) = pad64 (layerEncodingInputP lay tree leaf msg' c' pad')) :
    msg = msg' ∧ c = c' ∧ (∀ l r, msg = .pair l r → pad = pad') := by
  have hc := congrArg ctrBlock h
  rw [ctrBlock_layerEncodingInputP, ctrBlock_layerEncodingInputP] at hc
  have hcc := bytesLE_injective hc
  subst hcc
  cases msg with
  | forest root =>
      cases msg' with
      | forest root' =>
          have he := Sampling.pad64_inj_of_length (by simp [layerEncodingInputP, encodingInput, bytesLE_length]) h
          simp only [layerEncodingInputP, encodingInput] at he
          obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
          obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
          exact ⟨by rw [bytesLE_injective he], rfl, fun _ _ h => by cases h⟩
      | pair l r =>
          change lay.val = 3 at hf
          change lay.val < 3 at hf'
          omega
  | pair l r =>
      cases msg' with
      | forest root' =>
          change lay.val < 3 at hf
          change lay.val = 3 at hf'
          omega
      | pair l' r' =>
          rw [layerEncodingInputP_pair, layerEncodingInputP_pair, pad64_pairEncodingInputP,
            pad64_pairEncodingInputP] at h
          unfold WCT9.pairEncodingInputP at h
          obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
          obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
          obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
          obtain ⟨hL, -⟩ := List.append_inj h (by simp only [bytesLE_length])
          rw [bytesLE_injective hL, bytesLE_injective hr]
          exact ⟨rfl, rfl, fun _ _ _ => bytesLE_injective hp⟩
def GoodZ (answers : SigGolfCandidate.T3.Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  Extract.Good answers w index lay ∧ (lay.val < 3 → wbcPad w lay = 0)
theorem GoodZ.good {answers : SigGolfCandidate.T3.Correctness.Answers} {w : WBytes} {index : Nat} {lay : Layer}
    (h : GoodZ answers w index lay) : Extract.Good answers w index lay := h.1
end ClaudeWCT.W9.T3M.BC
