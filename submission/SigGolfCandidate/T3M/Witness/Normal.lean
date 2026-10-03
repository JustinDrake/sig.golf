import SigGolfCandidate.T3M.Witness.Encode
import SigGolfCandidate.T3M.Witness.Basic

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !selectionsOk (selections N) then pure false
  else if !digestGate N then pure false
  else (fun _ => false) <$> ftsP w (N.toNat % 2 ^ 31) (selections N)
def segShape (w : WBytes) : List Nat → Nat → Nat → Option (Nat × Nat × List Nat)
  | stack, E, ptr =>
      let b := (wbyte w ptr).toNat
      if 11 < b % 16 then none
      else if 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2 then none
      else
        let E := E / 2 ^ (b % 16)
        let ptr := segNext ptr (b % 16)
        match stack with
        | [] => if b / 16 % 2 = 1 then none else some (E, ptr, [])
        | Q :: rest =>
            if b / 16 % 2 = 0 then some (E, ptr, Q :: rest)
            else if Q ≠ E then none
            else segShape w rest (E / 2) ptr
def coordShape (w : WBytes) (sel : Selection) (ptr : Nat) : Option Nat := do
  let (E0, p0, s0) ← segShape w [] (2048 + selLeaf sel 0) ptr
  let (E1, p1, s1) ← segShape w ((E0 ^^^ 1) :: s0) (2048 + selLeaf sel 1) p0
  let (E2, p2, s2) ← segShape w ((E1 ^^^ 1) :: s1) (2048 + selLeaf sel 2) p1
  if E2 = 1 ∧ s2 = [] then some p2 else none
def ftsShape (w : WBytes) (chosen : List Selection) : Option Nat :=
  ((List.range 7).foldlM (fun ptr c => coordShape w (chosen.getD c ⟨0, []⟩) ptr) streamBase).filter
    (fun ptr => decide (ptr ≤ streamEnd))
def VerifyPNormal : Prop := ∀ (m : Message) (pk : Digest) (w : WBytes),
  verifyP m pk w =
    if (wdc w).toNat ≥ attemptLimit then pure false else do
      let N ← digest (wrho w) m (wdc w)
      if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N
def RejectTailFalse : Prop := ∀ (w : WBytes) (N : HashOutput), ∀ b ∈ support (rejectTail w N), b = false
def VerifyPadsZero : Prop := ∀ (m : Message) (pk : Digest) (w : Witness), verifyPads m pk w 0 = verify m pk w
def StreamShapedIff : Prop := ∀ (N : HashOutput) (w : WBytes), selectionsOk (selections N) = true →
  ((ftsShape w (selections N)).isSome = true ↔
    admissible (selections N) = true ∧ StreamMatches (selections N) w)
theorem rejectTail_false (w : WBytes) (N : HashOutput) : ∀ b ∈ support (rejectTail w N), b = false := by
  intro b hb
  unfold rejectTail at hb
  split at hb
  · simpa using hb
  · split at hb
    · simpa using hb
    · simp only [support_map, Set.mem_image] at hb
      obtain ⟨_, _, rfl⟩ := hb
      rfl
theorem recoverChildP_zero (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) : ∀ level node used,
    recoverChildP index coord leaves values proof 0 level node used =
      recoverChild index coord leaves values proof level node used := by
  intro level
  induction level with
  | zero => intro node used; simp only [recoverChildP, recoverChild, Pads.zero_leaf, ftsLeafP_zero]
  | succ level ih =>
      intro node used
      simp only [recoverChildP, recoverChild, ih, foldPad_zero, nodeHashP_zero]
      rfl
theorem recoverFtsP_zero (sig : Signature) (index : Nat) (chosen : List Selection) :
    recoverFtsP sig 0 index chosen = recoverFts sig index chosen := by
  simp only [recoverFtsP, recoverFts, recoverChildP_zero, Pads.zero_fold, nodeHashP_zero]
  rfl
theorem recoverLayerP_zero (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    recoverLayerP sig 0 index lay digits = recoverLayer sig index lay digits := by
  simp only [recoverLayerP, recoverLayer, Pads.zero_chain, chainP_zero, Pads.zero_merkle, nodeHashP_zero]
theorem verifyLayersP_zero (w : Witness) (index : Nat) : ∀ n root,
    verifyLayersP w 0 index n root = verifyLayers w index n root := by
  intro n
  induction n with
  | zero => intro root; rfl
  | succ n ih => intro root; simp only [verifyLayersP, verifyLayers, recoverLayerP_zero, ih]; rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : Witness) : verifyPads m pk w 0 = verify m pk w := by
  simp only [verifyPads, verifyPadsTail, verify, recoverFtsP_zero, verifyLayersP_zero]
  rfl
theorem verifyPadsZero_holds : VerifyPadsZero := verifyPads_zero
theorem rejectTailFalse_holds : RejectTailFalse := rejectTail_false
end SigGolfCandidate.T3M
