import SigGolfCandidate.T3M.Extract.Header

/-!
Address arithmetic for the proposed one-word FTS tree label.

The current source bounds allow forty index bits and eight coordinate bits.
Keep all of them: the root prefix has a leading one at bit 48, followed by
the index and coordinate. Appending the remaining path bits produces a
label below 2^60. Shifting this label right is exactly the parent operation.
The old two-word header can retain its tag word; only its second word needs
this encoding. This module does not yet alter an image or claim a saving.
-/
namespace SigGolfCandidate.T3.PackedHeap

set_option maxHeartbeats 1000000

def root (index coord : Nat) : Nat := (2^40 + index)*256 + coord

def label (index coord depth node : Nat) : Nat := root index coord * 2^depth + node

theorem root_bounds {index coord : Nat} (hi : index < 2^40) (hc : coord < 256) :
    2^48 ≤ root index coord ∧ root index coord < 2^49 := by
  unfold root
  omega

/-- Division and remainder recover both independent root coordinates. -/
theorem root_injective {index coord index' coord' : Nat}
    (hc : coord < 256) (hc' : coord' < 256)
    (h : root index coord = root index' coord') : index = index' ∧ coord = coord' := by
  unfold root at h
  omega

theorem label_interval {index coord depth node : Nat}
    (hi : index < 2^40) (hc : coord < 256) (hn : node < 2^depth) :
    2^(48+depth) ≤ label index coord depth node ∧
      label index coord depth node < 2^(49+depth) := by
  obtain ⟨hlo, hhi⟩ := root_bounds hi hc
  have hp : 0 < (2 : Nat)^depth := pow_pos (by decide) _
  unfold label
  rw [pow_add, pow_add]
  constructor <;> nlinarith

/-- Labels at different depths occupy disjoint power-of-two intervals. -/
theorem label_depth {index coord depth node index' coord' depth' node' : Nat}
    (hi : index < 2^40) (hc : coord < 256) (hn : node < 2^depth)
    (hi' : index' < 2^40) (hc' : coord' < 256) (hn' : node' < 2^depth')
    (he : label index coord depth node = label index' coord' depth' node') :
    depth = depth' := by
  obtain ⟨hl, hu⟩ := label_interval hi hc hn
  obtain ⟨hl', hu'⟩ := label_interval hi' hc' hn'
  by_contra hd
  rcases lt_or_gt_of_ne hd with hd | hd
  · have hp : (2 : Nat)^(49+depth) ≤ 2^(48+depth') :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : (2 : Nat)^(49+depth') ≤ 2^(48+depth) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Equality of bounded labels recovers the complete source position. -/
theorem label_injective {index coord depth node index' coord' depth' node' : Nat}
    (hi : index < 2^40) (hc : coord < 256) (hn : node < 2^depth)
    (hi' : index' < 2^40) (hc' : coord' < 256) (hn' : node' < 2^depth')
    (he : label index coord depth node = label index' coord' depth' node') :
    index = index' ∧ coord = coord' ∧ depth = depth' ∧ node = node' := by
  have hd := label_depth hi hc hn hi' hc' hn' he
  subst depth'
  have hp : 0 < (2 : Nat)^depth := pow_pos (by decide) _
  have hdiv : ∀ i c n, n < 2^depth → label i c depth n / 2^depth = root i c := by
    intro i c n hn
    unfold label
    rw [Nat.mul_comm (root i c), Nat.mul_add_div hp, Nat.div_eq_of_lt hn, Nat.add_zero]
  have hr : root index coord = root index' coord' := by
    have h := congrArg (fun x => x / 2^depth) he
    rw [hdiv _ _ _ hn, hdiv _ _ _ hn'] at h
    exact h
  obtain ⟨hidx, hcoord⟩ := root_injective hc hc' hr
  refine ⟨hidx, hcoord, rfl, ?_⟩
  unfold label at he
  rw [hr] at he
  exact Nat.add_left_cancel he

/-- The label fits one RV64 register for every FTS leaf and node. -/
theorem label_lt_word {index coord depth node : Nat}
    (hi : index < 2^40) (hc : coord < 256) (hd : depth ≤ 11) (hn : node < 2^depth) :
    label index coord depth node < 2^64 := by
  have h := (label_interval hi hc hn).2
  have hp : (2 : Nat)^(49+depth) ≤ 2^64 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- No recombination with the tree index is needed after a parent shift. -/
theorem label_parent (index coord depth node : Nat) :
    label index coord (depth+1) node / 2 = label index coord depth (node/2) := by
  unfold label
  rw [pow_succ, show root index coord * (2^depth * 2) =
    2 * (root index coord * 2^depth) by ring, Nat.mul_add_div (by decide : 0 < 2)]

/-- Existing left/right decisions retain exactly their original low bit. -/
theorem label_parity (index coord depth node : Nat) :
    label index coord (depth+1) node % 2 = node % 2 := by
  unfold label
  rw [pow_succ, show root index coord * (2^depth * 2) =
    2 * (root index coord * 2^depth) by ring, Nat.mul_add_mod]

/-- The actual machine word loses no information on these bounded labels. -/
theorem word_injective {index coord depth node index' coord' depth' node' : Nat}
    (hi : index < 2^40) (hc : coord < 256) (hd : depth ≤ 11) (hn : node < 2^depth)
    (hi' : index' < 2^40) (hc' : coord' < 256) (hd' : depth' ≤ 11) (hn' : node' < 2^depth')
    (he : BitVec.ofNat 64 (label index coord depth node) =
      BitVec.ofNat 64 (label index' coord' depth' node')) :
    index = index' ∧ coord = coord' ∧ depth = depth' ∧ node = node' := by
  apply label_injective hi hc hn hi' hc' hn'
  have h := congrArg BitVec.toNat he
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (label_lt_word hi hc hd hn),
    Nat.mod_eq_of_lt (label_lt_word hi' hc' hd' hn')] using h

end SigGolfCandidate.T3.PackedHeap
