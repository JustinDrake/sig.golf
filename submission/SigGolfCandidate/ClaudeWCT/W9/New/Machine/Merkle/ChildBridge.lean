import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildMain

section

namespace ClaudeWCT.W9.Machine.Merkle
set_option maxRecDepth 100000
theorem childBlocks_length : childBlocks.length = 128 := by decide +kernel
theorem childWords_tmpl : ∀ j, j < 128 → childWords j = childTmpl j := by decide +kernel
theorem childTemplate : ChildTemplate := ⟨childBlocks_length, childWords_tmpl⟩
end ClaudeWCT.W9.Machine.Merkle
end

section


namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem childBlocks_len64 : (childBlocks.dropLast.all fun c => c.length == 64) = true := by decide +kernel
theorem childWords_length (j : Nat) (hj : j < 128) : (childWords j).length = 64 := by
  rw [childWords_tmpl j hj]; rfl
theorem childCodeAt_of_region {im : Image} (h : ChildRegionAt im) {j : Nat} (hj : j < 128) :
    ChildCodeAt im j := by
  intro i w hw
  have hi : i < 64 := by
    have := (List.getElem?_eq_some_iff.mp hw).1
    rwa [childWords_length j hj] at this
  have hreg : childRegion[64 * j + i]? = some w := by
    apply lookup_chunks 64 (by decide) childBlocks (64 * j + i) w childBlocks_len64
    rw [show (64 * j + i) / 64 = j by omega, show (64 * j + i) % 64 = i by omega]
    have hb : childBlocks[j]? = some (childWords j) := by
      unfold childWords
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [childBlocks_length]; exact hj)]
      rfl
    rw [hb]; exact hw
  obtain ⟨rest, hrest⟩ := h
  have hlen : 64 * j + i < childRegion.length := (List.getElem?_eq_some_iff.mp hreg).1
  have h2 : (im.code.drop 210432)[64 * j + i]? = some w := by
    rw [← hrest, List.getElem?_append_left hlen]; exact hreg
  rw [List.getElem?_drop] at h2
  unfold childBase
  rw [show 210432 + 64 * j + i = 210432 + (64 * j + i) by omega]
  exact h2
theorem childCodeAt_of_codeAt {im : Image} {j : Nat} (hj : j < 128)
    (h : CodeAt im (pcOf (childBase j)) (childWords j)) : ChildCodeAt im j := by
  obtain ⟨-, -, -, hpre⟩ := h
  have hp : ((pcOf (childBase j)).toNat - 0x1000) / 4 = childBase j := by
    simp only [pcOf, childBase, BitVec.toNat_ofNat]
    omega
  rw [hp] at hpre
  intro i w hw
  obtain ⟨rest, hrest⟩ := hpre
  have hlen : i < (childWords j).length := (List.getElem?_eq_some_iff.mp hw).1
  have h2 : (im.code.drop (childBase j))[i]? = some w := by
    rw [← hrest, List.getElem?_append_left hlen]; exact hw
  rwa [List.getElem?_drop] at h2
theorem childRegionAt_of_codeAt {im : Image} (h : CodeAt im (pcOf 210432) childRegion) : ChildRegionAt im := by
  obtain ⟨-, -, -, hpre⟩ := h
  have hp : ((pcOf 210432).toNat - 0x1000) / 4 = 210432 := by decide
  rwa [hp] at hpre
theorem leafBytes_canon (k index j : Nat) (ends : List Digest) (h : ends.length = 7) :
    leafBytes (leafFields k index j ends) =
      bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ClaudeWCT.WCT9.wctHeader 6 k index 0 j) ++
        (ends.drop 1).flatMap (bytesLE 16) := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    simp only [leafBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.flatMap_cons,
      List.flatMap_nil, leafFields, List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    rfl
theorem childLevelP_zero (k index j : Nat) (path : Nat → Digest) (v : Digest) (l : Nat) :
    childLevelP k index j (fun _ => 0) path v l =
      (let other := path l
       let pair := if j / 2 ^ l % 2 = 0 then (v, other) else (other, v)
       SigGolfCandidate.T3.nodeHash 11 k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) := by
  simp only [childLevelP, nodeHashP_eq, nodeHash_eq, bitAt, heapOf]
  rfl
theorem childCanon : ChildCanon := by
  intro k index j ends path h
  unfold childProg ClaudeWCT.WCT9.leafHash sixLevels
  have hfg : childLevelP k index j (fun _ => 0) path = fun value l =>
      (let other := path l
       let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
       SigGolfCandidate.T3.nodeHash 11 k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) :=
    funext fun v => funext fun l => childLevelP_zero k index j path v l
  rw [leafBytes_canon k index j ends h, hfg]
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem pathSplit : PathSplit := by
  intro k index j path root hj
  let F : Digest → Nat → M Digest := fun value l =>
    let other := finPath path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    SigGolfCandidate.T3.nodeHash 11 k.val index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2
  have hf : (fun value (level : Fin 7) ↦ do
      let other := path level
      let pair := if j / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      SigGolfCandidate.T3.nodeHash 11 k.val index
        (2 ^ (6 - level.val) + j / 2 ^ (level.val + 1)) pair.1 pair.2 : Digest → Fin 7 → M Digest) =
      fun value level => F value level.val := by
    funext value level
    simp only [F, finPath, dif_pos level.isLt]
  have e : List.foldlM (fun value (level : Fin 7) => F value level.val) root (List.finRange 7) =
      List.foldlM F root ((List.finRange 7).map Fin.val) := by rw [List.foldlM_map]
  rw [hf]
  rw [e]
  rw [finRange_map_val]
  rw [show List.range 7 = List.range 6 ++ [6] from List.range_succ (n := 6)]
  rw [List.foldlM_append]
  unfold sixLevels
  show List.foldlM F root (List.range 6) >>= (fun s => List.foldlM F s [6]) =
    List.foldlM F root (List.range 6) >>= _
  apply congrArg (List.foldlM F root (List.range 6) >>= ·)
  funext value
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  simp only [F, finPath, show (6 : Nat) < 7 by decide, dif_pos]
  rw [show j / 2 ^ (6 + 1) = 0 from Nat.div_eq_of_lt hj]
  rfl
theorem rootInput : RootInput := by
  intro j B k index u t t' v pad sib hj _hidx h8 hhi hpost hpad hsib hmem h10 h11
  unfold MEMORY_BYTES at hhi
  have hb6 := bitAt_lt j 6
  have hT : ∀ o, o ≤ 1024 → o ∉ childWrites j →
      t'.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hn
    rw [hmem]
    refine hpost.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have : off = o := by omega
    subst this; exact hn hoff
  have hfree := fun off (h : off ∈ childWrites j) => childWrites_free (off := off) h
  have hpad' : DigAt t' (B + 32) pad := by
    refine DigAt.of_eq hpad ?_ ?_
    · exact hT 32 (by omega) (fun h => (hfree _ h).1 rfl)
    · rw [show B + 32 + 8 = B + 40 by omega]
      exact hT 40 (by omega) (fun h => (hfree _ h).2.1 rfl)
  have hsib' : DigAt t' (B + sibO 6 j) sib := by
    refine DigAt.of_eq hsib ?_ ?_
    · exact hT _ (by unfold sibO blkO; omega) (fun h => (hfree _ h).2.2.1 rfl)
    · rw [show B + sibO 6 j + 8 = B + (sibO 6 j + 8) by omega]
      exact hT _ (by unfold sibO blkO; omega) (fun h => (hfree _ h).2.2.2 rfl)
  have hnode : DigAt t' (B + curO 6 j) v := DigAt.of_eq hpost.node (hmem _) (hmem _)
  have hhdr : DigAt t' (B + 16) (header 11 k index 0 1) := by
    constructor
    · rw [hmem, hpost.hw0, hdr11_lo]
    · rw [hmem, show B + 16 + 8 = B + 24 by omega, hpost.hw1, hdr11_hi]
  unfold rootIn
  rcases Nat.lt_or_ge (bitAt j 6) 1 with h0 | h1
  · have e0 : bitAt j 6 = 0 := by omega
    have ec : curO 6 j = 0 := by unfold curO blkO; omega
    have es : sibO 6 j = 48 := by unfold sibO blkO; omega
    simp only [e0, if_true]
    rw [ec, Nat.add_zero] at hnode; rw [es] at hsib'
    exact hashInput_blk4 t' B _ _ _ _ h10 h11 h8 (by omega) hnode hhdr hpad' hsib'
  · have e1 : bitAt j 6 = 1 := by omega
    have ec : curO 6 j = 48 := by unfold curO blkO; omega
    have es : sibO 6 j = 0 := by unfold sibO blkO; omega
    simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
    rw [ec] at hnode; rw [es, Nat.add_zero] at hsib'
    exact hashInput_blk4 t' B _ _ _ _ h10 h11 h8 (by omega) hsib' hhdr hpad' hnode
theorem child_refines_canon (im : Image) (j : Nat) (hj : j < 128) (hcode : ChildCodeAt im j) :
    ChildRefinesCanon im j := by
  intro B k index ends path P hends hidx hP
  rw [← childCanon k index j ends path hends]
  exact child_refines im j hj hcode B k index _ _ _ P hidx hP
theorem allChildren (im : Image) : AllChildren im := by
  intro hreg j hj
  have hc := childCodeAt_of_region hreg hj
  exact ⟨child_good im j hj hc, child_refines im j hj hc, child_refines_canon im j hj hc⟩
end ClaudeWCT.W9.Machine.Merkle
end
