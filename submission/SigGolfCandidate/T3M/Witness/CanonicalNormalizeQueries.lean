import SigGolfCandidate.T3M.Witness.CanonicalScheduleRun

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalSchedule
open OracleComp OracleSpec SigGolfCandidate.T3
open CanonicalAdapter CanonicalBytes

def LeafSame (w v : WBytes) : Prop :=
  (∀ s, s<22 → wleafPad w s=wleafPad v s) ∧ (∀ s, s<21 → wsecret w s=wsecret v s)
def ReadsAt (w v : WBytes) (ptr A : Nat) : Prop :=
  ∀ r, r<A → ∀ off∈[0,32,48], wdig w (ptr+8+80*r+off)=wdig v (ptr+8+80*r+off)
def SegmentReads (w v : WBytes) : Nat → List Segment → Prop
  | _,[] => True
  | ptr,s::rest => ReadsAt w v ptr s.a ∧ SegmentReads w v (segNext ptr s.a) rest

theorem leaf_same_normalize (chosen : List Selection) (w : WBytes) :
    LeafSame (CanonicalAdapter.normalize chosen w) w := by
  constructor
  · intro s hs; unfold wleafPad CanonicalAdapter.normalize
    apply digest_patch_frame
    · unfold leafBlock; omega
    · intro j hj; apply replacement_before_stream; unfold leafBlock; omega
  · intro s hs; unfold wsecret CanonicalAdapter.normalize
    apply digest_patch_frame
    · unfold leafBlock; omega
    · intro j hj; apply replacement_before_stream; unfold leafBlock; omega

theorem pending_congr (w v : WBytes) (index coord : Nat) (node : Digest) (p : Pending)
    (hl : LeafSame w v) (hp : ∀ s g, p=.leaf s g → s<21) :
    pendingHash w index coord node p=pendingHash v index coord node p := by
  cases p with
  | leaf s g =>
    have hs := hp s g rfl
    simp only [pendingHash,hl.1 s (by omega),hl.1 (s+1) (by omega),hl.2 s hs]
  | merge heap left => rfl

theorem fold_step_congr (w v : WBytes) (index coord ptr r : Nat) (state : Digest × Nat)
    (hr : ∀ off∈[0,32,48], wdig w (ptr+8+80*r+off)=wdig v (ptr+8+80*r+off)) :
    foldStep w index coord ptr state r=foldStep v index coord ptr state r := by
  unfold foldStep foldBlock
  dsimp only
  have h0 := hr 0 (by simp)
  simp only [Nat.add_zero] at h0
  rw [h0,hr 32 (by simp),hr 48 (by simp)]

theorem folds_congr (w v : WBytes) (index coord ptr : Nat) :
    ∀ n start node heap,
    (∀ r, start ≤ r → r<start+n → ∀ off∈[0,32,48],
      wdig w (ptr+8+80*r+off)=wdig v (ptr+8+80*r+off)) →
    (List.range' start n).foldlM (foldStep w index coord ptr) (node,heap)=
      (List.range' start n).foldlM (foldStep v index coord ptr) (node,heap) := by
  intro n
  induction n with
  | zero => intro start node heap h; rfl
  | succ n ih =>
    intro start node heap h
    rw [List.range'_succ,List.foldlM_cons,List.foldlM_cons,fold_step_congr w v index coord ptr start _
      (h start (by omega) (by omega))]
    apply bind_congr
    intro p
    exact ih (start+1) p.1 p.2 (fun r h0 h1 => h r (by omega) (by omega))

theorem foldsP_congr (w v : WBytes) (index coord ptr A : Nat) (node : Digest) (heap : Nat)
    (hr : ReadsAt w v ptr A) : foldsP w index coord ptr A node heap=foldsP v index coord ptr A node heap := by
  unfold foldsP
  rw [List.range_eq_range']
  exact folds_congr w v index coord ptr A 0 node heap (fun r _ h => hr r (by omega))

theorem segment_congr (w v : WBytes) (index coord ptr A E : Nat) (node : Digest) (p : Pending)
    (hl : LeafSame w v) (hp : ∀ s g, p=.leaf s g → s<21) (hr : ReadsAt w v ptr A) :
    segmentDigestP w index coord ptr A E node p=segmentDigestP v index coord ptr A E node p := by
  unfold segmentDigestP
  rw [pending_congr w v index coord node p hl hp]
  apply bind_congr
  intro n
  rw [foldsP_congr w v index coord ptr A n E hr]

theorem coord_program_congr (w v : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat)
    (hc : coord<7) (hl : LeafSame w v) (hr : SegmentReads w v ptr (coordSchedule coord sel)) :
    coordProgram w index coord sel ptr=coordProgram v index coord sel ptr := by
  unfold coordSchedule at hr
  unfold coordProgram
  dsimp only at hr ⊢
  split_ifs with hA <;> simp only [hA,if_true,if_false,SegmentReads] at hr
  all_goals
    obtain ⟨h0,h1,h2,h3,h4,-⟩ := hr
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h; omega) h0]
    apply bind_congr; intro n0
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h; omega) h1]
    apply bind_congr; intro n1
  · rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h) h2]
    apply bind_congr; intro n2
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h; omega) h3]
    apply bind_congr; intro n3
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h) h4]
  · rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h; omega) h2]
    apply bind_congr; intro n2
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h) h3]
    apply bind_congr; intro n3
    rw [segment_congr _ _ _ _ _ _ _ _ _ hl (by intro s g h; cases h) h4]

#print axioms coord_program_congr
end SigGolfCandidate.T3M.CanonicalSchedule
