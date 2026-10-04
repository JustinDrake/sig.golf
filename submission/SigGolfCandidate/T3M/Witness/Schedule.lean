import SigGolfCandidate.T3M.Witness.Layout

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
def lcaLevel (x y : Nat) : Nat := (x ^^^ y).log2 + 1
structure Segment where
  coord : Nat
  g : Nat
  lo : Nat
  a : Nat
  merge : Bool
  deriving DecidableEq, Repr, Inhabited
def Segment.heap (seg : Segment) (r : Nat) : Nat := (2048 + seg.g) / 2 ^ (seg.lo + r)
def Segment.t (seg : Segment) : Nat := seg.heap 0 % 2
def Segment.byte0 (seg : Segment) : Nat := seg.a + 16 * (if seg.merge then 1 else 0) + 32 * seg.t
def Segment.sib (seg : Segment) (r : Nat) : Nat × Nat :=
  (seg.lo + r, seg.g / 2 ^ (seg.lo + r) ^^^ 1)
def coordSchedule (coord : Nat) (sel : Selection) : List Segment :=
  let g0 := selLeaf sel 0
  let g1 := selLeaf sel 1
  let g2 := selLeaf sel 2
  let d01 := lcaLevel g0 g1
  let d12 := lcaLevel g1 g2
  if d01 < d12 then
    [⟨coord, g0, 0, d01 - 1, false⟩, ⟨coord, g1, 0, d01 - 1, true⟩, ⟨coord, g1, d01, d12 - 1 - d01, false⟩,
      ⟨coord, g2, 0, d12 - 1, true⟩, ⟨coord, g2, d12, 11 - d12, false⟩]
  else
    [⟨coord, g0, 0, d01 - 1, false⟩, ⟨coord, g1, 0, d12 - 1, false⟩, ⟨coord, g2, 0, d12 - 1, true⟩,
      ⟨coord, g2, d12, d01 - 1 - d12, true⟩, ⟨coord, g2, d01, 11 - d01, false⟩]
def schedule (chosen : List Selection) : List Segment :=
  (List.range 7).flatMap fun c => coordSchedule c (chosen.getD c ⟨0, []⟩)
def segPtr (segs : List Segment) (n : Nat) : Nat :=
  streamBase + ((segs.take n).map fun s => 8 + 64 * s.a).sum
def selectedLeaves (sel : Selection) : List Nat := sel.leaves.map fun s => sel.bucket * 128 + s
def slotPositions (sel : Selection) : List (Nat × Nat) :=
  frontier (selectedLeaves sel) 7 sel.bucket ++ (List.range 4).map fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)
def slotBase (chosen : List Selection) (c : Nat) : Nat :=
  ((List.range c).map fun c' => (slotPositions (chosen.getD c' ⟨0, []⟩)).length).sum
def foldSlot (chosen : List Selection) (seg : Segment) (r : Nat) : Nat :=
  slotBase chosen seg.coord + (slotPositions (chosen.getD seg.coord ⟨0, []⟩)).idxOf (seg.sib r)
def foldPositions (segs : List Segment) : List (Nat × Nat) :=
  (List.range segs.length).flatMap fun n => (List.range (segs.getD n default).a).map fun r => (n, r)
def streamPlan (chosen : List Selection) (k : Fin 115) : Option (Nat × Nat) :=
  (foldPositions (schedule chosen)).find? fun p =>
    foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k.val
def slotBlock (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p => foldBlock (segPtr (schedule chosen) p.1) p.2
def slotOffset (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p =>
    let seg := (schedule chosen).getD p.1 default
    foldBlock (segPtr (schedule chosen) p.1) p.2 + sibOff (seg.heap p.2 % 2)
def Segment.Matches (seg : Segment) (b : Nat) : Prop :=
  b % 16 = seg.a ∧ (b / 16 % 2 = 1 ↔ seg.merge = true) ∧ (0 < seg.a → b / 32 % 2 = seg.t)
instance (seg : Segment) (b : Nat) : Decidable (seg.Matches b) := by
  unfold Segment.Matches; infer_instance
def StreamMatches (chosen : List Selection) (w : WBytes) : Prop :=
  ∀ n, n < (schedule chosen).length →
    ((schedule chosen).getD n default).Matches (wbyte w (segPtr (schedule chosen) n)).toNat
instance (chosen : List Selection) (w : WBytes) : Decidable (StreamMatches chosen w) := by
  unfold StreamMatches; infer_instance
end SigGolfCandidate.T3M
