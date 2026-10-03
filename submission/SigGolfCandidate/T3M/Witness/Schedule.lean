import SigGolfCandidate.T3M.Witness.SideCode

/-! # The honest fold-stream schedule (stream W)

For a coordinate with sorted distinct global leaves `g_0 < g_1 < g_2` (one bucket of the coordinate tree, so
`g_j = 128 bucket + x_j`), let `d01`, `d12` be the levels of the lowest common ancestors of `(g_0, g_1)` and
`(g_1, g_2)` (bit lengths of the XORs; Core's `authCount` sums them). They differ, and Core's post-order DFS
(`recoverChild` at `(8, bucket)` and the three outer folds) has one of two shapes, which the W2 stack machine
replays as exactly five segments:

* `d01 < d12` (`g_0, g_1` merge first): leaf 0 folds `d01-1` levels; leaf 1 folds `d01-1`, merges, folds up to
  level `d12-1`; leaf 2 folds `d12-1`, merges, folds to the coordinate root (level 11);
* `d12 < d01` (`g_1, g_2` merge first): leaf 0 folds `d01-1`; leaf 1 folds `d12-1`; leaf 2 folds `d12-1`, merges,
  folds to level `d01-1`, merges, folds to the root.

A segment's folds follow the root path of one leaf: fold `r` of segment `⟨c, g, lo, a, m⟩` hashes the node at
level `lo + r`, heap index `(2048 + g) / 2^(lo + r)`, with its sibling `(lo + r, g / 2^(lo + r) ^^^ 1)`.
Checked against `t3m/ref3/witness.schedule` on all 8 · C(256, 3) buckets and triples (segment bytes and fold heap
indices) and against `stream_plan`'s slots on 20,000 random selections (`checks/closed_schedule.py`).

The sibling of a fold is a proof slot of Core's signature: Core consumes slots in DFS order (`frontier` of the
bucket subtree, then the three outer siblings, coordinate after coordinate), the stream places them in fold
order; `foldSlot` is the map fold ↦ slot and `streamPlan` its inverse. -/
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3

/-- Level of the lowest common ancestor of two distinct leaves of one coordinate tree. -/
def lcaLevel (x y : Nat) : Nat := (x ^^^ y).log2 + 1

/-- A stream segment of coordinate `coord`: `a` folds along the root path of the global leaf `g` starting at
level `lo`, then a merge with the stacked node (`merge`) or a stop. -/
structure Segment where
  coord : Nat
  g : Nat
  lo : Nat
  a : Nat
  merge : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Heap index of the current node before fold `r` of a segment. -/
def Segment.heap (seg : Segment) (r : Nat) : Nat := (2048 + seg.g) / 2 ^ (seg.lo + r)

/-- Parity bit `t` of a segment (heap index at its start, checked by the machine when `a > 0`). -/
def Segment.t (seg : Segment) : Nat := seg.heap 0 % 2

/-- Three low bits of the path node, packed into the segment header. -/
def Segment.sideCode (seg : Segment) : Nat := seg.g / 2 ^ seg.lo % 8

/-- Header byte 0 of a segment: `a | merge << 4 | t << 5` (header bytes 1..7 are zero). -/
def Segment.byte0 (seg : Segment) : Nat := seg.a + 16 * (if seg.merge then 1 else 0) + 32 * seg.sideCode

/-- Core position `(level, node)` of the sibling of fold `r` (the empty subtree whose proof slot it carries). -/
def Segment.sib (seg : Segment) (r : Nat) : Nat × Nat :=
  (seg.lo + r, seg.g / 2 ^ (seg.lo + r) ^^^ 1)

/-- The five segments of one coordinate (sorted distinct leaves; for other selections the schedule is not used). -/
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

/-- The 35 segments of the honest stream, coordinate after coordinate. -/
def schedule (chosen : List Selection) : List Segment :=
  (List.range 7).flatMap fun c => coordSchedule c (chosen.getD c ⟨0, []⟩)

/-- Header pointer of segment `n` of a segment list (from `streamBase`). -/
def segPtr (segs : List Segment) (n : Nat) : Nat :=
  streamBase + ((segs.take n).map fun s => 8 + 80 * s.a).sum

/-! ## Proof slots -/

/-- Core's global leaves of a selection (the `selected` list of `recoverFts`). -/
def selectedLeaves (sel : Selection) : List Nat := sel.leaves.map fun s => sel.bucket * 128 + s

/-- Proof positions of one coordinate in Core's consumption order: the frontier of the bucket subtree, then the
three outer siblings `(8 + j, bucket / 2^j ^^^ 1)`. -/
def slotPositions (sel : Selection) : List (Nat × Nat) :=
  frontier (selectedLeaves sel) 7 sel.bucket ++ (List.range 4).map fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)

/-- First proof slot of coordinate `c` (Core's `used` when it starts coordinate `c`). -/
def slotBase (chosen : List Selection) (c : Nat) : Nat :=
  ((List.range c).map fun c' => (slotPositions (chosen.getD c' ⟨0, []⟩)).length).sum

/-- The proof slot carried by fold `r` of a segment: its sibling's index in Core's consumption order. -/
def foldSlot (chosen : List Selection) (seg : Segment) (r : Nat) : Nat :=
  slotBase chosen seg.coord + (slotPositions (chosen.getD seg.coord ⟨0, []⟩)).idxOf (seg.sib r)

/-- All folds of a segment list as `(segment, fold)` positions, in stream order. -/
def foldPositions (segs : List Segment) : List (Nat × Nat) :=
  (List.range segs.length).flatMap fun n => (List.range (segs.getD n default).a).map fun r => (n, r)

/-- `streamPlan chosen k`: the `(segment, fold)` position of the honest stream that carries proof slot `k`
(`none` for slots beyond the used ones). -/
def streamPlan (chosen : List Selection) (k : Fin 115) : Option (Nat × Nat) :=
  (foldPositions (schedule chosen)).find? fun p =>
    foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k.val

/-- Witness offset of the fold block carrying proof slot `k` (`none` if unused). -/
def slotBlock (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p => foldBlock (segPtr (schedule chosen) p.1) p.2

/-- Offset of proof slot `k`'s value in the witness (`L` or `R` of its fold block by the parity of the folded
node), `none` if unused. -/
def slotOffset (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p =>
    let seg := (schedule chosen).getD p.1 default
    foldBlock (segPtr (schedule chosen) p.1) p.2 + sibOff (seg.heap p.2 % 2)

/-! ## Matching streams -/

/-- A header byte agrees with a segment on its live bits: `a`, `merge`, and up to three direction bits when `a > 0` (header
bytes 1..7 are never read). -/
def Segment.Matches (seg : Segment) (b : Nat) : Prop :=
  b % 16 = seg.a ∧ (b / 16 % 2 = 1 ↔ seg.merge = true) ∧ (0 < seg.a → b / 32 % segSideMod seg.a = seg.heap 0 % segSideMod seg.a)

instance (seg : Segment) (b : Nat) : Decidable (seg.Matches b) := by
  unfold Segment.Matches; infer_instance

/-- Every header byte of the stream agrees with the honest schedule on its live bits. -/
def StreamMatches (chosen : List Selection) (w : WBytes) : Prop :=
  ∀ n, n < (schedule chosen).length →
    ((schedule chosen).getD n default).Matches (wbyte w (segPtr (schedule chosen) n)).toNat

instance (chosen : List Selection) (w : WBytes) : Decidable (StreamMatches chosen w) := by
  unfold StreamMatches; infer_instance

end SigGolfCandidate.T3M
