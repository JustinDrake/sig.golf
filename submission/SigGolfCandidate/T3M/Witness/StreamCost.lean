import SigGolfCandidate.T3M.Witness.FourCost
import SigGolfCandidate.T3M.Witness.Skeleton

namespace SigGolfCandidate.T3M.FourCost
open SigGolfCandidate.T3 OracleComp
set_option autoImplicit false

/-- Exact cost of the next `n` segments read at their actual witness pointers. -/
def streamCost (w : WBytes) (ptr : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => let a := segFoldCount (wbyte w ptr).toNat
           segCost a + streamCost w (segNext ptr a) n

@[simp] theorem streamCost_zero (w : WBytes) (ptr : Nat) : streamCost w ptr 0 = 0 := rfl

theorem streamCost_step (w : WBytes) (ptr n : Nat) (hn : 0 < n) :
    streamCost w ptr n = segCost (segFoldCount (wbyte w ptr).toNat) +
      streamCost w (segNext ptr (segFoldCount (wbyte w ptr).toNat)) (n-1) := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem streamCost_headers (w : WBytes) (ss : List Segment) (ptr : Nat)
    (h : HdrsOk w ptr ss) :
    streamCost w ptr ss.length = (ss.map fun s => segCost s.a).sum := by
  induction ss generalizing ptr with
  | nil => rfl
  | cons s ss ih =>
    have ha := h.1.1
    simp only [List.length_cons,streamCost,List.map_cons,List.sum_cons,ha]
    rw [ih _ h.2]

theorem streamCost_matches (w : WBytes) (chosen : List Selection)
    (hm : StreamMatches chosen w) :
    streamCost w 1088 35 = ((schedule chosen).map fun s => segCost s.a).sum := by
  have hh := (hdrsOk_of_getD w (schedule chosen) (segPtr (schedule chosen))
    (fun i hi => segPtr_succ _ hi)).1.mp hm
  rw [segPtr_zero] at hh
  have hs := streamCost_headers w (schedule chosen) streamBase hh
  simpa only [schedule_length,streamBase] using hs

theorem source_fold_count (chosen : List Selection) (hc : ChosenOk chosen) :
    ((SideCost.sourceBanks chosen).map List.sum).sum = slotBase chosen 7 := by
  unfold SideCost.sourceBanks slotBase
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc7
  exact coord_fold_count c _ (hc c (List.mem_range.mp hc7))

theorem schedule_sums (chosen : List Selection) (f : Nat → Nat) :
    ((schedule chosen).map fun s => f s.a).sum =
      ((SideCost.sourceBanks chosen).map fun xs => (xs.map f).sum).sum := by
  simp only [schedule,SideCost.sourceBanks,List.map_flatMap,List.map_map]
  generalize List.range 7 = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    rw [ih]
    simp only [Function.comp_def,List.map_map]

/-- This bound covers every matching admissible stream, without assumptions on hash answers. -/
theorem streamCost_canonical (w : WBytes) (N : HashOutput)
    (hsel : selectionsOk (selections N) = true)
    (hadm : admissible (selections N) = true) (hm : StreamMatches (selections N) w) :
    386 + streamCost w 1088 35 ≤ 2548 := by
  have hc := chosenOk_of N hsel
  have hf : ((SideCost.sourceBanks (selections N)).map List.sum).sum ≤ 115 := by
    rw [source_fold_count _ hc]
    exact slotBase_seven_le N hc hadm
  rw [streamCost_matches w _ hm,schedule_sums]
  exact source_seven (selections N) hc hf

end SigGolfCandidate.T3M.FourCost
