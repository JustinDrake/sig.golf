import SigGolfCandidate.T3M.Witness.Slots
import SigGolfCandidate.T3M.Witness.Encode

/-! # The FTS normal form on shaped streams (stream W)

Core's per-coordinate recovery (`recoverChildP` at the bucket node and the four outer folds) is `coordCanon` with
the valuation `valOf proof base (slotPositions sel)`; for the decoded witness of a shaped stream this valuation agrees
with the stream's reads at every fold, so `ftsP` and Core's padded `recoverFtsP` coincide (`ftsP_shaped`). -/
set_option maxRecDepth 10000

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The valuation of proof positions by slots: position `p` reads slot `base + idxOf p ps`. -/
def valOf (proof : Fin 115 → Digest) (base : Nat) (ps : List (Nat × Nat)) (p : Nat × Nat) : Digest :=
  proof ⟨(base + ps.idxOf p) % 115, Nat.mod_lt _ (by decide)⟩

theorem slotsMatch_valOf (proof : Fin 115 → Digest) (pads : Pads) (base : Nat) (ps : List (Nat × Nat))
    (hnd : ps.Nodup) : SlotsMatch proof pads (valOf proof base ps) (valOf pads.fold base ps) base ps := by
  intro i hi h
  refine ⟨?_, ?_⟩ <;> simp only [valOf, List.Nodup.idxOf_getElem hnd, Nat.mod_eq_of_lt h]

/-! ## Core's per-coordinate step -/

/-- The four outer folds of `recoverFtsP` (one step). -/
def outerStepP (sig : Signature) (pads : Pads) (index coord bucket : Nat) (state : Option (Digest × Nat)) (j : Nat) :
    M (Option (Digest × Nat)) := do
  let some (value, used) := state | pure none
  if h : used < 115 then
    let other := sig.proof ⟨used, h⟩
    let pair := if bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
    let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + bucket / 2 ^ (j + 1)) pair.1
      (pads.fold ⟨used, h⟩) pair.2
    pure (some (parent, used + 1))
  else pure none

/-- One coordinate of `recoverFtsP`. -/
def ftsStepP (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (state : Option (List Digest × Nat)) (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, used) := state | pure none
  let sel := chosen.getD coord ⟨0, []⟩
  let selected := sel.leaves.map (fun s => sel.bucket * 128 + s)
  let values := (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
  let some (value, next) ← recoverChildP index coord selected values sig.proof pads 7 sel.bucket used
    | pure none
  let result ← (List.range 4).foldlM (outerStepP sig pads index coord sel.bucket) (some (value, next))
  let some (root, next) := result | pure none
  pure (some (roots ++ [root], next))

theorem recoverFtsP_eq (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection) :
    recoverFtsP sig pads index chosen = (do
      let state ← (List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0))
      let some (roots, used) := state | pure none
      if !(List.range (115 - used)).all (fun j =>
          decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
      pure (some (← forestPk index roots))) := rfl

/-- The outer folds climb `g`'s root path from level 7. -/
theorem outer_climb (sig : Signature) (pads : Pads) (index coord bucket g : Nat) (hg : g / 2 ^ 7 = bucket)
    (val pad : Nat × Nat → Digest) : ∀ n j0 (v : Digest) (u : Nat), j0 + n ≤ 4 → u + n ≤ 115 →
      (∀ j < n, ∀ h : u + j < 115, sig.proof ⟨u + j, h⟩ = val (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1) ∧
        pads.fold ⟨u + j, h⟩ = pad (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1)) →
      (List.range' j0 n).foldlM (outerStepP sig pads index coord bucket) (some (v, u)) =
        (fun v' => some (v', u + n)) <$> climbV index coord val pad g (7 + j0) n v := by
  intro n
  induction n with
  | zero => intro j0 v u _ _ _; simp
  | succ n ih =>
      intro j0 v u hj hu hm
      have hb : g / 2 ^ (7 + j0) = bucket / 2 ^ j0 := by
        rw [pow_add, ← Nat.div_div_eq_div_mul, hg]
      obtain ⟨hv, hp⟩ := hm 0 (by omega) (by omega)
      simp only [Nat.add_zero] at hv hp
      rw [List.range'_succ, List.foldlM_cons, climbV_succ, map_bind]
      have hstep : outerStepP sig pads index coord bucket (some (v, u)) j0 =
          (fun p => some (p, u + 1)) <$> climbStep index coord val pad g (7 + j0) v := by
        unfold outerStepP climbStep
        simp only [dif_pos (show u < 115 by omega), hb, hv, hp]
        have hh : 2 ^ (11 - (7 + j0 + 1)) + bucket / 2 ^ j0 / 2 = 2 ^ (4 - j0 - 1) + bucket / 2 ^ (j0 + 1) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show 11 - (7 + j0 + 1) = 4 - j0 - 1 by omega]
        rw [hh]
        rcases Nat.mod_two_eq_zero_or_one (bucket / 2 ^ j0) with h0 | h0 <;>
          simp [h0, map_eq_bind_pure_comp]
      rw [hstep, bind_map_left]
      congr 1; funext x
      rw [ih (j0 + 1) x (u + 1) (by omega) (by omega) (fun j hj h => by
        have := hm (j + 1) (by omega) (by omega)
        simpa only [show u + (j + 1) = u + 1 + j by omega, show 7 + j0 + (j + 1) = 7 + (j0 + 1) + j by omega]
          using this)]
      simp only [show u + 1 + n = u + (n + 1) by omega, show 7 + j0 + 1 = 7 + (j0 + 1) by omega]

theorem ftsStepP_some (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) :
    ftsStepP sig pads index chosen (some (roots, used)) coord = (do
      let some (value, next) ← recoverChildP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
        ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩))
        sig.proof pads 7 (chosen.getD coord ⟨0, []⟩).bucket used | pure none
      let result ← (List.range 4).foldlM (outerStepP sig pads index coord (chosen.getD coord ⟨0, []⟩).bucket)
        (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) := rfl

/-- **Core side of one coordinate.** -/
theorem ftsStepP_canon (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) (hs : SelOk (chosen.getD coord ⟨0, []⟩))
    (hfit : used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length ≤ 115)
    (val pad : Nat × Nat → Digest)
    (hm : SlotsMatch sig.proof pads val pad used (slotPositions (chosen.getD coord ⟨0, []⟩))) :
    ftsStepP sig pads index chosen (some (roots, used)) coord =
      (fun v => some (roots ++ [v], used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length)) <$>
        coordCanon index coord (leafHP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
            ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
          val pad (selLeaf (chosen.getD coord ⟨0, []⟩) 0) (selLeaf (chosen.getD coord ⟨0, []⟩) 1)
          (selLeaf (chosen.getD coord ⟨0, []⟩) 2) := by
  rw [ftsStepP_some]
  generalize chosen.getD coord ⟨0, []⟩ = sel at *
  generalize hvals : (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩) =
    values
  have hsp : slotPositions sel = T3.frontier (selectedLeaves sel) 7 sel.bucket ++
      (List.range 4).map (fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)) := rfl
  rw [hsp] at hfit hm ⊢
  rw [List.length_append] at hfit ⊢
  simp only [List.length_map, List.length_range] at hfit ⊢
  have hF := recoverChildP_eq_dfsP index coord (selectedLeaves sel) values sig.proof pads val pad 7 sel.bucket used
    (by omega) hm.left
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have hb2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hs.selected]; simp)
  have hO := outer_climb sig pads index coord sel.bucket (selLeaf sel 2) hb2 val pad 4 0
  have hbk : ∀ j, selLeaf sel 2 / 2 ^ (7 + 0 + j) = sel.bucket / 2 ^ j := by
    intro j; rw [Nat.add_zero]; exact bucket_div_outer hs.l2
  have hD := dfsP_bucket (index := index) (coord := coord)
    (leafH := leafHP index coord (selectedLeaves sel) values pads)
    (val := val) (pad := pad) g01 g12 (hs.bucket_div (by rw [hs.selected]; simp))
    (hs.bucket_div (by rw [hs.selected]; simp)) hb2
  rw [← hs.selected] at hD
  rw [hF, bind_map_left, ← hD, map_bind]
  congr 1; funext v
  dsimp only
  rw [show List.range 4 = List.range' 0 4 from List.range_eq_range' ..]
  rw [hO v _ (by omega) (by omega) (fun j hj h => by
    have := hm.right j (by simp; omega) h
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hbk j, Nat.add_zero]; exact this)]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, List.length_map, List.length_range,
    Nat.add_assoc, Nat.zero_add, Nat.add_zero, bind_assoc, pure_bind]

/-! ## Bookkeeping of a shaped stream -/

theorem selectionsOk_sel {chosen : List Selection} (h : selectionsOk chosen = true) {sel : Selection}
    (hm : sel ∈ chosen) : ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 := by
  unfold selectionsOk at h
  have := List.all_eq_true.mp h sel hm
  match hl : sel.leaves, this with
  | [x0, x1, x2], h' =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact ⟨x0, x1, x2, rfl, h'.1, h'.2⟩

theorem chosenOk_of (N : HashOutput) (h : selectionsOk (selections N) = true) : ChosenOk (selections N) := by
  intro c hc
  have hm := Correctness.selection_getD_mem N c hc
  obtain ⟨x0, x1, x2, hl, h01, h12⟩ := selectionsOk_sel h hm
  have hb := selection_bucket_bound N _ hm
  have h2 := selection_leaf_bound N _ x2 hm (by rw [hl]; simp)
  exact ⟨by rw [hl]; rfl, hb, by rw [hl]; simpa using h2, by rw [hl]; simpa using h01, by rw [hl]; simpa using h12⟩

theorem slotPositions_length {sel : Selection} (hs : SelOk sel) :
    (slotPositions sel).length = authCount sel.leaves + 4 := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  unfold slotPositions selectedLeaves
  rw [List.length_append, Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb]
  simp

theorem sum_range_getD {α : Type} (items : List α) (d : α) (f : α → Nat) :
    ((List.range items.length).map (fun i => f (items.getD i d))).sum = (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
      simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]

theorem slotBase_seven_eq (N : HashOutput) (hc : ChosenOk (selections N)) :
    slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  unfold slotBase
  rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
    List.sum_map_add]
  simp
  omega

/-- The used proof slots fit (Core's cap). -/
theorem slotBase_seven_le (N : HashOutput) (hc : ChosenOk (selections N))
    (hadm : admissible (selections N) = true) : slotBase (selections N) 7 ≤ 115 := by
  have h := hadm
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  have hsum : slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
    unfold slotBase
    rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
      List.sum_map_add]
    simp
    omega
  omega

theorem segPtr_succ (segs : List Segment) {m : Nat} (hm : m < segs.length) :
    segPtr segs (m + 1) = segNext (segPtr segs m) (segs.getD m default).a := by
  unfold segPtr segNext
  rw [List.take_add_one, List.getElem?_eq_getElem hm, List.map_append, List.sum_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD,
    List.getElem?_eq_getElem hm, Option.getD_some]
  omega

theorem segsOk_of_getD (w : WBytes) (val pad : Nat × Nat → Digest) : ∀ (segs : List Segment) (f : Nat → Nat),
    (∀ i < segs.length, f (i + 1) = segNext (f i) (segs.getD i default).a) →
    (∀ i < segs.length, SegOk w val pad (segs.getD i default) (f i)) →
    SegsOk w val pad (f 0) segs ∧ segsEnd (f 0) segs = f segs.length := by
  intro segs
  induction segs with
  | nil => intro f _ _; exact ⟨trivial, rfl⟩
  | cons s rest ih =>
      intro f hf hok
      have h0 := hf 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      obtain ⟨h1, h2⟩ := ih (fun i => f (i + 1)) (fun i hi => by
          have := hf (i + 1) (by simp; omega); simpa using this)
        (fun i hi => by have := hok (i + 1) (by simp; omega); simpa using this)
      simp only [h0] at h1 h2
      refine ⟨⟨by simpa using hok 0 (by simp), h1⟩, ?_⟩
      simp only [segsEnd, h2, List.length_cons]

/-- Total folds of the schedule: as many as the used proof slots. -/
theorem sum_flatMap_nat {β : Type} (l : List β) (f : β → List Nat) :
    (l.flatMap f).sum = (l.map fun b => (f b).sum).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem schedule_folds (chosen : List Selection) (hc : ChosenOk chosen) :
    ((schedule chosen).map Segment.a).sum = slotBase chosen 7 := by
  unfold schedule slotBase
  rw [List.map_flatMap, sum_flatMap_nat]
  congr 1
  apply List.map_congr_left
  intro c hc'
  rw [List.mem_range] at hc'
  exact coord_fold_count c _ (hc c hc')

theorem segPtr_end (chosen : List Selection) (hc : ChosenOk chosen) :
    segPtr (schedule chosen) 35 = streamBase + 280 + 80 * slotBase chosen 7 := by
  unfold segPtr
  rw [List.take_of_length_le (by rw [schedule_length])]
  have h1 := schedule_folds chosen hc
  have h2 : ((schedule chosen).map fun s => 8 + 80 * s.a).sum = 8 * 35 + 80 * ((schedule chosen).map Segment.a).sum := by
    rw [List.sum_map_add, List.map_const', List.sum_replicate, schedule_length, List.sum_map_mul_left]; rfl
  rw [h2, h1]; omega

/-! ## The decoded witness agrees with the stream -/

/-- The valuation of the decoded proof slots of coordinate `c`. -/
def decVal (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (witDecP N w).signature.proof (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))

/-- The valuation of the decoded fold pads of coordinate `c`. -/
def decPad (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (padDecP N w).fold (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))

theorem decoded_foldOk (N : HashOutput) (w : WBytes) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) {c i r : Nat} (hc7 : c < 7) (hi : i < 5)
    (hr : r < ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).a) :
    FoldOk w (decVal N w c) (decPad N w c) ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r)
      (segPtr (schedule (selections N)) (5 * c + i)) r := by
  have hn : 5 * c + i < 35 := by omega
  have hsg := schedule_getD (selections N) hn
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsg
  have hr' : r < ((schedule (selections N)).getD (5 * c + i) default).a := by rw [hsg]; exact hr
  obtain ⟨hsplit, hlt⟩ := foldSlot_split (selections N) hc hn hr'
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsplit hlt
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1
  have hk : foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r < 115 := by omega
  have hplan := streamPlan_foldSlot (selections N) hc hn hr' hk
  have htop := (foldFacts c _ (hc c hc7)).top i hi
  have hpar : ((schedule (selections N)).getD (5 * c + i) default).heap r % 2 =
      ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g /
        2 ^ (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r) % 2 := by
    rw [hsg]; unfold Segment.heap; exact heap_mod_two (by omega)
  have hidx : (slotBase (selections N) c + (slotPositions ((selections N).getD c ⟨0, []⟩)).idxOf
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).sib r)) % 115 =
      foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r := by
    rw [hsplit, Nat.mod_eq_of_lt (by omega)]
  have hP : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (witDecP N w).signature.proof x = (witDecP N w).signature.proof ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  have hQ : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (padDecP N w).fold x = (padDecP N w).fold ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  constructor
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hP _ hidx]
    unfold witDecP
    simp only [slotOffset, hplan, Option.map_some, hpar]
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hQ _ hidx]
    unfold padDecP
    simp only [slotBlock, hplan, Option.map_some]

theorem segPtr_zero (segs : List Segment) : segPtr segs 0 = streamBase := by simp [segPtr]

theorem decoded_segsOk (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7) :
    SegsOk w (decVal N w c) (decPad N w c) (segPtr (schedule (selections N)) (5 * c))
      (coordSchedule c ((selections N).getD c ⟨0, []⟩)) ∧
    segsEnd (segPtr (schedule (selections N)) (5 * c)) (coordSchedule c ((selections N).getD c ⟨0, []⟩)) =
      segPtr (schedule (selections N)) (5 * (c + 1)) := by
  obtain ⟨hok, hadm, hmatch⟩ := h
  have hc := chosenOk_of N hok
  have hle := slotBase_seven_le N hc hadm
  have hlen := coordSchedule_length c ((selections N).getD c ⟨0, []⟩)
  have := segsOk_of_getD w (decVal N w c) (decPad N w c) (coordSchedule c ((selections N).getD c ⟨0, []⟩))
    (fun i => segPtr (schedule (selections N)) (5 * c + i))
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      have := segPtr_succ (schedule (selections N)) (m := 5 * c + i) (by rw [schedule_length]; exact hn)
      rw [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this
      simpa only [Nat.add_assoc] using this)
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      refine ⟨?_, fun r hr => decoded_foldOk N w hc hle hc7 hi hr⟩
      have := hmatch (5 * c + i) (by rw [schedule_length]; exact hn)
      rwa [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this)
  simp only [Nat.add_zero, hlen] at this
  exact ⟨this.1, by rw [this.2]; ring_nf⟩

/-! ## Assembling the seven coordinates -/

/-- One coordinate of `ftsP`. -/
def ftsStreamStep (w : WBytes) (index : Nat) (chosen : List Selection) (state : Option (List Digest × Nat))
    (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, ptr) := state | pure none
  let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
  pure (some (roots ++ [root], ptr))

theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← (List.range 7).foldlM (ftsStreamStep w index chosen) (some ([], streamBase))
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl

/-- The canonical program of coordinate `c` of a shaped witness. -/
def canonD (N : HashOutput) (w : WBytes) (c : Nat) : M Digest :=
  coordCanon (N.toNat % 2 ^ 31) c
    (leafAt w (N.toNat % 2 ^ 31) c [selLeaf ((selections N).getD c ⟨0, []⟩) 0, selLeaf ((selections N).getD c ⟨0, []⟩) 1,
      selLeaf ((selections N).getD c ⟨0, []⟩) 2])
    (decVal N w c) (decPad N w c) (selLeaf ((selections N).getD c ⟨0, []⟩) 0)
    (selLeaf ((selections N).getD c ⟨0, []⟩) 1) (selLeaf ((selections N).getD c ⟨0, []⟩) 2)

theorem stream_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStreamStep w (N.toNat % 2 ^ 31) (selections N) (some (roots, segPtr (schedule (selections N)) (5 * c))) c =
      (fun v => some (roots ++ [v], segPtr (schedule (selections N)) (5 * (c + 1)))) <$> canonD N w c := by
  have hs := chosenOk_of N h.1 c hc7
  obtain ⟨hok, hend⟩ := decoded_segsOk N w h hc7
  unfold ftsStreamStep
  simp only []
  rw [ftsCoordP_canon w _ c _ _ (decVal N w c) (decPad N w c) hs.b hs.l2 hs.s01 hs.s12 hok, hend]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, canonD, bind_assoc, pure_bind]

theorem leafHP_dec (N : HashOutput) (w : WBytes) {c : Nat} (hc7 : c < 7) (gs : List Nat) (g : Nat)
    (hg : gs.idxOf g < 3) :
    leafHP (N.toNat % 2 ^ 31) c gs ((List.range 3).map (fun j =>
        (witDecP N w).signature.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) (padDecP N w) g =
      leafAt w (N.toNat % 2 ^ 31) c gs g := by
  unfold leafHP leafAt pendingHash
  have h1 : (3 * c + gs.idxOf g) % 22 = 3 * c + gs.idxOf g := Nat.mod_eq_of_lt (by omega)
  have h2 : (3 * c + gs.idxOf g + 1) % 22 = 3 * c + gs.idxOf g + 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (c * 3 + gs.idxOf g) % 21 = 3 * c + gs.idxOf g := by rw [Nat.mod_eq_of_lt (by omega)]; ring
  simp only [padDecP, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg,
    Option.map_some, Option.getD_some, witDecP, h3]

theorem core_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)
        (some (roots, slotBase (selections N) c)) c =
      (fun v => some (roots ++ [v], slotBase (selections N) (c + 1))) <$> canonD N w c := by
  have hc := chosenOk_of N h.1
  have hs := hc c hc7
  have hle := slotBase_seven_le N hc h.2.1
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1 ⊢
  rw [ftsStepP_canon _ _ _ _ roots _ c hs (by omega) (decVal N w c) (decPad N w c)
    (slotsMatch_valOf _ _ _ _ (slotPositions_nodup _))]
  unfold canonD
  rw [hs.selected]
  congr 1
  have hg := hs.selected
  have g01 : selLeaf ((selections N).getD c ⟨0, []⟩) 0 < selLeaf ((selections N).getD c ⟨0, []⟩) 1 := by
    unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf ((selections N).getD c ⟨0, []⟩) 1 < selLeaf ((selections N).getD c ⟨0, []⟩) 2 := by
    unfold selLeaf; have := hs.s12; omega
  apply coordCanon_congr_leaf <;> apply leafHP_dec N w hc7 <;>
    exact List.idxOf_lt_length_of_mem (by simp)

/-- Folding seven coordinates that each run a canonical program. -/
theorem foldlM_canon (step : Option (List Digest × Nat) → Nat → M (Option (List Digest × Nat)))
    (P : Nat → M Digest) (pos : Nat → Nat)
    (hstep : ∀ c < 7, ∀ roots, step (some (roots, pos c)) c = (fun v => some (roots ++ [v], pos (c + 1))) <$> P c) :
    ∀ n ≤ 7, (List.range n).foldlM step (some ([], pos 0)) =
      (fun roots => some (roots, pos n)) <$> (List.range n).foldlM (fun roots c => (fun v => roots ++ [v]) <$> P c) [] := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldlM_append, List.foldlM_append, ih (by omega), bind_map_left, map_bind]
      congr 1; funext roots
      simp only [List.foldlM_cons, List.foldlM_nil, hstep n (by omega), bind_map_left, map_bind,
        Functor.map_map, bind_pure]

theorem dec_proof_tail (N : HashOutput) (w : WBytes) (h : Shaped N w) (k : Fin 115)
    (hk : slotBase (selections N) 7 ≤ k.val) : (witDecP N w).signature.proof k = 0 := by
  have hc := chosenOk_of N h.1
  have hnone : streamPlan (selections N) k = none := by
    unfold streamPlan
    rw [List.find?_eq_none]
    rintro ⟨n, r⟩ hp
    obtain ⟨hm1, hm2⟩ := mem_foldPositions.mp hp
    rw [schedule_length] at hm1
    simp only at hm1 hm2
    obtain ⟨e, l⟩ := foldSlot_split (selections N) hc hm1 hm2
    have hb1 := slotBase_mono (selections N) (show n / 5 + 1 ≤ 7 by omega)
    rw [slotBase_succ] at hb1
    simp only [decide_eq_true_eq]
    omega
  show (match slotOffset (selections N) k with | some off => wdig w off | none => 0) = 0
  simp [slotOffset, hnone]


/-- **FTS normal form.** On a shaped stream the stream machine is Core's padded FTS recovery of the decoded witness
with the decoded pads. -/
theorem ftsP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    ftsP w (N.toNat % 2 ^ 31) (selections N) =
      recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N) := by
  have hc := chosenOk_of N h.1
  have hle := slotBase_seven_le N hc h.2.1
  rw [ftsP_eq, recoverFtsP_eq]
  have A := foldlM_canon (ftsStreamStep w (N.toNat % 2 ^ 31) (selections N)) (canonD N w)
      (fun c => segPtr (schedule (selections N)) (5 * c)) (fun c hc7 roots => stream_step_dec N w h hc7 roots) 7 le_rfl
  have B := foldlM_canon (ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))
      (canonD N w) (fun c => slotBase (selections N) c) (fun c hc7 roots => core_step_dec N w h hc7 roots) 7 le_rfl
  simp only [Nat.mul_zero, segPtr_zero] at A
  simp only [show slotBase (selections N) 0 = 0 from rfl] at B
  rw [A, B, bind_map_left, bind_map_left]
  refine bind_congr (fun roots => ?_)
  have hend : ¬ streamEnd < segPtr (schedule (selections N)) (5 * 7) := by
    rw [show 5 * 7 = 35 by rfl, segPtr_end _ hc]; unfold streamEnd streamBase; omega
  have htail : ((List.range (115 - slotBase (selections N) 7)).all fun j =>
      decide ((witDecP N w).signature.proof ⟨(slotBase (selections N) 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) =
        true := by
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    exact dec_proof_tail N w h _ (by simp only [Nat.mod_eq_of_lt (show slotBase (selections N) 7 + j < 115 by omega)]; omega)
  dsimp only
  rw [if_neg hend, htail]
  rfl

/-! ## Layers -/

theorem layerP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayerP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) lay digits := rfl

theorem layersP_dec (N : HashOutput) (w : WBytes) : ∀ n root,
    layersP w (N.toNat % 2 ^ 31) n root = verifyLayersP (witDecP N w) (padDecP N w) (N.toNat % 2 ^ 31) n root := by
  intro n
  induction n with
  | zero => intro root; rfl
  | succ n ih =>
      intro root
      simp only [layersP, verifyLayersP, layerP_dec, ih]
      rfl

/-- `verifyP` after the digest query (a copy of its tail, so that statements can name it). -/
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)

theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl

/-- **The shaped tail of `verifyP`**: after the digest query, on a stream with the honest shape, `verifyP` is Core's
verification with the decoded witness and pads. -/
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  simp only []
  rw [if_neg (by simp [h.1])]
  cases hg : digestGate N with
  | false => simp [digestAdmissible, hg]
  | true =>
      have ha : digestAdmissible N=true := by simp [digestAdmissible,h.2.1,hg]
      simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [ftsP_shaped N w h]
      simp only [layersP_dec]
      refine bind_congr (fun r => ?_)
      rcases r with _ | root
      · rfl
      · refine bind_congr (fun r => ?_)
        rcases r with _ | root <;> rfl

end SigGolfCandidate.T3M
