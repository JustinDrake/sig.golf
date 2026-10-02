import SigGolfCandidate.T3.Gate6.ScoreGate
import SigGolfCandidate.T3.Secc.InjectiveCoverUpdate

/-!
# Stream CC: the occurrence score of a fresh target against an exposure list

For a target digest output `N` and a list `X` of exposed (selected) digest outputs, `score X N` counts, in each of
the seven coordinates, the injective assignments of `N`'s three raw leaves to opening occurrences of `X` at `N`'s
index and coordinate bucket with the same leaf value (SEC's `InjectiveCover.score`), and multiplies over the
coordinates. Within-coordinate distinctness is kept exactly:

* `one_le_score`: if all of `N`'s (distinct) leaves are exposed at its index and buckets, the score is at least one;
* `average_score`: averaged over a uniform target, the score is exactly `fullPrice (labels X) / 2^128`
  (per coordinate-bucket `(3r)_3 / 128^3`), whatever the exposed leaf values are;
* `score_append_mono`: the score only grows when exposures are appended.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Raw coordinates of a digest output -/

/-- The FTS index of an output (raw view, `output mod 2^31`). -/
def outIdx (x : HashOutput) : Fin (2 ^ 31) := (rawView x).1

/-- The bucket of coordinate `c`. -/
def outBucket (x : HashOutput) (c : Fin 7) : Fin 16 := ((rawView x).2 c).1

/-- The three raw (unsorted) leaves of coordinate `c`. -/
def outLeaves (x : HashOutput) (c : Fin 7) : Fin 3 → Fin 128 := ((rawView x).2 c).2

/-- The proposal label (index and buckets) of an output. -/
def label (x : HashOutput) : BPORS.History.Proposal := (outIdx x, fun c => outBucket x c)

/-- The labels of an exposure list. -/
def labels (X : List HashOutput) : List BPORS.History.Proposal := X.map label

theorem labels_append (X Y : List HashOutput) : labels (X ++ Y) = labels X ++ labels Y := List.map_append

/-! ## The score -/

/-- Opening occurrences of the exposures at index `i`, coordinate `c` and bucket `b`. -/
abbrev Slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Type :=
  {s : Fin X.length × Fin 3 // outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b}

/-- The leaf value at an occurrence. -/
def slotValue (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) (s : Slot X i c b) : Fin 128 :=
  outLeaves (X.get s.1.1) c s.1.2

/-- Injective occurrence assignments of a three-leaf target at `(i, c, b)`. -/
noncomputable def coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : ENNReal :=
  BPORS.InjectiveCover.score (slotValue X i c b) target

/-- **The score** of a target output against an exposure list. -/
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal :=
  if digestGate N=true then
    ∏ c : Fin 7, coordScore X (outIdx N) c (outBucket N c) (outLeaves N c) else 0

/-! ## Covered targets score at least one -/

/-- Every raw leaf of `N` at coordinate `c` is the leaf value of some occurrence at `N`'s index and bucket. -/
def CoordCovered (X : List HashOutput) (N : HashOutput) (c : Fin 7) : Prop :=
  ∀ j, ∃ s : Slot X (outIdx N) c (outBucket N c), slotValue X (outIdx N) c (outBucket N c) s = outLeaves N c j

theorem one_le_score (X : List HashOutput) (N : HashOutput)
    (hinj : ∀ c, Function.Injective (outLeaves N c)) (hgate : digestGate N=true)
    (hcov : ∀ c, CoordCovered X N c) : 1 ≤ score X N := by
  simp only [score,hgate,if_true]
  apply Finset.one_le_prod''
  intro c
  exact BPORS.InjectiveCover.one_le_score _ _ (hinj c) (hcov c)

/-! ## Monotonicity -/

/-- Occurrences of `X` embed into occurrences of `X ++ Y`. -/
def slotEmbed (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Slot X i c b ↪ Slot (X ++ Y) i c b where
  toFun s := ⟨(Fin.castLE (by simp) s.1.1, s.1.2), by
    have h := s.2
    simp only [List.get_eq_getElem, Fin.val_castLE] at h ⊢
    rw [List.getElem_append_left s.1.1.isLt]
    exact h⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have h1 := congrArg (fun u : Slot (X ++ Y) i c b => u.1) h
    simp only [Prod.mk.injEq] at h1
    exact Prod.ext (Fin.castLE_injective _ h1.1) h1.2

theorem coordScore_append_mono (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : coordScore X i c b target ≤ coordScore (X ++ Y) i c b target := by
  unfold coordScore
  apply BPORS.InjectiveCover.score_source_le (slotEmbed X Y i c b)
  intro s
  simp only [slotValue, slotEmbed, Function.Embedding.coeFn_mk, List.get_eq_getElem, Fin.val_castLE]
  rw [List.getElem_append_left s.1.1.isLt]

theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  split_ifs with hg
  · exact Finset.prod_le_prod' fun c _ => coordScore_append_mono X Y _ c _ _
  · exact le_rfl

/-! ## The average over a uniform target -/

/-- Exposures at index `i` with bucket `b` in coordinate `c`. -/
noncomputable def hits (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Nat :=
  (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b).card

theorem card_slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Fintype.card (Slot X i c b) = 3 * hits X i c b := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun s : Fin X.length × Fin 3 =>
      outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b) =
      (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b) ×ˢ
        (Finset.univ : Finset (Fin 3)) := by
    ext s
    simp
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, hits, Nat.mul_comm]

/-- The occurrence count is the bucket count of the index history. -/
theorem hits_eq_count (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    hits X i c b = ((BPORS.History.atIndex i (labels X)).map fun row => row c).count b := by
  induction X with
  | nil => simp [hits, labels, BPORS.History.atIndex]
  | cons x X ih =>
      have hsplit : hits (x :: X) i c b =
          (if outIdx x = i ∧ outBucket x c = b then 1 else 0) + hits X i c b := by
        unfold hits
        rw [Finset.card_filter, Finset.card_filter]
        exact Fin.sum_univ_succ (n := X.length) _
      rw [hsplit, ih]
      simp only [labels, List.map_cons, BPORS.History.atIndex_cons, label]
      by_cases hi : outIdx x = i
      · simp only [hi, if_true, true_and, List.map_cons, List.count_cons]
        by_cases hb : outBucket x c = b
        · simp [hb, Nat.add_comm]
        · simp [hb]
      · simp [hi]

theorem average_coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    BPORS.finiteAverage (fun target : Fin 3 → Fin 128 => coordScore X i c b target) =
      BPORS.bucketMass ((BPORS.History.atIndex i (labels X)).map fun row => row c) b / 128 ^ 3 := by
  unfold coordScore
  rw [BPORS.InjectiveCover.average_score, card_slot, hits_eq_count, BPORS.bucketMass]
  simp only [Fintype.card_fin, Nat.cast_ofNat]

/-- One coordinate, averaged over a uniform bucket and three uniform leaves. -/
theorem average_coordinate (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) :
    BPORS.finiteAverage (fun d : Fin 16 × (Fin 3 → Fin 128) => coordScore X i c d.1 d.2) =
      BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) / 128 ^ 3 := by
  rw [BPORS.finiteAverage_pair]
  simp_rw [average_coordScore]
  unfold BPORS.finiteAverage BPORS.coordinateEnvelope
  simp only [Fintype.card_fin, Nat.cast_ofNat, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The average of the score at a fixed index over uniform buckets and leaves is the index envelope. -/
theorem average_at_index (X : List HashOutput) (i : Fin (2 ^ 31)) :
    BPORS.finiteAverage (fun v : Fin 7 → Fin 16 × (Fin 3 → Fin 128) =>
        ∏ c : Fin 7, coordScore X i c (v c).1 (v c).2)/8 =
      BPORS.History.wordEnvelope (BPORS.History.atIndex i (labels X)) := by
  rw [BPORS.finiteAverage_product 7
    (fun c (d : Fin 16 × (Fin 3 → Fin 128)) => coordScore X i c d.1 d.2)]
  simp_rw [average_coordinate]
  unfold BPORS.History.wordEnvelope
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv]

/-- **Exact average** of the gated score over a uniform target output. -/
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = BPORS.History.fullPrice (labels X) / 2 ^ 128 := by
  change BPORS.finiteAverage (fun N : HashOutput => if digestGate N=true then
    (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2) (rawView N) else 0)=_
  rw [average_gate_weight (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2),
    BPORS.finiteAverage_pair,←finiteAverage_div]
  simp_rw [average_at_index]
  unfold BPORS.finiteAverage BPORS.History.fullPrice
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (2 ^ 97 : ENNReal), mul_assoc]
  congr 1
  rw [show (2 : ENNReal) ^ 128 = 2 ^ 97 * 2 ^ 31 by rw [← pow_add]]
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

end SigGolfCandidate.T3.Security.CaseC
