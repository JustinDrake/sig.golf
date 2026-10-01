import SigGolfCandidate.Final.Main
import SigGolfCandidate.Keygen.Main
import SigGolfCandidate.Sign.Main
import SigGolfCandidate.Verify.Main
import SigGolfCandidate.SphincsSecurity
import Lean.Elab.Tactic.Omega
import SigGolfCandidate.SphincsSecurity.Completeness.Stack
import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsSchedule
import SigGolfCandidate.Verify.PorsGood
import SigGolfCandidate.Equiv.Wit
import SigGolfCandidate.Equiv.Verify
import SigGolfCandidate.Final.RO

section StructuralCostCertificate

/-! Universal structural PORS segment credit and exact accepting-run accounting.
Consolidated from twelve independently checked research modules to respect the
submission entry limit. The executable image and verification predicate are unchanged. -/

/-! ## PorsPositiveBound -/
/- Standalone finite upper-bound certificate. This does not connect the relation below
   to schedule, reference execution, or machine execution, and changes no claim. -/
namespace SigGolfCandidate.Research.PorsPositiveBound

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A finite lower bound on branching penalties for up to15 leaves. The transition
inequality is checked below by the kernel, independently of how these literals were found. -/
def penalty (k : Nat) : Nat :=
  (#[0, 0, 3, 8, 13, 20, 27, 34, 41, 50, 59, 68, 77, 86, 95, 104] : Array Nat).getD k 0

private theorem penalty_step : ∀ k : Fin 16, ∀ a : Fin 16,
    1 ≤ a.val → a.val < k.val →
    penalty k.val ≤ 2*k.val-1 + penalty a.val + penalty (k.val-a.val) := by decide +kernel

/-- An abstract compressed binary tree in which every emitted segment has positive folds.
`h` is the common leaf height, `k` the leaf count, and `f` the number of unary edges/folds.
No correspondence to the verifier is asserted by this definition. -/
inductive PositiveTree : Nat → Nat → Nat → Prop
  | leaf (h : Nat) (hp : 1 ≤ h) : PositiveTree h 1 h
  | fork (h k j a l r : Nat)
      (hj : 1 ≤ j) (hjh : j < h) (ha : 1 ≤ a) (hak : a < k)
      (left : PositiveTree (h-j-1) a l)
      (right : PositiveTree (h-j-1) (k-a) r) : PositiveTree h k (j+l+r)

theorem positiveTree_penalty {h k f : Nat} (ht : PositiveTree h k f)
    (hk : k ≤ 15) : f + penalty k ≤ k*h := by
  induction ht with
  | leaf h hp =>
      have e : penalty 1 = 0 := by decide +kernel
      simpa only [e, Nat.one_mul, Nat.add_zero] using (Nat.le_refl h)
  | fork h k j a l r hj hjh ha hak left right ihl ihr =>
      have hl := ihl (by omega)
      have hr := ihr (by omega)
      have hc := penalty_step ⟨k, by omega⟩ ⟨a, by omega⟩ ha hak
      dsimp only at hc
      have hsum : l+r+penalty a+penalty (k-a) ≤ k*(h-j-1) := by
        have em : a*(h-j-1)+(k-a)*(h-j-1) = k*(h-j-1) := by
          rw [← Nat.add_mul]
          congr 1
          omega
        omega
      have hm : j+(2*k-1) ≤ k*(j+1) := by
        have h1 := Nat.mul_le_mul_left (k-1) hj
        simp only [Nat.mul_one] at h1
        have e : k*j = (k-1)*j+j := by
          calc
            k*j = ((k-1)+1)*j := congrArg (fun z => z*j) (by omega)
            _ = (k-1)*j+j := by rw [Nat.add_mul, Nat.one_mul]
        rw [Nat.mul_add, Nat.mul_one, e]
        omega
      have htotal : j+l+r+penalty k ≤ k*(h-j-1)+k*(j+1) := by omega
      rw [← Nat.mul_add] at htotal
      have e : h-j-1+(j+1) = h := by omega
      rwa [e] at htotal

theorem penalty_15 : penalty 15 = 104 := by decide +kernel

theorem positiveTree_14_15 {f : Nat} (ht : PositiveTree 14 15 f) : f ≤ 106 := by
  have h := positiveTree_penalty ht (by decide)
  rw [penalty_15] at h
  omega

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsPositiveClimb -/
namespace SigGolfCandidate.Research.PorsPositiveBound

/-- A pending hash before its positive run of unary folds. -/
inductive PendingTree : Nat → Nat → Nat → Prop
  | leaf : PendingTree 0 1 0
  | merge {h a b l r : Nat} (left : PositiveTree h a l) (right : PositiveTree h b r) :
      PendingTree (h+1) (a+b) (l+r)

theorem PositiveTree.leaves_pos {h k f : Nat} (ht : PositiveTree h k f) : 0 < k := by
  cases ht <;> omega

theorem PendingTree.fold {x k f top : Nat} (ht : PendingTree x k f) (hx : x < top) :
    PositiveTree top k (f+(top-x)) := by
  cases ht with
  | leaf => simpa using PositiveTree.leaf top hx
  | @merge h a b l r left right =>
      have ha := left.leaves_pos
      have hb := right.leaves_pos
      have eh : top-(top-(h+1))-1 = h := by omega
      have hl : PositiveTree (top-(top-(h+1))-1) a l := by simpa [eh] using left
      have hr : PositiveTree (top-(top-(h+1))-1) ((a+b)-a) r := by
        simpa [eh, Nat.add_sub_cancel_left] using right
      have q := PositiveTree.fork top (a+b) (top-(h+1)) a l r (by omega) (by omega)
        (by omega) (by omega) hl hr
      have e : top-(h+1)+l+r = (l+r)+(top-(h+1)) := by omega
      simpa only [e] using q

/-- A subtree waiting on the PORS stack. -/
structure Node where
  height : Nat
  leaves : Nat
  folds : Nat
  tree : PositiveTree height leaves folds

def leafSum (stack : List Node) : Nat := (stack.map Node.leaves).sum
def foldSum (stack : List Node) : Nat := (stack.map Node.folds).sum

/-- Exact positivity condition for `Completeness.climbSegs` read lengths. -/
def PositiveRuns : Nat → List Nat → Nat → Prop
  | x, [], top => x < top
  | x, y :: ys, top => x < y ∧ PositiveRuns (y+1) ys top

/-- A complete leaf climb builds a positive compressed subtree from its popped forest.
The equation accounts for one non-folding height per merge. -/
theorem positiveClimb (stack : List Node) : ∀ (x k f top : Nat), PendingTree x k f →
    PositiveRuns x (stack.map Node.height) top →
    ∃ total, PositiveTree top (k+leafSum stack) total ∧
      total+x+stack.length = f+top+foldSum stack := by
  induction stack with
  | nil =>
      intro x k f top ht hp
      have hx : x < top := hp
      refine ⟨f+(top-x), ?_, ?_⟩
      · simpa [leafSum] using ht.fold hx
      · simp only [List.length_nil, foldSum, List.map_nil, List.sum_nil]
        omega
  | cons node rest ih =>
      intro x k f top ht hp
      have hp' : x < node.height ∧ PositiveRuns (node.height+1) (rest.map Node.height) top := hp
      have hcurrent := ht.fold hp'.1
      have hnext := PendingTree.merge node.tree hcurrent
      obtain ⟨total, htree, heq⟩ := ih (node.height+1) (node.leaves+k)
        (node.folds+(f+(node.height-x))) top hnext hp'.2
      refine ⟨total, ?_, ?_⟩
      · have e : node.leaves+k+leafSum rest = k+leafSum (node::rest) := by
          simp only [leafSum, List.map_cons, List.sum_cons]
          omega
        rwa [e] at htree
      · simp only [List.length_cons, foldSum, List.map_cons, List.sum_cons] at heq ⊢
        omega

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsPositiveTrace -/
namespace SigGolfCandidate.Research.PorsPositiveBound

theorem PositiveRuns.length_lt {x top : Nat} {heights : List Nat}
    (hp : PositiveRuns x heights top) : x+heights.length < top := by
  induction heights generalizing x with
  | nil => simpa [PositiveRuns] using hp
  | cons y ys ih =>
      obtain ⟨hxy, hp⟩ := hp
      have h := ih hp
      simp only [List.length_cons]
      omega

/-- The height-only abstraction of a complete positive PORS schedule. Each nonlast
leaf pops a prefix then pushes its result; the last leaf consumes the entire stack. -/
inductive PositiveTrace : List Nat → Nat → Nat → Nat → Prop
  | last (heights : List Nat) (top : Nat) (hp : PositiveRuns 0 heights top) :
      PositiveTrace heights 1 top (top-heights.length)
  | next (lo hi : List Nat) (t n top f : Nat) (hp : PositiveRuns 0 lo t)
      (tail : PositiveTrace (t::hi) n top f) :
      PositiveTrace (lo++hi) (n+1) top ((t-lo.length)+f)

theorem positiveTrace_tree {heights : List Nat} {n top f : Nat}
    (ht : PositiveTrace heights n top f) : ∀ stack : List Node,
    stack.map Node.height = heights →
    PositiveTree top (n+leafSum stack) (f+foldSum stack) := by
  induction ht with
  | last heights top hp =>
      intro stack hmap
      have hp' : PositiveRuns 0 (stack.map Node.height) top := by simpa [hmap] using hp
      obtain ⟨total, htree, heq⟩ := positiveClimb stack 0 1 0 top PendingTree.leaf hp'
      have hlen : stack.length = heights.length := by
        have h := congrArg List.length hmap
        simpa only [List.length_map] using h
      have hbound := hp.length_lt
      have e : total = top-heights.length+foldSum stack := by omega
      simpa only [e] using htree
  | next lo hi t n top f hp tail ih =>
      intro stack hmap
      obtain ⟨low, high, hs, hl, hh⟩ := List.map_eq_append_iff.mp hmap
      subst stack
      have hp' : PositiveRuns 0 (low.map Node.height) t := by simpa [hl] using hp
      obtain ⟨total, htree, heq⟩ := positiveClimb low 0 1 0 t PendingTree.leaf hp'
      let node : Node := ⟨t, 1+leafSum low, total, htree⟩
      have hmap' : (node::high).map Node.height = t::hi := by
        simp only [List.map_cons, node, hh]
      have hresult := ih (node::high) hmap'
      have hlen : low.length = lo.length := by
        have h := congrArg List.length hl
        simpa only [List.length_map] using h
      have hbound := hp.length_lt
      have etotal : total = t-lo.length+foldSum low := by omega
      have eleaves : n+leafSum (node::high) = (n+1)+leafSum (low++high) := by
        simp only [leafSum, List.map_cons, List.map_append, List.sum_cons, List.sum_append, node]
        omega
      have efolds : f+foldSum (node::high) = (t-lo.length+f)+foldSum (low++high) := by
        simp only [foldSum] at etotal
        simp only [foldSum, List.map_cons, List.map_append, List.sum_cons, List.sum_append, node]
        omega
      rwa [eleaves, efolds] at hresult

theorem positiveTrace_15_14 {f : Nat} (ht : PositiveTrace [] 15 14 f) : f ≤ 106 := by
  have h := positiveTrace_tree ht [] rfl
  simp only [leafSum, foldSum, List.map_nil, List.sum_nil, Nat.add_zero] at h
  exact positiveTree_14_15 h

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsPositiveSchedule -/
namespace SigGolfCandidate.Research.PorsPositiveBound

open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness

def readSum (ss : List ScheduleSegment) : Nat := (ss.map (·.reads.length)).sum

theorem climbSegs_positive (v x top : Nat) (L : List Nat)
    (hp : ∀ s ∈ climbSegs v x L top, 0 < s.reads.length) :
    PositiveRuns x L top := by
  induction L generalizing x with
  | nil =>
      have h := hp ⟨false, decide (anc v x % 2 = 1), sibs v x (top-x)⟩ (by simp [climbSegs])
      simpa [PositiveRuns, sibs] using h
  | cons y L ih =>
      have h := hp ⟨true, decide (anc v x % 2 = 1), sibs v x (y-x)⟩ (by simp [climbSegs])
      refine ⟨?_, ih (y+1) (fun s hs => hp s (by simp [climbSegs, hs]))⟩
      simpa [sibs] using h

theorem climbSegs_readSum (v x top : Nat) (L : List Nat)
    (hp : PositiveRuns x L top) : readSum (climbSegs v x L top) + x + L.length = top := by
  induction L generalizing x with
  | nil =>
      have hx : x < top := hp
      simp only [climbSegs, readSum, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, sibs, List.length_map, List.length_range', List.length_nil]
      omega
  | cons y L ih =>
      obtain ⟨hxy, hp⟩ := hp
      have h := ih (y+1) hp
      simp only [climbSegs, readSum, List.map_cons, List.sum_cons, sibs,
        List.length_map, List.length_range', List.length_cons] at *
      omega

theorem allSegs_positiveTrace (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight)
    (hL : Pending v L)
    (hp : ∀ s ∈ allSegs (v::rest) L, 0 < s.reads.length) :
    PositiveTrace L (v::rest).length 14 (readSum (allSegs (v::rest) L)) := by
  induction rest generalizing v L with
  | nil =>
      have hf : L.filter (· < ftsTreeHeight) = L := by
        apply List.filter_eq_self.mpr
        intro y hy
        simpa using (hL.2 y hy).1
      have he : allSegs [v] L = climbSegs v 0 L 14 := by
        change climbSegs v 0 (L.filter (· < ftsTreeHeight)) ftsTreeHeight ++ [] = _
        rw [hf, List.append_nil]
        rfl
      rw [he] at hp ⊢
      have hr := climbSegs_positive v 0 14 L hp
      have hsum := climbSegs_readSum v 0 14 L hr
      have heq : readSum (climbSegs v 0 L 14) = 14-L.length := by omega
      simpa only [List.length_cons, List.length_nil, heq] using PositiveTrace.last L 14 hr
  | cons w rest ih =>
      let t := leafTop v (w::rest)
      let lo := L.filter (· < t)
      let hi := L.filter (t < ·)
      have hsplit : L = lo++hi := pending_split hL hs hb
      have hn : Pending w (t::hi) :=
        (pending_next ((List.pairwise_cons.mp hs).1 w (by simp))
          (hb w (by simp)) (by rfl) hL).1
      have hpre : ∀ s ∈ climbSegs v 0 lo t, 0 < s.reads.length := by
        intro s hm
        apply hp s
        exact List.mem_append_left _ hm
      have htail : ∀ s ∈ allSegs (w::rest) (t::hi), 0 < s.reads.length := by
        intro s hm
        apply hp s
        exact List.mem_append_right _ hm
      have ht := ih w (t::hi) (List.pairwise_cons.mp hs).2
        (fun z hz => hb z (List.mem_cons_of_mem v hz)) hn htail
      have hr := climbSegs_positive v 0 t lo hpre
      have hsum := climbSegs_readSum v 0 t lo hr
      have heq : readSum (climbSegs v 0 lo t) = t-lo.length := by omega
      have htrace := PositiveTrace.next lo hi t (w::rest).length 14
        (readSum (allSegs (w::rest) (t::hi))) hr ht
      rw [← hsplit] at htrace
      simpa only [allSegs, readSum, List.map_append, List.sum_append,
        List.length_cons, ← heq] using htrace

theorem allSegs_positive_readSum (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight)
    (hL : Pending v L)
    (hp : ∀ s ∈ allSegs (v::rest) L, 0 < s.reads.length) :
    readSum (allSegs (v::rest) L) + L.length + rest.length = sumTops (v::rest) := by
  induction rest generalizing v L with
  | nil =>
      have hf : L.filter (· < ftsTreeHeight) = L := by
        apply List.filter_eq_self.mpr
        intro y hy
        simpa using (hL.2 y hy).1
      have he : allSegs [v] L = climbSegs v 0 L 14 := by
        change climbSegs v 0 (L.filter (· < ftsTreeHeight)) ftsTreeHeight ++ [] = _
        rw [hf, List.append_nil]
        rfl
      rw [he] at hp ⊢
      have h := climbSegs_readSum v 0 14 L (climbSegs_positive v 0 14 L hp)
      simpa [sumTops, leafTop, ftsTreeHeight] using h
  | cons w rest ih =>
      let t := leafTop v (w::rest)
      let lo := L.filter (· < t)
      let hi := L.filter (t < ·)
      have hsplit : L = lo++hi := pending_split hL hs hb
      have hn : Pending w (t::hi) :=
        (pending_next ((List.pairwise_cons.mp hs).1 w (by simp))
          (hb w (by simp)) (by rfl) hL).1
      have hpre : ∀ s ∈ climbSegs v 0 lo t, 0 < s.reads.length :=
        fun s hm => hp s (List.mem_append_left _ hm)
      have htail : ∀ s ∈ allSegs (w::rest) (t::hi), 0 < s.reads.length :=
        fun s hm => hp s (List.mem_append_right _ hm)
      have ht := ih w (t::hi) (List.pairwise_cons.mp hs).2
        (fun z hz => hb z (List.mem_cons_of_mem v hz)) hn htail
      have hsum := climbSegs_readSum v 0 t lo (climbSegs_positive v 0 t lo hpre)
      have hlen : L.length = lo.length+hi.length := by rw [hsplit, List.length_append]
      have he : readSum (allSegs (v::w::rest) L) =
          readSum (climbSegs v 0 lo t)+readSum (allSegs (w::rest) (t::hi)) := by
        change readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) = _
        simp only [readSum, List.map_append, List.sum_append]
      rw [he]
      change _ = t + sumTops (w::rest)
      simp only [List.length_cons] at ht ⊢
      omega

theorem schedule_positive_readSum (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves)
    (hp : ∀ s ∈ schedule (sortedLeaves leaves), 0 < s.reads.length) :
    readSum (schedule (sortedLeaves leaves)) ≤ 106 := by
  obtain ⟨hlen, hs, hb⟩ := sortedLeaves_facts leaves hinj
  obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  rw [he] at hlen hs hb
  have hL : Pending v [] := ⟨List.Pairwise.nil, by simp⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (v::rest) [] := by
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ [] hs hb hL rfl
    rw [schedule, he, h.1, List.nil_append]
  rw [hsch] at hp ⊢
  have ht := allSegs_positiveTrace v rest [] hs hb hL hp
  rw [hlen] at ht
  exact positiveTrace_15_14 ht

theorem schedule_positive_octopus (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves)
    (hp : ∀ s ∈ schedule (sortedLeaves leaves), 0 < s.reads.length) :
    octopusSize (sortedLeaves leaves) ≤ 106 := by
  obtain ⟨hlen, hs, hb⟩ := sortedLeaves_facts leaves hinj
  obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  have hbound := schedule_positive_readSum leaves hinj hp
  rw [he] at hlen hs hb
  have hL : Pending v [] := ⟨List.Pairwise.nil, by simp⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (v::rest) [] := by
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ [] hs hb hL rfl
    rw [schedule, he, h.1, List.nil_append]
  rw [hsch] at hp hbound
  have hsum := allSegs_positive_readSum v rest [] hs hb hL hp
  have htop := sumTops_add (v::rest) (by simp) hs
  rw [he, SphincsSecurity.Completeness.Octopus.octopusSize_eq]
  simp only [SphincsSecurity.Completeness.Octopus.octH, List.length_nil, List.length_cons, ftsTreeHeight] at hsum htop ⊢
  omega

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsPositiveAccepted -/
namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open OracleComp

theorem schedule_length_of_injective (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves) : (schedule (sortedLeaves leaves)).length = ftsSegments := by
  obtain ⟨hlen, hs, hb⟩ := sortedLeaves_facts leaves hinj
  obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  rw [he] at hlen hs hb
  have hL : Pending v [] := ⟨List.Pairwise.nil, by simp⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (v::rest) [] := by
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ [] hs hb hL rfl
    rw [schedule, he, h.1, List.nil_append]
  rw [hsch, allSegs_length rest v [] hs hb hL]
  simp only [List.length_nil, List.length_cons, ftsOpenings, ftsSegments] at hlen ⊢
  omega

/-- Every accepting abstract PORS run whose 29 decoded segments all have positive
fold counts uses at most 106 folds, irrespective of hash answers or witness values. -/
theorem recoverRun_positive_folds (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r)
    (hp : ∀ j : Fin ftsSegments, 0 < (fts.segments j).folds.val) : r.folds ≤ 106 := by
  obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hlen := schedule_length_of_injective leaves hadm.1
  have hm := (PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1
  have hpos : ∀ s ∈ schedule (sortedLeaves leaves), 0 < s.reads.length := by
    intro s hs
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hs
    have hj : i < ftsSegments := by omega
    have h := (hm ⟨i, hj⟩).1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
    rw [← he, ← h]
    exact hp ⟨i, hj⟩
  rw [hfolds]
  exact schedule_positive_octopus leaves hadm.1 hpos

theorem recoverRun_large_has_zero (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r)
    (hlarge : 106 < r.folds) : ∃ j : Fin ftsSegments, (fts.segments j).folds.val = 0 := by
  by_contra hnone
  have hp : ∀ j : Fin ftsSegments, 0 < (fts.segments j).folds.val := by
    intro j
    have hn : (fts.segments j).folds.val ≠ 0 := fun h => hnone ⟨j, h⟩
    omega
  have := recoverRun_positive_folds f parameter index leaves fts r hrun hp
  omega

/-- The exact segment formula improves the old universal envelope by one whenever
there is a zero segment, or the all-positive structural bound holds. -/
theorem segment_cost_envelope (F Z cap : Nat) (hcap : 107 ≤ cap) (hF : F ≤ cap)
    (hz : Z = 0 → F ≤ 106) : 16*29 + 17*F - Z ≤ 16*29 + 17*cap - 1 := by
  by_cases h : Z = 0
  · have := hz h; omega
  · omega

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsExactSegmentBudget -/
namespace SigGolfCandidate.Research.PorsPositiveBound

def exactSegmentCost (a : Nat) : Nat := if a = 0 then 15 else 16+17*a
def exactSegmentsCost (as : List Nat) : Nat := (as.map exactSegmentCost).sum
def zeroSegments : List Nat → Nat
  | [] => 0
  | a::as => (if a = 0 then 1 else 0) + zeroSegments as

theorem exactSegmentsCost_cons (a : Nat) (as : List Nat) :
    exactSegmentsCost (a::as) = exactSegmentCost a + exactSegmentsCost as := rfl

theorem exactSegmentsCost_add_zeros (as : List Nat) :
    exactSegmentsCost as + zeroSegments as = 16*as.length + 17*as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [exactSegmentsCost_cons, zeroSegments, exactSegmentCost, List.length_cons,
        List.sum_cons]
      by_cases ha : a = 0
      · subst a; simp only [ite_true]; omega
      · simp only [if_neg ha]; omega

theorem zeroSegments_eq_zero_iff (as : List Nat) :
    zeroSegments as = 0 ↔ ∀ a ∈ as, 0 < a := by
  induction as with
  | nil => simp [zeroSegments]
  | cons a as ih =>
      simp only [zeroSegments, List.mem_cons, forall_eq_or_imp]
      rw [← ih]
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]; omega

/-- The exact PORS segment cost is at least one below the old uniform envelope.
The structural premise concerns all positive segments, not an honest-witness path. -/
theorem exactSegmentsCost_envelope (as : List Nat) (cap : Nat)
    (hlen : as.length = 29) (hcap : 107 ≤ cap) (hfolds : as.sum ≤ cap)
    (hpositive : (∀ a ∈ as, 0 < a) → as.sum ≤ 106) :
    exactSegmentsCost as ≤ 16*29 + 17*cap - 1 := by
  have h := exactSegmentsCost_add_zeros as
  by_cases hz : zeroSegments as = 0
  · have hp := hpositive ((zeroSegments_eq_zero_iff as).mp hz)
    omega
  · omega

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsDecodedCounts -/
namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open OracleComp

theorem climbSegs_readSum_general (v top : Nat) (L : List Nat) : ∀ x,
    L.Pairwise (· < ·) → (∀ y ∈ L, x ≤ y ∧ y < top) → x ≤ top →
    readSum (climbSegs v x L top) + x + L.length = top := by
  induction L with
  | nil =>
      intro x hs hb hx
      simp only [climbSegs, readSum, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, sibs, List.length_map, List.length_range', List.length_nil]
      omega
  | cons y L ih =>
      intro x hs hb hx
      have hy := hb y (by simp)
      have h := ih (y+1) (List.pairwise_cons.mp hs).2
        (fun z hz => ⟨(List.pairwise_cons.mp hs).1 z hz, (hb z (by simp [hz])).2⟩) (by omega)
      simp only [climbSegs, readSum, List.map_cons, List.sum_cons, sibs,
        List.length_map, List.length_range', List.length_cons] at *
      omega

theorem allSegs_readSum_general (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight) (hL : Pending v L) :
    readSum (allSegs (v::rest) L) + L.length + rest.length = sumTops (v::rest) := by
  induction rest generalizing v L with
  | nil =>
      have hf : L.filter (· < ftsTreeHeight) = L := by
        apply List.filter_eq_self.mpr
        intro y hy
        simpa using (hL.2 y hy).1
      have he : allSegs [v] L = climbSegs v 0 L 14 := by
        change climbSegs v 0 (L.filter (· < ftsTreeHeight)) ftsTreeHeight ++ [] = _
        rw [hf, List.append_nil]
        rfl
      rw [he]
      have h := climbSegs_readSum_general v 14 L 0 hL.1
        (fun y hy => ⟨Nat.zero_le y, (hL.2 y hy).1⟩) (by omega)
      simpa [sumTops, leafTop, ftsTreeHeight] using h
  | cons w rest ih =>
      let t := leafTop v (w::rest)
      let lo := L.filter (· < t)
      let hi := L.filter (t < ·)
      have hsplit : L = lo++hi := pending_split hL hs hb
      have hn : Pending w (t::hi) :=
        (pending_next ((List.pairwise_cons.mp hs).1 w (by simp))
          (hb w (by simp)) (by rfl) hL).1
      have ht := ih w (t::hi) (List.pairwise_cons.mp hs).2
        (fun z hz => hb z (List.mem_cons_of_mem v hz)) hn
      have hsum := climbSegs_readSum_general v t lo 0 (hL.1.filter _)
        (fun y hy => ⟨Nat.zero_le y, (mem_filter_lt hy).2⟩) (Nat.zero_le _)
      have hlen : L.length = lo.length+hi.length := by rw [hsplit, List.length_append]
      have he : readSum (allSegs (v::w::rest) L) =
          readSum (climbSegs v 0 lo t)+readSum (allSegs (w::rest) (t::hi)) := by
        change readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) = _
        simp only [readSum, List.map_append, List.sum_append]
      rw [he]
      change _ = t + sumTops (w::rest)
      simp only [List.length_cons] at ht ⊢
      omega

theorem schedule_readSum_eq_octopus (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves) :
    readSum (schedule (sortedLeaves leaves)) = octopusSize (sortedLeaves leaves) := by
  obtain ⟨hlen, hs, hb⟩ := sortedLeaves_facts leaves hinj
  obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  rw [he] at hlen hs hb
  have hL : Pending v [] := ⟨List.Pairwise.nil, by simp⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (v::rest) [] := by
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ [] hs hb hL rfl
    rw [schedule, he, h.1, List.nil_append]
  have hsum := allSegs_readSum_general v rest [] hs hb hL
  have htop := sumTops_add (v::rest) (by simp) hs
  rw [hsch, he, SphincsSecurity.Completeness.Octopus.octopusSize_eq]
  simp only [SphincsSecurity.Completeness.Octopus.octH, List.length_nil, List.length_cons, ftsTreeHeight] at hsum htop ⊢
  omega

def decodedFolds (fts : FtsSignature) : List Nat :=
  List.ofFn fun j : Fin ftsSegments => (fts.segments j).folds.val

theorem recoverRun_decodedFolds_sum (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    (decodedFolds fts).sum = r.folds := by
  obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hlen := schedule_length_of_injective leaves hadm.1
  have hm := (PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1
  have he : decodedFolds fts = (schedule (sortedLeaves leaves)).map (·.reads.length) := by
    apply List.ext_getElem
    · simp only [decodedFolds, List.length_ofFn, List.length_map, hlen]
    · intro i hi hj
      have hilt : i < ftsSegments := by simpa only [decodedFolds, List.length_ofFn] using hi
      have hil : i < (schedule (sortedLeaves leaves)).length := by omega
      have h := (hm ⟨i, hilt⟩).1
      simpa only [decodedFolds, List.getElem_ofFn, List.getElem_map,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some] using h
  rw [he, hfolds]
  exact schedule_readSum_eq_octopus leaves hadm.1

theorem recoverRun_exactSegmentsCost (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    exactSegmentsCost (decodedFolds fts) ≤ 16*29 + 17*117 - 1 := by
  have hsum := recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  apply exactSegmentsCost_envelope (decodedFolds fts) 117
  · simp [decodedFolds, ftsSegments, ftsOpenings]
  · omega
  · rw [hsum, hfolds]; exact hadm.2
  · intro hp
    rw [hsum]
    apply recoverRun_positive_folds f parameter index leaves fts r hrun
    intro j
    exact hp _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsExactMachine -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem seg_step_exact (P : PCtx) (_hP : P.ok) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) (h : DispIn P s0 s x c ptr E folds pend node stk m) :
    (14 < wbyte P.wl ptr % 16 → ∃ u, Steps image m 8 8 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (1 ≤ wbyte P.wl ptr % 16 → wbyte P.wl ptr % 16 ≤ 14 → segT (wbyte P.wl ptr) ≠ E % 2 →
        ∃ u, Steps image m 11 11 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (wbyte P.wl ptr % 16 ≤ 14 → (wbyte P.wl ptr % 16 = 0 ∨ segT (wbyte P.wl ptr) = E % 2) →
        ∃ k u, k = 4 + (if wbyte P.wl ptr % 16 = 0 then 3 else 4) ∧ Steps image m k k u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧ hashInput u = addrFmt (pendInput P node pend) ∧
        (addrFmt (pendInput P node pend)).blocks = 1 ∧
        ∀ ans, (wbyte P.wl ptr % 16 = 0 → TailIn P s0 s x (segV (tsel s) (wbyte P.wl ptr)) 2 (ptr + 8) E folds
            (answerBytes 16 ans) stk (writeHash u ans)) ∧
          (1 ≤ wbyte P.wl ptr % 16 → EntIn P s0 s x (segV (tsel s) (wbyte P.wl ptr)) (segT (wbyte P.wl ptr))
            (wbyte P.wl ptr % 16) ptr E folds (answerBytes 16 ans) stk (writeHash u ans))) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb, heq⟩ := h.bnd
  have hp2 : ptr < 16384 := by omega
  set b := wbyte P.wl ptr with hbdef
  have hbl : b < 256 := wbyte_lt P.wl ptr
  have htb : tbOf s = tbN ∨ tbOf s = tbL := by unfold tbOf; split_ifs <;> simp
  have hc18 : c < 18 := by rcases h.copy with ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> omega
  have cD := dispCheck2_ok c (tbOf s) hc18 (fun hc => by rcases h.copy with ⟨h1, -⟩ | ⟨h1, -, -⟩ <;> [rw [h1]; omega]) htb
  obtain ⟨u1, hu1⟩ := pspec_run cD m h.pc h.pb.known (by simp [dispSpec])
    (dispObl_holds ptr h.fr hp hp8 hp2)
  have htbl : tbOf s < 2 ^ 32 := by rcases htb with e | e <;> rw [e] <;> decide
  have hpc1 : u1.pc = pcOf (slotPc (tsel s) b) := by
    rw [hu1.spc _ rfl]
    show (dispT (tbOf s)).eval m &&& ~~~1#64 = _
    rw [dispT_eval h.pb ptr (tbOf s) h.fr hp hp8 hp2 htbl, even_andNot1' _ (by
      rw [tbOf_tsel]; omega), pcOf, tbOf_tsel, slotPc]
    congr 1; omega
  have pb1 := h.pb.run hu1 (hu1.known (.x20, BitVec.ofNat 64 (tbOf s)) (by simp [dispKnown])) (by simp [dispKeep])
  have hts : tsel s < 2 := by unfold tsel; split_ifs <;> omega
  obtain ⟨cRej, cOk, cPar⟩ := tabCheck1_parts (tsel s) b hts hbl
  have hE1 : u1.getReg .x23 = BitVec.ofNat 64 E := by rw [hu1.keep .x23 (by simp [dispKeep])]; exact h.rE
  have ht : segT b < 2 := by unfold segT; omega
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have ha1 : segA b > 14 := ha
    have hsp : tabSpec (tsel s) b = rejSpec 4 [] := by unfold tabSpec; rw [if_pos ha1]
    obtain ⟨u, hu⟩ := pspec_run (cRej ha1) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by rw [hsp]; simp [rejSpec]) (by simp)
    refine ⟨u, (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, hsp, rejSpec]) (by simp [dispSpec, hsp, rejSpec]),
      hu.ecall (by simp [hsp, rejSpec]), hu.regs (.x5, cw 1) (by simp [hsp, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [hsp, rejSpec])⟩
  · intro h1 h14 hne
    obtain ⟨u, hu⟩ := pspec_run (cPar h1 h14) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by
        intro br hbr; simp only [tabRej, rejSpec, List.mem_singleton] at hbr; subst hbr
        exact (parBr_holds hE1 _ ht true).mpr (by simp [Ne.symm hne])) (by simp)
    refine ⟨u, (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, tabRej, rejSpec])
        (by simp [dispSpec, tabRej, rejSpec]),
      hu.ecall (by simp [tabRej, rejSpec]), hu.regs (.x5, cw 1) (by simp [tabRej, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [tabRej, rejSpec])⟩
  · intro ha hpar
    have ha' : ¬ segA b > 14 := by unfold segA; omega
    have hsp : tabSpec (tsel s) b = ⟨[(.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))),
        (.x12, if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b))], [],
        if b % 16 = 0 then entry0Pc (segV (tsel s) b) + 1 else slotPc (tsel s) b + 4,
        true, if b % 16 = 0 then 3 else 4, if b % 16 = 0 then [] else [parBr (segT b) false], none,
        if b % 16 = 0 then 3 else 4⟩ := by
      unfold tabSpec; rw [if_neg ha']; rfl
    obtain ⟨u, hu⟩ := pspec_run (cOk (by unfold segA; omega)) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by
        rw [hsp]; intro br hbr
        by_cases h0 : b % 16 = 0
        · simp [h0] at hbr
        · simp only [if_neg h0, List.mem_singleton] at hbr; subst hbr
          exact (parBr_holds hE1 _ ht false).mpr (by
            rcases hpar with e | e
            · exact absurd e h0
            · simp [e])) (by simp)
    have pb := pb1.run hu (by rw [hu.keep .x20 (by simp [tabKeep])]; exact pb1.x20) (by simp [tabKeep])
    have hK := hu.known
    have hkeep1 := hu1.keep
    have hkeep := hu.keep
    have r10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr pend stk.length) := by
      rw [hkeep .x10 (by simp [tabKeep]), hkeep1 .x10 (by simp [dispKeep])]; exact h.a0
    have r11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK (.x11, 64) (by simp [gkP])
    have r15 : u.getReg .x15 = BitVec.ofNat 64 (stkReg stk.length) := by
      rw [hkeep .x15 (by simp [tabKeep]), hkeep1 .x15 (by simp [dispKeep])]; exact h.rS
    have mem : ∀ A, u.getMem A = m.getMem A := by
      intro A; rw [hu.mem, hsp]; show u1.getMem A = _; rw [hu1.mem]; rfl
    have hpm : PendMem P node stk.length u pend := by
      cases pend <;> simpa [PendMem, mem] using h.pmem
    obtain ⟨hin, hbl1⟩ := pend_hashInput pb pend node stk.length r10 r11 hpm
    have r12 : u.getReg .x12 = (if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b)).eval u1 :=
      hu.regs (.x12, if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b)) (by rw [hsp]; simp)
    have hdest : u.getReg .x12 = BitVec.ofNat 64 (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length
        else 0x1E0 + 16 * segT b) := by
      rw [r12]
      split_ifs with h0
      · unfold destE destOf
        have r15' : u1.getReg .x15 = BitVec.ofNat 64 (stkReg stk.length) := by
          rw [hkeep1 .x15 (by simp [dispKeep])]; exact h.rS
        split_ifs <;> simp [Rv.E.eval, BinOp.eval, cw, r15', BitVec.ofNat_add_ofNat, stkReg, stkOf', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · rfl
    have hdl : stk.length ≤ 14 := by omega
    have hV1 : segV (tsel s) b = 1 → stk.length < 14 := by
      intro hv
      by_cases h14 : s = 14
      · subst h14; unfold segV tsel at hv; split_ifs at hv <;> simp_all
      · omega
    have hpa : pendAddr pend stk.length % 8 = 0 ∧ pendAddr pend stk.length + 64 ≤ 0x800 := by
      cases pend with
      | leaf => simp [pendAddr]
      | merge => simp only [pendAddr, PSB]; omega
    have hda : (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) % 8 = 0 ∧
        (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) + 32 ≤ 0x800 := by
      have ht : segT b < 2 := by unfold segT; omega
      split_ifs
      · unfold destOf stkOf' EMPTY; split_ifs <;> omega
      · omega
    have hsafe : safeDestP (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) = true := by
      split_ifs
      · exact safe_dest _ _ hdl hV1
      · exact safe_nb _ (by unfold segT; omega)
    have hargs : hashArgsB (pendAddr pend stk.length) (64 * (0 + 1))
        (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) = true := by
      simp only [hashArgsB, MEMORY_BYTES, Bool.and_eq_true, decide_eq_true_eq, Nat.reducePow,
        Nat.reduceMul, Nat.reduceAdd]
      refine ⟨⟨⟨⟨hpa.1, ?_, trivial⟩, decide_eq_true ?_⟩, decide_eq_true (And.intro ?_ hda.1)⟩, decide_eq_true ?_⟩ <;> omega
    refine ⟨4 + (if b % 16 = 0 then 3 else 4), u, rfl,
      (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, hsp]) (by simp [dispSpec, hsp]),
      hu.ecall (by simp [hsp]), pb.reg (by simp [gkP, baseK]),
      hashArgs_ofNat _ _ _ _ r10 r11 hdest (by omega) (by omega) (by omega) hargs,
      hin, hbl1, fun ans => ⟨fun h0 => ?_, fun h1 => ?_⟩⟩
    · -- a = 0: the pending hash went straight to the destination
      have hd0 : u.getReg .x12 = BitVec.ofNat 64 (destOf (segV (tsel s) b) stk.length) := by
        rw [hdest, if_pos h0]
      have hdl' : destOf (segV (tsel s) b) stk.length + 24 < 2 ^ 64 := by
        unfold destOf stkOf' EMPTY; split_ifs <;> omega
      refine ⟨pb.hash ans _ hd0 (safe_dest _ _ hdl hV1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        (writeHash_at0 _ ans _ hd0 hdl').trans (vw0_answer ans).symm,
        (writeHash_at8 _ ans _ hd0 hdl').trans (vw1_answer ans).symm, by simp,
        by rw [writeHash_getReg]; exact hd0, ?_, h.hE, h.hx,
        by decide, segV_lt _ _, hV1⟩
      · rw [writeHash_pc, hu.pc (by rw [hsp]), hsp]
        simp only [if_pos h0, pcOf_add4, tailPc, if_true]
      · rw [writeHash_getReg, hu.regs (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x14 (by simp [dispKeep]), h.fr, h0]
        rw [BitVec.ofNat_add_ofNat]; congr 1; omega
      · rw [writeHash_getReg, hkeep .x23 (by simp [tabKeep]), hkeep1 .x23 (by simp [dispKeep])]; exact h.rE
      · rw [writeHash_getReg]; exact pb.reg (by simp [gkP, baseK, FLIM])
      · rw [writeHash_getReg]; exact r15
      · apply StackOK.hash _ ans _ hd0 (by unfold destOf stkOf' EMPTY; split_ifs <;> omega)
          (stack_dest _ _ hdl) hdl
        apply h.stack.frame; intro i hi; simp [mem]
      · rw [writeHash_getReg, hkeep (xReg s) (by unfold xReg; split_ifs <;> simp [tabKeep]),
          hkeep1 (xReg s) (by unfold xReg; split_ifs <;> simp [dispKeep])]; exact h.cur
      · rw [writeHash_getReg, hkeep .x24 (by simp [tabKeep])]
        rcases h.copy with ⟨hc, -⟩ | ⟨hc, -, -⟩
        · rw [hu1.regs (.x24, cw (0x1000 + 4 * (dispPc c + 4))) (by simp [dispSpec, hc, hs])]
          simp [cw, Rv.E.eval, lnkOf, hc, dispPc, hs]
        · rw [hkeep1 .x24 (by simp [dispKeep, show ¬ c < 15 by omega])]; exact h.lnk hc
      · refine ⟨hs, hd, by omega, by omega, by omega, by omega, by omega⟩
    · -- a ≥ 1: the pending hash went into NB slot `t`
      have hdn : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * segT b) := by
        rw [hdest, if_neg (by omega)]
      refine ⟨pb.hash ans _ hdn (safe_nb _ ht), ?_, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        (writeHash_at0 _ ans _ hdn (by omega)).trans (vw0_answer ans).symm, ?_, by simp, h.bnd, h.hE, h.hx,
        ⟨h1, by omega⟩, ht, segV_lt _ _, hV1⟩
      · rw [writeHash_pc, hu.pc (by rw [hsp]), hsp]
        simp only [if_neg (show ¬ b % 16 = 0 by omega), pcOf_add4]
        rfl
      · rw [writeHash_getReg, hu.regs (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x14 (by simp [dispKeep]), h.fr]
        rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]
      · rw [writeHash_getReg, hkeep .x23 (by simp [tabKeep]), hkeep1 .x23 (by simp [dispKeep])]; exact h.rE
      · rw [writeHash_getReg]; exact pb.reg (by simp [gkP, baseK, FLIM])
      · rw [writeHash_getReg]; exact r15
      · apply StackOK.hash _ ans _ hdn (by omega) (fun i hi => by unfold blkQ blkL PSB; omega) hdl
        apply h.stack.frame; intro i hi; simp [mem]
      · rw [writeHash_getReg, hkeep (xReg s) (by unfold xReg; split_ifs <;> simp [tabKeep]),
          hkeep1 (xReg s) (by unfold xReg; split_ifs <;> simp [dispKeep])]; exact h.cur
      · rw [writeHash_getReg, hkeep .x24 (by simp [tabKeep])]
        rcases h.copy with ⟨hc, -⟩ | ⟨hc, -, -⟩
        · rw [hu1.regs (.x24, cw (0x1000 + 4 * (dispPc c + 4))) (by simp [dispSpec, hc, hs])]
          simp [cw, Rv.E.eval, lnkOf, hc, dispPc, hs]
        · rw [hkeep1 .x24 (by simp [dispKeep, show ¬ c < 15 by omega])]; exact h.lnk hc
      · rw [show 0x1E8 + 16 * segT b = 0x1E0 + 16 * segT b + 8 by omega]
        exact (writeHash_at8 _ ans _ hdn (by omega)).trans (vw1_answer ans).symm


/-! ## Entry tails and ladder positions -/


theorem segment_good_exact (P : PCtx) (hP : P.ok) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) (h : DispIn P s0 s x c ptr E folds pend node stk m)
    (K : Option (Nat × Nat × Nat × Val × Bool) → OracleComp HashSpec Obs) (hnone : K none = pure (false, 0))
    (N C A : Nat) (NT CT : Nat → Nat) (AT : Nat → Nat → Nat)
    (hK : ∀ (a V c' E' : Nat) (node' : Val) (u : MachineState), a ≤ 14 →
      V = segV (tsel s) (wbyte P.wl ptr) → a = wbyte P.wl ptr % 16 →
      TailIn P s0 s x V c' (ptr + 8 + 16 * a) E' (folds + a) node' stk u →
      GoodQ u (NT V) (CT V) (folds + a ≤ 117) (AT V (folds + a))
        (K (some (ptr + 8 + 16 * a, E', folds + a, node', decide (wbyte P.wl ptr / 16 % 2 = 1)))))
    (hN : ∀ V, V < 3 → 18 + 17 * 14 + NT V ≤ N) (hC : ∀ V a, V < 3 → a ≤ 14 → 18 + 17 * a + CT V ≤ C)
    (hA : ∀ V a, V < 3 → a ≤ 14 → a = wbyte P.wl ptr % 16 → folds + a ≤ 117 →
      SigGolfCandidate.Research.PorsPositiveBound.exactSegmentCost a + AT V (folds + a) ≤ A)
    (h9 : 13 ≤ N ∧ 13 ≤ C ∧ 13 ≤ A) :
    GoodQ m N C (folds ≤ 117) A (cc (Ref.segment P.idx P.wl ptr E folds pend node) K) := by
  obtain ⟨hrej, hpar, hacc⟩ := seg_step_exact P hP s0 s x c ptr E folds pend node stk m h
  unfold Ref.segment
  simp only []
  set b := wbyte P.wl ptr with hb
  by_cases ha : b % 16 > porsH
  · rw [if_pos ha, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej (by unfold porsH at ha; omega)
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  rw [if_neg ha]
  have ha14 : b % 16 ≤ 14 := by unfold porsH at ha; omega
  by_cases hp : 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2
  · rw [if_pos hp, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hpar (by omega) ha14 hp.2
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hp, cc_bind, pendingHash_eq]
    have hpar' : b % 16 = 0 ∨ segT b = E % 2 := by unfold segT; omega
    obtain ⟨k, u, hkeq, hst, hf, h5, hv, hin, hbl, hpost⟩ := hacc ha14 hpar'
    have hk : k ≤ 8 := by rw [hkeq]; split_ifs <;> omega
    have hVl := segV_lt (tsel s) b
    set a := b % 16 with hadef
    set V := segV (tsel s) b with hV
    -- after the pending hash
    have H : ∀ ans, GoodQ (writeHash u ans) (NT V + 17 * 14 + 2) (CT V + 17 * a) (folds + a ≤ 117) (AT V (folds + a) + 17 * a)
        ((fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1))))
          (answerBytes 16 ans)) := by
      intro ans
      simp only []
      by_cases ha0 : a = 0
      · rw [ha0, segFolds_eq]
        simp only [List.range_zero, List.foldlM_nil, cc_pure]
        have hT := (hpost ans).1 ha0
        have := hK 0 V 2 E (answerBytes 16 ans) (writeHash u ans) (by omega) rfl (by omega) (by simpa using hT)
        simp only [Nat.mul_zero, Nat.add_zero] at this
        simp only [ha0, Nat.mul_zero, Nat.add_zero]
        exact this.mono (by omega) (by omega) (fun q => ⟨by omega, by omega⟩)
      · have hE := (hpost ans).2 (by omega)
        obtain ⟨u2, hst2, hP2⟩ := ent_step P s0 s x V (segT b) a ptr E folds (answerBytes 16 ans) stk _ hE
        rw [segFolds_eq, List.range_eq_range']
        have := folds_good P s0 s x V a ptr folds stk
          (fun p => match p with
            | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1))))
          (NT V) (CT V) (AT V (folds + a)) (folds + a ≤ 117)
          (fun t node' E' u' hT => hK a V t E' node' u' ha14 rfl rfl hT) a 0 (segT b) E (answerBytes 16 ans)
          u2 (by omega) hP2 (by rcases hpar' with e | e <;> [omega; exact e])
        refine GoodQ.steps' hst2 this (by omega) (by omega) (fun q => ⟨by omega, by omega⟩)
    have h3 := GoodQ.hash (x := pendInput P node pend)
      (K := fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) hf h5 hv hin H
    rw [hbl] at h3
    have e2 : (fun node' => cc (segFolds P.idx P.wl ptr a node' E >>= fun x =>
          match x with
          | (node, E) => pure (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) K) =
        (fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) := by
      funext v; rw [cc_bind]; congr 1; funext p; obtain ⟨n1, e1⟩ := p; simp only [cc_pure]
    rw [e2]
    exact GoodQ.steps' hst h3 (by have := hN V hVl; omega) (by have := hC V a hVl ha14; omega)
      (fun q => ⟨by omega, by
        have hbudget := hA V a hVl ha14 rfl q
        unfold SigGolfCandidate.Research.PorsPositiveBound.exactSegmentCost at hbudget
        change k = 4 + (if a = 0 then 3 else 4) at hkeq
        by_cases hz : a = 0
        · simp only [if_pos hz] at hbudget hkeq; omega
        · simp only [if_neg hz] at hbudget hkeq; omega⟩)

end SigGolfCandidate.Verify

/-! ## PorsExactComposition -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp
open SigGolfCandidate.Research.PorsPositiveBound

def decodedFold (wl : List Byte) (j : Nat) : Nat := wbyte wl (Equiv.segPtr wl j) % 16
def decodedCostFrom (wl : List Byte) (j n : Nat) : Nat :=
  ((List.range' j n).map fun k => exactSegmentCost (decodedFold wl k)).sum
def decodedCostRem (wl : List Byte) (j : Nat) : Nat := decodedCostFrom wl j (29-j)

theorem decodedCostFrom_succ (wl : List Byte) (j n : Nat) :
    decodedCostFrom wl j (n+1) = exactSegmentCost (decodedFold wl j) + decodedCostFrom wl (j+1) n := by
  simp [decodedCostFrom, List.range'_succ]

theorem decodedCostRem_succ (wl : List Byte) (j : Nat) (hj : j < 29) :
    decodedCostRem wl j = exactSegmentCost (decodedFold wl j) + decodedCostRem wl (j+1) := by
  unfold decodedCostRem
  have h : 29-j = (29-(j+1))+1 := by omega
  rw [h, decodedCostFrom_succ]

theorem exactSegmentCost_ge (a : Nat) : 15 ≤ exactSegmentCost a := by
  unfold exactSegmentCost; split_ifs <;> omega

theorem decodedCostRem_ge (wl : List Byte) (j : Nat) (hj : j < 29) :
    15 ≤ decodedCostRem wl j := by
  rw [decodedCostRem_succ wl j hj]
  have := exactSegmentCost_ge (decodedFold wl j)
  omega

/-- A witness-dependent accepting budget. It retains every zero-segment saving
and the actual remaining decoded folds, independent of the final fold cap. -/
def Aexact (wl : List Byte) (s d : Nat) : Nat :=
  decodedCostRem wl (2*s-d) + 6*(d+14-s) + 4*(14-s) + lrest s + 11 + layC
def AexactPF (wl : List Byte) (s d : Nat) : Nat :=
  if s = 14 then 11 + layC else 4+leafCost (s+1)+Aexact wl (s+1) (d+1)
def AexactM (wl : List Byte) (s d : Nat) : Nat :=
  if d = 0 then 6 else 6+Aexact wl s (d-1)

theorem exact_seg_budget (wl : List Byte) (s d : Nat) (hs : s < 15) (hd : d ≤ s) :
    (∀ a, a = decodedFold wl (2*s-d) → exactSegmentCost a + AexactM wl s d ≤ Aexact wl s d) ∧
    (∀ a, a = decodedFold wl (2*s-d) → exactSegmentCost a + AexactPF wl s d ≤ Aexact wl s d) ∧
    13 ≤ Aexact wl s d := by
  have hj : 2*s-d < 29 := by omega
  have hrec := decodedCostRem_succ wl (2*s-d) hj
  have hge := decodedCostRem_ge wl (2*s-d) hj
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    subst a
    by_cases hz : d = 0
    · simp only [AexactM, if_pos hz, Aexact]
      omega
    · have he : 2*s-(d-1) = 2*s-d+1 := by omega
      simp only [AexactM, if_neg hz, Aexact, he]
      omega
  · intro a ha
    subst a
    by_cases h14 : s = 14
    · simp only [AexactPF, if_pos h14, Aexact]
      omega
    · have he : 2*(s+1)-(d+1) = 2*s-d+1 := by omega
      have hl := lrest_succ s (by omega)
      simp only [AexactPF, if_neg h14, Aexact, he]
      omega
  · unfold Aexact; omega

theorem decoded_ptr_next (wl : List Byte) (ptr j a : Nat)
    (hp : ptr = Equiv.segPtr wl j) (ha : a = wbyte wl ptr % 16) :
    ptr+8+16*a = Equiv.segPtr wl (j+1) := by
  rw [Equiv.segPtr, ← hp, ← ha]

theorem segLoop_good_exact (P : PCtx) (hP : P.ok) (s0 : MachineState) (s x : Nat)
    (K : Option (Nat × Nat × Nat × Val × List (Val × Nat)) → OracleComp HashSpec Obs)
    (hnone : K none = pure (false, 0))
    (hK : ∀ ptr E folds node stk c u, TailIn P s0 s x (if s = 14 then 2 else 1) c ptr E folds node stk u →
      ptr = Equiv.segPtr P.wl (2*s-stk.length+1) →
      GoodQ u (NtailPF s stk.length) (CtailPF s stk.length) (folds ≤ 117) (AexactPF P.wl s stk.length)
        (K (some (ptr, E, folds, node, stk)))) :
    ∀ stk ptr E folds pend node c m, DispIn P s0 s x c ptr E folds pend node stk m →
      ptr = Equiv.segPtr P.wl (2*s-stk.length) →
      GoodQ m (Nseg s stk.length) (Cseg s stk.length) (folds ≤ 117) (Aexact P.wl s stk.length)
        (cc (segLoop P.idx P.wl ptr E folds pend node stk) K) := by
  intro stk
  induction stk with
  | nil =>
    intro ptr E folds pend node c m h hptr
    obtain ⟨hs, hd, -⟩ := h.bnd
    simp only [List.length_nil, List.length_cons] at hd hptr
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s 0 hs (by omega)
    obtain ⟨bAMX, bAPFX, b13X⟩ := exact_seg_budget P.wl s _ hs hd
    simp only [segLoop, cc_bind]
    refine segment_good_exact P hP s0 s x c ptr E folds pend node [] m h _ (by simp [hnone])
      (Nseg s 0) (Cseg s 0) (Aexact P.wl s 0)
      (fun V => if V = 0 then NtailM s 0 else NtailPF s 0) (fun V => if V = 0 then CtailM s 0 else CtailPF s 0)
      (fun V F => if V = 0 then AexactM P.wl s 0 else AexactPF P.wl s 0) ?_
      (fun V _ => by split_ifs <;> omega) (fun V a _ ha => by split_ifs <;> [exact bM a ha; exact bPF a ha])
      (fun V a _ ha haw hF => by
        have he : a = decodedFold P.wl (2*s-0) := by unfold decodedFold; rw [← hptr]; exact haw
        split_ifs <;> [exact bAMX a he; exact bAPFX a he])
      ⟨(b9 folds).1, (b9 folds).2.1, b13X⟩
    intro a V c' E' node' u ha hV haw hT
    have hpnext := decoded_ptr_next P.wl ptr (2*s-0) a hptr haw
    by_cases hV0 : V = 0
    · -- merge on an empty stack: reject
      have hm := segV_M _ _ (hV ▸ hV0)
      simp only [hV0, if_true, hm, decide_true, if_true, cc_pure, hnone]
      rw [hV0] at hT
      obtain ⟨u2, hst2, hf2, h52, h102⟩ := (tailM_step P s0 s x c' _ E' _ node' [] u hT).2.1 rfl
      exact GoodQ.steps' hst2 (GoodQ.reject (Q := folds + a ≤ 117) (A := 0) hf2 h52 h102)
        (by unfold NtailM CtailM; simp) (by unfold CtailM; simp) (fun q => ⟨q, by unfold AexactM; simp⟩)
    · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ hV0)
      simp only [hV0, if_false, hm, decide_false, Bool.false_eq_true, cc_pure]
      rw [hV, hVe] at hT
      have hh := hK (ptr + 8 + 16 * a) E' (folds + a) node' [] c' u hT hpnext
      exact hh
  | cons e rest ih =>
    intro ptr E folds pend node c m h hptr
    obtain ⟨pnode, Q⟩ := e
    obtain ⟨hs, hd, -⟩ := h.bnd
    simp only [List.length_nil, List.length_cons] at hd hptr
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s (rest.length + 1) hs (by simpa using hd)
    obtain ⟨bAMX, bAPFX, b13X⟩ := exact_seg_budget P.wl s _ hs hd
    simp only [segLoop, cc_bind]
    refine segment_good_exact P hP s0 s x c ptr E folds pend node _ m h _ (by simp [hnone])
      (Nseg s (rest.length + 1)) (Cseg s (rest.length + 1)) (Aexact P.wl s (rest.length + 1))
      (fun V => if V = 0 then NtailM s (rest.length + 1) else NtailPF s (rest.length + 1))
      (fun V => if V = 0 then CtailM s (rest.length + 1) else CtailPF s (rest.length + 1))
      (fun V F => if V = 0 then AexactM P.wl s (rest.length + 1) else AexactPF P.wl s (rest.length + 1)) ?_
      (fun V _ => by split_ifs <;> omega) (fun V a _ ha => by split_ifs <;> [exact bM a ha; exact bPF a ha])
      (fun V a _ ha haw hF => by
        have he : a = decodedFold P.wl (2*s-(rest.length+1)) := by unfold decodedFold; rw [← hptr]; exact haw
        split_ifs <;> [exact bAMX a he; exact bAPFX a he])
      ⟨(b9 folds).1, (b9 folds).2.1, b13X⟩
    intro a V c' E' node' u ha hV haw hT
    have hpnext := decoded_ptr_next P.wl ptr (2*s-(rest.length+1)) a hptr haw
    by_cases hV0 : V = 0
    · have hm := segV_M _ _ (hV ▸ hV0)
      simp only [hV0, if_true, hm, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [hV0] at hT
      have tM := tailM_step P s0 s x c' _ E' _ node' ((pnode, Q) :: rest) u hT
      by_cases hQ : Q = E'
      · subst hQ
        simp only [ne_eq, not_true_eq_false, if_false]
        obtain ⟨u2, hst2, hD⟩ := tM.2.2 pnode rest rfl
        have hpnext' : ptr+8+16*a = Equiv.segPtr P.wl (2*s-rest.length) := by
          convert hpnext using 2 <;> omega
        have := ih _ _ _ _ _ _ u2 hD hpnext'
        simp only [NtailM, CtailM, AexactM, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact GoodQ.steps' hst2 this (by simp only [Nseg]; omega) (by omega) (fun q => ⟨q, by omega⟩)
      · simp only [ne_eq, hQ, not_false_eq_true, if_true, cc_pure, hnone]
        obtain ⟨u2, hst2, hf2, h52, h102⟩ := tM.1 pnode Q rest rfl hQ
        exact GoodQ.steps' hst2 (GoodQ.reject (Q := folds + a ≤ 117) (A := 0) hf2 h52 h102)
          (by unfold NtailM CtailM; split_ifs <;> omega) (by unfold CtailM; split_ifs <;> omega)
          (fun q => ⟨q, by unfold AexactM; split_ifs <;> omega⟩)
    · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ hV0)
      simp only [hV0, if_false, hm, decide_false, Bool.not_false, if_true, cc_pure]
      rw [hV, hVe] at hT
      have hh := hK (ptr + 8 + 16 * a) E' (folds + a) node' ((pnode, Q) :: rest) c' u hT hpnext
      exact hh

theorem leaves_good_exact (P : PCtx) (hP : P.ok) (s0 : MachineState)
    (Kr : Option PorsState → OracleComp HashSpec Obs) (hnone : Kr none = pure (false, 0))
    (hKr : ∀ (x c : Nat) (st : PorsState) (u : MachineState),
      TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u →
      st.ptr = Equiv.segPtr P.wl (29-st.stack.length) →
      GoodQ u (11 + layC + layN) (11 + layC) (st.folds ≤ 117) (11 + layC) (Kr (some st))) :
    ∀ n s (st : PorsState) m, s + n = 15 → LeafIn P s0 s st m →
      st.ptr = Equiv.segPtr P.wl (2*s-st.stack.length) →
      GoodQ m (leafCost s + Nseg s st.stack.length) (leafCost s + Cseg s st.stack.length) (st.folds ≤ 117)
        (leafCost s + Aexact P.wl s st.stack.length)
        (cc (porsLeaves P.idx P.v P.wl (List.range' s n) st) Kr) := by
  intro n
  induction n with
  | zero => intro s st m hsn h; have := h.bnd.1; omega
  | succ k ih =>
    intro s st m hsn h hptr
    obtain ⟨hs, hd, -⟩ := h.bnd
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s st.stack.length hs hd
    obtain ⟨hrej, hacc⟩ := pleaf_step P hP s0 s st m h
    rw [List.range'_succ]
    simp only [porsLeaves]
    have hx : (P.v ++ [porsT]).getD (witPi P.wl s / 8 % 16) 0 = leafX P s := rfl
    rw [hx]
    have hl := leafCost_le s
    have h9 := b9 st.folds
    have hAX := (exact_seg_budget P.wl s st.stack.length hs hd).2.2
    by_cases h1 : s ≠ 0 ∧ ¬ st.prev < leafX P s
    · rw [if_pos h1, cc_pure, hnone]
      obtain ⟨u, k', hk', hst, hf, h5, h10⟩ := hrej (Or.inl h1)
      exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 117) (A := 0) hf h5 h10)
        (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    · rw [if_neg h1]
      by_cases h2 : s = porsK - 1 ∧ ¬ leafX P s < porsT
      · rw [if_pos h2, cc_pure, hnone]
        obtain ⟨u, k', hk', hst, hf, h5, h10⟩ := hrej (Or.inr h2)
        exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 117) (A := 0) hf h5 h10)
          (by omega) (by omega) (fun q => ⟨q, by omega⟩)
      · rw [if_neg h2, cc_bind]
        obtain ⟨u, hst, hD⟩ := hacc (fun hc => hc.elim h1 h2)
        rw [leafCost_eq] at hst
        refine GoodQ.steps' hst (segLoop_good_exact P hP s0 s (leafX P s) _ (by simp [hnone]) ?_ st.stack st.ptr
          (porsT ||| leafX P s) st.folds _ st.node s u hD hptr) (by omega) (by omega) (fun q => ⟨q, by omega⟩)
        intro ptr E folds node stk c u' hT hptrT
        simp only []
        by_cases h14 : s = 14
        · subst h14
          have hk0 : k = 0 := by omega
          subst hk0
          simp only [if_true] at hT
          simp only [List.range'_zero, porsK, show ¬ (14 < 15 - 1) by decide, if_false]
          rw [show (porsLeaves P.idx P.v P.wl [] ⟨ptr, leafX P 14, E, folds, node, stk⟩ :
              OracleComp HashSpec (Option PorsState)) = pure (some ⟨ptr, leafX P 14, E, folds, node, stk⟩) from rfl,
            cc_pure]
          have hpT : ptr = Equiv.segPtr P.wl (29-stk.length) := by
            have hdT := hT.bnd.2.1
            convert hptrT using 2 <;> omega
          have := hKr (leafX P 14) c ⟨ptr, leafX P 14, E, folds, node, stk⟩ u' hT hpT
          simp only [NtailPF, CtailPF, AexactPF, if_true]
          exact this
        · simp only [h14, if_false] at hT
          have hs14 : s < 14 := by omega
          obtain ⟨u2, hst2, hL⟩ := tailP_step P s0 s (leafX P s) c ptr E folds node stk u' hs14 hT
          simp only [porsK, show s < 15 - 1 by omega, if_true]
          have hpL : ptr = Equiv.segPtr P.wl (2*(s+1)-((node, E ^^^ 1)::stk).length) := by
            have hdT := hT.bnd.2.1
            simp only [List.length_cons]
            convert hptrT using 2 <;> omega
          have := ih (s + 1) ⟨ptr, leafX P s, E, folds, node, (node, E ^^^ 1) :: stk⟩ u2 (by omega) hL hpL
          simp only [List.length_cons] at this
          simp only [NtailPF, CtailPF, AexactPF, h14, if_false]
          refine GoodQ.steps' hst2 this (by unfold Nseg; omega) (by omega) (fun q => ⟨q, by omega⟩)


end SigGolfCandidate.Verify

/-! ## PorsExactTop -/
set_option maxRecDepth 20000
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem pors_good_decoded (P : PCtx) (hP : P.ok) (s0 : MachineState)
    (h : LeafIn P s0 0 ⟨wStream, 0, 0, 0, [], []⟩ s0) :
    GoodQ s0 (leafCost 0 + Nseg 0 0) (leafCost 0 + Cseg 0 0) True (leafCost 0 + Aexact P.wl 0 0)
      (cc (porsRoot P.idx P.v P.wl) (Klay P)) := by
  have hr : ∀ (x c : Nat) (st : PorsState) (u : MachineState),
      TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u →
      GoodQ u (11 + layC + layN) (11 + layC) (st.folds ≤ 117) (11 + layC) (Kr P (some st)) :=
    fun x c st u hT => root_good P hP s0 x c st u hT
  have hg0 := leaves_good_exact P hP s0 (Kr P) (Kr_none P) (fun x c st u hT _ => hr x c st u hT)
  have hg := hg0 15 0 ⟨wStream, 0, 0, 0, [], []⟩ s0 (by rfl) h rfl
  have e : cc (porsRoot P.idx P.v P.wl) (Klay P) =
      cc (porsLeaves P.idx P.v P.wl (List.range' 0 15) ⟨wStream, 0, 0, 0, [], []⟩) (Kr P) := by
    unfold porsRoot
    rw [cc_bind, List.range_eq_range']
    rfl
  rw [e]
  have l0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).stack.length = 0 := rfl
  have f0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).folds = 0 := rfl
  rw [l0] at hg
  exact hg.mono (le_refl _) (le_refl _) (fun _ => ⟨trivial, le_refl _⟩)

def cycleBoundDecoded (wl : List Byte) : Nat := 450 + layC + decodedCostRem wl 0

theorem exact_cost_vals (wl : List Byte) :
    leafCost 0 + Aexact wl 0 0 = 318 + layC + decodedCostRem wl 0 := by
  have h0 : leafCost 0 = 10 := rfl
  simp only [Aexact, lrest_0, h0, Nat.mul_zero, Nat.sub_self]
  omega

theorem main_good_decoded (ml pkl wl : List Byte) (hml : ml.length = 32) (hpk : pkl.length = 16)
    (hwl : wl.length = 16384) (s : MachineState) (hs : InitOK ml pkl wl s) :
    GoodQ s fuelBound cycleBoundAll True (cycleBoundDecoded wl) (cc (verifyList ml pkl wl) Kb) := by
  unfold verifyList
  obtain ⟨hrej, hacc⟩ := start_step ml pkl wl hml hwl s hs
  have hL := layC_val
  obtain ⟨c1, -, c3⟩ := cost_vals
  have c2 := exact_cost_vals wl
  cases hc : countersOk wl
  · simp only [Bool.not_false, if_true, cc_pure, Kb]
    obtain ⟨t, hst, hf, h5, h10⟩ := hrej hc
    exact GoodQ.steps' hst (GoodQ.reject (Q := True) (A := 0) hf h5 h10)
      (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega) (fun q => ⟨q, by unfold cycleBoundDecoded; omega⟩)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := hacc hc
    unfold digest
    rw [cc_bind, cc_bind]
    simp only [cc_pure]
    have H : ∀ a, GoodQ (writeHash t a) (100 + (leafCost 0 + Nseg 0 0)) (100 + (leafCost 0 + Cseg 0 0)) True
        (100 + (leafCost 0 + Aexact wl 0 0))
        (cc (do
          let r ← porsRoot (idxOf a.toNat) (leavesOf a.toNat) wl
          match r with
          | none => pure false
          | some M => do
            let o ← verifyLayers wl (idxOf a.toNat) nLayers M
            match o with
            | none => pure false
            | some root => pure (root == pkl)) Kb) := by
      intro a
      rw [cc_bind]
      set P : PCtx := ⟨wl, pkl, a⟩
      obtain ⟨u, hsu, hS0, hLI⟩ := setup_step P ⟨hwl, hpk⟩ _ (hpost a)
      have := pors_good_decoded P ⟨hwl, hpk⟩ u hLI
      dsimp only [P] at this
      exact (GoodQ.steps hsu this).mono (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; omega
    have h3 := GoodQ.hashH (x := digestInput (witRho wl) ml) hf h5 hv hin H
    rw [fmt_digestInput_words _ _ hrho hml, blocks_qT] at h3
    have hN : layN = 25009 := rfl
    exact GoodQ.steps' hst h3 (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega)
      (fun q => ⟨q, by unfold cycleBoundDecoded; omega⟩)

end SigGolfCandidate.Verify

/-! ## PorsRefCostEnvelope -/
namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.Legacy SigGolfCandidate.Equiv SigGolfCandidate.Verify
open OracleComp

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem decodedCostRem_eq (wl : List Byte) :
    decodedCostRem wl 0 = exactSegmentsCost (decodedFolds (witFts wl)) := by
  unfold decodedCostRem decodedCostFrom exactSegmentsCost
  congr 1

/-- Every accepted reference PORS computation has exact segment cost below the
former uniform envelope. This statement is independent of sampled executions. -/
theorem porsRoot_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (index : Index) (wl : List Byte) (hl : wl.length = 16384)
    (leaves : IndexGroup → FtsLeaf) (node : Ref.Val)
    (hrun : evalWithAnswerFn hash
      (Ref.porsRoot index (List.ofFn fun r => (leaves r).val) wl) = some node) :
    decodedCostRem wl 0 ≤ 16*29 + 17*117 - 1 := by
  let f : QueryImpl SphincsSecurity.HashSpec Id := fun q => hash (fmtQ q)
  have he := congrArg (evalWithAnswerFn hash) (porsRoot_eq index wl hl leaves)
  rw [hrun, evalWithAnswerFn_map, Final.evalWithAnswerFn_relabel,
    PorsMachine.eval_ftsRecover] at he
  change some node = Option.map dv (Option.map (fun r : PorsMachine.Run => r.node)
    (PorsMachine.recoverRun f 0 index (slotValue leaves) (witFts wl))) at he
  cases hr : PorsMachine.recoverRun f 0 index (slotValue leaves) (witFts wl) with
  | none => rw [hr] at he; contradiction
  | some r =>
      rw [decodedCostRem_eq]
      exact recoverRun_exactSegmentsCost f 0 index leaves (witFts wl) r hr

theorem verifyList_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (ml pkl wl : List Byte) (hl : wl.length = 16384)
    (hverify : evalWithAnswerFn hash (Ref.verifyList ml pkl wl) = true) :
    decodedCostRem wl 0 ≤ 16*29 + 17*117 - 1 := by
  unfold Ref.verifyList at hverify
  cases hc : Ref.countersOk wl with
  | false => simp [hc] at hverify
  | true =>
      simp only [hc, Bool.not_true, Bool.false_eq_true, if_false] at hverify
      rw [evalWithAnswerFn_bind] at hverify
      let a := evalWithAnswerFn hash (Ref.H (Ref.digestInput (Ref.witRho wl) ml))
      have hdig : evalWithAnswerFn hash (Ref.digest (Ref.witRho wl) ml) = a.toNat := by
        simp only [Ref.digest, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        rfl
      rw [hdig, evalWithAnswerFn_bind] at hverify
      cases hr : evalWithAnswerFn hash (Ref.porsRoot (Ref.idxOf a.toNat) (Ref.leavesOf a.toNat) wl) with
      | none => rw [hr] at hverify; contradiction
      | some node =>
          let d := SphincsSecurity.truncateMessageDigest a
          have hd : d.toNat = a.toNat := truncateMessageDigest_toNat a
          rw [← hd, idxOf_eq, leavesOf_eq] at hr
          exact porsRoot_exact_cost hash (digestIndex d) wl hl (digestLeaves d) node hr

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsTightBound -/
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp
open SigGolfCandidate.Research.PorsPositiveBound

/-- Tighten the accepting bound using the exact decoded witness budget and the
universal positive-segment structural theorem. All-input bounds are unchanged. -/
theorem main_good_tight (ml pkl wl : List Byte) (hml : ml.length = 32)
    (hpk : pkl.length = 16) (hwl : wl.length = 16384) (s : MachineState)
    (hs : InitOK ml pkl wl s) :
    GoodQ s fuelBound cycleBoundAll True (cycleBound-1) (cc (verifyList ml pkl wl) Kb) := by
  intro F hF
  have hg := main_good_decoded ml pkl wl hml hpk hwl s hs F hF
  refine ⟨hg.1, fun hash => ⟨(hg.2 hash).1, (hg.2 hash).2.1, fun hsucc => ⟨trivial, ?_⟩⟩⟩
  have hobs := congrArg (fun X => (evalWithAnswerFn hash X).1) hg.1
  simp only [evalWithAnswerFn_map, cc_Kb, evalWith_countCalls_fst] at hobs
  have hv : evalWithAnswerFn hash (verifyList ml pkl wl) = true := by
    rw [← hobs]
    simp only [obs, hsucc, decide_true]
  have hcost := verifyList_exact_cost hash ml pkl wl hwl hv
  have hcycles := ((hg.2 hash).2.2 hsucc).2
  have hL := layC_val
  unfold cycleBoundDecoded at hcycles
  unfold cycleBound
  omega

theorem verify_good_tight (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (s : MachineState) (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True (cycleBound-1)
      (cc (verifyRef input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  exact main_good_tight _ _ _ (length_toList m) (length_toList pk) (length_toList w) s (init_ok m pk w s hs)

/-- Every accepting execution of the frozen verifier takes one fewer cycle than
its previous bound. This is universal over hash answers and arbitrary witnesses. -/
theorem verify_accept_cycles_tight (hash : Hash)
    (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ cycleBound-1 := by
  obtain ⟨s, hs⟩ := init_exists input
  have hg := (verify_good_tight input s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT fuelBound; norm_num)).2 hash
  rw [runWith_eq submission hash .verify input s hs, image_eq] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT image s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  exact (hg.2.2 hsucc).2

end SigGolfCandidate.Verify

#print axioms SigGolfCandidate.Verify.verify_accept_cycles_tight
end StructuralCostCertificate


/-!
# Discharging the pending component statements

Each pending statement of `Pending.lean` is one of the component theorems.
-/

namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem keygenRefinement : KeygenRefinementStatement := fun sk =>
  Keygen.keygen_run_counts sk

theorem keygenTermination : KeygenTerminationStatement := fun hash sk => by
  rw [Keygen.keygen_runWith]
  exact ⟨rfl, by show _ < 2 ^ 32; norm_num⟩

theorem signRefinement : SignRefinementStatement := fun sk cache m =>
  Sign.sign_refines sk cache m

theorem signTermination : SignTerminationStatement := fun hash sk cache m =>
  Sign.sign_terminates hash sk cache m

theorem verifyRefinement : VerifyRefinementStatement := fun m pk w =>
  Verify.verify_refines m pk w

theorem verifyTermination : VerifyTerminationStatement := fun hash m pk w =>
  ⟨(Verify.verify_terminates hash (m, pk, w)).1, (Verify.verify_terminates hash (m, pk, w)).2.2⟩

theorem verifyCycles : VerifyCyclesStatement := fun hash m pk w h =>
  Verify.verify_accept_cycles_tight hash (m, pk, w) (by
    cases hv : (submission.runWith hash .verify (m, pk, w)).value with
    | none => simp [hv] at h
    | some u => cases u; rfl)

theorem eventSecurity : EventSecurityStatement := fun q hq adversary =>
  SphincsSecurity.security127_event q hq adversary

/-- The competition certificate for `SigGolfCandidate.submission` with `C = claimedC`. -/
theorem certificate : SigGolfCandidate.Legacy.Certificate submission claimedC :=
  certificate_of ⟨keygenRefinement, keygenTermination, signRefinement, signTermination,
    verifyRefinement, verifyTermination, verifyCycles, eventSecurity⟩

end SigGolfCandidate.Final
