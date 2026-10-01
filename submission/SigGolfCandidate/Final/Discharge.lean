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
submission entry limit. The checked three-bit path prefixes have an exact
per-segment saving that is aggregated over every accepting witness. -/

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
      have h := hp ⟨false, decide (anc v x % 2 = 1), sibs v x (top-x), ⟨anc v x / 2 % 4, Nat.mod_lt _ (by decide)⟩⟩ (by simp [climbSegs])
      simpa [PositiveRuns, sibs] using h
  | cons y L ih =>
      have h := hp ⟨true, decide (anc v x % 2 = 1), sibs v x (y-x), ⟨anc v x / 2 % 4, Nat.mod_lt _ (by decide)⟩⟩ (by simp [climbSegs])
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
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hs hb hL rfl
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
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hs hb hL rfl
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
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hs hb hL rfl
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

namespace SigGolfCandidate.Research.PorsPrefixCredit

/-- Cycles saved by inlining at most two nonfinal folds. -/
def prefixSave (a : Nat) : Nat := if a < 2 then 0 else 2 * min (a - 1) 2 - 1

def zeroIndicator (a : Nat) : Nat := if a = 0 then 1 else 0

def credit (a : Nat) : Nat := zeroIndicator a + prefixSave a

def segmentCost (a : Nat) : Nat := 16 + 17 * a - credit a

def totalCredit (as : List Nat) : Nat := (as.map credit).sum

def totalZeros (as : List Nat) : Nat := (as.map zeroIndicator).sum

def segmentsCost (as : List Nat) : Nat := (as.map segmentCost).sum

/-- The scalar inequality is tight at lengths 0, 1 and 14. -/
theorem scalar_credit (a : Nat) (ha : a ≤ 14) :
    3 * a + 16 * zeroIndicator a ≤ 13 * credit a + 3 := by
  unfold credit zeroIndicator prefixSave
  split_ifs <;> omega

theorem credit_le_base (a : Nat) : credit a ≤ 16 + 17 * a := by
  unfold credit zeroIndicator prefixSave
  split_ifs <;> omega

/-- Same natural subtraction order as the proposed machine segment accounting. -/
theorem segmentCost_eq_subtractions (a : Nat) :
    segmentCost a = 16 + 17 * a - zeroIndicator a - prefixSave a := by
  simp only [segmentCost, credit, Nat.sub_sub]

theorem cost_add_credit (a : Nat) : segmentCost a + credit a = 16 + 17 * a := by
  exact Nat.sub_add_cancel (credit_le_base a)

theorem total_scalar_credit (as : List Nat) (ha : ∀ a ∈ as, a ≤ 14) :
    3 * as.sum + 16 * totalZeros as ≤ 13 * totalCredit as + 3 * as.length := by
  induction as with
  | nil => simp [totalZeros, totalCredit]
  | cons a as ih =>
      have hs := scalar_credit a (ha a (by simp))
      have ht := ih (fun b hb => ha b (by simp [hb]))
      simp only [totalZeros, totalCredit, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem segmentsCost_add_credit (as : List Nat) :
    segmentsCost as + totalCredit as = 16 * as.length + 17 * as.sum := by
  induction as with
  | nil => simp [segmentsCost, totalCredit]
  | cons a as ih =>
      have hs := cost_add_credit a
      simp only [segmentsCost, totalCredit, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem totalZeros_pos (as : List Nat) (hz : 0 ∈ as) : 1 ≤ totalZeros as := by
  induction as with
  | nil => simp at hz
  | cons a as ih =>
      simp only [List.mem_cons] at hz
      rcases hz with h | h
      · subst a
        simp [totalZeros, zeroIndicator]
      · have ht := ih h
        simp only [totalZeros, List.map_cons, List.sum_cons] at *
        omega

/-- Includes the one-time constant-register initializer. It permits fewer than29
segments as well, so the caller need only supply an upper length bound. -/
theorem segmentsCost_with_initializer_le (as : List Nat)
    (hlen : as.length ≤ 29) (ha : ∀ a ∈ as, a ≤ 14)
    (hsum : as.sum ≤ 117) (hz : 0 ∈ as) :
    segmentsCost as + 1 ≤ 2432 := by
  have hp := total_scalar_credit as ha
  have hc := segmentsCost_add_credit as
  have hzero := totalZeros_pos as hz
  omega

/-- Handles the all-positive structural branch supplied by the existing
`positiveTree_14_15` / schedule certificate, where folds are at most106. -/
theorem segmentsCost_low_folds_le (as : List Nat)
    (hlen : as.length ≤ 29) (hsum : as.sum ≤ 106) :
    segmentsCost as + 1 ≤ 2267 := by
  have hc := segmentsCost_add_credit as
  omega

/-- Direct bridge for the existing structural dichotomy: either the fold count
is at most106 or the schedule has a zero-fold segment. -/
theorem segmentsCost_structural_le (as : List Nat)
    (hlen : as.length ≤ 29) (ha : ∀ a ∈ as, a ≤ 14)
    (hsum : as.sum ≤ 117) (hstructure : as.sum ≤ 106 ∨ 0 ∈ as) :
    segmentsCost as + 1 ≤ 2432 := by
  rcases hstructure with hlow | hzero
  · have h := segmentsCost_low_folds_le as hlen hlow
    omega
  · exact segmentsCost_with_initializer_le as hlen ha hsum hzero


end SigGolfCandidate.Research.PorsPrefixCredit

/-! ## PorsExactSegmentBudget -/
namespace SigGolfCandidate.Research.PorsPositiveBound

def exactSegmentCost (a : Nat) : Nat := if a = 0 then 15 else 16+17*a-Verify.prefixSave a
def exactSegmentsCost (as : List Nat) : Nat := (as.map exactSegmentCost).sum
def zeroSegments : List Nat → Nat
  | [] => 0
  | a::as => (if a = 0 then 1 else 0) + zeroSegments as

theorem exactSegmentsCost_cons (a : Nat) (as : List Nat) :
    exactSegmentsCost (a::as) = exactSegmentCost a + exactSegmentsCost as := rfl

theorem exactSegmentsCost_add_zeros (as : List Nat) :
    exactSegmentsCost as + zeroSegments as ≤ 16*as.length + 17*as.sum := by
  induction as with
  | nil => exact Nat.le_refl 0
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


theorem exactSegmentsCost_prefix_eq (as : List Nat) :
    exactSegmentsCost as = PorsPrefixCredit.segmentsCost as := by
  unfold exactSegmentsCost PorsPrefixCredit.segmentsCost
  congr 1
  apply List.map_congr_left
  intro a _
  unfold exactSegmentCost PorsPrefixCredit.segmentCost PorsPrefixCredit.credit
    PorsPrefixCredit.zeroIndicator PorsPrefixCredit.prefixSave
  rw [Verify.prefixSave_eq]
  split_ifs <;> omega

/-- The checked two-fold prefixes improve the universal segment envelope by22
cycles. The premise applies to arbitrary accepted witnesses. -/
theorem exactSegmentsCost_prefix_envelope (as : List Nat)
    (hlen : as.length = 29) (ha : ∀ a ∈ as, a ≤ 14) (hfolds : as.sum ≤ 117)
    (hpositive : (∀ a ∈ as, 0 < a) → as.sum ≤ 106) :
    exactSegmentsCost as ≤ 16*29 + 17*117 - 22 := by
  have hstructure : as.sum ≤ 106 ∨ 0 ∈ as := by
    by_cases hz : 0 ∈ as
    · exact Or.inr hz
    · exact Or.inl (hpositive (fun a ha => by
        have hn : a ≠ 0 := fun h => hz (h ▸ ha)
        omega))
  have h := PorsPrefixCredit.segmentsCost_structural_le as (by omega) ha hfolds hstructure
  rw [exactSegmentsCost_prefix_eq]
  omega


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
    have h := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hs hb hL rfl
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

theorem recoverRun_exactSegmentsCost_prefix_relaxed (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    exactSegmentsCost (decodedFolds fts) ≤ 16*29 + 17*117 - 22 := by
  have hsum := recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  apply exactSegmentsCost_prefix_envelope (decodedFolds fts)
  · simp [decodedFolds, ftsSegments, ftsOpenings]
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    have hclimb : ∀ (L : List Nat) (v x top : Nat), top ≤ 14 →
        (∀ y ∈ L, y ≤ 14) → ∀ seg ∈ climbSegs v x L top, seg.reads.length ≤ 14 := by
      intro L
      induction L with
      | nil =>
          intro v x top ht hL seg hs
          simp only [climbSegs, List.mem_singleton] at hs
          subst seg
          simp only [sibs, List.length_map, List.length_range']
          omega
      | cons y L ih =>
          intro v x top ht hL seg hs
          simp only [climbSegs, List.mem_cons] at hs
          rcases hs with rfl | hs
          · have hy := hL y (by simp)
            simp only [sibs, List.length_map, List.length_range']
            omega
          · exact ih v (y+1) top ht (fun z hz => hL z (by simp [hz])) seg hs
    have hall : ∀ (vs : List Nat), (∀ v ∈ vs, v < 2^ftsTreeHeight) →
        ∀ (L : List Nat) seg, seg ∈ allSegs vs L → seg.reads.length ≤ 14 := by
      intro vs
      induction vs with
      | nil => intro hv L seg hs; simp [allSegs] at hs
      | cons v rest ih =>
          intro hv L seg hs
          have htop : leafTop v rest ≤ 14 := by
            cases rest with
            | nil => simp [leafTop, ftsTreeHeight]
            | cons w rest =>
                have hh := bitLength_xor_le v w (hv v (by simp)) (hv w (by simp))
                simp only [leafTop]
                change bitLength (v ^^^ w) ≤ 14 at hh
                omega
          rw [allSegs_cons] at hs
          rcases List.mem_append.mp hs with hs | hs
          · exact hclimb _ v 0 _ htop (fun y hy => by
              have hh := (mem_filter_lt hy).2
              omega) seg hs
          · exact ih (fun w hw => hv w (by simp [hw])) _ seg hs
    obtain ⟨hlen, hsorted', hbound⟩ := sortedLeaves_facts leaves hadm.1
    obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
      cases h : sortedLeaves leaves with
      | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
      | cons v rest => exact ⟨v, rest, rfl⟩
    have hsch : schedule (sortedLeaves leaves) = allSegs (sortedLeaves leaves) [] := by
      rw [he] at hsorted' hbound ⊢
      have hh := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hsorted' hbound
        ⟨List.Pairwise.nil, by simp⟩ rfl
      simpa only [schedule, List.nil_append] using hh.1
    have hmatch := ((PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1 j).1
    rw [hmatch]
    have hlen' := schedule_length_of_injective leaves hadm.1
    have hj : j.val < (schedule (sortedLeaves leaves)).length := by rw [hlen']; exact j.isLt
    have hmem : (schedule (sortedLeaves leaves)).getD j.val default ∈ schedule (sortedLeaves leaves) := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        using List.getElem_mem hj
    rw [hsch] at hmem ⊢
    exact hall (sortedLeaves leaves) (sortedLeaves_lt leaves) [] _ hmem
  · rw [hsum, hfolds]; exact hadm.2
  · intro hp
    rw [hsum]
    apply recoverRun_positive_folds f parameter index leaves fts r hrun
    intro j
    exact hp _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

end SigGolfCandidate.Research.PorsPositiveBound


/-! ## Topology-aware PORS cost certificate -/

namespace SiggolfPrefixCertificate

/-- Zero-length unary runs are permitted, including at the root and leaves. -/
inductive Tree (credit : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | leaf (h : Nat) : Tree credit h 1 h (credit h)
  | fork (h a p q fl fr cl cr : Nat) (ha : a < h)
      (left : Tree credit (h-a-1) p fl cl)
      (right : Tree credit (h-a-1) q fr cr) :
      Tree credit h (p+q) (a+fl+fr) (credit a+cl+cr)

theorem Tree.leaves_pos {credit : Nat → Nat} {h k f c : Nat}
    (ht : Tree credit h k f c) : 0 < k := by
  induction ht with
  | leaf => omega
  | fork h a p q fl fr cl cr ha left right ihl ihr => omega

/-- Each table value is one plus a fold upper bound; zero denotes infeasibility. -/
structure Certificate (credit : Nat → Nat) (upper : Nat → Nat → Nat → Nat) : Prop where
  leaf : ∀ h, h≤14 → credit h≤39 → h+1≤upper h 1 (credit h)
  fork : ∀ h a p q cl cr, h≤14 → a<h → 0<p → 0<q → p+q≤15 →
    credit a+cl+cr≤39 → 0<upper (h-a-1) p cl → 0<upper (h-a-1) q cr →
    a+upper (h-a-1) p cl+upper (h-a-1) q cr-1≤upper h (p+q) (credit a+cl+cr)

theorem Tree.fold_bound {credit : Nat → Nat} {upper : Nat → Nat → Nat → Nat}
    (hc : Certificate credit upper) {h k f c : Nat} (ht : Tree credit h k f c)
    (hh : h≤14) (hk : k≤15) (hcc : c≤39) : f<upper h k c := by
  induction ht with
  | leaf h => have := hc.leaf h hh hcc; omega
  | fork h a p q fl fr cl cr ha left right ihl ihr =>
      have hp := left.leaves_pos
      have hq := right.leaves_pos
      have hl := ihl (by omega) (by omega) (by omega)
      have hr := ihr (by omega) (by omega) (by omega)
      have hs := hc.fork h a p q cl cr hh ha hp hq hk hcc (by omega) (by omega)
      omega

theorem cost_2413 {credit : Nat → Nat} {upper : Nat → Nat → Nat → Nat}
    (hc : Certificate credit upper)
    (hroot : ∀ c : Fin 40, 464+17*(upper 14 15 c.val-1)-c.val≤2413)
    {f c : Nat} (ht : Tree credit 14 15 f c) (hf : f≤117) :
    464+17*f-c≤2413 := by
  by_cases hcc : c≤39
  · have hb := ht.fold_bound hc (by omega) (by omega) hcc
    have hs := hroot ⟨c,by omega⟩
    simp only at hs
    omega
  · omega

end SiggolfPrefixCertificate

namespace SiggolfPrefixTable
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def save (a : Nat) : Nat := if a<2 then 0 else 2*min (a-1) 2-1
def credit (a : Nat) : Nat := (if a=0 then 1 else 0)+save a

def row0 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 15296605450596291897003637061602511075924463299623145836628444171172474686655185024

  | 2 => 0

  | 3 => 0

  | 4 => 0

  | 5 => 0

  | 6 => 0

  | 7 => 0

  | 8 => 0

  | 9 => 0

  | 10 => 0

  | 11 => 0

  | 12 => 0

  | 13 => 0

  | 14 => 0

  | 15 => 0

  | _ => 0

def row1 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 30593210901192583794007274123205022151848926599246291673256888342344949373310370050

  | 2 => 15296605450596291897003637061602511075924463299623145836628444171172474686655168512

  | 3 => 0

  | 4 => 0

  | 5 => 0

  | 6 => 0

  | 7 => 0

  | 8 => 0

  | 9 => 0

  | 10 => 0

  | 11 => 0

  | 12 => 0

  | 13 => 0

  | 14 => 0

  | 15 => 0

  | _ => 0

def row2 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 45889816351788875691010911184807533227773389898869437509885332513517424059965555072

  | 2 => 45889816351788875691010911184807533227773389898869437509885332513517424059965555072

  | 3 => 30593210901192583794007274123205022151848926599246291673256888342344949373306142720

  | 4 => 15296605450596291897003637061602511075924463299623145836628444171172470253978386432

  | 5 => 0

  | 6 => 0

  | 7 => 0

  | 8 => 0

  | 9 => 0

  | 10 => 0

  | 11 => 0

  | 12 => 0

  | 13 => 0

  | 14 => 0

  | 15 => 0

  | _ => 0

def row3 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 61186421802385167588014548246410044303697853198492583346513776684689898746620674048

  | 2 => 76483027252981459485018185308012555379622316498115729183142220855862373433275908612

  | 3 => 76483027252981459485018185308012555379622316498115729183142220855862373433275842560

  | 4 => 76483027252981459485018185308012555379622316498115729183142220855862373433275842560

  | 5 => 61186421802385167588014548246410044303697853198492583346513776684689898608099590144

  | 6 => 45889816351788875691010911184807533227773389898869437509885332513299549129961111552

  | 7 => 30593210901192583794007274123205022151848926599246291673256583731114810254148239360

  | 8 => 15296605450596291897003637061602511075924463299623145517220418916815460136304771072

  | 9 => 0

  | 10 => 0

  | 11 => 0

  | 12 => 0

  | 13 => 0

  | 14 => 0

  | 15 => 0

  | _ => 0

def row4 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 76483027252981459485018185308012555379622316498115729183142220855862373433275842560

  | 2 => 107076238154174043279025459431217577531471243097362020856399109198207318373909496448

  | 3 => 122372843604770335176029096492820088607395706396985166693027553369379793060562567168

  | 4 => 137669449055366627073032733554422599683320169696608312529655997540552267747217752960

  | 5 => 137669449055366627073032733554422599683320169696608312529655997540552267747202957312

  | 6 => 137669449055366627073032733554422599683320169696608312529655997540552267747202957312

  | 7 => 137669449055366627073032733554422599683320169696608312529655997540552232285805477888

  | 8 => 137669449055366627073032733554422599683320169696608312529655997540552232285805477888

  | 9 => 122372843604770335176029096492820088607395706396985166693027553295011821385058091008

  | 10 => 107076238154174043279025459431217577531471243097362020856262643367104997421951746048

  | 11 => 91779632703577751382021822369615066455546779797738629714407269680847673450813194240

  | 12 => 76483027252981459485018185308012555379622316069413534637078014917752631786953768960

  | 13 => 61186421802385167588014548246410044302978610266735249233224561707959444504664080384

  | 14 => 45889816351788875691010911184806401956458774331306672982060172344336603140337958912

  | 15 => 30593210901192583794007272541573088826071096341409586613057476411042790138278051840

  | _ => 0

def row5 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 91779632703577751382021822369615066455546779797738875019770665027034848119931011072

  | 2 => 137669449055366627073032733554422599683320169696608312529655997540552267712589463552

  | 3 => 168262659956559210867040007677627621835169096295854604202912884693009603787371839488

  | 4 => 198855870857751794661047281800832643987018022895100895556761748961589159362371388424

  | 5 => 214152476308348086558050918862435155062942486194724041393390193132761629616349642752

  | 6 => 229449081758944378455054555924037666138866949494347187230018637303934104303275343872

  | 7 => 244745687209540670352058192985640177214791412793970333066646929178714885865227681792

  | 8 => 260042292660136962249061830047242688290715876093593478903275373349887360551908016128

  | 9 => 260042292660136962249061830047242688290715876093593478903275373349887360101714493440

  | 10 => 260042292660136962249061830047242688290715876093593478903275373349887360101714493440

  | 11 => 260042292660136962249061830047242688290715876093593478903275373348870610913184448512

  | 12 => 260042292660136962249061830047242688290715876093593478903275373348870610913184448512

  | 13 => 260042292660136962249061830047242688290715876093593478903273088765733942169490685952

  | 14 => 260042292660136962249061830047242688290715876093593478903273088765733942169490685952

  | 15 => 260042292660136962249061830047242688290715876093593473792747121585862822317181108224

  | _ => 0

def row6 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 107076238154174043279025459431217577531471243097362020856399109198207322806586179584

  | 2 => 168262659956559210867040007677627621835169096295854604202912885882897217050998996992

  | 3 => 214152476308348086558050918862435155062942486194724041712798217197231026435746955264

  | 4 => 260042292660136962249061830047242688290715876093593478900780150448906764523743118464

  | 5 => 290635503561329546043069104170447710442564802607099331984212727748553306122653532160

  | 6 => 321228714462522129837076378293652732571397955475181523764944575593051966227888668672

  | 7 => 351821925363714713631083652410679505006529025508943112903904587359025945497391071232

  | 8 => 382415136264907297423432465253895498507879472122371026309188408213052612478180247424

  | 9 => 397711741715503589320436102315498009583803935421994172145797357265568241132465291264

  | 10 => 413008347166099881217439739377100520659728398721617317982425802626555708608012615680

  | 11 => 428304952616696173114443376438703031735652862020570657204914571592405131729764876288

  | 12 => 443601558067292465011447013500305542811577325320193803041543015772873036052410925056

  | 13 => 458898163517888756908450650561908053864487408600821779731668185780299632598516236288

  | 14 => 474194768968485048805454287623510564940411871900444925568296629951544723396485971968

  | 15 => 489491374419081340702457923894344999861935453070309709085721637745011527976510029824

  | _ => 0

def row7 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 122372843604770335176029096492820088607395706396985166693027553369379797493241348096

  | 2 => 198855870857751794661047281800832643987018022895100895876169774225242166389679063040

  | 3 => 260042292660136962249061830047242688290715876093593479222683549701379832866253307904

  | 4 => 321228714462522129837076378293652732594413729292086062247274430834275008559091548160

  | 5 => 367118530814311005528087289478460265822187119104545213671463919730149970361687474176

  | 6 => 413008347166099881219098200663267799026764924539975831755918638155838139737126731776

  | 7 => 458898163517888756910109111841848814961908599618942717492938254709386325404069920768

  | 8 => 504787979869677632599448605017917405252851490157099378674685941897423727614329358352

  | 9 => 535381190770425026583516536064683249369023890149723320132822192838400506334443208704

  | 10 => 565854896941976538613286021293722541454796885924826907327884448956676106937853542400

  | 11 => 581270073491955293167576891544133152382360790799349344679269070174312056643158802432

  | 12 => 596567605279265510554090585115023226738376187236276391230856546978660027298238955520

  | 13 => 611864217966867379993981019493104546902426360951034682910088750042065994447910338560

  | 14 => 627160823474002777965538459658742048674350401677665422439635359269204564996645715968

  | 15 => 657634529645554289995307844454153574573231176080138238631423487894716594722850209792

  | _ => 0

def row8 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 137669449055366627073032733554422599683320169696608312529655997540552272179896516608

  | 2 => 229449081758944378455054555924037666138866949494347187549426662567587115728359129088

  | 3 => 305932109011925837940072741232050221518489265992462916732568882214824627447883890688

  | 4 => 382415136264907297425090926540062776898111582490578645593749218452875902783487737856

  | 5 => 443601558067292465013105474786472821201809435602650476809347104747321401850533511168

  | 6 => 504787979869677632601120023032882865482310299481292985615542061563958883632581443584

  | 7 => 565974401672062800189134571273066015380105663383310405966577603312506627483613790208

  | 8 => 627160823474447967775477600280163775877969087009772808500308613280384158295753263232

  | 9 => 673050639825788175609500657209023907420066254329952401061727638075682433816848236544

  | 10 => 718820017817235658663102715842077804879742182426837226974986448533467133360736305152

  | 11 => 734236120703928338706903540598920666570812870990448194140119147196708251468012978176

  | 12 => 749533659728244106678002868096073657184059927203103850259031472065094186390639738880

  | 13 => 764830272472385081981835377739203532236950566548718235300620319745643898545176051712

  | 14 => 795303978700475700084500306795191612303221035107435537607812076714554779963198799872

  | 15 => 825896255970967989965296039915802972386677331432325754226964085490727172662445998080

  | _ => 0

def row9 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 152966054505962918970036370616025110759244632996231458366284441711724746866551685120

  | 2 => 260042292660136962249061830047242688290715876093593479222683550909932065067039195136

  | 3 => 351821925363714713631083652416857754746262655891332354242454214728269426496280461312

  | 4 => 443601558067292465013105474786472821201809435689071228940262841651213302747872886784

  | 5 => 520084585320273924498123660094485376581431752100766164788854216536376544247351869440

  | 6 => 596567612573255383983141845402497931937857057414550091604545280415203991465744138240

  | 7 => 673050639826236843468160030704283587042374772607211689378823285010338020863489605632

  | 8 => 749533667079218302951506695982119630246205803328883810312524703318583844884201865216

  | 9 => 810720088881154775299666138923612882482481654594783427970962373542631752936873525248

  | 10 => 871786065028766992437880273365660724417526707191917582131625074656612335729086824448

  | 11 => 887083604053082787368939124308575277783789945194512486321706845152676882457944915968

  | 12 => 902380216797665474437307869972425696301669176230302310272642938078674157519939567616

  | 13 => 932972494068599449124364487172007602206030821823883057911415580449960836862222270464

  | 14 => 948388596955292129380435501041551903535575447764229192584932819059778771552198197248

  | 15 => 963686136036147003212185894695240264959316943342419614349056209197579232794852196352

  | _ => 0

def row10 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 168262659956559210867040007677627621835169096295854604202912885882897221553206853632

  | 2 => 290635503561329546043069104170447710442564802692839770895940439252277014405719261184

  | 3 => 397711741715503589322094563601665287974036045790201791752339547241714225544677031936

  | 4 => 504787979869677632601120023032882865505507288887563812286776466020848019698683478016

  | 5 => 596567612573255383983141845402497931961054068598881853087730216948898434191537995776

  | 6 => 688347245276833135365163667772112998393403826151772306134719397318637767986100830208

  | 7 => 780126877980410886747185490135501164527814468071434438921507027864664886649521438720

  | 8 => 871906510683988638127535792462583219374491071859053590160837967338211843868956033024

  | 9 => 948389537936521402369381949905796709302663568654590423038375700617549797257830727680

  | 10 => 1024752119477742137478007434016646962472167971333830552001090149581210882304295043072

  | 11 => 1040048724928338429587294115701482480667630726192457451704056963665837239603413647360

  | 12 => 1055345337672924594701065967630283828777542370583297023333140715349446863611051900928

  | 13 => 1085938541337111600950527983157069280766860169565506182285895884953551463670676979712

  | 14 => 1116531752181319888860029256386262406017973145587822955094996675464199856735121309696

  | 15 => 1131828357631916180969316039295540902882520448276664236485140799185803175865299763200

  | _ => 0

def row11 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 183559265407155502764043644739230132911093559595477750039541330054069696239862022144

  | 2 => 321228714462522129837076378293652732594413729292086062569197327594621963744399327232

  | 3 => 443601558067292465013105474786472821201809435689071229262224879755159024593073602560

  | 4 => 565974401672062800189134571279292909809205142086056395633290090399850223874424700928

  | 5 => 673050639826236843468160030710510487340676385096997541386644900645056178028393005056

  | 6 => 780126877980410886747185490141728064848950605863765468499333256231851310259577552896

  | 7 => 887203116134584930026210949566718742036269915403668788210970753100246738790604865536

  | 8 => 994279354288758973303564888955355037436761680770976070291269685528392339214858977280

  | 9 => 1086058986991888029442401726719065375933290735087117639467069455424629252964367728640

  | 10 => 1177718173983698100357224532567896743099800529205321983597632766948057091573245018112

  | 11 => 1208310443960203995066668214248734031307235204261486819617959422366844670437647974400

  | 12 => 1208311384884897640242051078743520592935119069336149047747115328250683732565237432320

  | 13 => 1238904595786090224034399891580606604295843350320316255423701316137225358762217308160

  | 14 => 1269497806687279329783004058654222985824360033548876065218673780412436281782477783040

  | 15 => 1300090083957768141832338190634646353131580316625860462544000501314988038274905276416

  | _ => 0

def row12 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 198855870857751794661047281800832643987018022895100895876169774225242170926517190656

  | 2 => 351821925363714713631083652416857754746262655891332354242454215936966913083079393280

  | 3 => 489491374419081340704116385971280354429582825587940666772110212268603823641470173184

  | 4 => 627160823474447967777149119525702954112902995284548978979803714778852428050165923840

  | 5 => 749533667079218302953178216018523042720298701595113229685559736637532994411306156032

  | 6 => 871906510683988638129207312511343131304497385575763863725663695198367050621234708480

  | 7 => 994279354288758973305236408997936319567561347596615790017441423102566717340671541248

  | 8 => 1116652197893529308479593985448126858444872921224574611896160380509028942529056210944

  | 9 => 1223728436047254656515421503544593635669429130336526522689702389007339528833053229056

  | 10 => 1330684228489660992153359874607219092766599778978253676447534872827015751646545182720

  | 11 => 1376573096622766376835099914207808045349763654280377153735920114778970763030446473216

  | 12 => 1376573103916318016334393561829703851167137461609816291993022324950315916493712261120

  | 13 => 1391869716661349371256433239177264026855864617757177582815074932304804422962361925632

  | 14 => 1422463861193238770705978758919280736795407627024531425356732990426534029547542675456

  | 15 => 1468352736620334001435548413521556926316326949729533265387082689056207194825873686528

  | _ => 0

def row13 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 214152476308348086558050918862435155062942486194724041712798218396414645613172359168

  | 2 => 382415136264907297425090926540062776898111582490578645915711104279311862421759459328

  | 3 => 535381190770870216395127297156087887657356215486810104281995544782048622689866743808

  | 4 => 688347245276833135365163667772112998416600848483041562326317339157854632225907146752

  | 5 => 826016694332199762438196401326535598099921018093228958549293779933350658688721879040

  | 6 => 963686143387566389511229134880958197760044165287762299516813341477735241290400923648

  | 7 => 1101355592442933016584261868429153897098852779875297997552077847848081039878260785152

  | 8 => 1239025041498299643655623081940946569961650611613687144224892712707439468805883953152

  | 9 => 1361397885102621283588454135874572125389514162577265381333316977052791494180979343360

  | 10 => 1483650282995623883951166432224879021253946583331010537213919596621436132120791613440

  | 11 => 1544835756522341237474820001197826149438682466541152247545273348231116252545424556032

  | 12 => 1544835756522341291820937784813281235137162988494285006649964162832072167644752510976

  | 13 => 1544835763873322416800722113691231040674870922794214927759990782108722643044235476992

  | 14 => 1575429915698759923568652018579951794007256974119378150087249119645186700470971793408

  | 15 => 1636496818126543455119776698504236921252772817576731168905067419460209354755832545280

  | _ => 0

def row14 (k : Nat) : Nat := match k with

  | 0 => 0

  | 1 => 229449081758944378455054555924037666138866949494347187549426662567587120299827527680

  | 2 => 413008347166099881219098200663267799049960509089824937588967992621656811760439525376

  | 3 => 581271007122659092086138208340895420885129605385679541791880877295493421738263314432

  | 4 => 749533667079218302953178216018523042720298701681534145672830963536856836401648369664

  | 5 => 902499721585181221923214586634548153479543334591344687413027823229168322966137602048

  | 6 => 1055465776091144140893250957250573264215590944999760735307962987757103431959567138816

  | 7 => 1208431830597107059863287327860371474630144212153980205086714125019642772739437101056

  | 8 => 1361397885103069978831652178433766281478428302002804908786351728253438267881194258432

  | 9 => 1499067334157987910661486768204550615132435179677392612460253420999743740324874289152

  | 10 => 1636616337501586802708919656993178747354146362206748237051858098018928847743331860480

  | 11 => 1713098416421916152245058005838497803608314689539326878196798974965940941452409307136

  | 12 => 1728275517142429687996129057598024639995234116362842751805455205527067004318926241792

  | 13 => 1728275517256398306935725064950707911515298077705529445770123310327444037909096693760

  | 14 => 1743691634730622038383844755778398274110877853209320212203502281184758921801999843328

  | 15 => 1789581443674897638900673253879869067154850231111310948552069677665787879979690754048

  | _ => 0

def row (h k : Nat) : Nat := match h with
  | 0 => row0 k
  | 1 => row1 k
  | 2 => row2 k
  | 3 => row3 k
  | 4 => row4 k
  | 5 => row5 k
  | 6 => row6 k
  | 7 => row7 k
  | 8 => row8 k
  | 9 => row9 k
  | 10 => row10 k
  | 11 => row11 k
  | 12 => row12 k
  | 13 => row13 k
  | 14 => row14 k
  | _ => 0


def upper (h k c : Nat) : Nat := (row h k / 128^c) % 128

def checkLeaf (h : Nat) : Bool := (List.range 40).all fun c =>
  decide (credit h ≤ c → h+1 ≤ upper h 1 c)

def checkFork (h k c : Nat) : Bool := (List.range h).all fun a =>
  if credit a > c then true else
    (List.range k).all fun p => if p=0 then true else
      (List.range (c-credit a+1)).all fun cl =>
        let cr := c-credit a-cl
        let ul := upper (h-a-1) p cl
        if ul=0 then true else
          let ur := upper (h-a-1) (k-p) cr
          decide (ur=0 ∨ a+ul+ur-1 ≤ upper h k c)

def checkHeight (h : Nat) : Bool := checkLeaf h &&
  (List.range 16).all fun k => (List.range 40).all fun c => checkFork h k c


end SiggolfPrefixTable

namespace SiggolfPrefixTable
open SiggolfPrefixCertificate

set_option maxRecDepth 2000
set_option maxHeartbeats 4000000

 theorem certificate_of_checks
    (checks : ∀ h, h≤14 → checkHeight h=true) : Certificate credit upper := by
  constructor
  · intro h hh hc
    have H := checks h hh
    simp only [checkHeight, Bool.and_eq_true] at H
    have HL := H.1
    simp only [checkLeaf, List.all_eq_true] at HL
    have HS := HL (credit h) (List.mem_range.mpr (by omega))
    simpa using HS
  · intro h a p q cl cr hh ha hp hq hpq hc hul hur
    have H := checks h hh
    simp only [checkHeight, Bool.and_eq_true] at H
    have HF := H.2
    simp only [List.all_eq_true] at HF
    have HF := HF (p+q) (List.mem_range.mpr (by omega)) (credit a+cl+cr)
      (List.mem_range.mpr (by omega))
    simp only [checkFork, List.all_eq_true] at HF
    have HA := HF a (List.mem_range.mpr ha)
    have hca : ¬credit a > credit a+cl+cr := by omega
    simp only [hca, ↓reduceIte, List.all_eq_true] at HA
    have HP := HA p (List.mem_range.mpr (by omega))
    have hp0 : ¬p=0 := by omega
    simp only [hp0, ↓reduceIte, List.all_eq_true] at HP
    have HC := HP cl (List.mem_range.mpr (by omega))
    have eqcr : credit a+cl+cr-credit a-cl=cr := by omega
    have eqq : p+q-p=q := by omega
    have hnul : ¬upper (h-a-1) p cl=0 := by omega
    simp only [eqcr, eqq, hnul, ↓reduceIte, decide_eq_true_eq] at HC
    omega

end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
 theorem root_check : ∀ c : Fin 40, 464+17*(upper 14 15 c.val-1)-c.val≤2413 := by
  decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_0 : checkHeight 0 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_1 : checkHeight 1 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_2 : checkHeight 2 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_3 : checkHeight 3 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_4 : checkHeight 4 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_5 : checkHeight 5 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_6 : checkHeight 6 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_7 : checkHeight 7 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_8 : checkHeight 8 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_9 : checkHeight 9 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_10 : checkHeight 10 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_height_11 : checkHeight 11 = true := by decide +kernel
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_leaf_12 : checkLeaf 12=true := by decide +kernel
theorem check_h12_k0 : (List.range 40).all (fun c => checkFork 12 0 c)=true := by decide +kernel
theorem check_h12_k1 : (List.range 40).all (fun c => checkFork 12 1 c)=true := by decide +kernel
theorem check_h12_k2 : (List.range 40).all (fun c => checkFork 12 2 c)=true := by decide +kernel
theorem check_h12_k3 : (List.range 40).all (fun c => checkFork 12 3 c)=true := by decide +kernel
theorem check_h12_k4 : (List.range 40).all (fun c => checkFork 12 4 c)=true := by decide +kernel
theorem check_h12_k5 : (List.range 40).all (fun c => checkFork 12 5 c)=true := by decide +kernel
theorem check_h12_k6 : (List.range 40).all (fun c => checkFork 12 6 c)=true := by decide +kernel
theorem check_h12_k7 : (List.range 40).all (fun c => checkFork 12 7 c)=true := by decide +kernel
theorem check_h12_k8 : (List.range 40).all (fun c => checkFork 12 8 c)=true := by decide +kernel
theorem check_h12_k9 : (List.range 40).all (fun c => checkFork 12 9 c)=true := by decide +kernel
theorem check_h12_k10 : (List.range 40).all (fun c => checkFork 12 10 c)=true := by decide +kernel
theorem check_h12_k11 : (List.range 40).all (fun c => checkFork 12 11 c)=true := by decide +kernel
theorem check_h12_k12 : (List.range 40).all (fun c => checkFork 12 12 c)=true := by decide +kernel
theorem check_h12_k13 : (List.range 40).all (fun c => checkFork 12 13 c)=true := by decide +kernel
theorem check_h12_k14 : (List.range 40).all (fun c => checkFork 12 14 c)=true := by decide +kernel
theorem check_h12_k15 : (List.range 40).all (fun c => checkFork 12 15 c)=true := by decide +kernel
theorem check_height_12 : checkHeight 12=true := by
  simp only [checkHeight,Bool.and_eq_true]
  constructor
  · exact check_leaf_12
  · apply List.all_eq_true.mpr
    intro k hk
    have hk : k<16 := List.mem_range.mp hk
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_h12_k0
    · exact check_h12_k1
    · exact check_h12_k2
    · exact check_h12_k3
    · exact check_h12_k4
    · exact check_h12_k5
    · exact check_h12_k6
    · exact check_h12_k7
    · exact check_h12_k8
    · exact check_h12_k9
    · exact check_h12_k10
    · exact check_h12_k11
    · exact check_h12_k12
    · exact check_h12_k13
    · exact check_h12_k14
    · exact check_h12_k15
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_leaf_13 : checkLeaf 13=true := by decide +kernel
theorem check_h13_k0 : (List.range 40).all (fun c => checkFork 13 0 c)=true := by decide +kernel
theorem check_h13_k1 : (List.range 40).all (fun c => checkFork 13 1 c)=true := by decide +kernel
theorem check_h13_k2 : (List.range 40).all (fun c => checkFork 13 2 c)=true := by decide +kernel
theorem check_h13_k3 : (List.range 40).all (fun c => checkFork 13 3 c)=true := by decide +kernel
theorem check_h13_k4 : (List.range 40).all (fun c => checkFork 13 4 c)=true := by decide +kernel
theorem check_h13_k5 : (List.range 40).all (fun c => checkFork 13 5 c)=true := by decide +kernel
theorem check_h13_k6 : (List.range 40).all (fun c => checkFork 13 6 c)=true := by decide +kernel
theorem check_h13_k7 : (List.range 40).all (fun c => checkFork 13 7 c)=true := by decide +kernel
theorem check_h13_k8 : (List.range 40).all (fun c => checkFork 13 8 c)=true := by decide +kernel
theorem check_h13_k9 : (List.range 40).all (fun c => checkFork 13 9 c)=true := by decide +kernel
theorem check_h13_k10 : (List.range 40).all (fun c => checkFork 13 10 c)=true := by decide +kernel
theorem check_h13_k11 : (List.range 40).all (fun c => checkFork 13 11 c)=true := by decide +kernel
theorem check_h13_k12 : (List.range 40).all (fun c => checkFork 13 12 c)=true := by decide +kernel
theorem check_h13_k13 : (List.range 40).all (fun c => checkFork 13 13 c)=true := by decide +kernel
theorem check_h13_k14 : (List.range 40).all (fun c => checkFork 13 14 c)=true := by decide +kernel
theorem check_h13_k15 : (List.range 40).all (fun c => checkFork 13 15 c)=true := by decide +kernel
theorem check_height_13 : checkHeight 13=true := by
  simp only [checkHeight,Bool.and_eq_true]
  constructor
  · exact check_leaf_13
  · apply List.all_eq_true.mpr
    intro k hk
    have hk : k<16 := List.mem_range.mp hk
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_h13_k0
    · exact check_h13_k1
    · exact check_h13_k2
    · exact check_h13_k3
    · exact check_h13_k4
    · exact check_h13_k5
    · exact check_h13_k6
    · exact check_h13_k7
    · exact check_h13_k8
    · exact check_h13_k9
    · exact check_h13_k10
    · exact check_h13_k11
    · exact check_h13_k12
    · exact check_h13_k13
    · exact check_h13_k14
    · exact check_h13_k15
end SiggolfPrefixTable

namespace SiggolfPrefixTable
set_option maxRecDepth 5000
set_option maxHeartbeats 4000000
theorem check_leaf_14 : checkLeaf 14=true := by decide +kernel
theorem check_h14_k0 : (List.range 40).all (fun c => checkFork 14 0 c)=true := by decide +kernel
theorem check_h14_k1 : (List.range 40).all (fun c => checkFork 14 1 c)=true := by decide +kernel
theorem check_h14_k2 : (List.range 40).all (fun c => checkFork 14 2 c)=true := by decide +kernel
theorem check_h14_k3 : (List.range 40).all (fun c => checkFork 14 3 c)=true := by decide +kernel
theorem check_h14_k4 : (List.range 40).all (fun c => checkFork 14 4 c)=true := by decide +kernel
theorem check_h14_k5 : (List.range 40).all (fun c => checkFork 14 5 c)=true := by decide +kernel
theorem check_h14_k6 : (List.range 40).all (fun c => checkFork 14 6 c)=true := by decide +kernel
theorem check_h14_k7 : (List.range 40).all (fun c => checkFork 14 7 c)=true := by decide +kernel
theorem check_h14_k8 : (List.range 40).all (fun c => checkFork 14 8 c)=true := by decide +kernel
theorem check_h14_k9 : (List.range 40).all (fun c => checkFork 14 9 c)=true := by decide +kernel
theorem check_h14_k10 : (List.range 40).all (fun c => checkFork 14 10 c)=true := by decide +kernel
theorem check_h14_k11 : (List.range 40).all (fun c => checkFork 14 11 c)=true := by decide +kernel
theorem check_h14_k12 : (List.range 40).all (fun c => checkFork 14 12 c)=true := by decide +kernel
theorem check_h14_k13 : (List.range 40).all (fun c => checkFork 14 13 c)=true := by decide +kernel
theorem check_h14_k14 : (List.range 40).all (fun c => checkFork 14 14 c)=true := by decide +kernel
theorem check_h14_k15 : (List.range 40).all (fun c => checkFork 14 15 c)=true := by decide +kernel
theorem check_height_14 : checkHeight 14=true := by
  simp only [checkHeight,Bool.and_eq_true]
  constructor
  · exact check_leaf_14
  · apply List.all_eq_true.mpr
    intro k hk
    have hk : k<16 := List.mem_range.mp hk
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_h14_k0
    · exact check_h14_k1
    · exact check_h14_k2
    · exact check_h14_k3
    · exact check_h14_k4
    · exact check_h14_k5
    · exact check_h14_k6
    · exact check_h14_k7
    · exact check_h14_k8
    · exact check_h14_k9
    · exact check_h14_k10
    · exact check_h14_k11
    · exact check_h14_k12
    · exact check_h14_k13
    · exact check_h14_k14
    · exact check_h14_k15
end SiggolfPrefixTable

namespace SiggolfPrefixTable
open SiggolfPrefixCertificate
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

theorem checks_all (h : Nat) (hh : h≤14) : checkHeight h=true := by
  have hcases : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 ∨ h=9 ∨ h=10 ∨ h=11 ∨ h=12 ∨ h=13 ∨ h=14 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_height_0
  · exact check_height_1
  · exact check_height_2
  · exact check_height_3
  · exact check_height_4
  · exact check_height_5
  · exact check_height_6
  · exact check_height_7
  · exact check_height_8
  · exact check_height_9
  · exact check_height_10
  · exact check_height_11
  · exact check_height_12
  · exact check_height_13
  · exact check_height_14

theorem certificate : Certificate credit upper := certificate_of_checks checks_all

theorem bound_2413 {f c : Nat} (ht : Tree credit 14 15 f c) (hf : f≤117) :
    464+17*f-c≤2413 := cost_2413 certificate root_check ht hf

end SiggolfPrefixTable

namespace SiggolfPrefixSchedule
open SiggolfPrefixCertificate

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable (credit : Nat → Nat)

/-- A pending leaf or binary hash before the following unary run is emitted. -/
inductive PendingTree (credit : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | leaf : PendingTree credit 0 1 0 0
  | merge {h a b fl fr cl cr : Nat}
      (left : Tree credit h a fl cl) (right : Tree credit h b fr cr) :
      PendingTree credit (h+1) (a+b) (fl+fr) (cl+cr)

theorem PendingTree.fold {x k f c top : Nat} (ht : PendingTree credit x k f c)
    (hx : x ≤ top) : Tree credit top k (f+(top-x)) (c+credit (top-x)) := by
  cases ht with
  | leaf => simpa using Tree.leaf (credit := credit) top
  | @merge h a b fl fr cl cr left right =>
      have eh : top-(top-(h+1))-1 = h := by omega
      have hl : Tree credit (top-(top-(h+1))-1) a fl cl := by simpa [eh] using left
      have hr : Tree credit (top-(top-(h+1))-1) b fr cr := by simpa [eh] using right
      have q := Tree.fork top (top-(h+1)) a b fl fr cl cr (by omega) hl hr
      convert q using 1 <;> omega

structure Node where
  height : Nat
  leaves : Nat
  folds : Nat
  credits : Nat
  tree : Tree credit height leaves folds credits

def leafSum (stack : List (Node credit)) : Nat := (stack.map Node.leaves).sum
def foldSum (stack : List (Node credit)) : Nat := (stack.map Node.folds).sum
def creditSum (stack : List (Node credit)) : Nat := (stack.map Node.credits).sum

/-- Zero folds are allowed before a merge and at the end of a climb. -/
def Runs : Nat → List Nat → Nat → Prop
  | x, [], top => x ≤ top
  | x, y::ys, top => x ≤ y ∧ Runs (y+1) ys top

def climbCredit : Nat → List Nat → Nat → Nat
  | x, [], top => credit (top-x)
  | x, y::ys, top => credit (y-x) + climbCredit (y+1) ys top

theorem Runs.length_le {x top : Nat} {heights : List Nat}
    (hp : Runs x heights top) : x+heights.length ≤ top := by
  induction heights generalizing x with
  | nil => simpa [Runs] using hp
  | cons y ys ih =>
      obtain ⟨hxy,hp⟩ := hp
      have h := ih hp
      simp only [List.length_cons]
      omega

theorem runs_of_bounds (heights : List Nat) : ∀ x top,
    heights.Pairwise (· < ·) → (∀ y ∈ heights, x ≤ y ∧ y < top) → x ≤ top →
    Runs x heights top := by
  induction heights with
  | nil => intro x top _ _ hx; exact hx
  | cons y ys ih =>
      intro x top hs hb hx
      have hy := hb y (by simp)
      refine ⟨hy.1, ih (y+1) top (List.pairwise_cons.mp hs).2 ?_ (by omega)⟩
      intro z hz
      exact ⟨(List.pairwise_cons.mp hs).1 z hz, (hb z (by simp [hz])).2⟩

theorem climb (stack : List (Node credit)) : ∀ (x k f c top : Nat),
    PendingTree credit x k f c → Runs x (stack.map Node.height) top →
    ∃ total, Tree credit top (k+leafSum credit stack) total
      (c+creditSum credit stack+climbCredit credit x (stack.map Node.height) top) ∧
      total+x+stack.length = f+top+foldSum credit stack := by
  induction stack with
  | nil =>
      intro x k f c top ht hp
      have hx : x ≤ top := hp
      refine ⟨f+(top-x), ?_, ?_⟩
      · simpa [leafSum,creditSum,climbCredit] using ht.fold credit hx
      · simp only [List.length_nil,foldSum,List.map_nil,List.sum_nil]; omega
  | cons node rest ih =>
      intro x k f c top ht hp
      have hp' : x ≤ node.height ∧ Runs (node.height+1) (rest.map Node.height) top := hp
      have hcurrent := ht.fold credit hp'.1
      have hnext := PendingTree.merge node.tree hcurrent
      obtain ⟨total,htree,heq⟩ := ih (node.height+1) (node.leaves+k)
        (node.folds+(f+(node.height-x))) (node.credits+(c+credit (node.height-x)))
        top hnext hp'.2
      refine ⟨total, ?_, ?_⟩
      · have eleaves : node.leaves+k+leafSum credit rest = k+leafSum credit (node::rest) := by
          simp only [leafSum,List.map_cons,List.sum_cons]; omega
        have ecredit : node.credits+(c+credit (node.height-x))+creditSum credit rest+
              climbCredit credit (node.height+1) (rest.map Node.height) top =
            c+creditSum credit (node::rest)+climbCredit credit x ((node::rest).map Node.height) top := by
          simp only [creditSum,List.map_cons,List.sum_cons,climbCredit]; omega
        rwa [eleaves,ecredit] at htree
      · simp only [List.length_cons,foldSum,List.map_cons,List.sum_cons] at heq ⊢; omega

inductive Trace (credit : Nat → Nat) : List Nat → Nat → Nat → Nat → Nat → Prop
  | last (heights : List Nat) (top : Nat) (hp : Runs 0 heights top) :
      Trace credit heights 1 top (top-heights.length) (climbCredit credit 0 heights top)
  | next (lo hi : List Nat) (t n top f c : Nat) (hp : Runs 0 lo t)
      (tail : Trace credit (t::hi) n top f c) :
      Trace credit (lo++hi) (n+1) top ((t-lo.length)+f) (climbCredit credit 0 lo t+c)

theorem trace_tree {heights : List Nat} {n top f c : Nat}
    (ht : Trace credit heights n top f c) : ∀ stack : List (Node credit),
    stack.map Node.height = heights →
    Tree credit top (n+leafSum credit stack) (f+foldSum credit stack) (c+creditSum credit stack) := by
  induction ht with
  | last heights top hp =>
      intro stack hmap
      have hp' : Runs 0 (stack.map Node.height) top := by simpa [hmap] using hp
      obtain ⟨total,htree,heq⟩ := climb credit stack 0 1 0 0 top (PendingTree.leaf (credit := credit)) hp'
      have hlen : stack.length = heights.length := by
        have h := congrArg List.length hmap; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have e : total = top-heights.length+foldSum credit stack := by omega
      simpa only [e,hmap,Nat.zero_add,Nat.add_comm] using htree
  | next lo hi t n top f c hp tail ih =>
      intro stack hmap
      obtain ⟨low,high,hs,hl,hh⟩ := List.map_eq_append_iff.mp hmap
      subst stack
      have hp' : Runs 0 (low.map Node.height) t := by simpa [hl] using hp
      obtain ⟨total,htree,heq⟩ := climb credit low 0 1 0 0 t (PendingTree.leaf (credit := credit)) hp'
      let node : Node credit := ⟨t,1+leafSum credit low,total,
        creditSum credit low+climbCredit credit 0 (low.map Node.height) t,by simpa using htree⟩
      have hmap' : (node::high).map Node.height = t::hi := by simp only [List.map_cons,node,hh]
      have hresult := ih (node::high) hmap'
      have hlen : low.length = lo.length := by
        have h := congrArg List.length hl; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have etotal : total = t-lo.length+foldSum credit low := by omega
      have eleaves : n+leafSum credit (node::high) = (n+1)+leafSum credit (low++high) := by
        simp only [leafSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have efolds : f+foldSum credit (node::high) = (t-lo.length+f)+foldSum credit (low++high) := by
        simp only [foldSum] at etotal
        simp only [foldSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have ecredits : c+creditSum credit (node::high) =
          (climbCredit credit 0 lo t+c)+creditSum credit (low++high) := by
        simp only [creditSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node,hl]; omega
      rwa [eleaves,efolds,ecredits] at hresult

open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open SigGolfCandidate.Research.PorsPositiveBound

def scheduleCredit (ss : List ScheduleSegment) : Nat := (ss.map fun s => credit s.reads.length).sum

theorem climbSegs_credit (v x top : Nat) (L : List Nat) :
    scheduleCredit credit (climbSegs v x L top) = climbCredit credit x L top := by
  induction L generalizing x with
  | nil => simp [scheduleCredit,climbSegs,climbCredit,sibs]
  | cons y ys ih =>
      simp only [climbSegs,scheduleCredit,List.map_cons,List.sum_cons,sibs,
        List.length_map,List.length_range',climbCredit]
      exact congrArg (credit (y-x)+·) (ih (y+1))

theorem climbSegs_readSum_runs (v x top : Nat) (L : List Nat) (hp : Runs x L top) :
    readSum (climbSegs v x L top)+x+L.length = top := by
  induction L generalizing x with
  | nil =>
      have hx : x ≤ top := hp
      simp only [climbSegs,readSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        sibs,List.length_map,List.length_range',List.length_nil]
      omega
  | cons y ys ih =>
      obtain ⟨hxy,hp⟩ := hp
      have h := ih (y+1) hp
      simp only [climbSegs,readSum,List.map_cons,List.sum_cons,sibs,
        List.length_map,List.length_range',List.length_cons] at *
      omega

theorem allSegs_trace (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight) (hL : Pending v L) :
    Trace credit L (v::rest).length 14 (readSum (allSegs (v::rest) L))
      (scheduleCredit credit (allSegs (v::rest) L)) := by
  induction rest generalizing v L with
  | nil =>
      have hf : L.filter (· < ftsTreeHeight) = L := by
        apply List.filter_eq_self.mpr
        intro y hy
        simpa using (hL.2 y hy).1
      have he : allSegs [v] L = climbSegs v 0 L 14 := by
        change climbSegs v 0 (L.filter (· < ftsTreeHeight)) ftsTreeHeight ++ [] = _
        rw [hf,List.append_nil]
        rfl
      rw [he]
      have hr : Runs 0 L 14 := runs_of_bounds L 0 14 hL.1
        (fun y hy => ⟨Nat.zero_le y,(hL.2 y hy).1⟩) (by omega)
      have hsum := climbSegs_readSum_runs v 0 14 L hr
      have heq : readSum (climbSegs v 0 L 14) = 14-L.length := by omega
      simpa only [List.length_cons,List.length_nil,heq,climbSegs_credit] using Trace.last L 14 hr
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
      have hr : Runs 0 lo t := runs_of_bounds lo 0 t (hL.1.filter _)
        (fun y hy => ⟨Nat.zero_le y,(mem_filter_lt hy).2⟩) (Nat.zero_le _)
      have hsum := climbSegs_readSum_runs v 0 t lo hr
      have heq : readSum (climbSegs v 0 lo t) = t-lo.length := by omega
      have htrace := Trace.next lo hi t (w::rest).length 14
        (readSum (allSegs (w::rest) (t::hi)))
        (scheduleCredit credit (allSegs (w::rest) (t::hi))) hr ht
      rw [←hsplit] at htrace
      change Trace credit L ((v::w::rest).length) 14
        (readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)))
        (scheduleCredit credit (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)))
      have hread : readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) =
          (t-lo.length)+readSum (allSegs (w::rest) (t::hi)) := by
        simp only [readSum,List.map_append,List.sum_append] at heq ⊢
        rw [heq]
      have hcredit : scheduleCredit credit (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) =
          climbCredit credit 0 lo t+scheduleCredit credit (allSegs (w::rest) (t::hi)) := by
        simpa only [scheduleCredit,List.map_append,List.sum_append] using
          congrArg (fun n => n+scheduleCredit credit (allSegs (w::rest) (t::hi)))
            (climbSegs_credit credit v 0 t lo)
      rw [hread,hcredit]
      exact htrace

theorem schedule_tree (leaves : IndexGroup → FtsLeaf) (hinj : Function.Injective leaves) :
    Tree credit 14 15 (readSum (schedule (sortedLeaves leaves)))
      (scheduleCredit credit (schedule (sortedLeaves leaves))) := by
  obtain ⟨hlen,hs,hb⟩ := sortedLeaves_facts leaves hinj
  obtain ⟨v,rest,he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v,rest,rfl⟩
  rw [he] at hlen hs hb
  have hL : Pending v [] := ⟨List.Pairwise.nil,by simp⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (v::rest) [] := by
    have h := scheduleLeaves_eq rest v ⟨[],[],0,false,[],0⟩ [] hs hb hL rfl
    rw [schedule,he,h.1,List.nil_append]
  have ht := allSegs_trace credit v rest [] hs hb hL
  have htree := trace_tree credit ht [] rfl
  rw [hlen] at htree
  simpa only [hsch,leafSum,foldSum,creditSum,List.map_nil,List.sum_nil,Nat.add_zero,ftsOpenings] using htree

open OracleComp

theorem recoverRun_decodedFolds_eq (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    decodedFolds fts = (schedule (sortedLeaves leaves)).map (·.reads.length) := by
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hlen := schedule_length_of_injective leaves hadm.1
  have hm := (PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1
  apply List.ext_getElem
  · simp only [decodedFolds,List.length_ofFn,List.length_map,hlen]
  · intro i hi hj
    have hilt : i < ftsSegments := by simpa only [decodedFolds,List.length_ofFn] using hi
    have hil : i < (schedule (sortedLeaves leaves)).length := by omega
    have h := (hm ⟨i,hilt⟩).1
    simpa only [decodedFolds,List.getElem_ofFn,List.getElem_map,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hil,Option.getD_some] using h

/-- Every accepted PORS witness has a zero-inclusive tree with the exact decoded
fold total and exact total of any per-segment credit function. -/
theorem recoverRun_tree (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    Tree credit 14 15 r.folds (((decodedFolds fts).map credit).sum) := by
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have ht := schedule_tree credit leaves hadm.1
  have he := recoverRun_decodedFolds_eq f parameter index leaves fts r hrun
  have hc : scheduleCredit credit (schedule (sortedLeaves leaves)) =
      ((decodedFolds fts).map credit).sum := by
    rw [he,List.map_map]
    rfl
  have hf : readSum (schedule (sortedLeaves leaves)) = r.folds := by
    rw [readSum,←he]
    exact recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  rwa [hc,hf] at ht


end SiggolfPrefixSchedule

namespace SiggolfPrefixSubmissionBridge
open OracleComp SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open SigGolfCandidate.Research.PorsPositiveBound
open SiggolfPrefixCertificate

set_option maxHeartbeats 1000000

theorem recoverRun_exactSegmentsCost_2413_of
    (bound : ∀ {n c : Nat}, Tree SiggolfPrefixTable.credit 14 15 n c → n≤117 →
      464+17*n-c≤2413)
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    exactSegmentsCost (decodedFolds fts) ≤ 2413 := by
  have ht := SiggolfPrefixSchedule.recoverRun_tree SiggolfPrefixTable.credit
    f parameter index leaves fts r hrun
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hf : r.folds≤117 := by rw [hfolds]; exact hadm.2
  have hb := bound ht hf
  have hc := SigGolfCandidate.Research.PorsPrefixCredit.segmentsCost_add_credit (decodedFolds fts)
  rw [←exactSegmentsCost_prefix_eq] at hc
  have hsum := recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  have hlen : (decodedFolds fts).length=29 := by simp [decodedFolds,ftsSegments,ftsOpenings]
  rw [hsum,hlen] at hc
  have heq : SigGolfCandidate.Research.PorsPrefixCredit.totalCredit (decodedFolds fts) =
      ((decodedFolds fts).map SiggolfPrefixTable.credit).sum := rfl
  rw [heq] at hc
  omega

end SiggolfPrefixSubmissionBridge

namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete OracleComp

/-- The full compressed-tree topology gives forty cycles of segment credit
below the generic envelope for every accepted PORS witness. -/
theorem recoverRun_exactSegmentsCost (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    exactSegmentsCost (decodedFolds fts) ≤ 16*29 + 17*117 - 40 := by
  exact SiggolfPrefixSubmissionBridge.recoverRun_exactSegmentsCost_2413_of
    SiggolfPrefixTable.bound_2413 f parameter index leaves fts r hrun

end SigGolfCandidate.Research.PorsPositiveBound


namespace SiggolfNojoinFastBound
open SiggolfPrefixCertificate
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

def extra (a : Nat) : Nat := if 2≤a then 1 else 0

theorem scalar (a : Nat) (ha : a≤14) :
    a+SiggolfPrefixTable.credit a≤1+16*extra a := by
  unfold SiggolfPrefixTable.credit SiggolfPrefixTable.save extra
  split_ifs <;> omega

theorem total_scalar (as : List Nat) (ha : ∀ a∈as, a≤14) :
    as.sum+(as.map SiggolfPrefixTable.credit).sum≤as.length+16*(as.map extra).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have hs := scalar a (ha a (by simp))
    have ht := ih (fun b hb => ha b (by simp [hb]))
    simp only [List.sum_cons,List.map_cons,List.length_cons] at *
    omega

theorem root_small_credit : ∀ c : Fin 40,
    464+17*(SiggolfPrefixTable.upper 14 15 c.val-1)-c.val≤2397 := by decide +kernel

theorem nojoin_cost_2406
    (cert : Certificate SiggolfPrefixTable.credit SiggolfPrefixTable.upper)
    {n c e cost : Nat} (ht : Tree SiggolfPrefixTable.credit 14 15 n c)
    (hn : n≤117) (hscalar : n+c≤29+16*e)
    (hcost : cost+c+e≤464+17*n+1) : cost≤2406 := by
  by_cases hc : c≤39
  · have hb := ht.fold_bound cert (by omega) (by omega) hc
    have hr := root_small_credit ⟨c,by omega⟩
    simp only at hr
    omega
  · by_cases hlo : n≤116
    · omega
    · have he : n=117 := by omega
      omega

end SiggolfNojoinFastBound


namespace SiggolfNojoinCostBridge
open OracleComp SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open SigGolfCandidate.Research.PorsPositiveBound
open SiggolfPrefixCertificate
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def cheapSegment (a : Nat) : Nat := exactSegmentCost a - SiggolfNojoinFastBound.extra a
def cheapSegments (as : List Nat) : Nat := (as.map cheapSegment).sum

theorem cheapSegment_add_extra (a : Nat) :
    cheapSegment a + SiggolfNojoinFastBound.extra a = exactSegmentCost a := by
  unfold cheapSegment SiggolfNojoinFastBound.extra exactSegmentCost
  rw [SigGolfCandidate.Verify.prefixSave_eq]
  split_ifs <;> omega

theorem cheapSegments_add_extra (as : List Nat) :
    cheapSegments as + (as.map SiggolfNojoinFastBound.extra).sum = exactSegmentsCost as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have he := cheapSegment_add_extra a
    simp only [cheapSegments, List.map_cons, List.sum_cons, exactSegmentsCost_cons] at *
    omega

theorem accepted_lengths (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    ∀ a∈decodedFolds fts, a≤14 := by
  obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  have hclimb : ∀ (L : List Nat) (v x top : Nat), top ≤ 14 →
      (∀ y ∈ L, y ≤ 14) → ∀ seg ∈ climbSegs v x L top, seg.reads.length ≤ 14 := by
    intro L
    induction L with
    | nil =>
        intro v x top ht hL seg hs
        simp only [climbSegs, List.mem_singleton] at hs
        subst seg
        simp only [sibs, List.length_map, List.length_range']
        omega
    | cons y L ih =>
        intro v x top ht hL seg hs
        simp only [climbSegs, List.mem_cons] at hs
        rcases hs with rfl | hs
        · have hy := hL y (by simp)
          simp only [sibs, List.length_map, List.length_range']
          omega
        · exact ih v (y+1) top ht (fun z hz => hL z (by simp [hz])) seg hs
  have hall : ∀ (vs : List Nat), (∀ v ∈ vs, v < 2^ftsTreeHeight) →
      ∀ (L : List Nat) seg, seg ∈ allSegs vs L → seg.reads.length ≤ 14 := by
    intro vs
    induction vs with
    | nil => intro hv L seg hs; simp [allSegs] at hs
    | cons v rest ih =>
        intro hv L seg hs
        have htop : leafTop v rest ≤ 14 := by
          cases rest with
          | nil => simp [leafTop, ftsTreeHeight]
          | cons w rest =>
              have hh := bitLength_xor_le v w (hv v (by simp)) (hv w (by simp))
              simp only [leafTop]
              change bitLength (v ^^^ w) ≤ 14 at hh
              omega
        rw [allSegs_cons] at hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hclimb _ v 0 _ htop (fun y hy => by
            have hh := (mem_filter_lt hy).2
            omega) seg hs
        · exact ih (fun w hw => hv w (by simp [hw])) _ seg hs
  obtain ⟨hlen, hsorted', hbound⟩ := sortedLeaves_facts leaves hadm.1
  obtain ⟨v, rest, he⟩ : ∃ v rest, sortedLeaves leaves = v::rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  have hsch : schedule (sortedLeaves leaves) = allSegs (sortedLeaves leaves) [] := by
    rw [he] at hsorted' hbound ⊢
    have hh := scheduleLeaves_eq rest v ⟨[], [], 0, false, [], 0⟩ [] hsorted' hbound
      ⟨List.Pairwise.nil, by simp⟩ rfl
    simpa only [schedule, List.nil_append] using hh.1
  have hmatch := ((PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1 j).1
  rw [hmatch]
  have hlen' := schedule_length_of_injective leaves hadm.1
  have hj : j.val < (schedule (sortedLeaves leaves)).length := by rw [hlen']; exact j.isLt
  have hmem : (schedule (sortedLeaves leaves)).getD j.val default ∈ schedule (sortedLeaves leaves) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      using List.getElem_mem hj
  rw [hsch] at hmem ⊢
  exact hall (sortedLeaves leaves) (sortedLeaves_lt leaves) [] _ hmem

theorem recoverRun_cheapSegments (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    cheapSegments (decodedFolds fts) + 1 ≤ 2406 := by
  have ht := SiggolfPrefixSchedule.recoverRun_tree SiggolfPrefixTable.credit
    f parameter index leaves fts r hrun
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hf : r.folds≤117 := by rw [hfolds]; exact hadm.2
  have hs := SiggolfNojoinFastBound.total_scalar (decodedFolds fts)
    (accepted_lengths f parameter index leaves fts r hrun)
  have hc := SigGolfCandidate.Research.PorsPrefixCredit.segmentsCost_add_credit (decodedFolds fts)
  rw [←exactSegmentsCost_prefix_eq] at hc
  have hsum := recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  have hlen : (decodedFolds fts).length=29 := by simp [decodedFolds,ftsSegments,ftsOpenings]
  rw [hsum,hlen] at hc hs
  have heq : SigGolfCandidate.Research.PorsPrefixCredit.totalCredit (decodedFolds fts) =
      ((decodedFolds fts).map SiggolfPrefixTable.credit).sum := rfl
  rw [heq] at hc
  have he := cheapSegments_add_extra (decodedFolds fts)
  exact SiggolfNojoinFastBound.nojoin_cost_2406 SiggolfPrefixTable.certificate ht hf hs (by omega)

end SiggolfNojoinCostBridge

/-! ## PorsExactMachine -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem seg_step_exact (P : PCtx) (_hP : P.ok) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) (h : DispIn P s0 s x c ptr E folds pend node stk m) :
    (14 < wbyte P.wl ptr % 16 → ∃ u, Steps image m 8 8 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (1 ≤ wbyte P.wl ptr % 16 → wbyte P.wl ptr % 16 ≤ 14 → segBits (wbyte P.wl ptr) ≠ E % 8 →
        ∃ u, Steps image m 11 11 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (wbyte P.wl ptr % 16 ≤ 14 → (wbyte P.wl ptr % 16 = 0 ∨ segBits (wbyte P.wl ptr) = E % 8) →
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
  have hc18 : c < 226 := by rcases h.copy with ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> omega
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
  have hbits : segBits b < 8 := by unfold segBits; omega
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
        exact (parBr_holds hE1 _ hbits true).mpr (by simp [Ne.symm hne])) (by simp)
    refine ⟨u, (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, tabRej, rejSpec])
        (by simp [dispSpec, tabRej, rejSpec]),
      hu.ecall (by simp [tabRej, rejSpec]), hu.regs (.x5, cw 1) (by simp [tabRej, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [tabRej, rejSpec])⟩
  · intro ha hpar
    have ha' : ¬ segA b > 14 := by unfold segA; omega
    have hsp : tabSpec (tsel s) b = ⟨[(.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))),
        (.x12, if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b))], [],
        if b % 16 = 0 then entry0Pc (segV (tsel s) b) + 1 else slotPc (tsel s) b + 4,
        true, if b % 16 = 0 then 3 else 4, if b % 16 = 0 then [] else [parBr (segBits b) false], none,
        if b % 16 = 0 then 3 else 4⟩ := by
      unfold tabSpec; rw [if_neg ha']; rfl
    obtain ⟨u, hu⟩ := pspec_run (cOk (by unfold segA; omega)) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by
        rw [hsp]; intro br hbr
        by_cases h0 : b % 16 = 0
        · simp [h0] at hbr
        · simp only [if_neg h0, List.mem_singleton] at hbr; subst hbr
          exact (parBr_holds hE1 _ hbits false).mpr (by
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
        by unfold tailCopies; split_ifs <;> decide, segV_lt _ _, hV1⟩
      · rw [writeHash_pc, hu.pc (by rw [hsp]), hsp]
        simp only [if_pos h0, tailPc, show (2:Nat)<3 by decide, if_true]
        simpa only [Nat.add_assoc, Nat.reduceAdd] using pcOf_add4 (entry0Pc (segV (tsel s) b)+1)
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
        ⟨h1, by omega⟩, ht, segV_lt _ _, hV1, by
          rcases hpar with hh | hh
          · exact False.elim (by omega)
          · exact hh.symm⟩
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
    (hA : ∀ V a, V < 3 → a ≤ 14 → V = segV (tsel s) (wbyte P.wl ptr) → a = wbyte P.wl ptr % 16 → folds + a ≤ 117 →
      (if a = 0 then 15 else 16+17*a-segmentSave V a) + AT V (folds + a) ≤ A)
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
  by_cases hp : 0 < b % 16 ∧ b / 32 ≠ E % 8
  · rw [if_pos hp, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hpar (by omega) ha14 hp.2
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hp, cc_bind, pendingHash_eq]
    have hpar' : b % 16 = 0 ∨ segBits b = E % 8 := by unfold segBits; omega
    obtain ⟨k, u, hkeq, hst, hf, h5, hv, hin, hbl, hpost⟩ := hacc ha14 hpar'
    have hk : k ≤ 8 := by rw [hkeq]; split_ifs <;> omega
    have hVl := segV_lt (tsel s) b
    set a := b % 16 with hadef
    set V := segV (tsel s) b with hV
    -- after the pending hash
    have H : ∀ ans, GoodQ (writeHash u ans) (NT V + 17 * 14 + 2) (CT V + 17 * a) (folds + a ≤ 117) (AT V (folds + a) + (17 * a - segmentSave V a))
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
        simp only [ha0, segmentSave, noJoin, prefixSave, Nat.reduceLT, if_true, Nat.mul_zero, Nat.sub_self, Nat.add_zero]
        exact this.mono (by omega) (by omega) (fun q => ⟨by omega, by omega⟩)
      · have hE := (hpost ans).2 (by omega)
        obtain ⟨u2, hst2, hP2⟩ := ent_step P s0 s x V (segT b) a ptr E folds (answerBytes 16 ans) stk _ hE
        rw [segFolds_eq, List.range_eq_range']
        have := folds_good P s0 s x V a ptr folds stk
          (fun p => match p with
            | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1))))
          (NT V) (CT V) (AT V (folds + a)) (folds + a ≤ 117)
          (fun t node' E' u' hT => hK a V t E' node' u' ha14 rfl rfl hT) a 0 (segT b) E (answerBytes 16 ans)
          u2 (by omega) hP2 hP2.parity
        have hstart := foldBudget_start V a (by omega)
        have hsave : segmentSave V a ≤ 4 := by
          unfold segmentSave; rw [prefixSave_eq]; split_ifs <;> omega
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
        have hbudget := hA V a hVl ha14 rfl rfl q
        change k = 4 + (if a = 0 then 3 else 4) at hkeq
        by_cases hz : a = 0
        · simp only [if_pos hz] at hbudget hkeq; omega
        · simp only [if_neg hz] at hbudget hkeq
          have hsave : segmentSave V a ≤ 4 := by
            unfold segmentSave; rw [prefixSave_eq]; split_ifs <;> omega
          omega⟩)

end SigGolfCandidate.Verify

/-! ## PorsExactComposition -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp
open SigGolfCandidate.Research.PorsPositiveBound

open SiggolfNojoinCostBridge
def decodedFold (wl : List Byte) (j : Nat) : Nat := wbyte wl (Equiv.segPtr wl j) % 16
def decodedCostFrom (wl : List Byte) (j n : Nat) : Nat :=
  ((List.range' j n).map fun k => cheapSegment (decodedFold wl k)).sum
def decodedCostRem (wl : List Byte) (j : Nat) : Nat := decodedCostFrom wl j (29-j) + 1

theorem decodedCostFrom_succ (wl : List Byte) (j n : Nat) :
    decodedCostFrom wl j (n+1) = cheapSegment (decodedFold wl j) + decodedCostFrom wl (j+1) n := by
  simp [decodedCostFrom, List.range'_succ]

theorem decodedCostRem_succ (wl : List Byte) (j : Nat) (hj : j < 29) :
    decodedCostRem wl j = cheapSegment (decodedFold wl j) + decodedCostRem wl (j+1) := by
  unfold decodedCostRem
  have h : 29-j = (29-(j+1))+1 := by omega
  rw [h, decodedCostFrom_succ]
  omega

theorem cheapSegment_ge (a : Nat) : 15 ≤ cheapSegment a := by
  unfold cheapSegment exactSegmentCost SiggolfNojoinFastBound.extra
  rw [Verify.prefixSave_eq]
  split_ifs <;> omega

theorem decodedCostRem_ge (wl : List Byte) (j : Nat) (hj : j < 29) :
    15 ≤ decodedCostRem wl j := by
  rw [decodedCostRem_succ wl j hj]
  have := cheapSegment_ge (decodedFold wl j)
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
    (∀ a, a = decodedFold wl (2*s-d) → cheapSegment a + AexactM wl s d ≤ Aexact wl s d) ∧
    (∀ a, a = decodedFold wl (2*s-d) →
      (if s=14 then exactSegmentCost a else cheapSegment a) + AexactPF wl s d ≤ Aexact wl s d) ∧
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
    · have he := cheapSegment_add_extra (decodedFold wl (2*s-d))
      have hx : SiggolfNojoinFastBound.extra (decodedFold wl (2*s-d)) ≤ 1 := by unfold SiggolfNojoinFastBound.extra; split_ifs <;> omega
      have hrem : 1 ≤ decodedCostRem wl (2*s-d+1) := by unfold decodedCostRem; omega
      simp only [AexactPF, if_pos h14, Aexact]
      omega
    · have he : 2*(s+1)-(d+1) = 2*s-d+1 := by omega
      have hl := lrest_succ s (by omega)
      simp only [AexactPF, if_neg h14, Aexact, he]
      omega
  · unfold Aexact; omega


theorem machineSegmentCost_M (a : Nat) :
    (if a=0 then 15 else 16+17*a-segmentSave 0 a) = cheapSegment a := by
  unfold cheapSegment exactSegmentCost segmentSave noJoin SiggolfNojoinFastBound.extra
  rw [prefixSave_eq]
  simp only [show (0 : Nat) < 2 by decide, true_and]
  split_ifs <;> omega

theorem machineSegmentCost_PF (s a : Nat) :
    (if a=0 then 15 else 16+17*a-segmentSave (if s=14 then 2 else 1) a) =
      (if s=14 then exactSegmentCost a else cheapSegment a) := by
  unfold cheapSegment exactSegmentCost segmentSave noJoin SiggolfNojoinFastBound.extra
  rw [prefixSave_eq]
  split_ifs <;> omega

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
      (fun V a _ ha hV haw hF => by
        have he : a = decodedFold P.wl (2*s-0) := by unfold decodedFold; rw [← hptr]; exact haw
        by_cases h0 : V=0
        · simp only [h0, if_pos rfl]
          rw [machineSegmentCost_M]
          exact bAMX a he
        · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ h0)
          simp only [if_neg h0]
          rw [hV, hVe, machineSegmentCost_PF]
          exact bAPFX a he)
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
      (fun V a _ ha hV haw hF => by
        have he : a = decodedFold P.wl (2*s-(rest.length+1)) := by unfold decodedFold; rw [← hptr]; exact haw
        by_cases h0 : V=0
        · simp only [h0, if_pos rfl]
          rw [machineSegmentCost_M]
          exact bAMX a he
        · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ h0)
          simp only [if_neg h0]
          rw [hV, hVe, machineSegmentCost_PF]
          exact bAPFX a he)
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

def cycleBoundDecoded (wl : List Byte) : Nat := 451 + layC + decodedCostRem wl 0

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
    have H : ∀ a, GoodQ (writeHash t a) (101 + (leafCost 0 + Nseg 0 0)) (101 + (leafCost 0 + Cseg 0 0)) True
        (101 + (leafCost 0 + Aexact wl 0 0))
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
open OracleComp SiggolfNojoinCostBridge

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem decodedCostRem_eq (wl : List Byte) :
    decodedCostRem wl 0 = cheapSegments (decodedFolds (witFts wl)) + 1 := by
  unfold decodedCostRem decodedCostFrom cheapSegments
  congr 1

/-- Every accepted reference PORS computation has exact segment cost below the
former uniform envelope. This statement is independent of sampled executions. -/
theorem porsRoot_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (index : Index) (wl : List Byte) (hl : wl.length = 16384)
    (leaves : IndexGroup → FtsLeaf) (node : Ref.Val)
    (hrun : evalWithAnswerFn hash
      (Ref.porsRoot index (List.ofFn fun r => (leaves r).val) wl) = some node) :
    decodedCostRem wl 0 ≤ 16*29 + 17*117 - 47 := by
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
      exact recoverRun_cheapSegments f 0 index leaves (witFts wl) r hr

theorem verifyList_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (ml pkl wl : List Byte) (hl : wl.length = 16384)
    (hverify : evalWithAnswerFn hash (Ref.verifyList ml pkl wl) = true) :
    decodedCostRem wl 0 ≤ 16*29 + 17*117 - 47 := by
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
    GoodQ s fuelBound cycleBoundAll True (cycleBound-47) (cc (verifyList ml pkl wl) Kb) := by
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
    GoodQ s fuelBound cycleBoundAll True (cycleBound-47)
      (cc (verifyRef input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  exact main_good_tight _ _ _ (length_toList m) (length_toList pk) (length_toList w) s (init_ok m pk w s hs)

/-- Every accepting execution of the verifier takes47 fewer cycles than
its generic bound. This is universal over hash answers and arbitrary witnesses. -/
theorem verify_accept_cycles_tight (hash : Hash)
    (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ cycleBound-47 := by
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
