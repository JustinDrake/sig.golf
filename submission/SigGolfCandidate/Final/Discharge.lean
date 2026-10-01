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


/-! Root-aware accepted-schedule potential for the no-join copied-prefix design.
The separate root weight charges its retained join and the long-descriptor check.
This arithmetic certificate is connected to the exact machine cost below. -/
namespace SigGolfCandidate.Research.NoJoin

set_option Elab.async false
namespace GeneralTreeProbe
open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness

/-- Zero-length unary runs are allowed; every tree node emits one segment. -/
inductive Tree (weight : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | leaf (h : Nat) : Tree weight h 1 h (weight h)
  | fork (h k j a l r lc rc : Nat) (hj : j < h) (ha : 1 ≤ a) (hak : a < k)
      (left : Tree weight (h-j-1) a l lc)
      (right : Tree weight (h-j-1) (k-a) r rc) :
      Tree weight h k (j+l+r) (weight j+lc+rc)

inductive PendingTree (weight : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
  | leaf : PendingTree weight 0 1 0 0
  | merge {h a b l r lc rc : Nat} (left : Tree weight h a l lc)
      (right : Tree weight h b r rc) : PendingTree weight (h+1) (a+b) (l+r) (lc+rc)

theorem Tree.leaves_pos {w h k f c} (ht : Tree w h k f c) : 0 < k := by
  cases ht <;> omega

theorem Tree.leaves_le {w h k f c} (ht : Tree w h k f c) : k ≤ 2^h := by
  induction ht with
  | leaf h => exact Nat.one_le_pow h 2 (by decide)
  | fork h k j a l r lc rc hj ha hak left right ihl ihr =>
      have hm : h-j-1+1 ≤ h := by omega
      have hp : 2^(h-j-1)+2^(h-j-1) ≤ 2^h := by
        calc
          _ = 2^(h-j-1+1) := by rw [pow_succ]; omega
          _ ≤ _ := Nat.pow_le_pow_right (by decide) hm
      omega

theorem PendingTree.fold {w x k f c top} (ht : PendingTree w x k f c) (hx : x ≤ top) :
    Tree w top k (f+(top-x)) (c+w (top-x)) := by
  cases ht with
  | leaf => simpa using Tree.leaf (weight := w) top
  | @merge h a b l r lc rc left right =>
      have ha := left.leaves_pos
      have hb := right.leaves_pos
      have eh : top-(top-(h+1))-1 = h := by omega
      have hl : Tree w (top-(top-(h+1))-1) a l lc := by simpa [eh] using left
      have hr : Tree w (top-(top-(h+1))-1) ((a+b)-a) r rc := by
        simpa [eh, Nat.add_sub_cancel_left] using right
      have q := Tree.fork top (a+b) (top-(h+1)) a l r lc rc (by omega) (by omega) (by omega) hl hr
      convert q using 1 <;> omega

structure Node (weight : Nat → Nat) where
  height : Nat
  leaves : Nat
  folds : Nat
  credit : Nat
  tree : Tree weight height leaves folds credit

def leafSum {w} (stack : List (Node w)) : Nat := (stack.map Node.leaves).sum
def foldSum {w} (stack : List (Node w)) : Nat := (stack.map Node.folds).sum
def creditSum {w} (stack : List (Node w)) : Nat := (stack.map Node.credit).sum

def Runs : Nat → List Nat → Nat → Prop
  | x, [], top => x ≤ top
  | x, y::ys, top => x ≤ y ∧ Runs (y+1) ys top

def runWeight (w : Nat → Nat) : Nat → List Nat → Nat → Nat
  | x, [], top => w (top-x)
  | x, y::ys, top => w (y-x)+runWeight w (y+1) ys top

theorem runs_of_order (L : List Nat) (x top : Nat) (hs : L.Pairwise (· < ·))
    (hb : ∀ y ∈ L, x ≤ y ∧ y < top) (hx : x ≤ top) : Runs x L top := by
  induction L generalizing x with
  | nil => exact hx
  | cons y ys ih =>
      obtain ⟨hxy, hyt⟩ := hb y (by simp)
      refine ⟨hxy, ih (y+1) (List.pairwise_cons.mp hs).2 ?_ (by omega)⟩
      intro z hz
      have hyz := (List.pairwise_cons.mp hs).1 z hz
      have hzt := (hb z (by simp [hz])).2
      omega

theorem Runs.length_le {x top : Nat} {heights : List Nat}
    (hp : Runs x heights top) : x+heights.length ≤ top := by
  induction heights generalizing x with
  | nil => simpa [Runs] using hp
  | cons y ys ih =>
      obtain ⟨hxy,hp⟩ := hp
      have h := ih hp
      simp only [List.length_cons]
      omega

theorem climb {w} (stack : List (Node w)) : ∀ x k f c top,
    PendingTree w x k f c → Runs x (stack.map Node.height) top →
    ∃ total cost, Tree w top (k+leafSum stack) total cost ∧
      total+x+stack.length = f+top+foldSum stack ∧
      cost = c+creditSum stack+runWeight w x (stack.map Node.height) top := by
  induction stack with
  | nil =>
      intro x k f c top ht hp
      have hx : x ≤ top := hp
      refine ⟨f+(top-x), c+w (top-x), ?_, ?_, ?_⟩
      · simpa [leafSum] using ht.fold hx
      · simp only [List.length_nil, foldSum, List.map_nil, List.sum_nil]; omega
      · simp [creditSum, runWeight]
  | cons node rest ih =>
      intro x k f c top ht hp
      have hp' : x ≤ node.height ∧ Runs (node.height+1) (rest.map Node.height) top := hp
      have hcurrent := ht.fold hp'.1
      have hnext := PendingTree.merge node.tree hcurrent
      obtain ⟨total,cost,htree,heq,hcost⟩ := ih (node.height+1) (node.leaves+k)
        (node.folds+(f+(node.height-x))) (node.credit+(c+w (node.height-x))) top hnext hp'.2
      refine ⟨total,cost,?_,?_,?_⟩
      · have e : node.leaves+k+leafSum rest = k+leafSum (node::rest) := by
          simp only [leafSum,List.map_cons,List.sum_cons]; omega
        rwa [e] at htree
      · simp only [List.length_cons,foldSum,List.map_cons,List.sum_cons] at heq ⊢; omega
      · simp only [creditSum,List.map_cons,List.sum_cons,runWeight] at hcost ⊢; omega

inductive Trace (w : Nat → Nat) : List Nat → Nat → Nat → Nat → Nat → Prop
  | last (heights : List Nat) (top : Nat) (hp : Runs 0 heights top) :
      Trace w heights 1 top (top-heights.length) (runWeight w 0 heights top)
  | next (lo hi : List Nat) (t n top f c : Nat) (hp : Runs 0 lo t)
      (tail : Trace w (t::hi) n top f c) :
      Trace w (lo++hi) (n+1) top ((t-lo.length)+f) (runWeight w 0 lo t+c)

theorem trace_tree {w heights n top f c} (ht : Trace w heights n top f c) :
    ∀ stack : List (Node w), stack.map Node.height = heights →
      Tree w top (n+leafSum stack) (f+foldSum stack) (c+creditSum stack) := by
  induction ht with
  | last heights top hp =>
      intro stack hmap
      have hp' : Runs 0 (stack.map Node.height) top := by simpa [hmap] using hp
      obtain ⟨total,cost,htree,heq,hcost⟩ := climb stack 0 1 0 0 top PendingTree.leaf hp'
      have hlen : stack.length = heights.length := by
        have h := congrArg List.length hmap; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have e : total = top-heights.length+foldSum stack := by omega
      have ec : cost = runWeight w 0 heights top+creditSum stack := by rw [hmap] at hcost; omega
      simpa only [e,ec] using htree
  | next lo hi t n top f c hp tail ih =>
      intro stack hmap
      obtain ⟨low,high,hs,hl,hh⟩ := List.map_eq_append_iff.mp hmap
      subst stack
      have hp' : Runs 0 (low.map Node.height) t := by simpa [hl] using hp
      obtain ⟨total,cost,htree,heq,hcost⟩ := climb low 0 1 0 0 t PendingTree.leaf hp'
      let node : Node w := ⟨t,1+leafSum low,total,cost,htree⟩
      have hmap' : (node::high).map Node.height = t::hi := by simp only [List.map_cons,node,hh]
      have hresult := ih (node::high) hmap'
      have hlen : low.length = lo.length := by
        have h := congrArg List.length hl; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have etotal : total = t-lo.length+foldSum low := by omega
      have ecost : cost = runWeight w 0 lo t+creditSum low := by rw [hl] at hcost; omega
      have eleaves : n+leafSum (node::high) = (n+1)+leafSum (low++high) := by
        simp only [leafSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have efolds : f+foldSum (node::high) = (t-lo.length+f)+foldSum (low++high) := by
        simp only [foldSum] at etotal
        simp only [foldSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have ec : c+creditSum (node::high) = (runWeight w 0 lo t+c)+creditSum (low++high) := by
        simp only [creditSum] at ecost
        simp only [creditSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      rwa [eleaves,efolds,ec] at hresult

def readSum (ss : List ScheduleSegment) : Nat := (ss.map (·.reads.length)).sum
def weightSum (w : Nat → Nat) (ss : List ScheduleSegment) : Nat := (ss.map (fun s => w s.reads.length)).sum

theorem climbSegs_readSum (v x top : Nat) (L : List Nat) (hp : Runs x L top) :
    readSum (climbSegs v x L top)+x+L.length=top := by
  induction L generalizing x with
  | nil =>
      have hx : x ≤ top := hp
      simp only [climbSegs,readSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        sibs,List.length_map,List.length_range',List.length_nil]; omega
  | cons y L ih =>
      obtain ⟨hxy,hp⟩ := hp
      have h := ih (y+1) hp
      simp only [climbSegs,readSum,List.map_cons,List.sum_cons,sibs,List.length_map,
        List.length_range',List.length_cons] at *; omega

theorem climbSegs_weightSum (w : Nat → Nat) (v x top : Nat) (L : List Nat) :
    weightSum w (climbSegs v x L top)=runWeight w x L top := by
  induction L generalizing x with
  | nil => simp [weightSum,climbSegs,sibs,runWeight]
  | cons y L ih => simpa [weightSum,climbSegs,sibs,runWeight] using ih (y+1)

theorem allSegs_trace (wgt : Nat → Nat) (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight) (hL : Pending v L) :
    Trace wgt L (v::rest).length 14 (readSum (allSegs (v::rest) L))
      (weightSum wgt (allSegs (v::rest) L)) := by
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
      have hr : Runs 0 L 14 := runs_of_order L 0 14 hL.1
        (fun y hy => ⟨Nat.zero_le _, (hL.2 y hy).1⟩) (by omega)
      have hsum := climbSegs_readSum v 0 14 L hr
      have heq : readSum (climbSegs v 0 L 14) = 14-L.length := by omega
      simpa only [List.length_cons,List.length_nil,heq,climbSegs_weightSum] using Trace.last (w := wgt) L 14 hr
  | cons next rest ih =>
      let t := leafTop v (next::rest)
      let lo := L.filter (· < t)
      let hi := L.filter (t < ·)
      have hsplit : L = lo++hi := pending_split hL hs hb
      have hn : Pending next (t::hi) :=
        (pending_next ((List.pairwise_cons.mp hs).1 next (by simp))
          (hb next (by simp)) (by rfl) hL).1
      have ht := ih next (t::hi) (List.pairwise_cons.mp hs).2
        (fun z hz => hb z (List.mem_cons_of_mem v hz)) hn
      have hr : Runs 0 lo t := by
        apply runs_of_order lo 0 t (hL.1.filter _) ?_ (Nat.zero_le _)
        intro y hy
        exact ⟨Nat.zero_le _,(mem_filter_lt hy).2⟩
      have hsum := climbSegs_readSum v 0 t lo hr
      have heq : readSum (climbSegs v 0 lo t) = t-lo.length := by omega
      have htrace := Trace.next lo hi t (next::rest).length 14
        (readSum (allSegs (next::rest) (t::hi)))
        (weightSum wgt (allSegs (next::rest) (t::hi))) hr ht
      rw [←hsplit] at htrace
      change Trace wgt L (v::next::rest).length 14
        (readSum (climbSegs v 0 lo t ++ allSegs (next::rest) (t::hi)))
        (weightSum wgt (climbSegs v 0 lo t ++ allSegs (next::rest) (t::hi)))
      have rs : ∀ a b, readSum (a++b) = readSum a+readSum b := by
        intros; simp [readSum]
      have ws : ∀ a b, weightSum wgt (a++b) = weightSum wgt a+weightSum wgt b := by
        intros; simp [weightSum]
      rw [rs,ws,heq,climbSegs_weightSum]
      exact htrace

theorem schedule_tree (weight : Nat → Nat) (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves) :
    Tree weight 14 15 (readSum (schedule (sortedLeaves leaves)))
      (weightSum weight (schedule (sortedLeaves leaves))) := by
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
  rw [hsch]
  have ht := allSegs_trace weight v rest [] hs hb hL
  rw [hlen] at ht
  have hh := trace_tree ht [] rfl
  simpa only [leafSum,foldSum,creditSum,List.map_nil,List.sum_nil,Nat.add_zero,ftsOpenings] using hh

open OracleComp

def decodedFolds (fts : FtsSignature) : List Nat :=
  List.ofFn fun j : Fin ftsSegments => (fts.segments j).folds.val

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

theorem recover_tree (weight : Nat → Nat) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    Tree weight 14 15 (decodedFolds fts).sum ((decodedFolds fts).map weight).sum := by
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hlen := schedule_length_of_injective leaves hadm.1
  have hm := (PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1
  have he : decodedFolds fts = (schedule (sortedLeaves leaves)).map (·.reads.length) := by
    apply List.ext_getElem
    · simp only [decodedFolds,List.length_ofFn,List.length_map,hlen]
    · intro i hi hj
      have hilt : i < ftsSegments := by simpa only [decodedFolds,List.length_ofFn] using hi
      have hil : i < (schedule (sortedLeaves leaves)).length := by omega
      have h := (hm ⟨i,hilt⟩).1
      simpa only [decodedFolds,List.getElem_ofFn,List.getElem_map,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hil,Option.getD_some] using h
  rw [he]
  simpa only [readSum,weightSum,List.map_map,Function.comp_def] using schedule_tree weight leaves hadm.1

end GeneralTreeProbe

set_option Elab.async false
namespace AdjustedPotential
set_option maxRecDepth 10000
set_option maxHeartbeats 0
 def credit (j : Nat) : Nat := if j=0 ∨ 3≤j then 1 else 0
def row0 (k : Nat) : Int := match k with
 | 1 => -4
 | _ => 0
def row1 (k : Nat) : Int := match k with
 | 1 => 1
 | 2 => -12
 | _ => 0
def row2 (k : Nat) : Int := match k with
 | 1 => 2
 | 2 => -2
 | 3 => -15
 | 4 => -28
 | _ => 0
def row3 (k : Nat) : Int := match k with
 | 1 => -1
 | 2 => 3
 | 3 => -4
 | 4 => -8
 | 5 => -21
 | 6 => -34
 | 7 => -47
 | 8 => -60
 | _ => 0
def row4 (k : Nat) : Int := match k with
 | 1 => 0
 | 2 => 5
 | 3 => 1
 | 4 => 2
 | 5 => -5
 | 6 => -9
 | 7 => -16
 | 8 => -20
 | 9 => -33
 | 10 => -46
 | 11 => -59
 | 12 => -72
 | 13 => -85
 | 14 => -98
 | 15 => -111
 | _ => 0
def row5 (k : Nat) : Int := match k with
 | 1 => 1
 | 2 => 6
 | 3 => 3
 | 4 => 7
 | 5 => 2
 | 6 => 3
 | 7 => -1
 | 8 => 0
 | 9 => -7
 | 10 => -11
 | 11 => -18
 | 12 => -22
 | 13 => -29
 | 14 => -33
 | 15 => -40
 | _ => 0
def row6 (k : Nat) : Int := match k with
 | 1 => 2
 | 2 => 3
 | 3 => 6
 | 4 => 11
 | 5 => 7
 | 6 => 9
 | 7 => 6
 | 8 => 10
 | 9 => 5
 | 10 => 6
 | 11 => 2
 | 12 => 3
 | 13 => -2
 | 14 => -1
 | 15 => -5
 | _ => 0
def row7 (k : Nat) : Int := match k with
 | 1 => 3
 | 2 => 4
 | 3 => 8
 | 4 => 13
 | 5 => 10
 | 6 => 14
 | 7 => 13
 | 8 => 18
 | 9 => 14
 | 10 => 16
 | 11 => 13
 | 12 => 17
 | 13 => 13
 | 14 => 15
 | 15 => 12
 | _ => 0
def row8 (k : Nat) : Int := match k with
 | 1 => 4
 | 2 => 5
 | 3 => 9
 | 4 => 14
 | 5 => 14
 | 6 => 15
 | 7 => 18
 | 8 => 23
 | 9 => 19
 | 10 => 23
 | 11 => 22
 | 12 => 27
 | 13 => 24
 | 14 => 28
 | 15 => 27
 | _ => 0
def row9 (k : Nat) : Int := match k with
 | 1 => 5
 | 2 => 7
 | 3 => 8
 | 4 => 12
 | 5 => 17
 | 6 => 18
 | 7 => 22
 | 8 => 27
 | 9 => 24
 | 10 => 28
 | 11 => 28
 | 12 => 33
 | 13 => 33
 | 14 => 34
 | 15 => 37
 | _ => 0
def row10 (k : Nat) : Int := match k with
 | 1 => 6
 | 2 => 9
 | 3 => 10
 | 4 => 14
 | 5 => 19
 | 6 => 20
 | 7 => 24
 | 8 => 29
 | 9 => 29
 | 10 => 30
 | 11 => 33
 | 12 => 38
 | 13 => 40
 | 14 => 41
 | 15 => 45
 | _ => 0
def row11 (k : Nat) : Int := match k with
 | 1 => 7
 | 2 => 11
 | 3 => 13
 | 4 => 15
 | 5 => 20
 | 6 => 23
 | 7 => 25
 | 8 => 30
 | 9 => 33
 | 10 => 35
 | 11 => 36
 | 12 => 40
 | 13 => 45
 | 14 => 46
 | 15 => 50
 | _ => 0
def row12 (k : Nat) : Int := match k with
 | 1 => 8
 | 2 => 13
 | 3 => 16
 | 4 => 19
 | 5 => 21
 | 6 => 26
 | 7 => 29
 | 8 => 31
 | 9 => 36
 | 10 => 39
 | 11 => 40
 | 12 => 44
 | 13 => 49
 | 14 => 50
 | 15 => 54
 | _ => 0
def row13 (k : Nat) : Int := match k with
 | 1 => 9
 | 2 => 15
 | 3 => 19
 | 4 => 23
 | 5 => 25
 | 6 => 28
 | 7 => 32
 | 8 => 35
 | 9 => 38
 | 10 => 42
 | 11 => 45
 | 12 => 48
 | 13 => 51
 | 14 => 54
 | 15 => 58
 | _ => 0
def row14 (k : Nat) : Int := match k with
 | 1 => 10
 | 2 => 17
 | 3 => 22
 | 4 => 27
 | 5 => 30
 | 6 => 34
 | 7 => 38
 | 8 => 42
 | 9 => 44
 | 10 => 47
 | 11 => 51
 | 12 => 54
 | 13 => 57
 | 14 => 61
 | 15 => 64
 | _ => 0
def potential (h k : Nat) : Int := match h with
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

def checkForks (h k : Nat) : Bool := (List.range h).all fun j =>
  (List.range k).all fun a =>
    if a=0 ∨ a>2^(h-j-1) ∨ k-a>2^(h-j-1) then true else
      decide ((j:Int)-4*(credit j:Int)+potential (h-j-1) a+
        potential (h-j-1) (k-a) ≤ potential h k)

theorem check_0 : ((List.range 16).all fun k => checkForks 0 k)=true := by decide +kernel
theorem check_1 : ((List.range 16).all fun k => checkForks 1 k)=true := by decide +kernel
theorem check_2 : ((List.range 16).all fun k => checkForks 2 k)=true := by decide +kernel
theorem check_3 : ((List.range 16).all fun k => checkForks 3 k)=true := by decide +kernel
theorem check_4 : ((List.range 16).all fun k => checkForks 4 k)=true := by decide +kernel
theorem check_5 : ((List.range 16).all fun k => checkForks 5 k)=true := by decide +kernel
theorem check_6 : ((List.range 16).all fun k => checkForks 6 k)=true := by decide +kernel
theorem check_7 : ((List.range 16).all fun k => checkForks 7 k)=true := by decide +kernel
theorem check_8 : ((List.range 16).all fun k => checkForks 8 k)=true := by decide +kernel
theorem check_9 : ((List.range 16).all fun k => checkForks 9 k)=true := by decide +kernel
theorem check_10 : ((List.range 16).all fun k => checkForks 10 k)=true := by decide +kernel
theorem check_11 : ((List.range 16).all fun k => checkForks 11 k)=true := by decide +kernel
theorem check_12 : ((List.range 16).all fun k => checkForks 12 k)=true := by decide +kernel
theorem check_13 : ((List.range 16).all fun k => checkForks 13 k)=true := by decide +kernel
theorem check_14 : ((List.range 16).all fun k => checkForks 14 k)=true := by decide +kernel
theorem checks (h : Fin 15) : ((List.range 16).all fun k => checkForks h.val k)=true := by
 fin_cases h
 · exact check_0
 · exact check_1
 · exact check_2
 · exact check_3
 · exact check_4
 · exact check_5
 · exact check_6
 · exact check_7
 · exact check_8
 · exact check_9
 · exact check_10
 · exact check_11
 · exact check_12
 · exact check_13
 · exact check_14
theorem leaf_cert : ∀ h : Fin 15, (h.val:Int)-4*(credit h.val:Int) ≤ potential h.val 1 := by decide +kernel

theorem fork_cert (h k j a : Nat) (hh : h <15) (hk : k<16)
    (hj : j<h) (ha : 1≤a) (hak : a<k)
    (hal : a≤2^(h-j-1)) (har : k-a≤2^(h-j-1)) :
    (j:Int)-4*(credit j:Int)+potential (h-j-1) a+
      potential (h-j-1) (k-a) ≤ potential h k := by
  have H := List.all_eq_true.mp (checks ⟨h,hh⟩) k (List.mem_range.mpr hk)
  have H := List.all_eq_true.mp H j (List.mem_range.mpr hj)
  have H := List.all_eq_true.mp H a (List.mem_range.mpr hak)
  have hn : ¬ (a=0 ∨ a>2^(h-j-1) ∨ k-a>2^(h-j-1)) := by omega
  simpa only [hn, if_false, decide_eq_true_eq] using H
end AdjustedPotential

namespace AdjustedPotential
theorem tree_potential {h k f c : Nat} (ht : GeneralTreeProbe.Tree credit h k f c)
    (hh : h ≤ 14) (hk : k ≤ 15) :
    (f:Int)-4*(c:Int) ≤ potential h k := by
  induction ht with
  | leaf h => exact leaf_cert ⟨h,by omega⟩
  | fork h k j a l r lc rc hj ha hak left right ihl ihr =>
    have hml : h-j-1 ≤ 14 := by omega
    have hal : a ≤ 15 := by omega
    have hkr : k-a ≤ 15 := by omega
    have hl := ihl hml hal
    have hr := ihr hml hkr
    have hb := fork_cert h k j a (by omega) (by omega)
      hj ha hak left.leaves_le right.leaves_le
    push_cast
    omega

theorem root_potential {f c : Nat} (ht : GeneralTreeProbe.Tree credit 14 15 f c) :
    (f:Int)-4*(c:Int) ≤ 64 := by
  have h := tree_potential ht (by decide) (by decide)
  have hp : potential 14 15 = 64 := by decide +kernel
  rwa [hp] at h

theorem final_numeric (f c cost q : Nat) (hf : f ≤ 117) (hq : 1 ≤ q)
    (hp : (f:Int)-4*(c:Int) ≤ 64)
    (he : cost+c = 464+q*f) : cost ≤ 464+q*117-14 := by
  have hmul : q*f+q*(117-f) = q*117 := by rw [←Nat.mul_add]; congr 1; omega
  have hgap : 117-f ≤ q*(117-f) := by nlinarith
  omega

open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness OracleComp
 theorem recover_potential (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    ((GeneralTreeProbe.decodedFolds fts).sum:Int)-
      4*(((GeneralTreeProbe.decodedFolds fts).map credit).sum:Int) ≤ 64 :=
  root_potential (GeneralTreeProbe.recover_tree credit f parameter index leaves fts r hrun)

end AdjustedPotential

namespace RootAware
open GeneralTreeProbe SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

inductive RootTree (w wr : Nat → Nat) : Nat → Nat → Nat → Nat → Prop
 | leaf (h : Nat) : RootTree w wr h 1 h (wr h)
 | fork (h k j a l r lc rc : Nat) (hj : j<h) (ha : 1≤a) (hak : a<k)
     (left : Tree w (h-j-1) a l lc) (right : Tree w (h-j-1) (k-a) r rc) :
     RootTree w wr h k (j+l+r) (wr j+lc+rc)

def lastWeight (w wr : Nat → Nat) : List Nat → Nat
 | [] => 0
 | [a] => wr a
 | a::b::xs => w a + lastWeight w wr (b::xs)

def rootWeightSum (w wr : Nat → Nat) (ss : List ScheduleSegment) : Nat :=
 lastWeight w wr (ss.map (·.reads.length))

theorem lastWeight_append (w wr : Nat → Nat) (xs ys : List Nat) (hy : ys ≠ []) :
 lastWeight w wr (xs++ys) = (xs.map w).sum + lastWeight w wr ys := by
 induction xs with
 | nil => simp [lastWeight]
 | cons a xs ih =>
   cases xs with
   | nil => cases ys with
     | nil => contradiction
     | cons b ys => simp [lastWeight]
   | cons b xs => simp only [List.cons_append, lastWeight, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem rootWeightSum_append (w wr : Nat → Nat) (xs ys : List ScheduleSegment) (hy : ys ≠ []) :
 rootWeightSum w wr (xs++ys) = weightSum w xs + rootWeightSum w wr ys := by
 unfold rootWeightSum weightSum
 rw [List.map_append, lastWeight_append w wr _ _ (by simpa)]
 simp only [List.map_map, Function.comp_def]

def runRootWeight (w wr : Nat → Nat) : Nat → List Nat → Nat → Nat
 | x, [] ,top => wr (top-x)
 | x, y::ys, top => w (y-x)+runRootWeight w wr (y+1) ys top
theorem pending_rootFold {wr w x k f c top} (ht : PendingTree w x k f c) (hx : x ≤ top) :
    RootTree w wr top k (f+(top-x)) (c+wr (top-x)) := by
  cases ht with
  | leaf => simpa using RootTree.leaf (w := w) (wr := wr) top
  | @merge h a b l r lc rc left right =>
      have ha := left.leaves_pos
      have hb := right.leaves_pos
      have eh : top-(top-(h+1))-1 = h := by omega
      have hl : Tree w (top-(top-(h+1))-1) a l lc := by simpa [eh] using left
      have hr : Tree w (top-(top-(h+1))-1) ((a+b)-a) r rc := by
        simpa [eh, Nat.add_sub_cancel_left] using right
      have q := RootTree.fork (wr := wr) top (a+b) (top-(h+1)) a l r lc rc (by omega) (by omega) (by omega) hl hr
      convert q using 1 <;> omega

theorem climb_root {w wr} (stack : List (Node w)) : ∀ x k f c top,
    PendingTree w x k f c → Runs x (stack.map Node.height) top →
    ∃ total cost, RootTree w wr top (k+leafSum stack) total cost ∧
      total+x+stack.length = f+top+foldSum stack ∧
      cost = c+creditSum stack+runRootWeight w wr x (stack.map Node.height) top := by
  induction stack with
  | nil =>
      intro x k f c top ht hp
      have hx : x ≤ top := hp
      refine ⟨f+(top-x), c+wr (top-x), ?_, ?_, ?_⟩
      · simpa [leafSum] using pending_rootFold (wr := wr) ht hx
      · simp only [List.length_nil, foldSum, List.map_nil, List.sum_nil]; omega
      · simp [creditSum, runRootWeight]
  | cons node rest ih =>
      intro x k f c top ht hp
      have hp' : x ≤ node.height ∧ Runs (node.height+1) (rest.map Node.height) top := hp
      have hcurrent := ht.fold hp'.1
      have hnext := PendingTree.merge node.tree hcurrent
      obtain ⟨total,cost,htree,heq,hcost⟩ := ih (node.height+1) (node.leaves+k)
        (node.folds+(f+(node.height-x))) (node.credit+(c+w (node.height-x))) top hnext hp'.2
      refine ⟨total,cost,?_,?_,?_⟩
      · have e : node.leaves+k+leafSum rest = k+leafSum (node::rest) := by
          simp only [leafSum,List.map_cons,List.sum_cons]; omega
        rwa [e] at htree
      · simp only [List.length_cons,foldSum,List.map_cons,List.sum_cons] at heq ⊢; omega
      · simp only [creditSum,List.map_cons,List.sum_cons,runRootWeight] at hcost ⊢; omega

inductive RootTrace (w wr : Nat → Nat) : List Nat → Nat → Nat → Nat → Nat → Prop
  | last (heights : List Nat) (top : Nat) (hp : Runs 0 heights top) :
      RootTrace w wr heights 1 top (top-heights.length) (runRootWeight w wr 0 heights top)
  | next (lo hi : List Nat) (t n top f c : Nat) (hp : Runs 0 lo t)
      (tail : RootTrace w wr (t::hi) n top f c) :
      RootTrace w wr (lo++hi) (n+1) top ((t-lo.length)+f) (runWeight w 0 lo t+c)

theorem root_trace_tree {w wr heights n top f c} (ht : RootTrace w wr heights n top f c) :
    ∀ stack : List (Node w), stack.map Node.height = heights →
      RootTree w wr top (n+leafSum stack) (f+foldSum stack) (c+creditSum stack) := by
  induction ht with
  | last heights top hp =>
      intro stack hmap
      have hp' : Runs 0 (stack.map Node.height) top := by simpa [hmap] using hp
      obtain ⟨total,cost,htree,heq,hcost⟩ := climb_root (wr := wr) stack 0 1 0 0 top PendingTree.leaf hp'
      have hlen : stack.length = heights.length := by
        have h := congrArg List.length hmap; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have e : total = top-heights.length+foldSum stack := by omega
      have ec : cost = runRootWeight w wr 0 heights top+creditSum stack := by rw [hmap] at hcost; omega
      simpa only [e,ec] using htree
  | next lo hi t n top f c hp tail ih =>
      intro stack hmap
      obtain ⟨low,high,hs,hl,hh⟩ := List.map_eq_append_iff.mp hmap
      subst stack
      have hp' : Runs 0 (low.map Node.height) t := by simpa [hl] using hp
      obtain ⟨total,cost,htree,heq,hcost⟩ := climb low 0 1 0 0 t PendingTree.leaf hp'
      let node : Node w := ⟨t,1+leafSum low,total,cost,htree⟩
      have hmap' : (node::high).map Node.height = t::hi := by simp only [List.map_cons,node,hh]
      have hresult := ih (node::high) hmap'
      have hlen : low.length = lo.length := by
        have h := congrArg List.length hl; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have etotal : total = t-lo.length+foldSum low := by omega
      have ecost : cost = runWeight w 0 lo t+creditSum low := by rw [hl] at hcost; omega
      have eleaves : n+leafSum (node::high) = (n+1)+leafSum (low++high) := by
        simp only [leafSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have efolds : f+foldSum (node::high) = (t-lo.length+f)+foldSum (low++high) := by
        simp only [foldSum] at etotal
        simp only [foldSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have ec : c+creditSum (node::high) = (runWeight w 0 lo t+c)+creditSum (low++high) := by
        simp only [creditSum] at ecost
        simp only [creditSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      rwa [eleaves,efolds,ec] at hresult


theorem climbSegs_nonempty (v x top : Nat) (L : List Nat) : climbSegs v x L top ≠ [] := by
 cases L <;> simp [climbSegs]

theorem allSegs_nonempty (v : Nat) (rest L : List Nat) : allSegs (v::rest) L ≠ [] := by
 intro h
 have e := (List.append_eq_nil_iff.mp h).1
 exact climbSegs_nonempty _ _ _ _ e

theorem climbSegs_rootWeightSum (w wr : Nat → Nat) (v x top : Nat) (L : List Nat) :
 rootWeightSum w wr (climbSegs v x L top) = runRootWeight w wr x L top := by
 induction L generalizing x with
 | nil => simp [rootWeightSum,lastWeight,climbSegs,sibs,runRootWeight]
 | cons y L ih =>
   have he : lastWeight w wr ((y-x)::((climbSegs v (y+1) L top).map (·.reads.length))) =
       w (y-x) + rootWeightSum w wr (climbSegs v (y+1) L top) := by
     have h := lastWeight_append w wr [y-x] ((climbSegs v (y+1) L top).map (·.reads.length))
       (by simpa using climbSegs_nonempty v (y+1) top L)
     simpa [rootWeightSum] using h
   simp only [climbSegs,rootWeightSum,List.map_cons,sibs,List.length_map,List.length_range',runRootWeight]
   rw [he]
   exact congrArg (w (y-x) + ·) (ih (y+1))
theorem allSegs_rootTrace (wgt wr : Nat → Nat) (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight) (hL : Pending v L) :
    RootTrace wgt wr L (v::rest).length 14 (readSum (allSegs (v::rest) L))
      (rootWeightSum wgt wr (allSegs (v::rest) L)) := by
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
      have hr : Runs 0 L 14 := runs_of_order L 0 14 hL.1
        (fun y hy => ⟨Nat.zero_le _, (hL.2 y hy).1⟩) (by omega)
      have hsum := climbSegs_readSum v 0 14 L hr
      have heq : readSum (climbSegs v 0 L 14) = 14-L.length := by omega
      simpa only [List.length_cons,List.length_nil,heq,climbSegs_rootWeightSum] using RootTrace.last (w := wgt) (wr := wr) L 14 hr
  | cons next rest ih =>
      let t := leafTop v (next::rest)
      let lo := L.filter (· < t)
      let hi := L.filter (t < ·)
      have hsplit : L = lo++hi := pending_split hL hs hb
      have hn : Pending next (t::hi) :=
        (pending_next ((List.pairwise_cons.mp hs).1 next (by simp))
          (hb next (by simp)) (by rfl) hL).1
      have ht := ih next (t::hi) (List.pairwise_cons.mp hs).2
        (fun z hz => hb z (List.mem_cons_of_mem v hz)) hn
      have hr : Runs 0 lo t := by
        apply runs_of_order lo 0 t (hL.1.filter _) ?_ (Nat.zero_le _)
        intro y hy
        exact ⟨Nat.zero_le _,(mem_filter_lt hy).2⟩
      have hsum := climbSegs_readSum v 0 t lo hr
      have heq : readSum (climbSegs v 0 lo t) = t-lo.length := by omega
      have htrace := RootTrace.next lo hi t (next::rest).length 14
        (readSum (allSegs (next::rest) (t::hi)))
        (rootWeightSum wgt wr (allSegs (next::rest) (t::hi))) hr ht
      rw [←hsplit] at htrace
      change RootTrace wgt wr L (v::next::rest).length 14
        (readSum (climbSegs v 0 lo t ++ allSegs (next::rest) (t::hi)))
        (rootWeightSum wgt wr (climbSegs v 0 lo t ++ allSegs (next::rest) (t::hi)))
      have rs : ∀ a b, readSum (a++b) = readSum a+readSum b := by
        intros; simp [readSum]
      rw [rs,rootWeightSum_append wgt wr _ _ (allSegs_nonempty next rest (t::hi)),
        heq,climbSegs_weightSum]
      exact htrace

theorem schedule_rootTree (weight wr : Nat → Nat) (leaves : IndexGroup → FtsLeaf)
    (hinj : Function.Injective leaves) :
    RootTree weight wr 14 15 (readSum (schedule (sortedLeaves leaves)))
      (rootWeightSum weight wr (schedule (sortedLeaves leaves))) := by
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
  rw [hsch]
  have ht := allSegs_rootTrace weight wr v rest [] hs hb hL
  rw [hlen] at ht
  have hh := root_trace_tree ht [] rfl
  simpa only [leafSum,foldSum,creditSum,List.map_nil,List.sum_nil,Nat.add_zero,ftsOpenings] using hh

open OracleComp
theorem recover_rootTree (weight wr : Nat → Nat) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    RootTree weight wr 14 15 (decodedFolds fts).sum (lastWeight weight wr (decodedFolds fts)) := by
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hlen := schedule_length_of_injective leaves hadm.1
  have hm := (PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun).1
  have he : decodedFolds fts = (schedule (sortedLeaves leaves)).map (·.reads.length) := by
    apply List.ext_getElem
    · simp only [decodedFolds,List.length_ofFn,List.length_map,hlen]
    · intro i hi hj
      have hilt : i < ftsSegments := by simpa only [decodedFolds,List.length_ofFn] using hi
      have hil : i < (schedule (sortedLeaves leaves)).length := by omega
      have h := (hm ⟨i,hilt⟩).1
      simpa only [decodedFolds,List.getElem_ofFn,List.getElem_map,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hil,Option.getD_some] using h
  rw [he]
  simpa only [readSum,rootWeightSum] using schedule_rootTree weight wr leaves hadm.1


def rootCredit (j : Nat) : Nat := if j=0 then 1 else 0

def checkRoot : Bool := (List.range 14).all fun j => (List.range 15).all fun a =>
 if a=0 ∨ a>2^(13-j) ∨ 15-a>2^(13-j) then true else
 decide ((j:Int)-4*(rootCredit j:Int)+AdjustedPotential.potential (13-j) a+
     AdjustedPotential.potential (13-j) (15-a) ≤ 64)

theorem check_root : checkRoot = true := by decide +kernel

theorem root_potential {f c : Nat} (ht : RootTree AdjustedPotential.credit rootCredit 14 15 f c) :
 (f:Int)-4*(c:Int) ≤ 64 := by
 cases ht
 rename_i j a l r lc rc hj ha left hak right
 have hl := AdjustedPotential.tree_potential left (by omega) (by omega)
 have hr := AdjustedPotential.tree_potential right (by omega) (by omega)
 have hal := left.leaves_le
 have har := right.leaves_le
 have H := List.all_eq_true.mp check_root j (List.mem_range.mpr hj)
 have H := List.all_eq_true.mp H a (List.mem_range.mpr hak)
 have hm : 14-j-1 = 13-j := by omega
 have hn : ¬ (a=0 ∨ a>2^(13-j) ∨ 15-a>2^(13-j)) := by rw [hm] at hal har; omega
 simp only [hn,if_false,decide_eq_true_eq] at H
 rw [hm] at hl hr
 push_cast
 omega

theorem recover_potential (f : QueryImpl HashSpec Id)
 (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
 (fts : FtsSignature) (r : PorsMachine.Run)
 (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
 ((decodedFolds fts).sum:Int)-4*(lastWeight AdjustedPotential.credit rootCredit (decodedFolds fts):Int) ≤ 64 :=
 root_potential (recover_rootTree AdjustedPotential.credit rootCredit f parameter index leaves fts r hrun)

theorem conditional_cost (f c cost : Nat) (hf : f≤117)
 (ht : RootTree AdjustedPotential.credit rootCredit 14 15 f c)
 (he : cost+c=464+16*f) : cost≤2322 := by
 exact AdjustedPotential.final_numeric f c cost 16 hf (by decide) (root_potential ht) he

theorem lastWeight_terminal (w wr : Nat → Nat) (xs : List Nat) (a : Nat) :
 lastWeight w wr (xs++[a]) = (xs.map w).sum+wr a := by
 simpa only [lastWeight] using lastWeight_append w wr xs [a] (by simp)

theorem credit_at_cap {f c : Nat} (ht : RootTree AdjustedPotential.credit rootCredit 14 15 f c)
 (hf : f=117) : 14≤c := by
 have hp := root_potential ht
 omega

theorem recover_cost (f : QueryImpl HashSpec Id)
 (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
 (fts : FtsSignature) (r : PorsMachine.Run)
 (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r)
 (cost : Nat) (hcap : (decodedFolds fts).sum≤117)
 (hcost : cost+lastWeight AdjustedPotential.credit rootCredit (decodedFolds fts)
   =464+16*(decodedFolds fts).sum) : cost≤2322 :=
 conditional_cost _ _ _ hcap
   (recover_rootTree AdjustedPotential.credit rootCredit f parameter index leaves fts r hrun) hcost


end RootAware
end SigGolfCandidate.Research.NoJoin

section StructuralCostCertificate

/-! ## PorsDecodedCounts -/
namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open OracleComp
open SigGolfCandidate.Research.NoJoin.GeneralTreeProbe

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

end SigGolfCandidate.Research.PorsPositiveBound

/-! ## PorsExactMachine -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def noJoinSegmentCost (V a : Nat) : Nat := if a=0 then 15 else 16+16*a-segmentSave V a

theorem segmentSave_le (V a : Nat) : segmentSave V a ≤ 1 := by
  unfold segmentSave
  split <;> omega

theorem foldSave_eq (V a : Nat) : foldSave V a = tabExtra a+segmentSave V a := by
  by_cases ha : a<3
  · have hn : ¬3≤a := by omega
    have hnj : ¬noJoin V a := by unfold noJoin; omega
    rw [foldSave,if_pos ha,tabExtra,if_neg hn,segmentSave,if_neg hnj]
  · have hp : 3≤a := by omega
    rw [foldSave,if_neg ha,tabExtra,if_pos hp]
    by_cases hV : V<2
    · have hnj : noJoin V a := ⟨hV,hp⟩
      rw [if_pos hV,segmentSave,if_pos hnj]
    · have hnj : ¬noJoin V a := by unfold noJoin; omega
      rw [if_neg hV,segmentSave,if_neg hnj]

theorem noJoinSegmentCost_eq (V a : Nat) :
    7+tabExtra a+8+(if a=0 then 0 else 2+foldBudget V a 0) = noJoinSegmentCost V a := by
  by_cases hz : a=0
  · subst a
    simp [tabExtra,noJoinSegmentCost]
  · have hp : 0<a := by omega
    have he : prefixBefore V a 0=0 := by simp [prefixBefore]
    rw [if_neg hz,foldBudget,if_pos hp,he,Nat.sub_zero,Nat.add_zero,foldSave_eq,
      noJoinSegmentCost,if_neg hz]
    have hs := segmentSave_le V a
    have ht : tabExtra a ≤ 1 := by unfold tabExtra; split <;> omega
    omega

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
    (hA : ∀ V a, V < 3 → a ≤ 14 → V = segV (tsel s) (wbyte P.wl ptr) →
      a = wbyte P.wl ptr % 16 → folds + a ≤ 117 → noJoinSegmentCost V a + AT V (folds + a) ≤ A)
    (h9 : 13 ≤ N ∧ 13 ≤ C ∧ 13 ≤ A) :
    GoodQ m N C (folds ≤ 117) A (cc (Ref.segment P.idx P.wl ptr E folds pend node) K) := by
  obtain ⟨hrej, hpar, hacc⟩ := seg_step P hP s0 s x c ptr E folds pend node stk m h
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
  by_cases hp : 0 < b % 16 ∧ (b / 32 % 2 ≠ E % 2 ∨ (3 ≤ b % 16 ∧ b / 32 ≠ E % 8))
  · rw [if_pos hp, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hpar (by omega) ha14 hp.2
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hp, cc_bind, pendingHash_eq]
    have hpar' : b % 16 = 0 ∨ (segBits b % 2 = E % 2 ∧ (3 ≤ b % 16 → segBits b = E % 8)) := by unfold segBits; omega
    obtain ⟨k, u, hk, hst, hf, h5, hv, hin, hbl, hpost⟩ := hacc ha14 hpar'
    have hVl := segV_lt (tsel s) b
    have hextra := tabExtra_le (b % 16)
    set a := b % 16 with hadef
    set V := segV (tsel s) b with hV
    -- after the pending hash
    have H : ∀ ans, GoodQ (writeHash u ans) (NT V + 17 * 14 + 2) (CT V + 17 * a) (folds + a ≤ 117) (AT V (folds + a) + (if a = 0 then 0 else 2 + foldBudget V a 0))
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
        simp only [ha0, Nat.mul_zero, Nat.add_zero, if_true]
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
        have hbudget := foldBudget_old_bound ⟨V, hVl⟩ ⟨a, by omega⟩
        simp only at hbudget
        simp only [if_neg ha0]
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
        have he := noJoinSegmentCost_eq V a
        omega⟩)

end SigGolfCandidate.Verify

/-! ## PorsExactComposition -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp
open SigGolfCandidate.Research.PorsPositiveBound

def decodedFold (wl : List Byte) (j : Nat) : Nat := wbyte wl (Equiv.segPtr wl j) % 16
def indexedSegmentCost (j a : Nat) : Nat := noJoinSegmentCost (if j=28 then 2 else 0) a

open SigGolfCandidate.Research.NoJoin

def rootListCost (xs : List Nat) : Nat :=
 RootAware.lastWeight (noJoinSegmentCost 0) (noJoinSegmentCost 2) xs

theorem rootCost_balance (a : Nat) : noJoinSegmentCost 2 a+RootAware.rootCredit a=16+16*a := by
 by_cases hz : a=0
 · simp [noJoinSegmentCost,RootAware.rootCredit,hz]
 · simp [noJoinSegmentCost,segmentSave,noJoin,RootAware.rootCredit,hz]

theorem nonrootCost_balance (a : Nat) : noJoinSegmentCost 0 a+AdjustedPotential.credit a=16+16*a := by
 by_cases hz : a=0
 · simp [noJoinSegmentCost,AdjustedPotential.credit,hz]
 · by_cases ha : 3≤a
   · simp [noJoinSegmentCost,segmentSave,noJoin,AdjustedPotential.credit,hz,ha]; omega
   · simp [noJoinSegmentCost,segmentSave,noJoin,AdjustedPotential.credit,hz,ha]

theorem rootListCost_balance (xs : List Nat) :
 rootListCost xs+RootAware.lastWeight AdjustedPotential.credit RootAware.rootCredit xs =16*xs.length+16*xs.sum := by
 induction xs with
 | nil => rfl
 | cons a xs ih =>
   cases xs with
   | nil => simpa [rootListCost,RootAware.lastWeight] using rootCost_balance a
   | cons b xs =>
     have h := nonrootCost_balance a
     simp only [rootListCost,RootAware.lastWeight,List.length_cons,List.sum_cons] at ih ⊢
     omega

theorem indexedCost_last (f : Nat→Nat) (j n : Nat) (he : j+n=29) :
 ((List.range' j n).map fun k => indexedSegmentCost k (f k)).sum =
 rootListCost ((List.range' j n).map f) := by
 induction n generalizing j with
 | zero => simp [rootListCost,RootAware.lastWeight]
 | succ n ih =>
   cases n with
   | zero =>
     have hj : j=28 := by omega
     subst j
     simp [List.range'_succ,rootListCost,RootAware.lastWeight,indexedSegmentCost]
   | succ n =>
     have hj : j≠28 := by omega
     have hi := ih (j+1) (by omega)
     rw [List.range'_succ,List.map_cons,List.sum_cons,List.map_cons]
     have hn : ((List.range' (j+1) (n+1)).map f) ≠ [] := by simp
     have hc : rootListCost (f j :: ((List.range' (j+1) (n+1)).map f)) =
         noJoinSegmentCost 0 (f j)+rootListCost ((List.range' (j+1) (n+1)).map f) := by
       cases he : ((List.range' (j+1) (n+1)).map f) with
       | nil => exact False.elim (hn he)
       | cons b bs => rfl
     rw [hc,←hi]
     simp only [indexedSegmentCost,if_neg hj]


def decodedCostFrom (wl : List Byte) (j n : Nat) : Nat :=
  ((List.range' j n).map fun k => indexedSegmentCost k (decodedFold wl k)).sum
def decodedCostRem (wl : List Byte) (j : Nat) : Nat := decodedCostFrom wl j (29-j)

theorem decodedCostFrom_succ (wl : List Byte) (j n : Nat) :
    decodedCostFrom wl j (n+1) = indexedSegmentCost j (decodedFold wl j) + decodedCostFrom wl (j+1) n := by
  simp [decodedCostFrom, List.range'_succ]

theorem decodedCostRem_succ (wl : List Byte) (j : Nat) (hj : j < 29) :
    decodedCostRem wl j = indexedSegmentCost j (decodedFold wl j) + decodedCostRem wl (j+1) := by
  unfold decodedCostRem
  have h : 29-j = (29-(j+1))+1 := by omega
  rw [h, decodedCostFrom_succ]

theorem noJoinSegmentCost_ge (V a : Nat) : 15 ≤ noJoinSegmentCost V a := by
  have hs := segmentSave_le V a
  unfold noJoinSegmentCost
  split <;> omega

theorem noJoinSegmentCost_nonroot (V a : Nat) (hV : V<2) :
    noJoinSegmentCost V a = noJoinSegmentCost 0 a := by
  simp [noJoinSegmentCost, segmentSave, noJoin, hV]

theorem noJoinSegmentCost_zero_le (V a : Nat) :
    noJoinSegmentCost 0 a ≤ noJoinSegmentCost V a := by
  have hs : segmentSave V a ≤ segmentSave 0 a := by
    by_cases hn : noJoin V a
    · have hz : noJoin 0 a := ⟨by decide,hn.2⟩
      rw [segmentSave,if_pos hn,segmentSave,if_pos hz]
    · rw [segmentSave,if_neg hn]; omega
  unfold noJoinSegmentCost
  split <;> omega

theorem noJoinSegmentCost_le_succ (V a : Nat) :
    noJoinSegmentCost V a ≤ noJoinSegmentCost 0 a+1 := by
  have hs := segmentSave_le 0 a
  unfold noJoinSegmentCost
  split <;> omega

theorem decodedCostRem_ge (wl : List Byte) (j : Nat) (hj : j < 29) :
    15 ≤ decodedCostRem wl j := by
  rw [decodedCostRem_succ wl j hj]
  have h := noJoinSegmentCost_ge (if j=28 then 2 else 0) (decodedFold wl j)
  change 15 ≤ indexedSegmentCost j (decodedFold wl j) at h
  omega

/-- A witness-dependent accepting budget. It retains every zero-segment saving
and the actual remaining decoded folds, independent of the final fold cap. -/
def Aexact (wl : List Byte) (s d : Nat) : Nat :=
  decodedCostRem wl (2*s-d) + 6*(d+14-s) + 4*(14-s) + lrest s + 12 + layC
def AexactPF (wl : List Byte) (s d : Nat) : Nat :=
  if s = 14 then 12 + layC else 4+leafCost (s+1)+Aexact wl (s+1) (d+1)
def AexactM (wl : List Byte) (s d : Nat) : Nat :=
  if d = 0 then 7 else 6+Aexact wl s (d-1)

theorem exact_seg_budget (wl : List Byte) (s d : Nat) (hs : s < 15) (hd : d ≤ s) :
    (∀ a, a = decodedFold wl (2*s-d) → noJoinSegmentCost 0 a + AexactM wl s d ≤ Aexact wl s d) ∧
    (∀ a, a = decodedFold wl (2*s-d) → noJoinSegmentCost (if s=14 then 2 else 1) a + AexactPF wl s d ≤ Aexact wl s d) ∧
    13 ≤ Aexact wl s d := by
  have hj : 2*s-d < 29 := by omega
  have hrec := decodedCostRem_succ wl (2*s-d) hj
  have hge := decodedCostRem_ge wl (2*s-d) hj
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    subst a
    have hc := noJoinSegmentCost_zero_le (if 2*s-d=28 then 2 else 0) (decodedFold wl (2*s-d))
    change noJoinSegmentCost 0 (decodedFold wl (2*s-d)) ≤ indexedSegmentCost (2*s-d) (decodedFold wl (2*s-d)) at hc
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
      by_cases hz : d=0
      · have he : 2*s-d=28 := by omega
        simp only [he] at *
        simp only [indexedSegmentCost,if_true] at hrec
        omega
      · have he : 2*s-d≠28 := by omega
        simp only [indexedSegmentCost,if_neg he] at hrec
        have hc := noJoinSegmentCost_le_succ 2 (decodedFold wl (2*s-d))
        omega
    · have he : 2*(s+1)-(d+1) = 2*s-d+1 := by omega
      have hj' : 2*s-d≠28 := by omega
      simp only [indexedSegmentCost,if_neg hj'] at hrec
      have hl := lrest_succ s (by omega)
      simp only [AexactPF, if_neg h14, Aexact, he]
      rw [noJoinSegmentCost_nonroot 1 _ (by decide)]
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
      (fun V a hVl ha hV haw hF => by
        have he : a = decodedFold P.wl (2*s-0) := by unfold decodedFold; rw [← hptr]; exact haw
        by_cases hV0 : V=0
        · simp only [hV0,if_true]; exact bAMX a he
        · have hVe := (segV_PF s _ (hV ▸ hV0)).1
          have hv : V = if s=14 then 2 else 1 := hV.trans hVe
          simp only [if_neg hV0]
          rw [hv]
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
        (by unfold NtailM CtailM; split_ifs <;> omega) (by unfold CtailM; split_ifs <;> omega) (fun q => ⟨q, by unfold AexactM; split_ifs <;> omega⟩)
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
      (fun V a hVl ha hV haw hF => by
        have he : a = decodedFold P.wl (2*s-(rest.length+1)) := by unfold decodedFold; rw [← hptr]; exact haw
        by_cases hV0 : V=0
        · simp only [hV0,if_true]; exact bAMX a he
        · have hVe := (segV_PF s _ (hV ▸ hV0)).1
          have hv : V = if s=14 then 2 else 1 := hV.trans hVe
          simp only [if_neg hV0]
          rw [hv]
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
          (by unfold NtailM CtailM Cseg; split_ifs <;> omega) (by unfold CtailM Cseg; split_ifs <;> omega)
          (fun q => ⟨q, by unfold AexactM Aexact; split_ifs <;> omega⟩)
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
      GoodQ u (12 + layC + layN) (12 + layC) (st.folds ≤ 117) (12 + layC) (Kr (some st))) :
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
      GoodQ u (12 + layC + layN) (12 + layC) (st.folds ≤ 117) (12 + layC) (Kr P (some st)) :=
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

def cycleBoundDecoded (wl : List Byte) : Nat := 486 + layC + decodedCostRem wl 0

theorem exact_cost_vals (wl : List Byte) :
    leafCost 0 + Aexact wl 0 0 = 349 + layC + decodedCostRem wl 0 := by
  have h0 : leafCost 0 = 12 := rfl
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
    have H : ∀ a, GoodQ (writeHash t a) (105 + (leafCost 0 + Nseg 0 0)) (105 + (leafCost 0 + Cseg 0 0)) True
        (105 + (leafCost 0 + Aexact wl 0 0))
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
    have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; rw [wRho_eq]; omega
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
    decodedCostRem wl 0 = rootListCost (decodedFolds (witFts wl)) := by
  unfold decodedCostRem decodedCostFrom
  rw [indexedCost_last _ 0 29 rfl]
  congr 1

/-- Every accepted reference PORS computation has exact segment cost below the
former uniform envelope. This statement is independent of sampled executions. -/
theorem porsRoot_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (index : Index) (wl : List Byte) (hl : wl.length = 16384)
    (leaves : IndexGroup → FtsLeaf) (node : Ref.Val)
    (hrun : evalWithAnswerFn hash
      (Ref.porsRoot index (List.ofFn fun r => (leaves r).val) wl) = some node) :
    decodedCostRem wl 0 ≤ 2322 := by
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
      have hsum := recoverRun_decodedFolds_sum f 0 index leaves (witFts wl) r hr
      obtain ⟨slot, hperm, hsorted, hsegments, hfolds, hadm, hbij⟩ :=
        PorsMachine.recoverRun_structure f 0 index leaves (witFts wl) r hr
      have hcap : (decodedFolds (witFts wl)).sum ≤ 117 := by
        rw [hsum,hfolds]; exact hadm.2
      apply SigGolfCandidate.Research.NoJoin.RootAware.recover_cost f 0 index leaves (witFts wl) r hr _ hcap
      have hbalance := rootListCost_balance (decodedFolds (witFts wl))
      simpa only [decodedFolds,SigGolfCandidate.Research.NoJoin.GeneralTreeProbe.decodedFolds,List.length_ofFn,show ftsSegments=29 by rfl,show 16*(29:Nat)=464 by decide] using hbalance

theorem verifyList_exact_cost (hash : SigGolfCandidate.Legacy.Hash)
    (ml pkl wl : List Byte) (hl : wl.length = 16384)
    (hverify : evalWithAnswerFn hash (Ref.verifyList ml pkl wl) = true) :
    decodedCostRem wl 0 ≤ 2322 := by
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
    GoodQ s fuelBound cycleBoundAll True (cycleBound-14) (cc (verifyList ml pkl wl) Kb) := by
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
    GoodQ s fuelBound cycleBoundAll True (cycleBound-14)
      (cc (verifyRef input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  exact main_good_tight _ _ _ (length_toList m) (length_toList pk)
    (by rw [length_extW]; exact congrArg (fun n => witLead + n) (length_toList w)) s (init_ok m pk w s hs)

/-- Every accepting execution of the frozen verifier takes one fewer cycle than
its previous bound. This is universal over hash answers and arbitrary witnesses. -/
theorem verify_accept_cycles_tight (hash : Hash)
    (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ cycleBound-14 := by
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
