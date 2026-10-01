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
The compressed-tree certificate accounts for zero-length segments and restores the
actual final/root segment's branch cost. Its numeric table is checked in Params. -/

/-! ## PorsDecodedCounts -/
namespace SigGolfCandidate.Research.PorsPositiveBound
open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open OracleComp

def readSum (ss : List ScheduleSegment) : Nat := (ss.map (·.reads.length)).sum

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


namespace SiggolfReverseSchedule
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


end SiggolfReverseSchedule


namespace SiggolfReverseRootLast
open SiggolfPrefixCertificate SiggolfReverseSchedule
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable (credit : Nat → Nat)

/-- The ordinary tree witness, retaining its final/root unary-run length. -/
inductive RootedTree (credit : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Prop
  | leaf (h : Nat) : RootedTree credit h 1 h (credit h) h
  | fork (h a p q fl fr cl cr : Nat) (ha : a<h)
      (left : Tree credit (h-a-1) p fl cl) (right : Tree credit (h-a-1) q fr cr) :
      RootedTree credit h (p+q) (a+fl+fr) (credit a+cl+cr) a

theorem fold_root {x k f c top : Nat} (ht : PendingTree credit x k f c)
    (hx : x≤top) : RootedTree credit top k (f+(top-x)) (c+credit (top-x)) (top-x) := by
  cases ht with
  | leaf => simpa using RootedTree.leaf (credit := credit) top
  | @merge h a b fl fr cl cr left right =>
      have eh : top-(top-(h+1))-1=h := by omega
      have hl : Tree credit (top-(top-(h+1))-1) a fl cl := by simpa [eh] using left
      have hr : Tree credit (top-(top-(h+1))-1) b fr cr := by simpa [eh] using right
      have ht := RootedTree.fork top (top-(h+1)) a b fl fr cl cr (by omega) hl hr
      convert ht using 1 <;> omega

def lastRun : Nat → List Nat → Nat → Nat
  | x, [], top => top-x
  | _, y::ys, top => lastRun (y+1) ys top

theorem climb_root (stack : List (Node credit)) : ∀ (x k f c top : Nat),
    PendingTree credit x k f c → Runs x (stack.map Node.height) top →
    ∃ total, RootedTree credit top (k+leafSum credit stack) total
      (c+creditSum credit stack+climbCredit credit x (stack.map Node.height) top)
      (lastRun x (stack.map Node.height) top) ∧
      total+x+stack.length = f+top+foldSum credit stack := by
  induction stack with
  | nil =>
      intro x k f c top ht hp
      have hx : x≤top := hp
      refine ⟨f+(top-x), ?_, ?_⟩
      · simpa [leafSum,creditSum,climbCredit,lastRun] using fold_root credit ht hx
      · simp only [List.length_nil,foldSum,List.map_nil,List.sum_nil]; omega
  | cons node rest ih =>
      intro x k f c top ht hp
      have hp' : x≤node.height ∧ Runs (node.height+1) (rest.map Node.height) top := hp
      have hcurrent := ht.fold credit hp'.1
      have hnext := PendingTree.merge node.tree hcurrent
      obtain ⟨total,htree,heq⟩ := ih (node.height+1) (node.leaves+k)
        (node.folds+(f+(node.height-x))) (node.credits+(c+credit (node.height-x)))
        top hnext hp'.2
      refine ⟨total, ?_, ?_⟩
      · have eleaves : node.leaves+k+leafSum credit rest=k+leafSum credit (node::rest) := by
          simp only [leafSum,List.map_cons,List.sum_cons]; omega
        have ecredit : node.credits+(c+credit (node.height-x))+creditSum credit rest+
              climbCredit credit (node.height+1) (rest.map Node.height) top =
            c+creditSum credit (node::rest)+climbCredit credit x ((node::rest).map Node.height) top := by
          simp only [creditSum,List.map_cons,List.sum_cons,climbCredit]; omega
        rw [eleaves,ecredit] at htree
        simpa only [List.map_cons,lastRun] using htree
      · simp only [List.length_cons,foldSum,List.map_cons,List.sum_cons] at heq ⊢; omega

inductive TraceRoot (credit : Nat → Nat) : List Nat → Nat → Nat → Nat → Nat → Nat → Prop
  | last (heights : List Nat) (top : Nat) (hp : Runs 0 heights top) :
      TraceRoot credit heights 1 top (top-heights.length) (climbCredit credit 0 heights top)
        (lastRun 0 heights top)
  | next (lo hi : List Nat) (t n top f c a : Nat) (hp : Runs 0 lo t)
      (tail : TraceRoot credit (t::hi) n top f c a) :
      TraceRoot credit (lo++hi) (n+1) top ((t-lo.length)+f) (climbCredit credit 0 lo t+c) a

theorem trace_root {heights : List Nat} {n top f c a : Nat}
    (ht : TraceRoot credit heights n top f c a) : ∀ stack : List (Node credit),
    stack.map Node.height=heights →
    RootedTree credit top (n+leafSum credit stack) (f+foldSum credit stack)
      (c+creditSum credit stack) a := by
  induction ht with
  | last heights top hp =>
      intro stack hmap
      have hp' : Runs 0 (stack.map Node.height) top := by simpa [hmap] using hp
      obtain ⟨total,htree,heq⟩ := climb_root credit stack 0 1 0 0 top (PendingTree.leaf (credit := credit)) hp'
      have hlen : stack.length=heights.length := by
        have h := congrArg List.length hmap; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have e : total=top-heights.length+foldSum credit stack := by omega
      simpa only [e,hmap,Nat.zero_add,Nat.add_comm] using htree
  | next lo hi t n top f c a hp tail ih =>
      intro stack hmap
      obtain ⟨low,high,hs,hl,hh⟩ := List.map_eq_append_iff.mp hmap
      subst stack
      have hp' : Runs 0 (low.map Node.height) t := by simpa [hl] using hp
      obtain ⟨total,htree,heq⟩ := climb credit low 0 1 0 0 t (PendingTree.leaf (credit := credit)) hp'
      let node : Node credit := ⟨t,1+leafSum credit low,total,
        creditSum credit low+climbCredit credit 0 (low.map Node.height) t,by simpa using htree⟩
      have hmap' : (node::high).map Node.height=t::hi := by simp only [List.map_cons,node,hh]
      have hresult := ih (node::high) hmap'
      have hlen : low.length=lo.length := by
        have h := congrArg List.length hl; simpa only [List.length_map] using h
      have hbound := hp.length_le
      have etotal : total=t-lo.length+foldSum credit low := by omega
      have eleaves : n+leafSum credit (node::high)=(n+1)+leafSum credit (low++high) := by
        simp only [leafSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have efolds : f+foldSum credit (node::high)=(t-lo.length+f)+foldSum credit (low++high) := by
        simp only [foldSum] at etotal
        simp only [foldSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node]; omega
      have ecredits : c+creditSum credit (node::high)=
          (climbCredit credit 0 lo t+c)+creditSum credit (low++high) := by
        simp only [creditSum,List.map_cons,List.map_append,List.sum_cons,List.sum_append,node,hl]; omega
      rwa [eleaves,efolds,ecredits] at hresult

open SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open SigGolfCandidate.Research.PorsPositiveBound

def lastFold (ss : List ScheduleSegment) : Nat := (ss.map (·.reads.length)).getLastD 0

theorem lastFold_append_right (xs ys : List ScheduleSegment) (hy : ys≠[]) :
    lastFold (xs++ys)=lastFold ys := by
  have hm : ys.map (·.reads.length)≠[] := by simpa
  simp only [lastFold,List.map_append,List.getLastD_eq_getLast?,List.getLast?_append,
    List.getLast?_eq_some_getLast hm,Option.some_or,Option.getD_some]

theorem lastFold_cons (seg : ScheduleSegment) (xs : List ScheduleSegment) (hx : xs≠[]) :
    lastFold (seg::xs)=lastFold xs := lastFold_append_right [seg] xs hx

theorem climbSegs_nonempty (v x top : Nat) (L : List Nat) : climbSegs v x L top≠[] := by
  cases L <;> simp [climbSegs]

theorem climbSegs_last (v x top : Nat) (L : List Nat) :
    lastFold (climbSegs v x L top)=lastRun x L top := by
  induction L generalizing x with
  | nil => simp [climbSegs,lastFold,lastRun,sibs]
  | cons y ys ih =>
      change lastFold (_ :: climbSegs v (y+1) ys top)=_
      rw [lastFold_cons _ _ (climbSegs_nonempty _ _ _ _)]
      exact ih (y+1)

theorem allSegs_nonempty (v : Nat) (rest L : List Nat) : allSegs (v::rest) L≠[] := by
  rw [allSegs_cons]
  exact List.append_ne_nil_of_left_ne_nil (climbSegs_nonempty _ _ _ _) _

theorem allSegs_trace_root (v : Nat) (rest L : List Nat)
    (hs : (v::rest).Pairwise (· < ·))
    (hb : ∀ w ∈ v::rest, w < 2^ftsTreeHeight) (hL : Pending v L) :
    TraceRoot credit L (v::rest).length 14 (readSum (allSegs (v::rest) L))
      (scheduleCredit credit (allSegs (v::rest) L)) (lastFold (allSegs (v::rest) L)) := by
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
      simpa only [List.length_cons,List.length_nil,heq,climbSegs_credit,climbSegs_last] using TraceRoot.last L 14 hr
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
      have htrace := TraceRoot.next lo hi t (w::rest).length 14
        (readSum (allSegs (w::rest) (t::hi)))
        (scheduleCredit credit (allSegs (w::rest) (t::hi)))
        (lastFold (allSegs (w::rest) (t::hi))) hr ht
      rw [←hsplit] at htrace
      change TraceRoot credit L ((v::w::rest).length) 14
        (readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)))
        (scheduleCredit credit (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)))
        (lastFold (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)))
      have hread : readSum (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) =
          (t-lo.length)+readSum (allSegs (w::rest) (t::hi)) := by
        simp only [readSum,List.map_append,List.sum_append] at heq ⊢
        rw [heq]
      have hcredit : scheduleCredit credit (climbSegs v 0 lo t ++ allSegs (w::rest) (t::hi)) =
          climbCredit credit 0 lo t+scheduleCredit credit (allSegs (w::rest) (t::hi)) := by
        simpa only [scheduleCredit,List.map_append,List.sum_append] using
          congrArg (fun n => n+scheduleCredit credit (allSegs (w::rest) (t::hi)))
            (climbSegs_credit credit v 0 t lo)
      rw [hread,hcredit,lastFold_append_right _ _ (allSegs_nonempty _ _ _)]
      exact htrace

theorem schedule_rooted (leaves : IndexGroup → FtsLeaf) (hinj : Function.Injective leaves) :
    RootedTree credit 14 15 (readSum (schedule (sortedLeaves leaves)))
      (scheduleCredit credit (schedule (sortedLeaves leaves)))
      (lastFold (schedule (sortedLeaves leaves))) := by
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
  have ht := allSegs_trace_root credit v rest [] hs hb hL
  have htree := trace_root credit ht [] rfl
  rw [hlen] at htree
  simpa only [hsch,SiggolfReverseSchedule.leafSum,SiggolfReverseSchedule.foldSum,creditSum,List.map_nil,List.sum_nil,Nat.add_zero,ftsOpenings] using htree

open OracleComp

theorem recoverRun_rooted (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    RootedTree credit 14 15 r.folds (((decodedFolds fts).map credit).sum)
      ((decodedFolds fts).getLastD 0) := by
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have ht := schedule_rooted credit leaves hadm.1
  have he := recoverRun_decodedFolds_eq f parameter index leaves fts r hrun
  have hc : scheduleCredit credit (schedule (sortedLeaves leaves)) =
      ((decodedFolds fts).map credit).sum := by
    rw [he,List.map_map]
    rfl
  have hf : readSum (schedule (sortedLeaves leaves))=r.folds := by
    rw [readSum,←he]
    exact recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  have hl : lastFold (schedule (sortedLeaves leaves))=(decodedFolds fts).getLastD 0 := by
    rw [he]; rfl
  rwa [hc,hf,hl] at ht

theorem rooted_decomposition {h k f c a : Nat} (ht : RootedTree credit h k f c a)
    (hk : 2≤k) :
    ∃ p q fl fr cl cr, a<h ∧ p+q=k ∧ Tree credit (h-a-1) p fl cl ∧
      Tree credit (h-a-1) q fr cr ∧ f=a+fl+fr ∧ c=credit a+cl+cr := by
  cases ht with
  | leaf => omega
  | fork a p q fl fr cl cr ha left right =>
      exact ⟨p,q,fl,fr,cl,cr,ha,rfl,left,right,rfl,rfl⟩

/-- Accepted decoding identifies the root unary prefix with the LAST segment. -/
theorem recoverRun_root_decomposition (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    let a := (decodedFolds fts).getLastD 0
    ∃ p q fl fr cl cr,
      a<14 ∧ p+q=15 ∧ Tree credit (14-a-1) p fl cl ∧ Tree credit (14-a-1) q fr cr ∧
      r.folds=a+fl+fr ∧ ((decodedFolds fts).map credit).sum=credit a+cl+cr := by
  dsimp only
  have ht := recoverRun_rooted credit f parameter index leaves fts r hrun
  exact rooted_decomposition credit ht (by decide)

end SiggolfReverseRootLast


namespace SiggolfReverse2322CostBridge
open OracleComp SphincsSecurity SphincsSecurity.Concrete SphincsSecurity.Completeness
open SigGolfCandidate.Research.PorsPositiveBound
open SiggolfPrefixCertificate SiggolfReverse2322
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def extra (a : Nat) : Nat := if 3≤a then 1 else 0

def cheapSegment (a : Nat) : Nat := 16+16*a-credit a

def cheapSegments (as : List Nat) : Nat := (as.map cheapSegment).sum

theorem segment_add_credit (a : Nat) : cheapSegment a+credit a=16+16*a := by
  unfold cheapSegment credit oldCredit
  split <;> split <;> omega

theorem segments_add_credit (as : List Nat) :
    cheapSegments as+(as.map credit).sum=16*as.length+16*as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have h:=segment_add_credit a
    simp only [cheapSegments,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

/-- Universal accepted-schedule bound. The last/root segment receives no
lookahead branch saving, hence its one-cycle reserve is restored exactly.
This theorem does not assert any machine implementation of cheapSegment. -/
theorem recoverRun_cost_le (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : PorsMachine.Run)
    (hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts = some r) :
    cheapSegments (decodedFolds fts)+extra ((decodedFolds fts).getLastD 0)≤2322 := by
  obtain ⟨p,q,fl,fr,cl,cr,ha,hk,left,right,hfold,hcred⟩ :=
    SiggolfReverseRootLast.recoverRun_root_decomposition credit f parameter index leaves fts r hrun
  obtain ⟨slot,hperm,hsorted,hsegments,hfolds,hadm,hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  have hf : r.folds≤117 := by rw [hfolds]; exact hadm.2
  have hb := root_bound ha hk left right (by omega)
  have hc := segments_add_credit (decodedFolds fts)
  have hsum := recoverRun_decodedFolds_sum f parameter index leaves fts r hrun
  have hlen : (decodedFolds fts).length=29 := by simp [decodedFolds,ftsSegments,ftsOpenings]
  rw [hsum,hlen] at hc
  have hcr : credit ((decodedFolds fts).getLastD 0)=oldCredit ((decodedFolds fts).getLastD 0)+extra ((decodedFolds fts).getLastD 0) := rfl
  rw [hcr] at hcred
  omega

end SiggolfReverse2322CostBridge

namespace SigGolfCandidate.Research.PorsPositiveBound
/-- The root segment does not use a copied suffix and retains the branch cycle. -/
def exactSegmentCost (a : Nat) : Nat := if a = 0 then 15 else 16+16*a
end SigGolfCandidate.Research.PorsPositiveBound

namespace SiggolfReverse2322CostBridge
open SigGolfCandidate.Research.PorsPositiveBound
theorem cheapSegment_add_extra (a : Nat) : cheapSegment a + extra a = exactSegmentCost a := by
  unfold cheapSegment extra exactSegmentCost SiggolfReverse2322.credit SiggolfReverse2322.oldCredit
  split_ifs <;> omega
end SiggolfReverse2322CostBridge

/-! ## PorsExactMachine -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem exactSegmentCost_identity : ∀ V : Fin 3, ∀ a : Fin 15,
    4+(if a.val<3 then 3 else 4)+8+(if a.val=0 then 0 else 2+foldBudget V.val a.val 0) =
      (if a.val=0 then 15 else 16+16*a.val-segmentSave V.val a.val) := by decide +kernel


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
      (if a = 0 then 15 else 16+16*a-segmentSave V a) + AT V (folds + a) ≤ A)
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
  have hbl : b < 256 := wbyte_lt _ _
  by_cases hp : 0 < b % 16 ∧ (b / 32 % 2 ≠ E % 2 ∨ (3 ≤ b % 16 ∧ b / 32 / 2 ≠ E / 2 % 4))
  · rw [if_pos hp, cc_pure, hnone]
    obtain ⟨k, u, hk, hst, hf, h5, h10⟩ := hpar (by omega) ha14 (by
      rw [guardTag_iff b E hbl]
      omega)
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hp, cc_bind, pendingHash_eq]
    have hpar' : b % 16 = 0 ∨ guardTag b E := by
      rw [guardTag_iff b E hbl]
      omega
    obtain ⟨k, u, hk, hst, hf, h5, hv, hin, hbl, hpost⟩ := hacc ha14 hpar'
    have hVl := segV_lt (tsel s) b
    set a := b % 16 with hadef
    set V := segV (tsel s) b with hV
    -- after the pending hash
    have H : ∀ ans, GoodQ (writeHash u ans) (NT V + 17 * 14 + 2) (CT V + 17 * a) (folds + a ≤ 117) (AT V (folds + a) + (if a=0 then 0 else 2+foldBudget V a 0))
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
          u2 (by omega) hP2 hP2.parity
        have hb := foldBudget_old_bound ⟨V,hVl⟩ ⟨a,by omega⟩
        simp only at hb
        rw [if_neg ha0]
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
    have hk8 : k ≤ 8 := by unfold tabCycles at hk; split_ifs at hk <;> omega
    refine GoodQ.steps' hst h3 (by have := hN V hVl; omega) (by have := hC V a hVl ha14; omega) ?_
    intro q
    refine ⟨by omega, ?_⟩
    have hcost := hA V a hVl ha14 rfl rfl q
    have hk' : k ≤ 4+(if a<3 then 3 else 4) := by simpa only [tabCycles,segA,←hadef] using hk
    have hid := exactSegmentCost_identity ⟨V,hVl⟩ ⟨a,by omega⟩
    simp only at hid
    omega

end SigGolfCandidate.Verify

/-! ## PorsExactComposition -/
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp
open SigGolfCandidate.Research.PorsPositiveBound

open SiggolfReverse2322CostBridge

def decodedFold (wl : List Byte) (j : Nat) : Nat := wbyte wl (Equiv.segPtr wl j) % 16
def decodedCostFrom (wl : List Byte) (j n : Nat) : Nat :=
  ((List.range' j n).map fun k => cheapSegment (decodedFold wl k)).sum
def decodedCostRem (wl : List Byte) (j : Nat) : Nat := decodedCostFrom wl j (29-j) + SiggolfReverse2322CostBridge.extra (decodedFold wl 28)

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
  unfold cheapSegment SiggolfReverse2322.credit SiggolfReverse2322.oldCredit
  split_ifs <;> omega

theorem decodedCostRem_ge (wl : List Byte) (j : Nat) (hj : j < 29) :
    15 ≤ decodedCostRem wl j := by
  rw [decodedCostRem_succ wl j hj]
  have := cheapSegment_ge (decodedFold wl j)
  omega

/-- A witness-dependent accepting budget. It retains every zero-segment saving
and the actual remaining decoded folds, independent of the final fold cap. -/
def Aexact (wl : List Byte) (s d : Nat) : Nat :=
  decodedCostRem wl (2*s-d) + 6*(d+14-s) + 4*(14-s) + lrest s + 12 + layC
def AexactPF (wl : List Byte) (s d : Nat) : Nat :=
  if s = 14 then 12 + layC else 4+leafCost (s+1)+Aexact wl (s+1) (d+1)
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
      by_cases hd0 : d=0
      · have hj0 : 2*s-d=28 := by omega
        have hrem : decodedCostRem wl (2*s-d+1)=SiggolfReverse2322CostBridge.extra (decodedFold wl (2*s-d)) := by
          rw [hj0]
          simp [decodedCostRem,decodedCostFrom]
        simp only [AexactPF,if_pos h14,Aexact]
        omega
      · have hrem := decodedCostRem_ge wl (2*s-d+1) (by omega)
        have hx : SiggolfReverse2322CostBridge.extra (decodedFold wl (2*s-d))≤1 := by
          unfold SiggolfReverse2322CostBridge.extra; split_ifs <;> omega
        simp only [AexactPF,if_pos h14,Aexact]
        omega
    · have he : 2*(s+1)-(d+1) = 2*s-d+1 := by omega
      have hl := lrest_succ s (by omega)
      simp only [AexactPF, if_neg h14, Aexact, he]
      omega
  · unfold Aexact; omega


theorem machineSegmentCost_M (a : Nat) :
    (if a=0 then 15 else 16+16*a-segmentSave 0 a) = cheapSegment a := by
  unfold cheapSegment segmentSave noJoin SiggolfReverse2322.credit SiggolfReverse2322.oldCredit
  simp only [show (0 : Nat) < 2 by decide, true_and]
  split_ifs <;> omega

theorem machineSegmentCost_PF (s a : Nat) :
    (if a=0 then 15 else 16+16*a-segmentSave (if s=14 then 2 else 1) a) =
      (if s=14 then exactSegmentCost a else cheapSegment a) := by
  unfold cheapSegment exactSegmentCost segmentSave noJoin SiggolfReverse2322.credit SiggolfReverse2322.oldCredit
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

def cycleBoundDecoded (wl : List Byte) : Nat := 457 + layC + decodedCostRem wl 0

theorem exact_cost_vals (wl : List Byte) :
    leafCost 0 + Aexact wl 0 0 = 334 + layC + decodedCostRem wl 0 := by
  have h0 : leafCost 0 = 11 := rfl
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
    have H : ∀ a, GoodQ (writeHash t a) (91 + (leafCost 0 + Nseg 0 0)) (91 + (leafCost 0 + Cseg 0 0)) True
        (91 + (leafCost 0 + Aexact wl 0 0))
        (cc (do
          let r ← porsRoot (idxOf a.toNat) (leavesOf a.toNat) wl
          match r with
          | none => pure false
          | some M => do
            let o ← verifyLayers wl (idxOf a.toNat) nLayers (Ref.P ++ M)
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

open SiggolfReverse2322CostBridge

theorem decodedLast_eq (wl : List Byte) :
    (decodedFolds (Equiv.witFts wl)).getLastD 0=decodedFold wl 28 := by
  have hn : decodedFolds (Equiv.witFts wl)≠[] := by
    simp [decodedFolds,SphincsSecurity.ftsSegments,SphincsSecurity.ftsOpenings]
  rw [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast hn,Option.getD_some]
  unfold decodedFolds at hn ⊢
  rw [List.getLast_ofFn]
  rfl

theorem decodedCostRem_eq (wl : List Byte) :
    decodedCostRem wl 0 = cheapSegments (decodedFolds (Equiv.witFts wl)) +
      SiggolfReverse2322CostBridge.extra ((decodedFolds (Equiv.witFts wl)).getLastD 0) := by
  rw [decodedLast_eq]
  unfold decodedCostRem decodedCostFrom cheapSegments
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
      exact SiggolfReverse2322CostBridge.recoverRun_cost_le f 0 index leaves (witFts wl) r hr

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
zero-inclusive compressed-tree certificate, with the final root cost restored. -/
theorem main_good_tight (ml pkl wl : List Byte) (hml : ml.length = 32)
    (hpk : pkl.length = 16) (hwl : wl.length = 16384) (s : MachineState)
    (hs : InitOK ml pkl wl s) :
    GoodQ s fuelBound cycleBoundAll True 10272 (cc (verifyList ml pkl wl) Kb) := by
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
  omega

theorem verify_good_tight (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (s : MachineState) (hs : initialState submission .verify input = some s) :
    GoodQ s fuelBound cycleBoundAll True 10272
      (cc (verifyRef input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  exact main_good_tight _ _ _ (length_toList m) (length_toList pk)
    (by rw [length_extW]; exact congrArg (fun n => witLead + n) (length_toList w)) s (init_ok m pk w s hs)

/-- Every accepting execution uses at most10,272 machine cycles, universally
over hash answers and arbitrary witnesses. The witness charge is separate. -/
theorem verify_accept_cycles_tight (hash : Hash)
    (input : SigGolfCandidate.Legacy.Input submission.sizes .verify)
    (h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ 10272 := by
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
  Nat.le_trans (Verify.verify_accept_cycles_tight hash (m, pk, w) (by
    cases hv : (submission.runWith hash .verify (m, pk, w)).value with
    | none => simp [hv] at h
    | some u => cases u; rfl)) (by decide +kernel)

theorem eventSecurity : EventSecurityStatement := fun q hq adversary =>
  SphincsSecurity.security127_event q hq adversary

/-- The competition certificate for `SigGolfCandidate.submission` with `C = claimedC`. -/
theorem certificate : SigGolfCandidate.Legacy.Certificate submission claimedC :=
  certificate_of ⟨keygenRefinement, keygenTermination, signRefinement, signTermination,
    verifyRefinement, verifyTermination, verifyCycles, eventSecurity⟩

end SigGolfCandidate.Final
