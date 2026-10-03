import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne
import SigGolfCandidate.T3.Nonbinary.AcceptedCost

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def liveCredit (i d : Nat) : Nat := if d < topMax i then 1 else 0
def liveSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => liveCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum

theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d+liveCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit liveCredit
  split_ifs <;> omega

theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f+liveSum f=2205 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum+(l.map fun i => liveCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2205 := by decide +kernel
  exact hs.trans he

/-- Exact cost of all chains, seventeen four-instruction dispatches, and the final jump. -/
theorem total_cost_credit (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i)
    (hs : digitSum f=126) : totalCost f+17*4+1+creditSum f+liveSum f=1140 := by
  have h := total_balance f hd
  omega

/-- Every chain either saves a packed-head store or receives the existing
terminal-copy credit. Penultimate digits receive both credits. -/
theorem packed_credit_floor (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    54 ≤ creditSum f + liveSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      l.length ≤ (l.map fun i => digitCredit i (f i)).sum +
        (l.map fun i => liveCredit i (f i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hcredit : 1 ≤ digitCredit i (f i) + liveCredit i (f i) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))

theorem range_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem source_credit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : creditSum (coreDigit 0 v)=Cost.credit w := by
  unfold creditSum
  rw [range_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => digitCredit i.val (coreDigit 0 v i.val)).sum+
      (List.ofFn fun k : Fin 3 => digitCredit (51+k.val) (coreDigit 0 v (51+k.val))).sum=Cost.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold Cost.credit Cost.credit5 Cost.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse5 hp j k
    have hl : last (j.val*3+k.val)=3 := by
      unfold last topMax mx
      rw [if_pos (by have := j.isLt;have := k.isLt;omega)]
    simpa only [digitCredit,hl,Nat.mul_comm] using congrArg (fun d => if 3≤d then (1:Nat) else 0) he
  · apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse4 hp k
    have hl : last (51+k.val)=2 := by
      unfold last topMax mx
      rw [if_neg (by have := k.isLt;omega)]
    simpa only [digitCredit,hl] using congrArg (fun d => if 2≤d then (1:Nat) else 0) he

theorem source_accepted_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : 11≤creditSum (coreDigit 0 v) := by
  obtain ⟨w,hw,_,_,hc⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  rw [source_credit_parse hp]
  exact hc

theorem source_accepted_sum {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : digitSum (coreDigit 0 v)=126 := by
  obtain ⟨w,hw,_,hs,_⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  change (dataDigits 0 v).sum=126
  rw [T3.Nonbinary.dataDigits_parse hp,T3.Nonbinary.wordDigits_sum,hs]

theorem source_accepted_total {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4+1≤1086 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := packed_credit_floor (coreDigit 0 v) hd
  omega

#print axioms total_cost_credit
#print axioms source_accepted_total
end SigGolfCandidate.T3M.Nonbinary.NCtx
