import SigGolfCandidate.T3.Gate6.ProductFibres
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
attribute [local irreducible] Finset.univ
set_option backward.isDefEq.respectTransparency false

abbrev ChildSet := (powersetCard 3 (range 128))
abbrev SetFamily := Bank → ChildSet

def setCost (s : ChildSet) : Nat := octH 7 s.val.sort

def familyCost (s : SetFamily) : Nat := ∑ bank, setCost (s bank)

theorem childSet_card : Fintype.card ChildSet = 341376 := by
  rw [Fintype.card_coe,card_powersetCard,card_range]
  norm_num [Nat.choose]

theorem family_card : Fintype.card SetFamily = 341376^7 := by
  rw [Fintype.card_fun,childSet_card]
  simp only [Bank,Fintype.card_fin]

theorem child_weight_sum (y : Nat) : ∑ s : ChildSet, y^setCost s = (Q y 7).coeff 3 := by
  rw [coeff_Q y 7 3 (by decide),show (2 : Nat)^7=128 by decide]
  simp only [setCost,oc]
  convert (sum_coe_sort (powersetCard 3 (range 128)) (fun s : Finset Nat => y^octH 7 s.sort)) using 1

theorem family_weight_sum (y : Nat) : ∑ s : SetFamily, y^familyCost s = ((Q y 7).coeff 3)^7 := by
  simp only [familyCost,← prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : Bank) (s : ChildSet) => y^setCost s)]
  simp only [child_weight_sum,prod_const,card_univ,Bank,Fintype.card_fin]

/-- General form of the existing octopus no-carry truncation lemma. -/
theorem mod_pow_sum_generic {α : Type} {y n : Nat} (hn : 0<n)
    (s : Finset α) (g : α → Nat) (hc : s.card<y) :
    (∑ a ∈ s,y^g a)%y^n = ∑ a ∈ s.filter (fun a => g a<n),y^g a := by
  classical
  rw [← sum_filter_add_sum_filter_not s (fun a => g a<n)]
  obtain ⟨c,hdiv⟩ : y^n ∣ ∑ a ∈ s.filter (fun a => ¬g a<n),y^g a :=
    dvd_sum fun a ha => pow_dvd_pow y (not_lt.mp (mem_filter.mp ha).2)
  rw [hdiv,Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hy : 1≤y := by omega
  calc
    _ ≤ ∑ _a ∈ s.filter (fun a => g a<n),y^(n-1) :=
      sum_le_sum fun a ha => Nat.pow_le_pow_right hy (by have := (mem_filter.mp ha).2;omega)
    _ = (s.filter (fun a => g a<n)).card*y^(n-1) := by rw [sum_const,smul_eq_mul]
    _ ≤ s.card*y^(n-1) := Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ < y*y^(n-1) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = y^n := by rw [←pow_succ'];congr 1;omega

theorem sum_pow_mod_pred_generic {α : Type} {y : Nat} (hy : 3≤y)
    (s : Finset α) (g : α → Nat) :
    (∑ a ∈ s,y^g a)%(y-1)=s.card%(y-1) := by
  have hm : y%(y-1)=1 := by
    calc
      _ = (y-1+1)%(y-1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 1%(y-1) := Nat.add_mod_left _ _
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  rw [sum_nat_mod,sum_congr rfl fun a _ => by rw [Nat.pow_mod,hm,one_pow]]
  simp

theorem generic_capped_card {α : Type} [Fintype α] (g : α → Nat) (y cap : Nat)
    (hy : 3≤y) (hc : Fintype.card α<y-1) :
    (Finset.univ.filter (fun a => g a≤cap)).card =
      ((∑ a,y^g a)%y^(cap+1))%(y-1) := by
  classical
  rw [mod_pow_sum_generic (by omega) _ _ (by rw [card_univ];omega),
    sum_pow_mod_pred_generic hy,Nat.mod_eq_of_lt ((card_filter_le _ _).trans_lt (by rw [card_univ];exact hc))]
  exact congrArg card (filter_congr fun a _ => by omega)

def packedSetCount : Nat :=
  (((piter 3 (2^160) ((2^160)^(90+1)) 7 [0,1]).getD 3 0)^7 % (2^160)^(90+1)) % (2^160-1)

theorem packedSetCount_value : packedSetCount = 7581131291966449566946462729286713344 := by
  decide +kernel

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.family_weight_sum
#print axioms SigGolfResearch.Gate6.packedSetCount_value
