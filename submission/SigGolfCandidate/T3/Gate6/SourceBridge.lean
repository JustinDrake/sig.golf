import SigGolfCandidate.T3.Gate6.FreshProbability
import SigGolfCandidate.T3.Core

section

namespace SigGolfResearch.Gate6
set_option maxHeartbeats 500000
theorem digestRecord_index (output : BitVec 256) :
    (digestRecord output).1.1.val=output.toNat%2^31 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_bucket (output : BitVec 256) (c : Bank) :
    ((digestRecord output).1.2 c).val=output.toNat/2^(31+25*c.val)%16 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_leaf (output : BitVec 256) (c : Bank) (j : Fin 3) :
    ((digestRecord output).2.1 c j).val=
      output.toNat/2^(31+25*c.val)/2^(4+7*j.val)%128 := by
  simp only [digestRecord,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega
theorem digestRecord_gate (output : BitVec 256) :
    (digestRecord output).2.2.1.val=output.toNat/2^206%8 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_gate_zero (output : BitVec 256) :
    (digestRecord output).2.2.1=0 ↔ output.toNat/2^206%8=0 := by
  rw [←digestRecord_gate]
  exact Fin.ext_iff
theorem digest_acceptance_iff (output : BitVec 256) :
    DigestAccepted output ↔ output.toNat/2^206%8=0 ∧
      (∀ c, Function.Injective ((digestRecord output).2.1 c)) ∧
      (∑ c,childAuth ((digestRecord output).2.1 c))≤87 := by
  change ((digestRecord output).2.2.1=0 ∧ _ ∧ _) ↔ _
  rw [digestRecord_gate_zero]
end SigGolfResearch.Gate6
end

section


namespace SigGolfResearch.Gate6.Source
open SigGolfCandidate.T3 SigGolfCandidate.Budget.Octopus
open OracleComp ENNReal Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def sortedChild (v : Triple) : List Nat := (valList v).mergeSort (· ≤ ·)
theorem sortedChild_nodup (v : Triple) :
    (sortedChild v).Nodup ↔ Function.Injective v := by
  rw [sortedChild,(List.mergeSort_perm (valList v) (· ≤ ·)).nodup_iff]
  exact valList_nodup v
theorem sortedChild_length (v : Triple) : (sortedChild v).length=3 := by
  simp [sortedChild,valList]
theorem sortedChild_eq (v : Triple) (hv : Function.Injective v) :
    sortedChild v=(valList v).toFinset.sort := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (List.pairwise_mergeSort' _ _) (Finset.pairwise_sort _ _)
  refine (List.mergeSort_perm _ _).trans ?_
  rw [List.perm_ext_iff_of_nodup ((valList_nodup v).mpr hv) (Finset.sort_nodup _ _)]
  intro a
  simp
theorem authCount_eq_octH (leaves : List Nat) (hlen : leaves.length=3) (hn : leaves.Nodup) :
    authCount leaves=octH 7 leaves := by
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
  have hab : a ≠ b := by intro he;subst b;simp at hn
  have hbc : b ≠ c := by intro he;subst c;simp at hn
  have hx1 : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr hab
  have hx2 : b ^^^ c ≠ 0 := Nat.xor_ne_zero_iff.mpr hbc
  simp only [authCount,octH,xorSum,List.drop_succ_cons,List.drop_zero,List.tail_cons,
    List.zip_cons_cons,List.zip_nil_right,List.map_cons,List.map_nil,
    List.zipWith_cons_cons,List.zipWith_nil_right,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,bitLen,hx1,hx2,ite_false]
  omega
theorem source_child_auth (v : Triple) (hv : Function.Injective v) :
    authCount (sortedChild v)=childAuth v := by
  rw [authCount_eq_octH _ (sortedChild_length v) ((sortedChild_nodup v).mpr hv),sortedChild_eq v hv]
  rfl
def rawSelections (raw : RawRecord) : List Selection :=
  List.ofFn fun c : Bank => ⟨(raw.1.2 c).val,sortedChild (raw.2.1 c)⟩
theorem source_selections (output : BitVec 256) :
    rawSelections (digestRecord output)=selections output := by
  apply List.ext_getElem
  · simp [rawSelections,selections]
  · intro c hc hc'
    simp only [rawSelections,List.getElem_ofFn,selections,List.getElem_map,List.getElem_range]
    congr 1
    · exact digestRecord_bucket output ⟨c,by simpa [rawSelections] using hc⟩
    · simp only [sortedChild,valList]
      congr 1
      apply List.ext_getElem
      · simp [valList]
      · intro j hj hj'
        simp only [sortedChild,valList,List.getElem_ofFn,List.getElem_map,List.getElem_range]
        exact digestRecord_leaf output ⟨c,by simpa [rawSelections] using hc⟩ ⟨j,by simpa using hj⟩
theorem source_leaf_condition (output : BitVec 256) :
    SigGolfCandidate.T3.admissible (selections output)=true ↔
      (∀ c,Function.Injective ((digestRecord output).2.1 c)) ∧
      28+(∑ c,authCount (sortedChild ((digestRecord output).2.1 c)))≤115 := by
  rw [←source_selections]
  simp only [rawSelections,SigGolfCandidate.T3.admissible,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    List.mem_ofFn,forall_exists_index,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  constructor
  · rintro ⟨hi,hc⟩
    exact ⟨fun c => (sortedChild_nodup _).mp (hi _ c rfl),hc⟩
  · rintro ⟨hi,hc⟩
    refine ⟨?_,hc⟩
    intro x c hx
    subst x
    exact (sortedChild_nodup _).mpr (hi c)
theorem actual_predicate_iff (output : BitVec 256) :
    digestAdmissible output=true ↔ DigestAccepted output := by
  rw [digestAdmissible,Bool.and_eq_true,source_leaf_condition,digestGate,decide_eq_true_eq,
    digest_acceptance_iff]
  have he (hi : ∀ c,Function.Injective ((digestRecord output).2.1 c)) :
      (∑ c,authCount (sortedChild ((digestRecord output).2.1 c)))=
        ∑ c,childAuth ((digestRecord output).2.1 c) :=
    Finset.sum_congr rfl (fun c _ => source_child_auth _ (hi c))
  constructor
  · rintro ⟨⟨hi,hc⟩,hg⟩
    rw [he hi] at hc
    exact ⟨hg,hi,by omega⟩
  · rintro ⟨hg,hi,hc⟩
    exact ⟨⟨hi,by rw [he hi];omega⟩,hg⟩
theorem actual_acceptance_exact :
    Pr[fun output => digestAdmissible output=true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=acceptance := by
  simp_rw [actual_predicate_iff]
  exact digest_acceptance_exact
theorem actual_mark_joint_exact (mark : MarkedLabel) :
    Pr[fun output => digestAdmissible output=true ∧ (digestRecord output).1=mark |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=acceptance/2^59 := by
  simp_rw [actual_predicate_iff]
  exact digest_mark_joint_exact mark
end SigGolfResearch.Gate6.Source
end
