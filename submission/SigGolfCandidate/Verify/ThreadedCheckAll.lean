import SigGolfCandidate.Verify.ThreadedCheck4
import SigGolfCandidate.Verify.ThreadedFrames
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify.Threaded
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def layers : List Nat := [0,1,2,3,4]
theorem pairs_checked : (layers.all fun lay => pairStarts.all (pairCheck lay)) = true := by
  simp only [layers, pairStarts, List.all_cons, List.all_nil,
    pairCheck_0_0, pairCheck_0_2, pairCheck_0_4, pairCheck_0_6, pairCheck_0_8, pairCheck_0_10, pairCheck_0_12, pairCheck_0_14, pairCheck_0_16, pairCheck_0_18, pairCheck_0_21, pairCheck_0_23, pairCheck_0_25, pairCheck_0_27, pairCheck_0_29, pairCheck_0_31, pairCheck_0_33, pairCheck_0_35, pairCheck_0_37, pairCheck_0_39,
    pairCheck_1_0, pairCheck_1_2, pairCheck_1_4, pairCheck_1_6, pairCheck_1_8, pairCheck_1_10, pairCheck_1_12, pairCheck_1_14, pairCheck_1_16, pairCheck_1_18, pairCheck_1_21, pairCheck_1_23, pairCheck_1_25, pairCheck_1_27, pairCheck_1_29, pairCheck_1_31, pairCheck_1_33, pairCheck_1_35, pairCheck_1_37, pairCheck_1_39,
    pairCheck_2_0, pairCheck_2_2, pairCheck_2_4, pairCheck_2_6, pairCheck_2_8, pairCheck_2_10, pairCheck_2_12, pairCheck_2_14, pairCheck_2_16, pairCheck_2_18, pairCheck_2_21, pairCheck_2_23, pairCheck_2_25, pairCheck_2_27, pairCheck_2_29, pairCheck_2_31, pairCheck_2_33, pairCheck_2_35, pairCheck_2_37, pairCheck_2_39,
    pairCheck_3_0, pairCheck_3_2, pairCheck_3_4, pairCheck_3_6, pairCheck_3_8, pairCheck_3_10, pairCheck_3_12, pairCheck_3_14, pairCheck_3_16, pairCheck_3_18, pairCheck_3_21, pairCheck_3_23, pairCheck_3_25, pairCheck_3_27, pairCheck_3_29, pairCheck_3_31, pairCheck_3_33, pairCheck_3_35, pairCheck_3_37, pairCheck_3_39,
    pairCheck_4_0, pairCheck_4_2, pairCheck_4_4, pairCheck_4_6, pairCheck_4_8, pairCheck_4_10, pairCheck_4_12, pairCheck_4_14, pairCheck_4_16, pairCheck_4_18, pairCheck_4_21, pairCheck_4_23, pairCheck_4_25, pairCheck_4_27, pairCheck_4_29, pairCheck_4_31, pairCheck_4_33, pairCheck_4_35, pairCheck_4_37, pairCheck_4_39, Bool.and_self]
theorem frames_checked : layers.all layerFrames = true := by
  simp only [layers, List.all_cons, List.all_nil, layerFrames_0, layerFrames_1,
    layerFrames_2, layerFrames_3, layerFrames_4, Bool.and_self]
theorem topology_checked : layers.all unchangedTopologyCheck = true := by
  simp only [layers, List.all_cons, List.all_nil, unchangedTopologyCheck_0,
    unchangedTopologyCheck_1, unchangedTopologyCheck_2, unchangedTopologyCheck_3,
    unchangedTopologyCheck_4, Bool.and_self]

theorem layer_mem {lay : Nat} (hl : lay<5) : lay ∈ layers := by simp [layers]; omega

theorem pair_at {lay i : Nat} (hl : lay<5) (hi : i∈pairStarts) : pairCheck lay i = true :=
  List.all_eq_true.mp (List.all_eq_true.mp pairs_checked lay (layer_mem hl)) i hi

theorem frames_at {lay : Nat} (hl : lay<5) : layerFrames lay = true :=
  List.all_eq_true.mp frames_checked lay (layer_mem hl)

theorem topology_at {lay : Nat} (hl : lay<5) : unchangedTopologyCheck lay = true :=
  List.all_eq_true.mp topology_checked lay (layer_mem hl)

theorem variant_at {lay i d2 : Nat} (hl : lay<5) (hi : i∈pairStarts) (hd : d2<8) :
    variantCheck lay i d2 = true :=
  List.all_eq_true.mp (pair_at hl hi) d2 (List.mem_range.mpr hd)

theorem first_member {i : Nat} (hi : i<42) (hf : isFirst i=true) : i∈pairStarts := by
  interval_cases i <;> simp_all [isFirst, isSingle, pairStarts]

theorem second_member {i : Nat} (hi : i<42) (hf : isFirst i=false) (hs : isSingle i=false) :
    (i - 1) ∈ pairStarts ∧ 0 < i := by
  interval_cases i <;> simp_all [isFirst, isSingle, pairStarts]

theorem common_member {i : Nat} (hi : i<42) (hz : i≠0)
    (h : isSingle i=true ∨ isFirst i=true) : i∈pairStarts.drop 1 ++ [20,41] := by
  interval_cases i <;> simp_all [isFirst, isSingle, pairStarts]

theorem first_step_ok {lay i d2 mu : Nat} (hl : lay<5) (hi : i∈pairStarts)
    (hd : d2<8) (hm : 1≤mu) (hm7 : mu≤7) : stepOK lay i d2 mu = true := by
  have hv := variant_at hl hi hd
  simp only [variantCheck, pairStepCheck, Bool.and_eq_true] at hv
  have ho := List.all_eq_true.mp hv.1.1.1.1 (mu-1) (List.mem_range.mpr (by omega))
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hp := List.all_eq_true.mp hf.1.2 i hi
  simp only [Bool.and_eq_true] at hp
  have hd' := List.all_eq_true.mp hp.2 d2 (List.mem_range.mpr hd)
  simp only [Bool.and_eq_true] at hd'
  have hf' := List.all_eq_true.mp hd'.1.2 (mu-1) (List.mem_range.mpr (by omega))
  have heq : mu-1+1=mu := by omega
  rw [heq] at ho hf'
  exact okC_of_opt_frames ho hf'

theorem second_step_ok {lay i d2 mu : Nat} (hl : lay<5) (hi : i∈pairStarts)
    (hd : d2<8) (hm : d2<mu) (hm7 : mu≤7) : stepOK lay (i+1) d2 mu = true := by
  have hv := variant_at hl hi hd
  simp only [variantCheck, pairStepCheck, Bool.and_eq_true] at hv
  have ho := List.all_eq_true.mp hv.1.1.1.2 (mu-1-d2) (List.mem_range.mpr (by omega))
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hp := List.all_eq_true.mp hf.1.2 i hi
  simp only [Bool.and_eq_true] at hp
  have hd' := List.all_eq_true.mp hp.2 d2 (List.mem_range.mpr hd)
  simp only [Bool.and_eq_true] at hd'
  have hf' := List.all_eq_true.mp hd'.2 (mu-1-d2) (List.mem_range.mpr (by omega))
  have heq : mu-1-d2+d2=mu-1 := by omega
  have heq' : mu-1+1=mu := by omega
  simp only [heq,heq'] at ho hf'
  exact okC_of_opt_frames ho hf'

theorem second_ok {lay i d2 : Nat} (hl : lay<5) (hi : i∈pairStarts) (hd : d2<8) :
    secondOK lay i d2 = true := by
  have hv := variant_at hl hi hd
  simp only [variantCheck, Bool.and_eq_true] at hv
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hp := List.all_eq_true.mp hf.1.2 i hi
  simp only [Bool.and_eq_true] at hp
  have hd' := List.all_eq_true.mp hp.2 d2 (List.mem_range.mpr hd)
  simp only [Bool.and_eq_true] at hd'
  exact okC_of_opt_frames hv.1.1.2 hd'.1.1.1

theorem tail_ok {lay i d2 : Nat} (hl : lay<5) (hi : i∈pairStarts) (hd : d2<8) :
    tailOK lay i d2 = true := by
  have hv := variant_at hl hi hd
  simp only [variantCheck, Bool.and_eq_true] at hv
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hp := List.all_eq_true.mp hf.1.2 i hi
  simp only [Bool.and_eq_true] at hp
  exact okC_of_opt_frames hv.1.2 hp.1

theorem common_head_ok {lay i : Nat} (hl : lay<5) (hi : i∈pairStarts.drop 1 ++ [20,41]) :
    firstHeadOK lay i = true := by
  have hv := topology_at hl
  simp only [unchangedTopologyCheck, Bool.and_eq_true] at hv
  have ho := List.all_eq_true.mp hv.1.1 i hi
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hf' := List.all_eq_true.mp hf.1.1 i hi
  exact okC_of_opt_frames ho hf'

theorem first_entry_at {lay i d1 d2 : Nat} (hl : lay<5) (hi : i∈pairStarts)
    (h1 : d1<8) (h2 : d2<8) : entryCheck lay i d1 d2 = true := by
  have hv := variant_at hl hi h2
  simp only [variantCheck, Bool.and_eq_true] at hv
  exact List.all_eq_true.mp hv.2 d1 (List.mem_range.mpr h1)

theorem single_at {lay i : Nat} (hl : lay<5) (hi : i=20 ∨ i=41) : singleCheck lay i=true := by
  have h := topology_at hl
  simp only [unchangedTopologyCheck, Bool.and_eq_true] at h
  rcases hi with rfl | rfl
  · exact h.1.2
  · exact h.2

theorem single_entry_at {lay i d : Nat} (hl : lay<5) (hi : i=20 ∨ i=41) (hd : d<8) :
    optBeq (run [] [if d<7 then s1Pc lay i+2*d else nextPc' lay i] (entryIdx lay i d))
      (singleEntryExp lay i d) = true := by
  have h := single_at hl hi
  simp only [singleCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 d (List.mem_range.mpr hd)

theorem single_step_ok {lay i d2 mu : Nat} (hl : lay<5) (hi : i=20 ∨ i=41)
    (hm : 1≤mu) (hm7 : mu≤7) : stepOK lay i d2 mu = true := by
  have hs : isSingle i = true := by rcases hi with rfl | rfl <;> decide
  have hv := single_at hl hi
  simp only [singleCheck, Bool.and_eq_true] at hv
  have ho := List.all_eq_true.mp hv.2 (mu-1) (List.mem_range.mpr (by omega))
  have hf := frames_at hl
  simp only [layerFrames, Bool.and_eq_true] at hf
  have hp := List.all_eq_true.mp hf.2 i (by simp; exact hi)
  simp only [Bool.and_eq_true] at hp
  have hf' := List.all_eq_true.mp hp.2 (mu-1) (List.mem_range.mpr (by omega))
  have heq : mu-1+1=mu := by omega
  rw [heq] at ho hf'
  have he := okC_of_opt_frames ho hf'
  simpa only [stepOK, threadedStepExp, chainS1, hs, Bool.true_eq, if_true] using he

end SigGolfCandidate.Verify.Threaded
