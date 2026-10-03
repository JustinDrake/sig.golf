import SigGolfCandidate.T3M.Images.DataParts
import SigGolfCandidate.T3M.Images.Sizes
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Images.Verify
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Verify.Nonbinary.PairTables

section







namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem sign_table_check : (List.range 628).all (fun i => decide (signLegacyData.getD i 0 = tableByte i)) = true := by
  decide +kernel
private theorem expand_table_check : (List.range 628).all (fun i => decide (expandLegacyData.getD i 0 = tableByte i)) = true := by
  decide +kernel
theorem signLegacyData_table (i : Nat) (hi : i < 628) : signLegacyData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp sign_table_check) i (List.mem_range.mpr hi)
theorem expandLegacyData_table (i : Nat) (hi : i < 628) : expandLegacyData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp expand_table_check) i (List.mem_range.mpr hi)
theorem signLegacyData_length : signLegacyData.length = 4096 := by decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by decide +kernel
theorem verifyLegacyData_length : verifyLegacyData.length = 67584 := by decide +kernel
private theorem checked_slice_get (bs : List (BitVec 8)) (base n i : Nat) (f : Nat → BitVec 8)
    (hi : i < n) (hlen : ((bs.drop base).take n).length = n)
    (hcheck : ((bs.drop base).take n).zipIdx.all (fun p => decide (p.1 = f p.2)) = true) :
    bs.getD (base+i) 0 = f i := by
  have hbound : i < ((bs.drop base).take n).length := by rw [hlen]; exact hi
  have hm := List.getElem_mem (l := ((bs.drop base).take n).zipIdx) (n := i)
    (by simpa only [List.length_zipIdx] using hbound)
  have hh := List.all_eq_true.mp hcheck _ hm
  have hh' : (((bs.drop base).take n).getD i 0) = f i := by
    simpa only [List.getElem_zipIdx,Nat.zero_add,decide_eq_true_eq,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hbound,Option.getD_some] using hh
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_drop,if_pos hi] using hh'
private theorem verify_sum_check : ((verifyLegacyData.drop 63488).take 128).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (rankLookup p.2))) = true := by decide +kernel
private theorem verify_pair_check : ((verifyLegacyData.drop 34816).take 16384).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (Verify.Nonbinary.pairLookup p.2))) = true := by decide +kernel
private theorem verify_tail_check : ((verifyLegacyData.drop 51200).take 64).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum p.2))) = true := by decide +kernel
theorem verifyLegacyData_sum (i : Nat) (hi : i < 128) :
    verifyLegacyData.getD (63488+i) 0 = BitVec.ofNat 8 (rankLookup i) := by
  exact checked_slice_get verifyLegacyData 63488 128 i (fun r => BitVec.ofNat 8 (rankLookup r)) hi
    (by simp only [List.length_take,List.length_drop,verifyLegacyData_length]; decide) verify_sum_check
theorem verifyLegacyData_pair (i : Nat) (hi : i < 16384) :
    verifyLegacyData.getD (34816+i) 0 = BitVec.ofNat 8 (Verify.Nonbinary.pairLookup i) := by
  exact checked_slice_get verifyLegacyData 34816 16384 i (fun r => BitVec.ofNat 8 (Verify.Nonbinary.pairLookup r)) hi
    (by simp only [List.length_take,List.length_drop,verifyLegacyData_length]; decide) verify_pair_check
theorem verifyLegacyData_tail (i : Nat) (hi : i < 64) :
    verifyLegacyData.getD (51200+i) 0 = BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum i) := by
  exact checked_slice_get verifyLegacyData 51200 64 i (fun r => BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum r)) hi
    (by simp only [List.length_take,List.length_drop,verifyLegacyData_length]; decide) verify_tail_check
end SigGolfCandidate.T3M.Search
end

section

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
theorem getD_prefixed (pre tail : List (BitVec 8)) (n i : Nat)
    (hp : pre.length = n) :
    (pre ++ tail).getD (n + i) 0 = tail.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
  rfl
theorem signData_length : signData.length = 69632 := Images.signData_length
theorem signData_table (i : Nat) (hi : i < 628) :
    signData.getD (65536 + i) 0 = tableByte i := by
  rw [signData, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_table i hi
theorem expandData_length : expandData.length = 8704 := Images.expandData_length
theorem expandData_table (i : Nat) (hi : i < 628) :
    expandData.getD (4608 + i) 0 = tableByte i := by
  rw [expandData, getD_prefixed _ _ _ _ expandPrefixData_length]; exact expandLegacyData_table i hi
theorem verifyData_length : verifyData.length = 72192 := Images.verifyData_length
theorem verifyData_sum (i : Nat) (hi : i < 128) :
    verifyData.getD (68096 + i) 0 = BitVec.ofNat 8 (rankLookup i) := by
  rw [show 68096 + i = 4608 + (63488 + i) by omega, verifyData, getD_prefixed _ _ _ _ verifyPrefixData_length]; exact verifyLegacyData_sum i hi
theorem verifyData_pair (i : Nat) (hi : i < 16384) :
    verifyData.getD (39424 + i) 0 = BitVec.ofNat 8 (Verify.Nonbinary.pairLookup i) := by
  rw [show 39424 + i = 4608 + (34816 + i) by omega, verifyData, getD_prefixed _ _ _ _ verifyPrefixData_length]; exact verifyLegacyData_pair i hi
theorem verifyData_tail (i : Nat) (hi : i < 64) :
    verifyData.getD (55808 + i) 0 = BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum i) := by
  rw [show 55808 + i = 4608 + (51200 + i) by omega, verifyData, getD_prefixed _ _ _ _ verifyPrefixData_length]; exact verifyLegacyData_tail i hi
end SigGolfCandidate.T3M.Search
end
