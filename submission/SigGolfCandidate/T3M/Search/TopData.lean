import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Images.Verify
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Verify.Nonbinary.PairTables

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem sign_table_check : (List.range 628).all (fun i => decide (signData.getD i 0 = tableByte i)) = true := by
  decide +kernel

private theorem expand_table_check : (List.range 628).all (fun i => decide (expandData.getD i 0 = tableByte i)) = true := by
  decide +kernel

theorem signData_table (i : Nat) (hi : i < 628) : signData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp sign_table_check) i (List.mem_range.mpr hi)

theorem expandData_table (i : Nat) (hi : i < 628) : expandData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp expand_table_check) i (List.mem_range.mpr hi)

theorem signData_length : signData.length = 4096 := by decide +kernel
theorem expandData_length : expandData.length = 4096 := by decide +kernel
theorem verifyData_length : verifyData.length = 49152 := by decide +kernel

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

/-! T3X: the verify data starts with the 16384-byte WOTS header table; T3W's tables follow at offset 16384. -/

private theorem verify_sum_check : ((verifyData.drop 45056).take 128).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (rankLookup p.2))) = true := by decide +kernel

private theorem verify_pair_check : ((verifyData.drop 16384).take 16384).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (Verify.Nonbinary.pairLookup p.2))) = true := by decide +kernel

private theorem verify_tail_check : ((verifyData.drop 32768).take 64).zipIdx.all (fun p =>
    decide (p.1 = BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum p.2))) = true := by decide +kernel

theorem verifyData_sum (i : Nat) (hi : i < 128) :
    verifyData.getD (45056+i) 0 = BitVec.ofNat 8 (rankLookup i) := by
  exact checked_slice_get verifyData 45056 128 i (fun r => BitVec.ofNat 8 (rankLookup r)) hi
    (by simp only [List.length_take,List.length_drop,verifyData_length]; decide) verify_sum_check

theorem verifyData_pair (i : Nat) (hi : i < 16384) :
    verifyData.getD (16384+i) 0 = BitVec.ofNat 8 (Verify.Nonbinary.pairLookup i) := by
  exact checked_slice_get verifyData 16384 16384 i (fun r => BitVec.ofNat 8 (Verify.Nonbinary.pairLookup r)) hi
    (by simp only [List.length_take,List.length_drop,verifyData_length]; decide) verify_pair_check

theorem verifyData_tail (i : Nat) (hi : i < 64) :
    verifyData.getD (32768+i) 0 = BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum i) := by
  exact checked_slice_get verifyData 32768 64 i (fun r => BitVec.ofNat 8 (126 - Verify.Nonbinary.tailSum r)) hi
    (by simp only [List.length_take,List.length_drop,verifyData_length]; decide) verify_tail_check

end SigGolfCandidate.T3M.Search
