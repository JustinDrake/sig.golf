import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Images.Verify
import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem sign_table_check : (List.range 628).all (fun i => decide (signData.getD i 0 = tableByte i)) = true := by
  decide +kernel

private theorem expand_table_check : (List.range 628).all (fun i => decide (expandData.getD i 0 = tableByte i)) = true := by
  decide +kernel

private theorem verify_sum_check : (List.range 128).all (fun i => decide
    (verifyData.getD i 0 = BitVec.ofNat 8 (rankLookup i))) = true := by
  decide +kernel

theorem signData_table (i : Nat) (hi : i < 628) : signData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp sign_table_check) i (List.mem_range.mpr hi)

theorem expandData_table (i : Nat) (hi : i < 628) : expandData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp expand_table_check) i (List.mem_range.mpr hi)

theorem verifyData_sum (i : Nat) (hi : i < 128) : verifyData.getD i 0 = BitVec.ofNat 8 (rankLookup i) := by
  simpa using (List.all_eq_true.mp verify_sum_check) i (List.mem_range.mpr hi)

theorem signData_length : signData.length = 4096 := by decide +kernel
theorem expandData_length : expandData.length = 4096 := by decide +kernel
theorem verifyData_length : verifyData.length = 4096 := by decide +kernel

end SigGolfCandidate.T3M.Search
