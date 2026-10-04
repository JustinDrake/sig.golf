import SigGolfCandidate.W9Machine.WctImage

namespace W9Machine.Frozen
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem image_eq : image = SigGolfCandidate.T3M.Images.verifyImage := by
  have hc : SigGolfCandidate.T3M.Images.verifyCode = codeChunks.flatten := by
    change codeChunks.foldl (fun xs ys => xs ++ id ys) [] = codeChunks.flatten
    rw [List.foldl_append_eq_append, List.map_id, List.nil_append]
  have hd : dataChunks.flatten = SigGolfCandidate.T3M.Images.verifyData := by
    change [SigGolfCandidate.T3M.Images.verifyPrefixData ++
      SigGolfCandidate.T3M.Images.verifyLegacyData].flatten = _
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl
  unfold image SigGolfCandidate.T3M.Images.verifyImage
  rw [hc, hd]
end W9Machine.Frozen
