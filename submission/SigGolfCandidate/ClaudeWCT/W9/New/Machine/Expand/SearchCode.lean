import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.Rv.Api
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

namespace ClaudeWCT.W9.Machine.Expand.SearchCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 16384
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem toNat_four : (4 : Word).toNat = 4 := rfl
def seg_0 : List (BitVec 32) := [2097975,197395,6939747]
def seg_3 : List (BitVec 32) := [566231151]
def seg_4 : List (BitVec 32) := [134711,302910995,4919,0xc0130313,7223331,34181907,7224355,132407,302318867,67110291,132663,369493523]
def seg_16 : List (BitVec 32) := [115]
def seg_17 : List (BitVec 32) := [134711,370019859,932611,33248019,5047,0xfff38393,7566131,469962851]
def seg_25 : List (BitVec 32) := [134711,370019859,932995,45931667,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,409794659]
def seg_37 : List (BitVec 32) := [134711,370019859,9321603,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,376238691]
def seg_48 : List (BitVec 32) := [134711,370019859,9321603,22862995,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,309131875]
def seg_60 : List (BitVec 32) := [134711,370019859,9321603,44883091,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,275575395]
def seg_72 : List (BitVec 32) := [134711,370019859,17710211,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,0xc6cfc63]
def seg_83 : List (BitVec 32) := [134711,370019859,17710211,22862995,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,0xa6cf463]
def seg_95 : List (BitVec 32) := [134711,370019859,17710211,44883091,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,0x66cfc63]
def seg_107 : List (BitVec 32) := [134711,370019859,26098819,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,74249827]
def seg_118 : List (BitVec 32) := [134711,370019859,26098819,22862995,0x7fcfc13,8182931,17207,0xfff30313,7142579,17207,0xe9030313,7143011]
def seg_130 : List (BitVec 32) := [35330835,35347219,134711,0x550e0e13,23998499,25165935]
def seg_136 : List (BitVec 32) := [1673619]
def seg_137 : List (BitVec 32) := [0xdddff06f]
def seg_138 : List (BitVec 32) := [1049235,1049875]
def seg_140 : List (BitVec 32) := [115]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (3, seg_3), (4, seg_4), (16, seg_16), (17, seg_17), (25, seg_25), (37, seg_37), (48, seg_48), (60, seg_60), (72, seg_72), (83, seg_83), (95, seg_95), (107, seg_107), (118, seg_118), (130, seg_130), (136, seg_136), (137, seg_137), (138, seg_138), (140, seg_140)]
def code : List (BitVec 32) := layoutCode layout
theorem layout_ok : layoutOk 0 layout = true := by decide +kernel
theorem code_eq : code = [0x00200337, 0x00030313, 0x0069e463, 0x21c0006f, 0x00020e37, 0x120e0e13, 0x00001337, 0xc0130313, 0x006e3823, 0x02099313, 0x006e3c23, 0x00020537, 0x12050513, 0x04000593, 0x00020637, 0x16060613, 0x00000073, 0x00020e37, 0x160e0e13, 0x000e3b03, 0x01fb5313, 0x000013b7, 0xfff38393, 0x00737333, 0x1c031063, 0x00020e37, 0x160e0e13, 0x000e3c83, 0x02bcdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x186cf863, 0x00020e37, 0x160e0e13, 0x008e3c83, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x166cf263, 0x00020e37, 0x160e0e13, 0x008e3c83, 0x015cdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x126cfa63, 0x00020e37, 0x160e0e13, 0x008e3c83, 0x02acdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x106cf263, 0x00020e37, 0x160e0e13, 0x010e3c83, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x0c6cfc63, 0x00020e37, 0x160e0e13, 0x010e3c83, 0x015cdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x0a6cf463, 0x00020e37, 0x160e0e13, 0x010e3c83, 0x02acdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x066cfc63, 0x00020e37, 0x160e0e13, 0x018e3c83, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x046cf663, 0x00020e37, 0x160e0e13, 0x018e3c83, 0x015cdc93, 0x07fcfc13, 0x007cdc93, 0x00004337, 0xfff30313, 0x006cfcb3, 0x00004337, 0xe9030313, 0x006cfe63, 0x021b1b13, 0x021b5b13, 0x00020e37, 0x550e0e13, 0x016e3023, 0x0180006f, 0x00198993, 0xdddff06f, 0x00100293, 0x00100513, 0x00000073] := by decide +kernel
theorem codeAt_0 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 0)) seg_0 :=
  codeAt_sublayout h layout_ok (i := 0) (by kernel_rfl)
theorem codeAt_3 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 3)) seg_3 :=
  codeAt_sublayout h layout_ok (i := 1) (by kernel_rfl)
theorem codeAt_4 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 4)) seg_4 :=
  codeAt_sublayout h layout_ok (i := 2) (by kernel_rfl)
theorem codeAt_16 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 16)) seg_16 :=
  codeAt_sublayout h layout_ok (i := 3) (by kernel_rfl)
theorem codeAt_17 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 17)) seg_17 :=
  codeAt_sublayout h layout_ok (i := 4) (by kernel_rfl)
theorem codeAt_25 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 25)) seg_25 :=
  codeAt_sublayout h layout_ok (i := 5) (by kernel_rfl)
theorem codeAt_37 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 37)) seg_37 :=
  codeAt_sublayout h layout_ok (i := 6) (by kernel_rfl)
theorem codeAt_48 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 48)) seg_48 :=
  codeAt_sublayout h layout_ok (i := 7) (by kernel_rfl)
theorem codeAt_60 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 60)) seg_60 :=
  codeAt_sublayout h layout_ok (i := 8) (by kernel_rfl)
theorem codeAt_72 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 72)) seg_72 :=
  codeAt_sublayout h layout_ok (i := 9) (by kernel_rfl)
theorem codeAt_83 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 83)) seg_83 :=
  codeAt_sublayout h layout_ok (i := 10) (by kernel_rfl)
theorem codeAt_95 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 95)) seg_95 :=
  codeAt_sublayout h layout_ok (i := 11) (by kernel_rfl)
theorem codeAt_107 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 107)) seg_107 :=
  codeAt_sublayout h layout_ok (i := 12) (by kernel_rfl)
theorem codeAt_118 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 118)) seg_118 :=
  codeAt_sublayout h layout_ok (i := 13) (by kernel_rfl)
theorem codeAt_130 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 130)) seg_130 :=
  codeAt_sublayout h layout_ok (i := 14) (by kernel_rfl)
theorem codeAt_136 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 136)) seg_136 :=
  codeAt_sublayout h layout_ok (i := 15) (by kernel_rfl)
theorem codeAt_137 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 137)) seg_137 :=
  codeAt_sublayout h layout_ok (i := 16) (by kernel_rfl)
theorem codeAt_138 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 138)) seg_138 :=
  codeAt_sublayout h layout_ok (i := 17) (by kernel_rfl)
theorem codeAt_140 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) : CodeAt im (pcOf (b + 140)) seg_140 :=
  codeAt_sublayout h layout_ok (i := 18) (by kernel_rfl)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 1247) 200
theorem run_0 (b : Nat) : symRun { noAlias := true } seg_0 (pcOf (b + 0)) 200 =
    some ⟨blk_0.res.st, rebase blk_0.res.pc (pcOf b + 4 + 4 + (BitVec.ofNat 64 8)) (pcOf b + 4 + 4 + 4), blk_0.res.stop, blk_0.res.steps, blk_0.res.cycles⟩ := by
  krfl
theorem run'_0 (b : Nat) : symRun { noAlias := true } seg_0 (pcOf (b + 0)) 200 =
    some ⟨blk_0.res.st, rebase blk_0.res.pc (pcOf (b + 4)) (pcOf (b + 3)), blk_0.res.stop, blk_0.res.steps, blk_0.res.cycles⟩ := by
  have e1 : (pcOf b + 4 + 4 + (BitVec.ofNat 64 8)) = pcOf (b + 4) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf b + 4 + 4 + 4) = pcOf (b + 3) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_0 b, e1, e2]
sym_block blk_3 := symRun { noAlias := true } seg_3 (pcOf 1250) 200
theorem run_3 (b : Nat) : symRun { noAlias := true } seg_3 (pcOf (b + 3)) 200 =
    some ⟨blk_3.res.st, rebase blk_3.res.pc (pcOf (b + 3) + (BitVec.ofNat 64 540)) 0, blk_3.res.stop, blk_3.res.steps, blk_3.res.cycles⟩ := by
  krfl
theorem run'_3 (b : Nat) : symRun { noAlias := true } seg_3 (pcOf (b + 3)) 200 =
    some ⟨blk_3.res.st, rebase blk_3.res.pc (pcOf (b + 138)) 0, blk_3.res.stop, blk_3.res.steps, blk_3.res.cycles⟩ := by
  have e1 : (pcOf (b + 3) + (BitVec.ofNat 64 540)) = pcOf (b + 138) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_3 b, e1]
sym_block blk_4 := symRun { noAlias := true } seg_4 (pcOf 1251) 200
theorem run_4 (b : Nat) : symRun { noAlias := true } seg_4 (pcOf (b + 4)) 200 =
    some ⟨blk_4.res.st, rebase blk_4.res.pc (pcOf (b + 4) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) 0, blk_4.res.stop, blk_4.res.steps, blk_4.res.cycles⟩ := by
  krfl
theorem run'_4 (b : Nat) : symRun { noAlias := true } seg_4 (pcOf (b + 4)) 200 =
    some ⟨blk_4.res.st, rebase blk_4.res.pc (pcOf (b + 16)) 0, blk_4.res.stop, blk_4.res.steps, blk_4.res.cycles⟩ := by
  have e1 : (pcOf (b + 4) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 16) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_4 b, e1]
sym_block blk_17 := symRun { noAlias := true } seg_17 (pcOf 1264) 200
theorem run_17 (b : Nat) : symRun { noAlias := true } seg_17 (pcOf (b + 17)) 200 =
    some ⟨blk_17.res.st, rebase blk_17.res.pc (pcOf (b + 17) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 448)) (pcOf (b + 17) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_17.res.stop, blk_17.res.steps, blk_17.res.cycles⟩ := by
  krfl
theorem run'_17 (b : Nat) : symRun { noAlias := true } seg_17 (pcOf (b + 17)) 200 =
    some ⟨blk_17.res.st, rebase blk_17.res.pc (pcOf (b + 136)) (pcOf (b + 25)), blk_17.res.stop, blk_17.res.steps, blk_17.res.cycles⟩ := by
  have e1 : (pcOf (b + 17) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 448)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 17) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 25) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_17 b, e1, e2]
sym_block blk_25 := symRun { noAlias := true } seg_25 (pcOf 1272) 200
theorem run_25 (b : Nat) : symRun { noAlias := true } seg_25 (pcOf (b + 25)) 200 =
    some ⟨blk_25.res.st, rebase blk_25.res.pc (pcOf (b + 25) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 400)) (pcOf (b + 25) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_25.res.stop, blk_25.res.steps, blk_25.res.cycles⟩ := by
  krfl
theorem run'_25 (b : Nat) : symRun { noAlias := true } seg_25 (pcOf (b + 25)) 200 =
    some ⟨blk_25.res.st, rebase blk_25.res.pc (pcOf (b + 136)) (pcOf (b + 37)), blk_25.res.stop, blk_25.res.steps, blk_25.res.cycles⟩ := by
  have e1 : (pcOf (b + 25) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 400)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 25) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 37) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_25 b, e1, e2]
sym_block blk_37 := symRun { noAlias := true } seg_37 (pcOf 1284) 200
theorem run_37 (b : Nat) : symRun { noAlias := true } seg_37 (pcOf (b + 37)) 200 =
    some ⟨blk_37.res.st, rebase blk_37.res.pc (pcOf (b + 37) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 356)) (pcOf (b + 37) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_37.res.stop, blk_37.res.steps, blk_37.res.cycles⟩ := by
  krfl
theorem run'_37 (b : Nat) : symRun { noAlias := true } seg_37 (pcOf (b + 37)) 200 =
    some ⟨blk_37.res.st, rebase blk_37.res.pc (pcOf (b + 136)) (pcOf (b + 48)), blk_37.res.stop, blk_37.res.steps, blk_37.res.cycles⟩ := by
  have e1 : (pcOf (b + 37) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 356)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 37) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 48) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_37 b, e1, e2]
sym_block blk_48 := symRun { noAlias := true } seg_48 (pcOf 1295) 200
theorem run_48 (b : Nat) : symRun { noAlias := true } seg_48 (pcOf (b + 48)) 200 =
    some ⟨blk_48.res.st, rebase blk_48.res.pc (pcOf (b + 48) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 308)) (pcOf (b + 48) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_48.res.stop, blk_48.res.steps, blk_48.res.cycles⟩ := by
  krfl
theorem run'_48 (b : Nat) : symRun { noAlias := true } seg_48 (pcOf (b + 48)) 200 =
    some ⟨blk_48.res.st, rebase blk_48.res.pc (pcOf (b + 136)) (pcOf (b + 60)), blk_48.res.stop, blk_48.res.steps, blk_48.res.cycles⟩ := by
  have e1 : (pcOf (b + 48) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 308)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 48) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 60) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_48 b, e1, e2]
sym_block blk_60 := symRun { noAlias := true } seg_60 (pcOf 1307) 200
theorem run_60 (b : Nat) : symRun { noAlias := true } seg_60 (pcOf (b + 60)) 200 =
    some ⟨blk_60.res.st, rebase blk_60.res.pc (pcOf (b + 60) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 260)) (pcOf (b + 60) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_60.res.stop, blk_60.res.steps, blk_60.res.cycles⟩ := by
  krfl
theorem run'_60 (b : Nat) : symRun { noAlias := true } seg_60 (pcOf (b + 60)) 200 =
    some ⟨blk_60.res.st, rebase blk_60.res.pc (pcOf (b + 136)) (pcOf (b + 72)), blk_60.res.stop, blk_60.res.steps, blk_60.res.cycles⟩ := by
  have e1 : (pcOf (b + 60) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 260)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 60) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 72) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_60 b, e1, e2]
sym_block blk_72 := symRun { noAlias := true } seg_72 (pcOf 1319) 200
theorem run_72 (b : Nat) : symRun { noAlias := true } seg_72 (pcOf (b + 72)) 200 =
    some ⟨blk_72.res.st, rebase blk_72.res.pc (pcOf (b + 72) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 216)) (pcOf (b + 72) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_72.res.stop, blk_72.res.steps, blk_72.res.cycles⟩ := by
  krfl
theorem run'_72 (b : Nat) : symRun { noAlias := true } seg_72 (pcOf (b + 72)) 200 =
    some ⟨blk_72.res.st, rebase blk_72.res.pc (pcOf (b + 136)) (pcOf (b + 83)), blk_72.res.stop, blk_72.res.steps, blk_72.res.cycles⟩ := by
  have e1 : (pcOf (b + 72) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 216)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 72) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 83) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_72 b, e1, e2]
sym_block blk_83 := symRun { noAlias := true } seg_83 (pcOf 1330) 200
theorem run_83 (b : Nat) : symRun { noAlias := true } seg_83 (pcOf (b + 83)) 200 =
    some ⟨blk_83.res.st, rebase blk_83.res.pc (pcOf (b + 83) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 168)) (pcOf (b + 83) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_83.res.stop, blk_83.res.steps, blk_83.res.cycles⟩ := by
  krfl
theorem run'_83 (b : Nat) : symRun { noAlias := true } seg_83 (pcOf (b + 83)) 200 =
    some ⟨blk_83.res.st, rebase blk_83.res.pc (pcOf (b + 136)) (pcOf (b + 95)), blk_83.res.stop, blk_83.res.steps, blk_83.res.cycles⟩ := by
  have e1 : (pcOf (b + 83) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 168)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 83) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 95) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_83 b, e1, e2]
sym_block blk_95 := symRun { noAlias := true } seg_95 (pcOf 1342) 200
theorem run_95 (b : Nat) : symRun { noAlias := true } seg_95 (pcOf (b + 95)) 200 =
    some ⟨blk_95.res.st, rebase blk_95.res.pc (pcOf (b + 95) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 120)) (pcOf (b + 95) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_95.res.stop, blk_95.res.steps, blk_95.res.cycles⟩ := by
  krfl
theorem run'_95 (b : Nat) : symRun { noAlias := true } seg_95 (pcOf (b + 95)) 200 =
    some ⟨blk_95.res.st, rebase blk_95.res.pc (pcOf (b + 136)) (pcOf (b + 107)), blk_95.res.stop, blk_95.res.steps, blk_95.res.cycles⟩ := by
  have e1 : (pcOf (b + 95) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 120)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 95) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 107) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_95 b, e1, e2]
sym_block blk_107 := symRun { noAlias := true } seg_107 (pcOf 1354) 200
theorem run_107 (b : Nat) : symRun { noAlias := true } seg_107 (pcOf (b + 107)) 200 =
    some ⟨blk_107.res.st, rebase blk_107.res.pc (pcOf (b + 107) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 76)) (pcOf (b + 107) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_107.res.stop, blk_107.res.steps, blk_107.res.cycles⟩ := by
  krfl
theorem run'_107 (b : Nat) : symRun { noAlias := true } seg_107 (pcOf (b + 107)) 200 =
    some ⟨blk_107.res.st, rebase blk_107.res.pc (pcOf (b + 136)) (pcOf (b + 118)), blk_107.res.stop, blk_107.res.steps, blk_107.res.cycles⟩ := by
  have e1 : (pcOf (b + 107) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 76)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 107) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 118) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_107 b, e1, e2]
sym_block blk_118 := symRun { noAlias := true } seg_118 (pcOf 1365) 200
theorem run_118 (b : Nat) : symRun { noAlias := true } seg_118 (pcOf (b + 118)) 200 =
    some ⟨blk_118.res.st, rebase blk_118.res.pc (pcOf (b + 118) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 28)) (pcOf (b + 118) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4), blk_118.res.stop, blk_118.res.steps, blk_118.res.cycles⟩ := by
  krfl
theorem run'_118 (b : Nat) : symRun { noAlias := true } seg_118 (pcOf (b + 118)) 200 =
    some ⟨blk_118.res.st, rebase blk_118.res.pc (pcOf (b + 136)) (pcOf (b + 130)), blk_118.res.stop, blk_118.res.steps, blk_118.res.cycles⟩ := by
  have e1 : (pcOf (b + 118) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 28)) = pcOf (b + 136) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  have e2 : (pcOf (b + 118) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = pcOf (b + 130) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_118 b, e1, e2]
sym_block blk_130 := symRun { noAlias := true } seg_130 (pcOf 1377) 200
theorem run_130 (b : Nat) : symRun { noAlias := true } seg_130 (pcOf (b + 130)) 200 =
    some ⟨blk_130.res.st, rebase blk_130.res.pc (pcOf (b + 130) + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 24)) 0, blk_130.res.stop, blk_130.res.steps, blk_130.res.cycles⟩ := by
  krfl
theorem run'_130 (b : Nat) : symRun { noAlias := true } seg_130 (pcOf (b + 130)) 200 =
    some ⟨blk_130.res.st, rebase blk_130.res.pc (pcOf (b + 141)) 0, blk_130.res.stop, blk_130.res.steps, blk_130.res.cycles⟩ := by
  have e1 : (pcOf (b + 130) + 4 + 4 + 4 + 4 + 4 + (BitVec.ofNat 64 24)) = pcOf (b + 141) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_130 b, e1]
sym_block blk_136 := symRun { noAlias := true } seg_136 (pcOf 1383) 200
theorem run_136 (b : Nat) : symRun { noAlias := true } seg_136 (pcOf (b + 136)) 200 =
    some ⟨blk_136.res.st, rebase blk_136.res.pc (pcOf (b + 136) + 4) 0, blk_136.res.stop, blk_136.res.steps, blk_136.res.cycles⟩ := by
  krfl
theorem run'_136 (b : Nat) : symRun { noAlias := true } seg_136 (pcOf (b + 136)) 200 =
    some ⟨blk_136.res.st, rebase blk_136.res.pc (pcOf (b + 137)) 0, blk_136.res.stop, blk_136.res.steps, blk_136.res.cycles⟩ := by
  have e1 : (pcOf (b + 136) + 4) = pcOf (b + 137) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_136 b, e1]
theorem dec_137 : decodeInstruction (0xdddff06f : BitVec 32) = some (.base (.JAL .x0 (BitVec.ofNat 21 2096604))) := rfl
theorem jal_137 {im : Image} {b : Nat} (h : CodeAt im (pcOf b) code) (s : MachineState) (hpc : s.pc = pcOf (b + 137)) :
    Steps im s 1 1 (s.setPC (pcOf (b + 0))) :=
  jal_x0_step (codeAt_137 h) dec_137 (by
    have e : (signExtend21 (BitVec.ofNat 21 2096604)).toNat = 18446744073709551068 := by decide
    rw [e]; omega) s hpc
sym_block blk_138 := symRun { noAlias := true } seg_138 (pcOf 1385) 200
theorem run_138 (b : Nat) : symRun { noAlias := true } seg_138 (pcOf (b + 138)) 200 =
    some ⟨blk_138.res.st, rebase blk_138.res.pc (pcOf (b + 138) + 4 + 4) 0, blk_138.res.stop, blk_138.res.steps, blk_138.res.cycles⟩ := by
  krfl
theorem run'_138 (b : Nat) : symRun { noAlias := true } seg_138 (pcOf (b + 138)) 200 =
    some ⟨blk_138.res.st, rebase blk_138.res.pc (pcOf (b + 140)) 0, blk_138.res.stop, blk_138.res.steps, blk_138.res.cycles⟩ := by
  have e1 : (pcOf (b + 138) + 4 + 4) = pcOf (b + 140) := by (apply BitVec.eq_of_toNat_eq; simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]; omega)
  rw [run_138 b, e1]
end ClaudeWCT.W9.Machine.Expand.SearchCode
