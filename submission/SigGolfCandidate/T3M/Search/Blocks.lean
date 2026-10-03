import SigGolfCandidate.T3M.Search.KernelBlocks

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def dsE_0 : List (BitVec 32) := [1049399,0x50698663]
def dsS_0 : List (BitVec 32) := [1049399,0x60698a63]
def ds_0 (d : Nat) : List (BitVec 32) := if d = 30 then dsE_0 else dsS_0
def ds_2 (_d : Nat) : List (BitVec 32) := [4919,0xc0130313,34182035,134711,302910995,7223331,8272931,132407,302318867,67110291,132663,369493523]
def ds_14 (_d : Nat) : List (BitVec 32) := [115]
def dsE_15 : List (BitVec 32) := [348131567]
def dsS_15 : List (BitVec 32) := [0x74010ef]
def ds_15 (d : Nat) : List (BitVec 32) := if d = 30 then dsE_15 else dsS_15
def ds_16 (_d : Nat) : List (BitVec 32) := [431715]
def ds_17 (_d : Nat) : List (BitVec 32) := [1673619,0xfb9ff06f]
def dsL (d : Nat) : Rv.Layout := [(0, ds_0 d), (2, ds_2 d), (14, ds_14 d), (15, ds_15 d), (16, ds_16 d), (17, ds_17 d)]
theorem dsL_ok (d : Nat) : layoutOk 0 (dsL d) = true := by
  unfold dsL; by_cases h : d = 30 <;> simp [h, ds_0, ds_2, ds_14, ds_15, ds_16, ds_17, dsE_0, dsS_0, dsE_15, dsS_15, layoutOk]
def DsAt (image : Image) (d b : Nat) : Prop :=
  (CodeAt image (pcOf d) (layoutCode (dsL d)) ∧ GateAt image b) ∧ (d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543)
theorem codeAt_ds_0 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 0)) (ds_0 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 0) rfl
theorem codeAt_ds_2 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 2)) (ds_2 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 1) rfl
theorem codeAt_ds_14 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 14)) (ds_14 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 2) rfl
theorem codeAt_ds_15 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 15)) (ds_15 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 3) rfl
theorem codeAt_ds_16 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 16)) (ds_16 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 4) rfl
theorem codeAt_ds_17 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 17)) (ds_17 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 5) rfl
theorem dsAt_of {image : Image} {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543)
    (h : (image.code.drop d).take 19 = layoutCode (dsL d)) (hg : GateAt image b) : DsAt image d b := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, hg⟩, hdb⟩
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rw [← h]
    have e : (pcOf d).toNat = 0x1000 + 4 * d := by rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [e, show (0x1000 + 4 * d - 0x1000) / 4 = d by omega]
    exact List.take_prefix _ _
sym_block blkds30_0 := symRun { noAlias := true } (ds_0 30) (pcOf (30 + 0)) 100
sym_block blkds153_0 := symRun { noAlias := true } (ds_0 153) (pcOf (153 + 0)) 100
sym_block blkds30_2 := symRun { noAlias := true } (ds_2 30) (pcOf (30 + 2)) 100
sym_block blkds153_2 := symRun { noAlias := true } (ds_2 153) (pcOf (153 + 2)) 100
sym_block blkds30_15 := symRun { noAlias := true } (ds_15 30) (pcOf (30 + 15)) 100
sym_block blkds153_15 := symRun { noAlias := true } (ds_15 153) (pcOf (153 + 15)) 100
sym_block blkds30_16 := symRun { noAlias := true } (ds_16 30) (pcOf (30 + 16)) 100
sym_block blkds153_16 := symRun { noAlias := true } (ds_16 153) (pcOf (153 + 16)) 100
sym_block blkds30_17 := symRun { noAlias := true } (ds_17 30) (pcOf (30 + 17)) 100
sym_block blkds153_17 := symRun { noAlias := true } (ds_17 153) (pcOf (153 + 17)) 100
def stds_0 : SymState := blkds30_0.res.st
def pcEds_0 (d b : Nat) : E := rebase blkds30_0.res.pc (pcOf b) (pcOf (d + 2))
theorem run_ds0 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_0 d) (pcOf (d + 0)) 100 =
      some ⟨stds_0, pcEds_0 d b, blkds30_0.res.stop, blkds30_0.res.steps, blkds30_0.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_0.trans (congrArg some (by kernel_rfl))
  · exact blkds153_0.trans (congrArg some (by kernel_rfl))
def stds_2 : SymState := blkds30_2.res.st
def pcEds_2 (d b : Nat) : E := .c (pcOf (d + 14))
theorem run_ds2 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_2 d) (pcOf (d + 2)) 100 =
      some ⟨stds_2, pcEds_2 d b, blkds30_2.res.stop, blkds30_2.res.steps, blkds30_2.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_2.trans (congrArg some (by kernel_rfl))
  · exact blkds153_2.trans (congrArg some (by kernel_rfl))
def stds_15 (d : Nat) : SymState := { blkds30_15.res.st with regs := blkds30_15.res.st.regs.set Reg.x1 (.c (pcOf (d + 16))) }
def pcEds_15 (d b : Nat) : E := .c (pcOf (gatePc b))
theorem run_ds15 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_15 d) (pcOf (d + 15)) 100 =
      some ⟨stds_15 d, pcEds_15 d b, blkds30_15.res.stop, blkds30_15.res.steps, blkds30_15.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_15.trans (congrArg some (by kernel_rfl))
  · exact blkds153_15.trans (congrArg some (by kernel_rfl))
def stds_16 : SymState := blkds30_16.res.st
def pcEds_16 (d b : Nat) : E := rebase blkds30_16.res.pc (pcOf (d + 19)) (pcOf (d + 17))
theorem run_ds16 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_16 d) (pcOf (d + 16)) 100 =
      some ⟨stds_16, pcEds_16 d b, blkds30_16.res.stop, blkds30_16.res.steps, blkds30_16.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_16.trans (congrArg some (by kernel_rfl))
  · exact blkds153_16.trans (congrArg some (by kernel_rfl))
def stds_17 : SymState := blkds30_17.res.st
def pcEds_17 (d b : Nat) : E := .c (pcOf (d + 0))
theorem run_ds17 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_17 d) (pcOf (d + 17)) 100 =
      some ⟨stds_17, pcEds_17 d b, blkds30_17.res.stop, blkds30_17.res.steps, blkds30_17.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_17.trans (congrArg some (by kernel_rfl))
  · exact blkds153_17.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Search
