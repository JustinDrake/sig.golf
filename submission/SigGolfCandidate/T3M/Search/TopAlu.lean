import SigGolfCandidate.T3M.Search.TopExec
import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3M.Search.TopSegments

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Common two-instruction address formation before all seventeen checksum byte loads. -/
def rankPtrCode : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
sym_block rankPtrBase := symRun { noAlias := true } rankPtrCode 0#64 200

theorem rankPtr_run (pc : Word) :
    symRun { noAlias := true } rankPtrCode pc 200 =
      some ⟨rankPtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

/-- Forming a rank lookup address preserves the checksum, rolling input, and all memory. -/
theorem rankPtr_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc rankPtrCode) (hpc : s.pc = pc) (v : Digest) (j : Nat) (hj : j < 17)
    (h28 : s.getReg .x28 = topWindow v j) (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = BitVec.ofNat 64 (TOP_DATA + topRank v j) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (rankPtr_run pc) hc s hpc (by simp [rankPtrBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa only [Result.toState_getReg, rankPtrBase.res, rv_simp, h28, h30] using topRank_ptr v j hj
  · intro r hr; simp at hr; cases r <;> simp_all [rankPtrBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [rankPtrBase.res, rv_simp]


def rankStart (j : Nat) : Nat := if j = 0 then 267 else if j < 9 then 266 + 5 * j else 268 + 5 * j

theorem rankPtr_placement {image : Image} {b : Nat} (h : KernAt image b) (j : Fin 17) :
    CodeAt image (pcOf (b + rankStart j.val)) rankPtrCode := by
  fin_cases j
  · exact codeAt_top267 h
  · exact codeAt_top271 h
  · exact codeAt_top276 h
  · exact codeAt_top281 h
  · exact codeAt_top286 h
  · exact codeAt_top291 h
  · exact codeAt_top296 h
  · exact codeAt_top301 h
  · exact codeAt_top306 h
  · exact codeAt_top313 h
  · exact codeAt_top318 h
  · exact codeAt_top323 h
  · exact codeAt_top328 h
  · exact codeAt_top333 h
  · exact codeAt_top338 h
  · exact codeAt_top343 h
  · exact codeAt_top348 h

def topInitCode : List (BitVec 32) := [0x00ffff37, 0x00030e13]
sym_block topInitBase := symRun { noAlias := true } topInitCode 0#64 200

theorem topInit_run (pc : Word) : symRun { noAlias := true } topInitCode pc 200 =
    some ⟨topInitBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

theorem topInit_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc topInitCode) (hpc : s.pc = pc) (v : Digest)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x28 = topWindow v 0 ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (topInit_run pc) hc s hpc (by simp [topInitBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [topInitBase.res, rv_simp, h6, topWindow]
  · rfl
  · intro r hr; simp at hr; cases r <;> simp_all [topInitBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [topInitBase.res, rv_simp]

def rankTailCode : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
sym_block rankTailBase := symRun { noAlias := true } rankTailCode 0#64 200

theorem rankTail_run (pc : Word) : symRun { noAlias := true } rankTailCode pc 200 =
    some ⟨rankTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

theorem rankTail_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc rankTailCode) (hpc : s.pc = pc) (W : Word) (sum rank : Nat)
    (h28 : s.getReg .x28 = W) (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 (rankLookup rank)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x28 = W >>> 7 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup rank) ∧
      RegsExcept s t [.x25,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (rankTail_run pc) hc s hpc (by simp [rankTailBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [rankTailBase.res, rv_simp, h28]
  · simp [rankTailBase.res, rv_simp, h25, h29, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [rankTailBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [rankTailBase.res, rv_simp]

def rankShiftCode : List (BitVec 32) := [0x007e5e13]
sym_block rankShiftBase := symRun { noAlias := true } rankShiftCode 0#64 200

theorem rankShift_run (pc : Word) : symRun { noAlias := true } rankShiftCode pc 200 =
    some ⟨rankShiftBase.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl

theorem rankShift_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc rankShiftCode) (hpc : s.pc = pc) (W : Word) (h28 : s.getReg .x28 = W) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x28 = W >>> 7 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (rankShift_run pc) hc s hpc (by simp [rankShiftBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [rankShiftBase.res, rv_simp, h28]
  · intro r hr; simp at hr; cases r <;> simp_all [rankShiftBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [rankShiftBase.res, rv_simp]

def rankCrossCode : List (BitVec 32) := [0x00139e93, 0x01ceee33]
sym_block rankCrossBase := symRun { noAlias := true } rankCrossCode 0#64 200

theorem rankCross_run (pc : Word) : symRun { noAlias := true } rankCrossCode pc 200 =
    some ⟨rankCrossBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

theorem rankCross_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc rankCrossCode) (hpc : s.pc = pc) (v : Digest)
    (h28 : s.getReg .x28 = v.extractLsb' 0 64 >>> 63) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = topWindow v 9 ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (rankCross_run pc) hc s hpc (by simp [rankCrossBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa [rankCrossBase.res, rv_simp, h28, h7, topWindow] using topWindow_cross v
  · intro r hr; simp at hr; cases r <;> simp_all [rankCrossBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [rankCrossBase.res, rv_simp]

end SigGolfCandidate.T3M.Search
