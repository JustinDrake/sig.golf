import SigGolfCandidate.T3M.Search.Blocks

/-! Exact subsegments of the grouped-radix top decoder. Byte reads and stores are
singletons so their sound direct-step lemmas do not impose symbolic dword alignment. -/
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedVariables false

def topSeg265 : List (BitVec 32) := [0x00ffff37, 0x00030e13]
def topSeg267 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg269 : List (BitVec 32) := [0x000ecc83]
def topSeg270 : List (BitVec 32) := [0x007e5e13]
def topSeg271 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg273 : List (BitVec 32) := [0x000ece83]
def topSeg274 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg276 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg278 : List (BitVec 32) := [0x000ece83]
def topSeg279 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg281 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg283 : List (BitVec 32) := [0x000ece83]
def topSeg284 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg286 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg288 : List (BitVec 32) := [0x000ece83]
def topSeg289 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg291 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg293 : List (BitVec 32) := [0x000ece83]
def topSeg294 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg296 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg298 : List (BitVec 32) := [0x000ece83]
def topSeg299 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg301 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg303 : List (BitVec 32) := [0x000ece83]
def topSeg304 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg306 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg308 : List (BitVec 32) := [0x000ece83]
def topSeg309 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg311 : List (BitVec 32) := [0x00139e93, 0x01ceee33]
def topSeg313 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg315 : List (BitVec 32) := [0x000ece83]
def topSeg316 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg318 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg320 : List (BitVec 32) := [0x000ece83]
def topSeg321 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg323 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg325 : List (BitVec 32) := [0x000ece83]
def topSeg326 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg328 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg330 : List (BitVec 32) := [0x000ece83]
def topSeg331 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg333 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg335 : List (BitVec 32) := [0x000ece83]
def topSeg336 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg338 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg340 : List (BitVec 32) := [0x000ece83]
def topSeg341 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg343 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg345 : List (BitVec 32) := [0x000ece83]
def topSeg346 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg348 : List (BitVec 32) := [0x07fe7e93, 0x01ee8eb3]
def topSeg350 : List (BitVec 32) := [0x000ece83]
def topSeg351 : List (BitVec 32) := [0x01dc8cb3, 0x007e5e13]
def topSeg353 : List (BitVec 32) := [0x003e7e93, 0x01dc8cb3, 0x002e5e93, 0x003efe93, 0x01dc8cb3, 0x004e5e93, 0x01dc8cb3, 0x411c8eb3, 0x1a0e9663]
def topSeg362 : List (BitVec 32) := [0x00000a13, 0x00020ab7, 0x420a8a93, 0x080f0f13, 0x07f37e13, 0x002e1e13, 0x01ee0e33]
def topSeg369 : List (BitVec 32) := [0x000e6e83]
def topSeg370 : List (BitVec 32) := [0x01da8023]
def topSeg371 : List (BitVec 32) := [0x008ede93]
def topSeg372 : List (BitVec 32) := [0x01da80a3]
def topSeg373 : List (BitVec 32) := [0x008ede93]
def topSeg374 : List (BitVec 32) := [0x01da8123]
def topSeg375 : List (BitVec 32) := [0x00735313, 0x03939e13, 0x01c36333, 0x0073d393, 0x003a8a93, 0x001a0a13, 0x011a3e13, 0xfc0e10e3]
def topSeg383 : List (BitVec 32) := [0x00337e13]
def topSeg384 : List (BitVec 32) := [0x01ca8023]
def topSeg385 : List (BitVec 32) := [0x00235313, 0x00337e13]
def topSeg387 : List (BitVec 32) := [0x01ca80a3]
def topSeg388 : List (BitVec 32) := [0x00235313, 0x00337e13]
def topSeg390 : List (BitVec 32) := [0x01ca8123]
def topSeg391 : List (BitVec 32) := [0x00008067]
def topSeg392 : List (BitVec 32) := [0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013]

def topSegLayout : Rv.Layout := [(0, topSeg265), (2, topSeg267), (4, topSeg269), (5, topSeg270), (6, topSeg271), (8, topSeg273), (9, topSeg274), (11, topSeg276), (13, topSeg278), (14, topSeg279), (16, topSeg281), (18, topSeg283), (19, topSeg284), (21, topSeg286), (23, topSeg288), (24, topSeg289), (26, topSeg291), (28, topSeg293), (29, topSeg294), (31, topSeg296), (33, topSeg298), (34, topSeg299), (36, topSeg301), (38, topSeg303), (39, topSeg304), (41, topSeg306), (43, topSeg308), (44, topSeg309), (46, topSeg311), (48, topSeg313), (50, topSeg315), (51, topSeg316), (53, topSeg318), (55, topSeg320), (56, topSeg321), (58, topSeg323), (60, topSeg325), (61, topSeg326), (63, topSeg328), (65, topSeg330), (66, topSeg331), (68, topSeg333), (70, topSeg335), (71, topSeg336), (73, topSeg338), (75, topSeg340), (76, topSeg341), (78, topSeg343), (80, topSeg345), (81, topSeg346), (83, topSeg348), (85, topSeg350), (86, topSeg351), (88, topSeg353), (97, topSeg362), (104, topSeg369), (105, topSeg370), (106, topSeg371), (107, topSeg372), (108, topSeg373), (109, topSeg374), (110, topSeg375), (118, topSeg383), (119, topSeg384), (120, topSeg385), (122, topSeg387), (123, topSeg388), (125, topSeg390), (126, topSeg391), (127, topSeg392)]
theorem topSegLayout_ok : layoutOk 0 topSegLayout = true := by decide +kernel
theorem topSegLayout_code : k_265 = layoutCode topSegLayout := by decide +kernel

theorem codeAt_top265 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 265)) topSeg265 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 0) (o := 0) (seg := topSeg265) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_265 := symRun { noAlias := true } topSeg265 (pcOf (354 + 265)) 200
sym_block tb543_265 := symRun { noAlias := true } topSeg265 (pcOf (543 + 265)) 200
def topState265 : SymState := tb354_265.res.st
def topEnd265 (b : Nat) : E := .c (pcOf (b + 267))
theorem run_top265 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg265 (pcOf (b + 265)) 200 =
      some ⟨topState265, topEnd265 b, tb354_265.res.stop, tb354_265.res.steps, tb354_265.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_265.trans (congrArg some (by kernel_rfl))
  · exact tb543_265.trans (congrArg some (by kernel_rfl))

theorem codeAt_top267 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 267)) topSeg267 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 1) (o := 2) (seg := topSeg267) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_267 := symRun { noAlias := true } topSeg267 (pcOf (354 + 267)) 200
sym_block tb543_267 := symRun { noAlias := true } topSeg267 (pcOf (543 + 267)) 200
def topState267 : SymState := tb354_267.res.st
def topEnd267 (b : Nat) : E := .c (pcOf (b + 269))
theorem run_top267 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg267 (pcOf (b + 267)) 200 =
      some ⟨topState267, topEnd267 b, tb354_267.res.stop, tb354_267.res.steps, tb354_267.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_267.trans (congrArg some (by kernel_rfl))
  · exact tb543_267.trans (congrArg some (by kernel_rfl))

theorem codeAt_top269 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 269)) topSeg269 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 2) (o := 4) (seg := topSeg269) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top270 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 270)) topSeg270 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 3) (o := 5) (seg := topSeg270) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_270 := symRun { noAlias := true } topSeg270 (pcOf (354 + 270)) 200
sym_block tb543_270 := symRun { noAlias := true } topSeg270 (pcOf (543 + 270)) 200
def topState270 : SymState := tb354_270.res.st
def topEnd270 (b : Nat) : E := .c (pcOf (b + 271))
theorem run_top270 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg270 (pcOf (b + 270)) 200 =
      some ⟨topState270, topEnd270 b, tb354_270.res.stop, tb354_270.res.steps, tb354_270.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_270.trans (congrArg some (by kernel_rfl))
  · exact tb543_270.trans (congrArg some (by kernel_rfl))

theorem codeAt_top271 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 271)) topSeg271 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 4) (o := 6) (seg := topSeg271) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_271 := symRun { noAlias := true } topSeg271 (pcOf (354 + 271)) 200
sym_block tb543_271 := symRun { noAlias := true } topSeg271 (pcOf (543 + 271)) 200
def topState271 : SymState := tb354_271.res.st
def topEnd271 (b : Nat) : E := .c (pcOf (b + 273))
theorem run_top271 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg271 (pcOf (b + 271)) 200 =
      some ⟨topState271, topEnd271 b, tb354_271.res.stop, tb354_271.res.steps, tb354_271.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_271.trans (congrArg some (by kernel_rfl))
  · exact tb543_271.trans (congrArg some (by kernel_rfl))

theorem codeAt_top273 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 273)) topSeg273 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 5) (o := 8) (seg := topSeg273) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top274 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 274)) topSeg274 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 6) (o := 9) (seg := topSeg274) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_274 := symRun { noAlias := true } topSeg274 (pcOf (354 + 274)) 200
sym_block tb543_274 := symRun { noAlias := true } topSeg274 (pcOf (543 + 274)) 200
def topState274 : SymState := tb354_274.res.st
def topEnd274 (b : Nat) : E := .c (pcOf (b + 276))
theorem run_top274 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg274 (pcOf (b + 274)) 200 =
      some ⟨topState274, topEnd274 b, tb354_274.res.stop, tb354_274.res.steps, tb354_274.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_274.trans (congrArg some (by kernel_rfl))
  · exact tb543_274.trans (congrArg some (by kernel_rfl))

theorem codeAt_top276 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 276)) topSeg276 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 7) (o := 11) (seg := topSeg276) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_276 := symRun { noAlias := true } topSeg276 (pcOf (354 + 276)) 200
sym_block tb543_276 := symRun { noAlias := true } topSeg276 (pcOf (543 + 276)) 200
def topState276 : SymState := tb354_276.res.st
def topEnd276 (b : Nat) : E := .c (pcOf (b + 278))
theorem run_top276 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg276 (pcOf (b + 276)) 200 =
      some ⟨topState276, topEnd276 b, tb354_276.res.stop, tb354_276.res.steps, tb354_276.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_276.trans (congrArg some (by kernel_rfl))
  · exact tb543_276.trans (congrArg some (by kernel_rfl))

theorem codeAt_top278 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 278)) topSeg278 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 8) (o := 13) (seg := topSeg278) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top279 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 279)) topSeg279 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 9) (o := 14) (seg := topSeg279) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_279 := symRun { noAlias := true } topSeg279 (pcOf (354 + 279)) 200
sym_block tb543_279 := symRun { noAlias := true } topSeg279 (pcOf (543 + 279)) 200
def topState279 : SymState := tb354_279.res.st
def topEnd279 (b : Nat) : E := .c (pcOf (b + 281))
theorem run_top279 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg279 (pcOf (b + 279)) 200 =
      some ⟨topState279, topEnd279 b, tb354_279.res.stop, tb354_279.res.steps, tb354_279.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_279.trans (congrArg some (by kernel_rfl))
  · exact tb543_279.trans (congrArg some (by kernel_rfl))

theorem codeAt_top281 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 281)) topSeg281 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 10) (o := 16) (seg := topSeg281) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_281 := symRun { noAlias := true } topSeg281 (pcOf (354 + 281)) 200
sym_block tb543_281 := symRun { noAlias := true } topSeg281 (pcOf (543 + 281)) 200
def topState281 : SymState := tb354_281.res.st
def topEnd281 (b : Nat) : E := .c (pcOf (b + 283))
theorem run_top281 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg281 (pcOf (b + 281)) 200 =
      some ⟨topState281, topEnd281 b, tb354_281.res.stop, tb354_281.res.steps, tb354_281.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_281.trans (congrArg some (by kernel_rfl))
  · exact tb543_281.trans (congrArg some (by kernel_rfl))

theorem codeAt_top283 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 283)) topSeg283 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 11) (o := 18) (seg := topSeg283) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top284 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 284)) topSeg284 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 12) (o := 19) (seg := topSeg284) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_284 := symRun { noAlias := true } topSeg284 (pcOf (354 + 284)) 200
sym_block tb543_284 := symRun { noAlias := true } topSeg284 (pcOf (543 + 284)) 200
def topState284 : SymState := tb354_284.res.st
def topEnd284 (b : Nat) : E := .c (pcOf (b + 286))
theorem run_top284 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg284 (pcOf (b + 284)) 200 =
      some ⟨topState284, topEnd284 b, tb354_284.res.stop, tb354_284.res.steps, tb354_284.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_284.trans (congrArg some (by kernel_rfl))
  · exact tb543_284.trans (congrArg some (by kernel_rfl))

theorem codeAt_top286 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 286)) topSeg286 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 13) (o := 21) (seg := topSeg286) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_286 := symRun { noAlias := true } topSeg286 (pcOf (354 + 286)) 200
sym_block tb543_286 := symRun { noAlias := true } topSeg286 (pcOf (543 + 286)) 200
def topState286 : SymState := tb354_286.res.st
def topEnd286 (b : Nat) : E := .c (pcOf (b + 288))
theorem run_top286 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg286 (pcOf (b + 286)) 200 =
      some ⟨topState286, topEnd286 b, tb354_286.res.stop, tb354_286.res.steps, tb354_286.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_286.trans (congrArg some (by kernel_rfl))
  · exact tb543_286.trans (congrArg some (by kernel_rfl))

theorem codeAt_top288 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 288)) topSeg288 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 14) (o := 23) (seg := topSeg288) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top289 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 289)) topSeg289 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 15) (o := 24) (seg := topSeg289) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_289 := symRun { noAlias := true } topSeg289 (pcOf (354 + 289)) 200
sym_block tb543_289 := symRun { noAlias := true } topSeg289 (pcOf (543 + 289)) 200
def topState289 : SymState := tb354_289.res.st
def topEnd289 (b : Nat) : E := .c (pcOf (b + 291))
theorem run_top289 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg289 (pcOf (b + 289)) 200 =
      some ⟨topState289, topEnd289 b, tb354_289.res.stop, tb354_289.res.steps, tb354_289.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_289.trans (congrArg some (by kernel_rfl))
  · exact tb543_289.trans (congrArg some (by kernel_rfl))

theorem codeAt_top291 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 291)) topSeg291 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 16) (o := 26) (seg := topSeg291) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_291 := symRun { noAlias := true } topSeg291 (pcOf (354 + 291)) 200
sym_block tb543_291 := symRun { noAlias := true } topSeg291 (pcOf (543 + 291)) 200
def topState291 : SymState := tb354_291.res.st
def topEnd291 (b : Nat) : E := .c (pcOf (b + 293))
theorem run_top291 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg291 (pcOf (b + 291)) 200 =
      some ⟨topState291, topEnd291 b, tb354_291.res.stop, tb354_291.res.steps, tb354_291.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_291.trans (congrArg some (by kernel_rfl))
  · exact tb543_291.trans (congrArg some (by kernel_rfl))

theorem codeAt_top293 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 293)) topSeg293 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 17) (o := 28) (seg := topSeg293) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top294 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 294)) topSeg294 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 18) (o := 29) (seg := topSeg294) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_294 := symRun { noAlias := true } topSeg294 (pcOf (354 + 294)) 200
sym_block tb543_294 := symRun { noAlias := true } topSeg294 (pcOf (543 + 294)) 200
def topState294 : SymState := tb354_294.res.st
def topEnd294 (b : Nat) : E := .c (pcOf (b + 296))
theorem run_top294 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg294 (pcOf (b + 294)) 200 =
      some ⟨topState294, topEnd294 b, tb354_294.res.stop, tb354_294.res.steps, tb354_294.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_294.trans (congrArg some (by kernel_rfl))
  · exact tb543_294.trans (congrArg some (by kernel_rfl))

theorem codeAt_top296 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 296)) topSeg296 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 19) (o := 31) (seg := topSeg296) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_296 := symRun { noAlias := true } topSeg296 (pcOf (354 + 296)) 200
sym_block tb543_296 := symRun { noAlias := true } topSeg296 (pcOf (543 + 296)) 200
def topState296 : SymState := tb354_296.res.st
def topEnd296 (b : Nat) : E := .c (pcOf (b + 298))
theorem run_top296 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg296 (pcOf (b + 296)) 200 =
      some ⟨topState296, topEnd296 b, tb354_296.res.stop, tb354_296.res.steps, tb354_296.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_296.trans (congrArg some (by kernel_rfl))
  · exact tb543_296.trans (congrArg some (by kernel_rfl))

theorem codeAt_top298 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 298)) topSeg298 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 20) (o := 33) (seg := topSeg298) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top299 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 299)) topSeg299 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 21) (o := 34) (seg := topSeg299) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_299 := symRun { noAlias := true } topSeg299 (pcOf (354 + 299)) 200
sym_block tb543_299 := symRun { noAlias := true } topSeg299 (pcOf (543 + 299)) 200
def topState299 : SymState := tb354_299.res.st
def topEnd299 (b : Nat) : E := .c (pcOf (b + 301))
theorem run_top299 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg299 (pcOf (b + 299)) 200 =
      some ⟨topState299, topEnd299 b, tb354_299.res.stop, tb354_299.res.steps, tb354_299.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_299.trans (congrArg some (by kernel_rfl))
  · exact tb543_299.trans (congrArg some (by kernel_rfl))

theorem codeAt_top301 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 301)) topSeg301 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 22) (o := 36) (seg := topSeg301) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_301 := symRun { noAlias := true } topSeg301 (pcOf (354 + 301)) 200
sym_block tb543_301 := symRun { noAlias := true } topSeg301 (pcOf (543 + 301)) 200
def topState301 : SymState := tb354_301.res.st
def topEnd301 (b : Nat) : E := .c (pcOf (b + 303))
theorem run_top301 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg301 (pcOf (b + 301)) 200 =
      some ⟨topState301, topEnd301 b, tb354_301.res.stop, tb354_301.res.steps, tb354_301.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_301.trans (congrArg some (by kernel_rfl))
  · exact tb543_301.trans (congrArg some (by kernel_rfl))

theorem codeAt_top303 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 303)) topSeg303 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 23) (o := 38) (seg := topSeg303) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top304 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 304)) topSeg304 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 24) (o := 39) (seg := topSeg304) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_304 := symRun { noAlias := true } topSeg304 (pcOf (354 + 304)) 200
sym_block tb543_304 := symRun { noAlias := true } topSeg304 (pcOf (543 + 304)) 200
def topState304 : SymState := tb354_304.res.st
def topEnd304 (b : Nat) : E := .c (pcOf (b + 306))
theorem run_top304 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg304 (pcOf (b + 304)) 200 =
      some ⟨topState304, topEnd304 b, tb354_304.res.stop, tb354_304.res.steps, tb354_304.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_304.trans (congrArg some (by kernel_rfl))
  · exact tb543_304.trans (congrArg some (by kernel_rfl))

theorem codeAt_top306 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 306)) topSeg306 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 25) (o := 41) (seg := topSeg306) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_306 := symRun { noAlias := true } topSeg306 (pcOf (354 + 306)) 200
sym_block tb543_306 := symRun { noAlias := true } topSeg306 (pcOf (543 + 306)) 200
def topState306 : SymState := tb354_306.res.st
def topEnd306 (b : Nat) : E := .c (pcOf (b + 308))
theorem run_top306 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg306 (pcOf (b + 306)) 200 =
      some ⟨topState306, topEnd306 b, tb354_306.res.stop, tb354_306.res.steps, tb354_306.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_306.trans (congrArg some (by kernel_rfl))
  · exact tb543_306.trans (congrArg some (by kernel_rfl))

theorem codeAt_top308 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 308)) topSeg308 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 26) (o := 43) (seg := topSeg308) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top309 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 309)) topSeg309 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 27) (o := 44) (seg := topSeg309) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_309 := symRun { noAlias := true } topSeg309 (pcOf (354 + 309)) 200
sym_block tb543_309 := symRun { noAlias := true } topSeg309 (pcOf (543 + 309)) 200
def topState309 : SymState := tb354_309.res.st
def topEnd309 (b : Nat) : E := .c (pcOf (b + 311))
theorem run_top309 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg309 (pcOf (b + 309)) 200 =
      some ⟨topState309, topEnd309 b, tb354_309.res.stop, tb354_309.res.steps, tb354_309.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_309.trans (congrArg some (by kernel_rfl))
  · exact tb543_309.trans (congrArg some (by kernel_rfl))

theorem codeAt_top311 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 311)) topSeg311 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 28) (o := 46) (seg := topSeg311) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_311 := symRun { noAlias := true } topSeg311 (pcOf (354 + 311)) 200
sym_block tb543_311 := symRun { noAlias := true } topSeg311 (pcOf (543 + 311)) 200
def topState311 : SymState := tb354_311.res.st
def topEnd311 (b : Nat) : E := .c (pcOf (b + 313))
theorem run_top311 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg311 (pcOf (b + 311)) 200 =
      some ⟨topState311, topEnd311 b, tb354_311.res.stop, tb354_311.res.steps, tb354_311.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_311.trans (congrArg some (by kernel_rfl))
  · exact tb543_311.trans (congrArg some (by kernel_rfl))

theorem codeAt_top313 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 313)) topSeg313 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 29) (o := 48) (seg := topSeg313) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_313 := symRun { noAlias := true } topSeg313 (pcOf (354 + 313)) 200
sym_block tb543_313 := symRun { noAlias := true } topSeg313 (pcOf (543 + 313)) 200
def topState313 : SymState := tb354_313.res.st
def topEnd313 (b : Nat) : E := .c (pcOf (b + 315))
theorem run_top313 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg313 (pcOf (b + 313)) 200 =
      some ⟨topState313, topEnd313 b, tb354_313.res.stop, tb354_313.res.steps, tb354_313.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_313.trans (congrArg some (by kernel_rfl))
  · exact tb543_313.trans (congrArg some (by kernel_rfl))

theorem codeAt_top315 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 315)) topSeg315 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 30) (o := 50) (seg := topSeg315) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top316 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 316)) topSeg316 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 31) (o := 51) (seg := topSeg316) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_316 := symRun { noAlias := true } topSeg316 (pcOf (354 + 316)) 200
sym_block tb543_316 := symRun { noAlias := true } topSeg316 (pcOf (543 + 316)) 200
def topState316 : SymState := tb354_316.res.st
def topEnd316 (b : Nat) : E := .c (pcOf (b + 318))
theorem run_top316 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg316 (pcOf (b + 316)) 200 =
      some ⟨topState316, topEnd316 b, tb354_316.res.stop, tb354_316.res.steps, tb354_316.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_316.trans (congrArg some (by kernel_rfl))
  · exact tb543_316.trans (congrArg some (by kernel_rfl))

theorem codeAt_top318 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 318)) topSeg318 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 32) (o := 53) (seg := topSeg318) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_318 := symRun { noAlias := true } topSeg318 (pcOf (354 + 318)) 200
sym_block tb543_318 := symRun { noAlias := true } topSeg318 (pcOf (543 + 318)) 200
def topState318 : SymState := tb354_318.res.st
def topEnd318 (b : Nat) : E := .c (pcOf (b + 320))
theorem run_top318 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg318 (pcOf (b + 318)) 200 =
      some ⟨topState318, topEnd318 b, tb354_318.res.stop, tb354_318.res.steps, tb354_318.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_318.trans (congrArg some (by kernel_rfl))
  · exact tb543_318.trans (congrArg some (by kernel_rfl))

theorem codeAt_top320 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 320)) topSeg320 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 33) (o := 55) (seg := topSeg320) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top321 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 321)) topSeg321 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 34) (o := 56) (seg := topSeg321) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_321 := symRun { noAlias := true } topSeg321 (pcOf (354 + 321)) 200
sym_block tb543_321 := symRun { noAlias := true } topSeg321 (pcOf (543 + 321)) 200
def topState321 : SymState := tb354_321.res.st
def topEnd321 (b : Nat) : E := .c (pcOf (b + 323))
theorem run_top321 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg321 (pcOf (b + 321)) 200 =
      some ⟨topState321, topEnd321 b, tb354_321.res.stop, tb354_321.res.steps, tb354_321.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_321.trans (congrArg some (by kernel_rfl))
  · exact tb543_321.trans (congrArg some (by kernel_rfl))

theorem codeAt_top323 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 323)) topSeg323 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 35) (o := 58) (seg := topSeg323) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_323 := symRun { noAlias := true } topSeg323 (pcOf (354 + 323)) 200
sym_block tb543_323 := symRun { noAlias := true } topSeg323 (pcOf (543 + 323)) 200
def topState323 : SymState := tb354_323.res.st
def topEnd323 (b : Nat) : E := .c (pcOf (b + 325))
theorem run_top323 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg323 (pcOf (b + 323)) 200 =
      some ⟨topState323, topEnd323 b, tb354_323.res.stop, tb354_323.res.steps, tb354_323.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_323.trans (congrArg some (by kernel_rfl))
  · exact tb543_323.trans (congrArg some (by kernel_rfl))

theorem codeAt_top325 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 325)) topSeg325 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 36) (o := 60) (seg := topSeg325) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top326 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 326)) topSeg326 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 37) (o := 61) (seg := topSeg326) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_326 := symRun { noAlias := true } topSeg326 (pcOf (354 + 326)) 200
sym_block tb543_326 := symRun { noAlias := true } topSeg326 (pcOf (543 + 326)) 200
def topState326 : SymState := tb354_326.res.st
def topEnd326 (b : Nat) : E := .c (pcOf (b + 328))
theorem run_top326 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg326 (pcOf (b + 326)) 200 =
      some ⟨topState326, topEnd326 b, tb354_326.res.stop, tb354_326.res.steps, tb354_326.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_326.trans (congrArg some (by kernel_rfl))
  · exact tb543_326.trans (congrArg some (by kernel_rfl))

theorem codeAt_top328 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 328)) topSeg328 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 38) (o := 63) (seg := topSeg328) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_328 := symRun { noAlias := true } topSeg328 (pcOf (354 + 328)) 200
sym_block tb543_328 := symRun { noAlias := true } topSeg328 (pcOf (543 + 328)) 200
def topState328 : SymState := tb354_328.res.st
def topEnd328 (b : Nat) : E := .c (pcOf (b + 330))
theorem run_top328 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg328 (pcOf (b + 328)) 200 =
      some ⟨topState328, topEnd328 b, tb354_328.res.stop, tb354_328.res.steps, tb354_328.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_328.trans (congrArg some (by kernel_rfl))
  · exact tb543_328.trans (congrArg some (by kernel_rfl))

theorem codeAt_top330 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 330)) topSeg330 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 39) (o := 65) (seg := topSeg330) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top331 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 331)) topSeg331 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 40) (o := 66) (seg := topSeg331) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_331 := symRun { noAlias := true } topSeg331 (pcOf (354 + 331)) 200
sym_block tb543_331 := symRun { noAlias := true } topSeg331 (pcOf (543 + 331)) 200
def topState331 : SymState := tb354_331.res.st
def topEnd331 (b : Nat) : E := .c (pcOf (b + 333))
theorem run_top331 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg331 (pcOf (b + 331)) 200 =
      some ⟨topState331, topEnd331 b, tb354_331.res.stop, tb354_331.res.steps, tb354_331.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_331.trans (congrArg some (by kernel_rfl))
  · exact tb543_331.trans (congrArg some (by kernel_rfl))

theorem codeAt_top333 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 333)) topSeg333 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 41) (o := 68) (seg := topSeg333) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_333 := symRun { noAlias := true } topSeg333 (pcOf (354 + 333)) 200
sym_block tb543_333 := symRun { noAlias := true } topSeg333 (pcOf (543 + 333)) 200
def topState333 : SymState := tb354_333.res.st
def topEnd333 (b : Nat) : E := .c (pcOf (b + 335))
theorem run_top333 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg333 (pcOf (b + 333)) 200 =
      some ⟨topState333, topEnd333 b, tb354_333.res.stop, tb354_333.res.steps, tb354_333.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_333.trans (congrArg some (by kernel_rfl))
  · exact tb543_333.trans (congrArg some (by kernel_rfl))

theorem codeAt_top335 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 335)) topSeg335 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 42) (o := 70) (seg := topSeg335) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top336 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 336)) topSeg336 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 43) (o := 71) (seg := topSeg336) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_336 := symRun { noAlias := true } topSeg336 (pcOf (354 + 336)) 200
sym_block tb543_336 := symRun { noAlias := true } topSeg336 (pcOf (543 + 336)) 200
def topState336 : SymState := tb354_336.res.st
def topEnd336 (b : Nat) : E := .c (pcOf (b + 338))
theorem run_top336 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg336 (pcOf (b + 336)) 200 =
      some ⟨topState336, topEnd336 b, tb354_336.res.stop, tb354_336.res.steps, tb354_336.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_336.trans (congrArg some (by kernel_rfl))
  · exact tb543_336.trans (congrArg some (by kernel_rfl))

theorem codeAt_top338 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 338)) topSeg338 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 44) (o := 73) (seg := topSeg338) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_338 := symRun { noAlias := true } topSeg338 (pcOf (354 + 338)) 200
sym_block tb543_338 := symRun { noAlias := true } topSeg338 (pcOf (543 + 338)) 200
def topState338 : SymState := tb354_338.res.st
def topEnd338 (b : Nat) : E := .c (pcOf (b + 340))
theorem run_top338 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg338 (pcOf (b + 338)) 200 =
      some ⟨topState338, topEnd338 b, tb354_338.res.stop, tb354_338.res.steps, tb354_338.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_338.trans (congrArg some (by kernel_rfl))
  · exact tb543_338.trans (congrArg some (by kernel_rfl))

theorem codeAt_top340 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 340)) topSeg340 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 45) (o := 75) (seg := topSeg340) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top341 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 341)) topSeg341 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 46) (o := 76) (seg := topSeg341) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_341 := symRun { noAlias := true } topSeg341 (pcOf (354 + 341)) 200
sym_block tb543_341 := symRun { noAlias := true } topSeg341 (pcOf (543 + 341)) 200
def topState341 : SymState := tb354_341.res.st
def topEnd341 (b : Nat) : E := .c (pcOf (b + 343))
theorem run_top341 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg341 (pcOf (b + 341)) 200 =
      some ⟨topState341, topEnd341 b, tb354_341.res.stop, tb354_341.res.steps, tb354_341.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_341.trans (congrArg some (by kernel_rfl))
  · exact tb543_341.trans (congrArg some (by kernel_rfl))

theorem codeAt_top343 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 343)) topSeg343 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 47) (o := 78) (seg := topSeg343) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_343 := symRun { noAlias := true } topSeg343 (pcOf (354 + 343)) 200
sym_block tb543_343 := symRun { noAlias := true } topSeg343 (pcOf (543 + 343)) 200
def topState343 : SymState := tb354_343.res.st
def topEnd343 (b : Nat) : E := .c (pcOf (b + 345))
theorem run_top343 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg343 (pcOf (b + 343)) 200 =
      some ⟨topState343, topEnd343 b, tb354_343.res.stop, tb354_343.res.steps, tb354_343.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_343.trans (congrArg some (by kernel_rfl))
  · exact tb543_343.trans (congrArg some (by kernel_rfl))

theorem codeAt_top345 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 345)) topSeg345 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 48) (o := 80) (seg := topSeg345) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top346 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 346)) topSeg346 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 49) (o := 81) (seg := topSeg346) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_346 := symRun { noAlias := true } topSeg346 (pcOf (354 + 346)) 200
sym_block tb543_346 := symRun { noAlias := true } topSeg346 (pcOf (543 + 346)) 200
def topState346 : SymState := tb354_346.res.st
def topEnd346 (b : Nat) : E := .c (pcOf (b + 348))
theorem run_top346 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg346 (pcOf (b + 346)) 200 =
      some ⟨topState346, topEnd346 b, tb354_346.res.stop, tb354_346.res.steps, tb354_346.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_346.trans (congrArg some (by kernel_rfl))
  · exact tb543_346.trans (congrArg some (by kernel_rfl))

theorem codeAt_top348 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 348)) topSeg348 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 50) (o := 83) (seg := topSeg348) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_348 := symRun { noAlias := true } topSeg348 (pcOf (354 + 348)) 200
sym_block tb543_348 := symRun { noAlias := true } topSeg348 (pcOf (543 + 348)) 200
def topState348 : SymState := tb354_348.res.st
def topEnd348 (b : Nat) : E := .c (pcOf (b + 350))
theorem run_top348 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg348 (pcOf (b + 348)) 200 =
      some ⟨topState348, topEnd348 b, tb354_348.res.stop, tb354_348.res.steps, tb354_348.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_348.trans (congrArg some (by kernel_rfl))
  · exact tb543_348.trans (congrArg some (by kernel_rfl))

theorem codeAt_top350 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 350)) topSeg350 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 51) (o := 85) (seg := topSeg350) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top351 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 351)) topSeg351 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 52) (o := 86) (seg := topSeg351) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_351 := symRun { noAlias := true } topSeg351 (pcOf (354 + 351)) 200
sym_block tb543_351 := symRun { noAlias := true } topSeg351 (pcOf (543 + 351)) 200
def topState351 : SymState := tb354_351.res.st
def topEnd351 (b : Nat) : E := .c (pcOf (b + 353))
theorem run_top351 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg351 (pcOf (b + 351)) 200 =
      some ⟨topState351, topEnd351 b, tb354_351.res.stop, tb354_351.res.steps, tb354_351.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_351.trans (congrArg some (by kernel_rfl))
  · exact tb543_351.trans (congrArg some (by kernel_rfl))

theorem codeAt_top353 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 353)) topSeg353 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 53) (o := 88) (seg := topSeg353) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_353 := symRun { noAlias := true } topSeg353 (pcOf (354 + 353)) 200
sym_block tb543_353 := symRun { noAlias := true } topSeg353 (pcOf (543 + 353)) 200
def topState353 : SymState := tb354_353.res.st
def topEnd353 (b : Nat) : E := rebase tb354_353.res.pc (pcOf (b + 468)) (pcOf (b + 362))
theorem run_top353 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg353 (pcOf (b + 353)) 200 =
      some ⟨topState353, topEnd353 b, tb354_353.res.stop, tb354_353.res.steps, tb354_353.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_353.trans (congrArg some (by kernel_rfl))
  · exact tb543_353.trans (congrArg some (by kernel_rfl))

theorem codeAt_top362 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 362)) topSeg362 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 54) (o := 97) (seg := topSeg362) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_362 := symRun { noAlias := true } topSeg362 (pcOf (354 + 362)) 200
sym_block tb543_362 := symRun { noAlias := true } topSeg362 (pcOf (543 + 362)) 200
def topState362 : SymState := tb354_362.res.st
def topEnd362 (b : Nat) : E := .c (pcOf (b + 369))
theorem run_top362 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg362 (pcOf (b + 362)) 200 =
      some ⟨topState362, topEnd362 b, tb354_362.res.stop, tb354_362.res.steps, tb354_362.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_362.trans (congrArg some (by kernel_rfl))
  · exact tb543_362.trans (congrArg some (by kernel_rfl))

theorem codeAt_top369 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 369)) topSeg369 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 55) (o := 104) (seg := topSeg369) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top370 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 370)) topSeg370 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 56) (o := 105) (seg := topSeg370) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top371 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 371)) topSeg371 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 57) (o := 106) (seg := topSeg371) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_371 := symRun { noAlias := true } topSeg371 (pcOf (354 + 371)) 200
sym_block tb543_371 := symRun { noAlias := true } topSeg371 (pcOf (543 + 371)) 200
def topState371 : SymState := tb354_371.res.st
def topEnd371 (b : Nat) : E := .c (pcOf (b + 372))
theorem run_top371 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg371 (pcOf (b + 371)) 200 =
      some ⟨topState371, topEnd371 b, tb354_371.res.stop, tb354_371.res.steps, tb354_371.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_371.trans (congrArg some (by kernel_rfl))
  · exact tb543_371.trans (congrArg some (by kernel_rfl))

theorem codeAt_top372 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 372)) topSeg372 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 58) (o := 107) (seg := topSeg372) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top373 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 373)) topSeg373 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 59) (o := 108) (seg := topSeg373) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_373 := symRun { noAlias := true } topSeg373 (pcOf (354 + 373)) 200
sym_block tb543_373 := symRun { noAlias := true } topSeg373 (pcOf (543 + 373)) 200
def topState373 : SymState := tb354_373.res.st
def topEnd373 (b : Nat) : E := .c (pcOf (b + 374))
theorem run_top373 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg373 (pcOf (b + 373)) 200 =
      some ⟨topState373, topEnd373 b, tb354_373.res.stop, tb354_373.res.steps, tb354_373.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_373.trans (congrArg some (by kernel_rfl))
  · exact tb543_373.trans (congrArg some (by kernel_rfl))

theorem codeAt_top374 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 374)) topSeg374 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 60) (o := 109) (seg := topSeg374) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top375 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 375)) topSeg375 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 61) (o := 110) (seg := topSeg375) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_375 := symRun { noAlias := true } topSeg375 (pcOf (354 + 375)) 200
sym_block tb543_375 := symRun { noAlias := true } topSeg375 (pcOf (543 + 375)) 200
def topState375 : SymState := tb354_375.res.st
def topEnd375 (b : Nat) : E := rebase tb354_375.res.pc (pcOf (b + 366)) (pcOf (b + 383))
theorem run_top375 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg375 (pcOf (b + 375)) 200 =
      some ⟨topState375, topEnd375 b, tb354_375.res.stop, tb354_375.res.steps, tb354_375.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_375.trans (congrArg some (by kernel_rfl))
  · exact tb543_375.trans (congrArg some (by kernel_rfl))

theorem codeAt_top383 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 383)) topSeg383 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 62) (o := 118) (seg := topSeg383) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_383 := symRun { noAlias := true } topSeg383 (pcOf (354 + 383)) 200
sym_block tb543_383 := symRun { noAlias := true } topSeg383 (pcOf (543 + 383)) 200
def topState383 : SymState := tb354_383.res.st
def topEnd383 (b : Nat) : E := .c (pcOf (b + 384))
theorem run_top383 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg383 (pcOf (b + 383)) 200 =
      some ⟨topState383, topEnd383 b, tb354_383.res.stop, tb354_383.res.steps, tb354_383.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_383.trans (congrArg some (by kernel_rfl))
  · exact tb543_383.trans (congrArg some (by kernel_rfl))

theorem codeAt_top384 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 384)) topSeg384 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 63) (o := 119) (seg := topSeg384) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top385 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 385)) topSeg385 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 64) (o := 120) (seg := topSeg385) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_385 := symRun { noAlias := true } topSeg385 (pcOf (354 + 385)) 200
sym_block tb543_385 := symRun { noAlias := true } topSeg385 (pcOf (543 + 385)) 200
def topState385 : SymState := tb354_385.res.st
def topEnd385 (b : Nat) : E := .c (pcOf (b + 387))
theorem run_top385 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg385 (pcOf (b + 385)) 200 =
      some ⟨topState385, topEnd385 b, tb354_385.res.stop, tb354_385.res.steps, tb354_385.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_385.trans (congrArg some (by kernel_rfl))
  · exact tb543_385.trans (congrArg some (by kernel_rfl))

theorem codeAt_top387 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 387)) topSeg387 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 65) (o := 122) (seg := topSeg387) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top388 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 388)) topSeg388 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 66) (o := 123) (seg := topSeg388) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_388 := symRun { noAlias := true } topSeg388 (pcOf (354 + 388)) 200
sym_block tb543_388 := symRun { noAlias := true } topSeg388 (pcOf (543 + 388)) 200
def topState388 : SymState := tb354_388.res.st
def topEnd388 (b : Nat) : E := .c (pcOf (b + 390))
theorem run_top388 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg388 (pcOf (b + 388)) 200 =
      some ⟨topState388, topEnd388 b, tb354_388.res.stop, tb354_388.res.steps, tb354_388.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_388.trans (congrArg some (by kernel_rfl))
  · exact tb543_388.trans (congrArg some (by kernel_rfl))

theorem codeAt_top390 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 390)) topSeg390 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 67) (o := 125) (seg := topSeg390) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top391 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 391)) topSeg391 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 68) (o := 126) (seg := topSeg391) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_391 := symRun { noAlias := true } topSeg391 (pcOf (354 + 391)) 200
sym_block tb543_391 := symRun { noAlias := true } topSeg391 (pcOf (543 + 391)) 200
def topState391 : SymState := tb354_391.res.st
def topEnd391 (b : Nat) : E := tb354_391.res.pc
theorem run_top391 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg391 (pcOf (b + 391)) 200 =
      some ⟨topState391, topEnd391 b, tb354_391.res.stop, tb354_391.res.steps, tb354_391.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_391.trans (congrArg some (by kernel_rfl))
  · exact tb543_391.trans (congrArg some (by kernel_rfl))

theorem codeAt_top392 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 392)) topSeg392 := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code] at hc
  have hp := codeAt_sublayout hc topSegLayout_ok (i := 69) (o := 127) (seg := topSeg392) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

sym_block tb354_392 := symRun { noAlias := true } topSeg392 (pcOf (354 + 392)) 200
sym_block tb543_392 := symRun { noAlias := true } topSeg392 (pcOf (543 + 392)) 200
def topState392 : SymState := tb354_392.res.st
def topEnd392 (b : Nat) : E := .c (pcOf (b + 438))
theorem run_top392 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } topSeg392 (pcOf (b + 392)) 200 =
      some ⟨topState392, topEnd392 b, tb354_392.res.stop, tb354_392.res.steps, tb354_392.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact tb354_392.trans (congrArg some (by kernel_rfl))
  · exact tb543_392.trans (congrArg some (by kernel_rfl))

end SigGolfCandidate.T3M.Search
