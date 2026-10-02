import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
def foldCode : List (BitVec 32) := [0x00fff9b7, 0x00080e93, 0x07fef713, 0x01370733, 0x00074c83, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x00189713, 0x01d76eb3, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93, 0x07fef713, 0x01370733, 0x00074703, 0x00ec8cb3, 0x007ede93]

def KernAt (im : Image) (b : Nat) : Prop := CodeAt im (pcOf (b + 265)) foldCode

def topSeg265 : List (BitVec 32) := [0x00fff9b7, 0x00080e93]
def topSeg267 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg269 : List (BitVec 32) := [0x00074c83]
def topSeg270 : List (BitVec 32) := [0x007ede93]
def topSeg271 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg273 : List (BitVec 32) := [0x00074703]
def topSeg274 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg276 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg278 : List (BitVec 32) := [0x00074703]
def topSeg279 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg281 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg283 : List (BitVec 32) := [0x00074703]
def topSeg284 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg286 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg288 : List (BitVec 32) := [0x00074703]
def topSeg289 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg291 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg293 : List (BitVec 32) := [0x00074703]
def topSeg294 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg296 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg298 : List (BitVec 32) := [0x00074703]
def topSeg299 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg301 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg303 : List (BitVec 32) := [0x00074703]
def topSeg304 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg306 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg308 : List (BitVec 32) := [0x00074703]
def topSeg309 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg311 : List (BitVec 32) := [0x00189713, 0x01d76eb3]
def topSeg313 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg315 : List (BitVec 32) := [0x00074703]
def topSeg316 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg318 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg320 : List (BitVec 32) := [0x00074703]
def topSeg321 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg323 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg325 : List (BitVec 32) := [0x00074703]
def topSeg326 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg328 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg330 : List (BitVec 32) := [0x00074703]
def topSeg331 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg333 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg335 : List (BitVec 32) := [0x00074703]
def topSeg336 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg338 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg340 : List (BitVec 32) := [0x00074703]
def topSeg341 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg343 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg345 : List (BitVec 32) := [0x00074703]
def topSeg346 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
def topSeg348 : List (BitVec 32) := [0x07fef713, 0x01370733]
def topSeg350 : List (BitVec 32) := [0x00074703]
def topSeg351 : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]

def foldLayout : Rv.Layout := [(0, topSeg265), (2, topSeg267), (4, topSeg269), (5, topSeg270), (6, topSeg271), (8, topSeg273), (9, topSeg274), (11, topSeg276), (13, topSeg278), (14, topSeg279), (16, topSeg281), (18, topSeg283), (19, topSeg284), (21, topSeg286), (23, topSeg288), (24, topSeg289), (26, topSeg291), (28, topSeg293), (29, topSeg294), (31, topSeg296), (33, topSeg298), (34, topSeg299), (36, topSeg301), (38, topSeg303), (39, topSeg304), (41, topSeg306), (43, topSeg308), (44, topSeg309), (46, topSeg311), (48, topSeg313), (50, topSeg315), (51, topSeg316), (53, topSeg318), (55, topSeg320), (56, topSeg321), (58, topSeg323), (60, topSeg325), (61, topSeg326), (63, topSeg328), (65, topSeg330), (66, topSeg331), (68, topSeg333), (70, topSeg335), (71, topSeg336), (73, topSeg338), (75, topSeg340), (76, topSeg341), (78, topSeg343), (80, topSeg345), (81, topSeg346), (83, topSeg348), (85, topSeg350), (86, topSeg351)]
theorem foldLayout_ok : layoutOk 0 foldLayout = true := by decide +kernel
theorem foldLayout_code : foldCode = layoutCode foldLayout := by decide +kernel

theorem codeAt_top265 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 265)) topSeg265 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 0) (o := 0) (seg := topSeg265) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top267 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 267)) topSeg267 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 1) (o := 2) (seg := topSeg267) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top269 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 269)) topSeg269 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 2) (o := 4) (seg := topSeg269) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top270 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 270)) topSeg270 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 3) (o := 5) (seg := topSeg270) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top271 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 271)) topSeg271 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 4) (o := 6) (seg := topSeg271) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top273 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 273)) topSeg273 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 5) (o := 8) (seg := topSeg273) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top274 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 274)) topSeg274 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 6) (o := 9) (seg := topSeg274) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top276 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 276)) topSeg276 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 7) (o := 11) (seg := topSeg276) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top278 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 278)) topSeg278 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 8) (o := 13) (seg := topSeg278) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top279 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 279)) topSeg279 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 9) (o := 14) (seg := topSeg279) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top281 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 281)) topSeg281 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 10) (o := 16) (seg := topSeg281) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top283 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 283)) topSeg283 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 11) (o := 18) (seg := topSeg283) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top284 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 284)) topSeg284 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 12) (o := 19) (seg := topSeg284) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top286 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 286)) topSeg286 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 13) (o := 21) (seg := topSeg286) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top288 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 288)) topSeg288 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 14) (o := 23) (seg := topSeg288) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top289 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 289)) topSeg289 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 15) (o := 24) (seg := topSeg289) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top291 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 291)) topSeg291 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 16) (o := 26) (seg := topSeg291) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top293 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 293)) topSeg293 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 17) (o := 28) (seg := topSeg293) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top294 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 294)) topSeg294 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 18) (o := 29) (seg := topSeg294) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top296 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 296)) topSeg296 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 19) (o := 31) (seg := topSeg296) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top298 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 298)) topSeg298 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 20) (o := 33) (seg := topSeg298) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top299 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 299)) topSeg299 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 21) (o := 34) (seg := topSeg299) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top301 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 301)) topSeg301 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 22) (o := 36) (seg := topSeg301) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top303 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 303)) topSeg303 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 23) (o := 38) (seg := topSeg303) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top304 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 304)) topSeg304 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 24) (o := 39) (seg := topSeg304) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top306 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 306)) topSeg306 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 25) (o := 41) (seg := topSeg306) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top308 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 308)) topSeg308 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 26) (o := 43) (seg := topSeg308) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top309 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 309)) topSeg309 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 27) (o := 44) (seg := topSeg309) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top311 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 311)) topSeg311 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 28) (o := 46) (seg := topSeg311) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top313 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 313)) topSeg313 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 29) (o := 48) (seg := topSeg313) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top315 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 315)) topSeg315 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 30) (o := 50) (seg := topSeg315) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top316 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 316)) topSeg316 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 31) (o := 51) (seg := topSeg316) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top318 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 318)) topSeg318 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 32) (o := 53) (seg := topSeg318) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top320 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 320)) topSeg320 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 33) (o := 55) (seg := topSeg320) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top321 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 321)) topSeg321 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 34) (o := 56) (seg := topSeg321) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top323 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 323)) topSeg323 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 35) (o := 58) (seg := topSeg323) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top325 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 325)) topSeg325 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 36) (o := 60) (seg := topSeg325) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top326 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 326)) topSeg326 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 37) (o := 61) (seg := topSeg326) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top328 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 328)) topSeg328 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 38) (o := 63) (seg := topSeg328) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top330 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 330)) topSeg330 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 39) (o := 65) (seg := topSeg330) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top331 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 331)) topSeg331 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 40) (o := 66) (seg := topSeg331) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top333 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 333)) topSeg333 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 41) (o := 68) (seg := topSeg333) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top335 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 335)) topSeg335 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 42) (o := 70) (seg := topSeg335) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top336 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 336)) topSeg336 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 43) (o := 71) (seg := topSeg336) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top338 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 338)) topSeg338 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 44) (o := 73) (seg := topSeg338) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top340 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 340)) topSeg340 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 45) (o := 75) (seg := topSeg340) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top341 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 341)) topSeg341 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 46) (o := 76) (seg := topSeg341) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top343 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 343)) topSeg343 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 47) (o := 78) (seg := topSeg343) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top345 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 345)) topSeg345 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 48) (o := 80) (seg := topSeg345) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top346 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 346)) topSeg346 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 49) (o := 81) (seg := topSeg346) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top348 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 348)) topSeg348 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 50) (o := 83) (seg := topSeg348) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top350 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 350)) topSeg350 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 51) (o := 85) (seg := topSeg350) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

theorem codeAt_top351 {im : Image} {b : Nat} (h : KernAt im b) :
    CodeAt im (pcOf (b + 351)) topSeg351 := by
  rw [KernAt, foldLayout_code] at h
  have hp := codeAt_sublayout h foldLayout_ok (i := 52) (o := 86) (seg := topSeg351) (by kernel_rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp

/-- The frozen full verifier really contains this complete checksum fold. -/
theorem fold_at : KernAt Verify.image 95899 := by
  have h := codeAt_from 96164 (by decide)
  have hp : foldCode <+: codeFrom 96164 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
end SigGolfCandidate.T3M.Verify.Nonbinary
