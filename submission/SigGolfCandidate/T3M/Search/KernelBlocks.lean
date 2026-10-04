import SigGolfCandidate.T3M.Search.Basic
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Sizes

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def k_0 : List (BitVec 32) := [1049235,1049875]
def k_2 : List (BitVec 32) := [115]
def k_3 : List (BitVec 32) := [22022803,2579,134327,0x4a0c8c93]
def k_7 : List (BitVec 32) := [7340819,376066659]
def k_9 : List (BitVec 32) := [5903123,3806099,0x40730333,21168947,32703251,6509459,3380115,134711,370019859,29590451,245251,8633987,66286355,7233075,2006675,66061203,0x406383b3,8298163,31354419,33555383,0xfff38393,8289843]
def k_31 : List (BitVec 32) := [0xfe7313,7541523,5135123,0x7fb7b13,0xbe5b93,0x7fbfb93,19815443,0x7fc7c13,23844963]
def k_40 : List (BitVec 32) := [721811,756499,232339]
def k_43 : List (BitVec 32) := [24926307]
def k_44 : List (BitVec 32) := [754579,789395,232467]
def k_47 : List (BitVec 32) := [23844963]
def k_48 : List (BitVec 32) := [721811,756499,232339]
def k_51 : List (BitVec 32) := [0xd7b0463]
def k_52 : List (BitVec 32) := [0xd8b8263]
def k_53 : List (BitVec 32) := [24855475,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,25936819,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,4885139,23266227,8171555,24314803,8172579,25363379,8173603,25988243,1706515,0xe9dff06f]
def k_97 : List (BitVec 32) := [0x7400313,7001699]
def k_99 : List (BitVec 32) := [1050259,32871]
def k_101 : List (BitVec 32) := [1683,32871]
def k_103 : List (BitVec 32) := [17044243,0x40136313,295827,34152211,31712179,134711,638455315,7223331,8272931,2451]
def k_113 : List (BitVec 32) := [4195127,0xe2698ce3]
def k_115 : List (BitVec 32) := [134711,638455315,54403107,132407,637863187,67110291,132663,705037843]
def k_123 : List (BitVec 32) := [115]
def k_124 : List (BitVec 32) := [134711,705564179,930563,9319299,3219,537136227]
def k_130 : List (BitVec 32) := [65265171,0x540e1263]
def k_132 : List (BitVec 32) := [7568915,30182579,3366419,8289811,30182579,6512147,8289811,30182579,9657875,8289811,30182579,0xc35e13,8289811,30182579,0xf35e13,8289811,30182579,19095059,8289811,30182579,22240787,8289811,30182579,25386515,8289811,30182579,28532243,8289811,30182579,31677971,8289811,30182579,34823699,8289811,30182579,37969427,8289811,30182579,41115155,8289811,30182579,44260883,8289811,30182579,47406611,8289811,30182579,50552339,8289811,30182579,53698067,8289811,30182579,56843795,8289811,30182579,59989523,8289811,30182579,63135251,8289811,30182579,66280979,1285779,8322707,31354419,30182579,2350611,8289811,30182579,5496339,8289811,30182579,8642067,8289811,30182579,0xb3de13,8289811,30182579,0xe3de13,8289811,30182579,18079251,8289811,30182579,21224979,8289811,30182579,24370707,8289811,30182579,27516435,8289811,30182579,30662163,8289811,30182579,33807891,8289811,30182579,36953619,8289811,30182579,40099347,8289811,30182579,43245075,8289811,30182579,46390803,8289811,30182579,49536531,8289811,30182579,52682259,8289811,30182579,55827987,8289811,30182579,58973715,8289811,30182579,62119443,8289811,30182579,0x41988e33,8392339,870219363]
def k_262 : List (BitVec 32) := [738197615]
def k_263 : List (BitVec 32) := [64216595,839784547]
def k_265 : List (BitVec 32) := [0xffff37,200211,0x7fe7e93,32411315,969859,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,1285779,30338611,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,4095635,31231155,3038867,4128403,31231155,5136019,31231155,0x411c8eb3,437163619,2579,133815,0x420a8a93,0x80f0f13,0x7f37e13,3022355,32378419,945795,31096867,9363091,31096995,9363091,31097123,7557907,60005907,29582131,7590803,3836563,1706515,18497043,0xfc0e10e3,3374611,30048291,2315027,3374611,30048419,2315027,3374611,30048547,32871,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19]
def k_438 : List (BitVec 32) := [854675,263267]
def k_440 : List (BitVec 32) := [0xfffd0a93]
def k_441 : List (BitVec 32) := [2579]
def k_442 : List (BitVec 32) := [89806435]
def k_443 : List (BitVec 32) := [7343635,3149459,28989027]
def k_446 : List (BitVec 32) := [3149331,2100883]
def k_448 : List (BitVec 32) := [29589299,134711,0x420e0e13,21892659]
def k_452 : List (BitVec 32) := [32374819]
def k_453 : List (BitVec 32) := [30626611,67112467,0x41de0e33,29597235,29582131,30659507,1706515,0xfb9ff06f]
def k_461 : List (BitVec 32) := [265315]
def k_462 : List (BitVec 32) := [0x41988e33,134839,0x420e8e93,22974131]
def k_466 : List (BitVec 32) := [30310435]
def k_467 : List (BitVec 32) := [32871]
def k_468 : List (BitVec 32) := [1673619,0xa71ff06f]
def kernL : Rv.Layout := [(0, k_0), (2, k_2), (3, k_3), (7, k_7), (9, k_9), (31, k_31), (40, k_40), (43, k_43), (44, k_44), (47, k_47), (48, k_48), (51, k_51), (52, k_52), (53, k_53), (97, k_97), (99, k_99), (101, k_101), (103, k_103), (113, k_113), (115, k_115), (123, k_123), (124, k_124), (130, k_130), (132, k_132), (262, k_262), (263, k_263), (265, k_265), (438, k_438), (440, k_440), (441, k_441), (442, k_442), (443, k_443), (446, k_446), (448, k_448), (452, k_452), (453, k_453), (461, k_461), (462, k_462), (466, k_466), (467, k_467), (468, k_468)]
def kernCode : List (BitVec 32) := layoutCode kernL
theorem kernL_ok : layoutOk 0 kernL = true := by decide +kernel
def KernAt (image : Image) (b : Nat) : Prop := CodeAt image (pcOf b) kernCode ∧ (b = 354 ∨ b = 543)
theorem codeAt_k_0 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 0)) k_0 :=
  codeAt_sublayout h.1 kernL_ok (i := 0) (by kernel_rfl)
theorem codeAt_k_2 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 2)) k_2 :=
  codeAt_sublayout h.1 kernL_ok (i := 1) (by kernel_rfl)
theorem codeAt_k_3 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 3)) k_3 :=
  codeAt_sublayout h.1 kernL_ok (i := 2) (by kernel_rfl)
theorem codeAt_k_7 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 7)) k_7 :=
  codeAt_sublayout h.1 kernL_ok (i := 3) (by kernel_rfl)
theorem codeAt_k_9 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 9)) k_9 :=
  codeAt_sublayout h.1 kernL_ok (i := 4) (by kernel_rfl)
theorem codeAt_k_31 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 31)) k_31 :=
  codeAt_sublayout h.1 kernL_ok (i := 5) (by kernel_rfl)
theorem codeAt_k_40 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 40)) k_40 :=
  codeAt_sublayout h.1 kernL_ok (i := 6) (by kernel_rfl)
theorem codeAt_k_43 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 43)) k_43 :=
  codeAt_sublayout h.1 kernL_ok (i := 7) (by kernel_rfl)
theorem codeAt_k_44 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 44)) k_44 :=
  codeAt_sublayout h.1 kernL_ok (i := 8) (by kernel_rfl)
theorem codeAt_k_47 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 47)) k_47 :=
  codeAt_sublayout h.1 kernL_ok (i := 9) (by kernel_rfl)
theorem codeAt_k_48 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 48)) k_48 :=
  codeAt_sublayout h.1 kernL_ok (i := 10) (by kernel_rfl)
theorem codeAt_k_51 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 51)) k_51 :=
  codeAt_sublayout h.1 kernL_ok (i := 11) (by kernel_rfl)
theorem codeAt_k_52 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 52)) k_52 :=
  codeAt_sublayout h.1 kernL_ok (i := 12) (by kernel_rfl)
theorem codeAt_k_53 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 53)) k_53 :=
  codeAt_sublayout h.1 kernL_ok (i := 13) (by kernel_rfl)
theorem codeAt_k_97 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 97)) k_97 :=
  codeAt_sublayout h.1 kernL_ok (i := 14) (by kernel_rfl)
theorem codeAt_k_99 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 99)) k_99 :=
  codeAt_sublayout h.1 kernL_ok (i := 15) (by kernel_rfl)
theorem codeAt_k_101 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 101)) k_101 :=
  codeAt_sublayout h.1 kernL_ok (i := 16) (by kernel_rfl)
theorem codeAt_k_103 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 103)) k_103 :=
  codeAt_sublayout h.1 kernL_ok (i := 17) (by kernel_rfl)
theorem codeAt_k_113 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 113)) k_113 :=
  codeAt_sublayout h.1 kernL_ok (i := 18) (by kernel_rfl)
theorem codeAt_k_115 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 115)) k_115 :=
  codeAt_sublayout h.1 kernL_ok (i := 19) (by kernel_rfl)
theorem codeAt_k_123 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 123)) k_123 :=
  codeAt_sublayout h.1 kernL_ok (i := 20) (by kernel_rfl)
theorem codeAt_k_124 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 124)) k_124 :=
  codeAt_sublayout h.1 kernL_ok (i := 21) (by kernel_rfl)
theorem codeAt_k_130 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 130)) k_130 :=
  codeAt_sublayout h.1 kernL_ok (i := 22) (by kernel_rfl)
theorem codeAt_k_132 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 132)) k_132 :=
  codeAt_sublayout h.1 kernL_ok (i := 23) (by kernel_rfl)
theorem codeAt_k_262 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 262)) k_262 :=
  codeAt_sublayout h.1 kernL_ok (i := 24) (by kernel_rfl)
theorem codeAt_k_263 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 263)) k_263 :=
  codeAt_sublayout h.1 kernL_ok (i := 25) (by kernel_rfl)
theorem codeAt_k_265 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 265)) k_265 :=
  codeAt_sublayout h.1 kernL_ok (i := 26) (by kernel_rfl)
theorem codeAt_k_438 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 438)) k_438 :=
  codeAt_sublayout h.1 kernL_ok (i := 27) (by kernel_rfl)
theorem codeAt_k_440 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 440)) k_440 :=
  codeAt_sublayout h.1 kernL_ok (i := 28) (by kernel_rfl)
theorem codeAt_k_441 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 441)) k_441 :=
  codeAt_sublayout h.1 kernL_ok (i := 29) (by kernel_rfl)
theorem codeAt_k_442 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 442)) k_442 :=
  codeAt_sublayout h.1 kernL_ok (i := 30) (by kernel_rfl)
theorem codeAt_k_443 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 443)) k_443 :=
  codeAt_sublayout h.1 kernL_ok (i := 31) (by kernel_rfl)
theorem codeAt_k_446 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 446)) k_446 :=
  codeAt_sublayout h.1 kernL_ok (i := 32) (by kernel_rfl)
theorem codeAt_k_448 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 448)) k_448 :=
  codeAt_sublayout h.1 kernL_ok (i := 33) (by kernel_rfl)
theorem codeAt_k_452 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 452)) k_452 :=
  codeAt_sublayout h.1 kernL_ok (i := 34) (by kernel_rfl)
theorem codeAt_k_453 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 453)) k_453 :=
  codeAt_sublayout h.1 kernL_ok (i := 35) (by kernel_rfl)
theorem codeAt_k_461 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 461)) k_461 :=
  codeAt_sublayout h.1 kernL_ok (i := 36) (by kernel_rfl)
theorem codeAt_k_462 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 462)) k_462 :=
  codeAt_sublayout h.1 kernL_ok (i := 37) (by kernel_rfl)
theorem codeAt_k_466 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 466)) k_466 :=
  codeAt_sublayout h.1 kernL_ok (i := 38) (by kernel_rfl)
theorem codeAt_k_467 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 467)) k_467 :=
  codeAt_sublayout h.1 kernL_ok (i := 39) (by kernel_rfl)
theorem codeAt_k_468 {image : Image} {b : Nat} (h : KernAt image b) :
    CodeAt image (pcOf (b + 468)) k_468 :=
  codeAt_sublayout h.1 kernL_ok (i := 40) (by kernel_rfl)
theorem kernCode_expand : (Images.expandImage.code.drop 354).take 470 = kernCode := by decide +kernel
theorem kernCode_sign : (Images.signImage.code.drop 543).take 470 = kernCode := by decide +kernel
theorem kernAt_of {image : Image} {b : Nat} (hb : b = 354 ∨ b = 543) (hlen : b + 470 ≤ image.code.length)
    (h : (image.code.drop b).take 470 = kernCode) : KernAt image b := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hb⟩
  · rcases hb with rfl | rfl <;> decide
  · rcases hb with rfl | rfl <;> decide
  · rcases hb with rfl | rfl <;> decide
  · rw [← h]
    have e : (pcOf b).toNat = 0x1000 + 4 * b := by rcases hb with rfl | rfl <;> rfl
    rw [e, show (0x1000 + 4 * b - 0x1000) / 4 = b by omega]
    exact List.take_prefix _ _
theorem kernAt_expand : KernAt Images.expandImage 354 := by
  apply kernAt_of (Or.inl rfl) _ kernCode_expand
  rw [show Images.expandImage.code.length = 41715 from Images.expandCode_length]
  decide
theorem kernAt_sign : KernAt Images.signImage 543 := by
  apply kernAt_of (Or.inr rfl) _ kernCode_sign
  rw [show Images.signImage.code.length = 10952 from Images.signCode_length]
  decide
sym_block blk354_0 := symRun { noAlias := true } k_0 (pcOf (354 + 0)) 200
sym_block blk543_0 := symRun { noAlias := true } k_0 (pcOf (543 + 0)) 200
sym_block blk354_3 := symRun { noAlias := true } k_3 (pcOf (354 + 3)) 200
sym_block blk543_3 := symRun { noAlias := true } k_3 (pcOf (543 + 3)) 200
sym_block blk354_7 := symRun { noAlias := true } k_7 (pcOf (354 + 7)) 200
sym_block blk543_7 := symRun { noAlias := true } k_7 (pcOf (543 + 7)) 200
sym_block blk354_9 := symRun { noAlias := true } k_9 (pcOf (354 + 9)) 200
sym_block blk543_9 := symRun { noAlias := true } k_9 (pcOf (543 + 9)) 200
sym_block blk354_31 := symRun { noAlias := true } k_31 (pcOf (354 + 31)) 200
sym_block blk543_31 := symRun { noAlias := true } k_31 (pcOf (543 + 31)) 200
sym_block blk354_40 := symRun { noAlias := true } k_40 (pcOf (354 + 40)) 200
sym_block blk543_40 := symRun { noAlias := true } k_40 (pcOf (543 + 40)) 200
sym_block blk354_43 := symRun { noAlias := true } k_43 (pcOf (354 + 43)) 200
sym_block blk543_43 := symRun { noAlias := true } k_43 (pcOf (543 + 43)) 200
sym_block blk354_44 := symRun { noAlias := true } k_44 (pcOf (354 + 44)) 200
sym_block blk543_44 := symRun { noAlias := true } k_44 (pcOf (543 + 44)) 200
sym_block blk354_47 := symRun { noAlias := true } k_47 (pcOf (354 + 47)) 200
sym_block blk543_47 := symRun { noAlias := true } k_47 (pcOf (543 + 47)) 200
sym_block blk354_48 := symRun { noAlias := true } k_48 (pcOf (354 + 48)) 200
sym_block blk543_48 := symRun { noAlias := true } k_48 (pcOf (543 + 48)) 200
sym_block blk354_51 := symRun { noAlias := true } k_51 (pcOf (354 + 51)) 200
sym_block blk543_51 := symRun { noAlias := true } k_51 (pcOf (543 + 51)) 200
sym_block blk354_52 := symRun { noAlias := true } k_52 (pcOf (354 + 52)) 200
sym_block blk543_52 := symRun { noAlias := true } k_52 (pcOf (543 + 52)) 200
sym_block blk354_53 := symRun { noAlias := true } k_53 (pcOf (354 + 53)) 200
sym_block blk543_53 := symRun { noAlias := true } k_53 (pcOf (543 + 53)) 200
sym_block blk354_97 := symRun { noAlias := true } k_97 (pcOf (354 + 97)) 200
sym_block blk543_97 := symRun { noAlias := true } k_97 (pcOf (543 + 97)) 200
sym_block blk354_99 := symRun { noAlias := true } k_99 (pcOf (354 + 99)) 200
sym_block blk543_99 := symRun { noAlias := true } k_99 (pcOf (543 + 99)) 200
sym_block blk354_101 := symRun { noAlias := true } k_101 (pcOf (354 + 101)) 200
sym_block blk543_101 := symRun { noAlias := true } k_101 (pcOf (543 + 101)) 200
sym_block blk354_103 := symRun { noAlias := true } k_103 (pcOf (354 + 103)) 200
sym_block blk543_103 := symRun { noAlias := true } k_103 (pcOf (543 + 103)) 200
sym_block blk354_113 := symRun { noAlias := true } k_113 (pcOf (354 + 113)) 200
sym_block blk543_113 := symRun { noAlias := true } k_113 (pcOf (543 + 113)) 200
sym_block blk354_115 := symRun { noAlias := true } k_115 (pcOf (354 + 115)) 200
sym_block blk543_115 := symRun { noAlias := true } k_115 (pcOf (543 + 115)) 200
sym_block blk354_124 := symRun { noAlias := true } k_124 (pcOf (354 + 124)) 200
sym_block blk543_124 := symRun { noAlias := true } k_124 (pcOf (543 + 124)) 200
sym_block blk354_130 := symRun { noAlias := true } k_130 (pcOf (354 + 130)) 200
sym_block blk543_130 := symRun { noAlias := true } k_130 (pcOf (543 + 130)) 200
sym_block blk354_132 := symRun { noAlias := true } k_132 (pcOf (354 + 132)) 200
sym_block blk543_132 := symRun { noAlias := true } k_132 (pcOf (543 + 132)) 200
sym_block blk354_262 := symRun { noAlias := true } k_262 (pcOf (354 + 262)) 200
sym_block blk543_262 := symRun { noAlias := true } k_262 (pcOf (543 + 262)) 200
sym_block blk354_263 := symRun { noAlias := true } k_263 (pcOf (354 + 263)) 200
sym_block blk543_263 := symRun { noAlias := true } k_263 (pcOf (543 + 263)) 200
sym_block blk354_265 := symRun { noAlias := true } k_265 (pcOf (354 + 265)) 200
sym_block blk543_265 := symRun { noAlias := true } k_265 (pcOf (543 + 265)) 200
sym_block blk354_438 := symRun { noAlias := true } k_438 (pcOf (354 + 438)) 200
sym_block blk543_438 := symRun { noAlias := true } k_438 (pcOf (543 + 438)) 200
sym_block blk354_440 := symRun { noAlias := true } k_440 (pcOf (354 + 440)) 200
sym_block blk543_440 := symRun { noAlias := true } k_440 (pcOf (543 + 440)) 200
sym_block blk354_441 := symRun { noAlias := true } k_441 (pcOf (354 + 441)) 200
sym_block blk543_441 := symRun { noAlias := true } k_441 (pcOf (543 + 441)) 200
sym_block blk354_442 := symRun { noAlias := true } k_442 (pcOf (354 + 442)) 200
sym_block blk543_442 := symRun { noAlias := true } k_442 (pcOf (543 + 442)) 200
sym_block blk354_443 := symRun { noAlias := true } k_443 (pcOf (354 + 443)) 200
sym_block blk543_443 := symRun { noAlias := true } k_443 (pcOf (543 + 443)) 200
sym_block blk354_446 := symRun { noAlias := true } k_446 (pcOf (354 + 446)) 200
sym_block blk543_446 := symRun { noAlias := true } k_446 (pcOf (543 + 446)) 200
sym_block blk354_448 := symRun { noAlias := true } k_448 (pcOf (354 + 448)) 200
sym_block blk543_448 := symRun { noAlias := true } k_448 (pcOf (543 + 448)) 200
sym_block blk354_453 := symRun { noAlias := true } k_453 (pcOf (354 + 453)) 200
sym_block blk543_453 := symRun { noAlias := true } k_453 (pcOf (543 + 453)) 200
sym_block blk354_461 := symRun { noAlias := true } k_461 (pcOf (354 + 461)) 200
sym_block blk543_461 := symRun { noAlias := true } k_461 (pcOf (543 + 461)) 200
sym_block blk354_462 := symRun { noAlias := true } k_462 (pcOf (354 + 462)) 200
sym_block blk543_462 := symRun { noAlias := true } k_462 (pcOf (543 + 462)) 200
sym_block blk354_467 := symRun { noAlias := true } k_467 (pcOf (354 + 467)) 200
sym_block blk543_467 := symRun { noAlias := true } k_467 (pcOf (543 + 467)) 200
sym_block blk354_468 := symRun { noAlias := true } k_468 (pcOf (354 + 468)) 200
sym_block blk543_468 := symRun { noAlias := true } k_468 (pcOf (543 + 468)) 200
def st_0 : SymState := blk354_0.res.st
def pcE_0 (b : Nat) : E := .c (pcOf (b + 2))
theorem run_0 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_0 (pcOf (b + 0)) 200 =
      some ⟨st_0, pcE_0 b, blk354_0.res.stop, blk354_0.res.steps, blk354_0.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_0.trans (congrArg some (by kernel_rfl))
  · exact blk543_0.trans (congrArg some (by kernel_rfl))
def st_3 : SymState := blk354_3.res.st
def pcE_3 (b : Nat) : E := .c (pcOf (b + 7))
theorem run_3 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_3 (pcOf (b + 3)) 200 =
      some ⟨st_3, pcE_3 b, blk354_3.res.stop, blk354_3.res.steps, blk354_3.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_3.trans (congrArg some (by kernel_rfl))
  · exact blk543_3.trans (congrArg some (by kernel_rfl))
def st_7 : SymState := blk354_7.res.st
def pcE_7 (b : Nat) : E := rebase blk354_7.res.pc (pcOf (b + 97)) (pcOf (b + 9))
theorem run_7 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_7 (pcOf (b + 7)) 200 =
      some ⟨st_7, pcE_7 b, blk354_7.res.stop, blk354_7.res.steps, blk354_7.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_7.trans (congrArg some (by kernel_rfl))
  · exact blk543_7.trans (congrArg some (by kernel_rfl))
def st_9 : SymState := blk354_9.res.st
def pcE_9 (b : Nat) : E := .c (pcOf (b + 31))
theorem run_9 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_9 (pcOf (b + 9)) 200 =
      some ⟨st_9, pcE_9 b, blk354_9.res.stop, blk354_9.res.steps, blk354_9.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_9.trans (congrArg some (by kernel_rfl))
  · exact blk543_9.trans (congrArg some (by kernel_rfl))
def st_31 : SymState := blk354_31.res.st
def pcE_31 (b : Nat) : E := rebase blk354_31.res.pc (pcOf (b + 43)) (pcOf (b + 40))
theorem run_31 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_31 (pcOf (b + 31)) 200 =
      some ⟨st_31, pcE_31 b, blk354_31.res.stop, blk354_31.res.steps, blk354_31.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_31.trans (congrArg some (by kernel_rfl))
  · exact blk543_31.trans (congrArg some (by kernel_rfl))
def st_40 : SymState := blk354_40.res.st
def pcE_40 (b : Nat) : E := .c (pcOf (b + 43))
theorem run_40 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_40 (pcOf (b + 40)) 200 =
      some ⟨st_40, pcE_40 b, blk354_40.res.stop, blk354_40.res.steps, blk354_40.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_40.trans (congrArg some (by kernel_rfl))
  · exact blk543_40.trans (congrArg some (by kernel_rfl))
def st_43 : SymState := blk354_43.res.st
def pcE_43 (b : Nat) : E := rebase blk354_43.res.pc (pcOf (b + 47)) (pcOf (b + 44))
theorem run_43 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_43 (pcOf (b + 43)) 200 =
      some ⟨st_43, pcE_43 b, blk354_43.res.stop, blk354_43.res.steps, blk354_43.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_43.trans (congrArg some (by kernel_rfl))
  · exact blk543_43.trans (congrArg some (by kernel_rfl))
def st_44 : SymState := blk354_44.res.st
def pcE_44 (b : Nat) : E := .c (pcOf (b + 47))
theorem run_44 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_44 (pcOf (b + 44)) 200 =
      some ⟨st_44, pcE_44 b, blk354_44.res.stop, blk354_44.res.steps, blk354_44.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_44.trans (congrArg some (by kernel_rfl))
  · exact blk543_44.trans (congrArg some (by kernel_rfl))
def st_47 : SymState := blk354_47.res.st
def pcE_47 (b : Nat) : E := rebase blk354_47.res.pc (pcOf (b + 51)) (pcOf (b + 48))
theorem run_47 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_47 (pcOf (b + 47)) 200 =
      some ⟨st_47, pcE_47 b, blk354_47.res.stop, blk354_47.res.steps, blk354_47.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_47.trans (congrArg some (by kernel_rfl))
  · exact blk543_47.trans (congrArg some (by kernel_rfl))
def st_48 : SymState := blk354_48.res.st
def pcE_48 (b : Nat) : E := .c (pcOf (b + 51))
theorem run_48 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_48 (pcOf (b + 48)) 200 =
      some ⟨st_48, pcE_48 b, blk354_48.res.stop, blk354_48.res.steps, blk354_48.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_48.trans (congrArg some (by kernel_rfl))
  · exact blk543_48.trans (congrArg some (by kernel_rfl))
def st_51 : SymState := blk354_51.res.st
def pcE_51 (b : Nat) : E := rebase blk354_51.res.pc (pcOf (b + 101)) (pcOf (b + 52))
theorem run_51 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_51 (pcOf (b + 51)) 200 =
      some ⟨st_51, pcE_51 b, blk354_51.res.stop, blk354_51.res.steps, blk354_51.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_51.trans (congrArg some (by kernel_rfl))
  · exact blk543_51.trans (congrArg some (by kernel_rfl))
def st_52 : SymState := blk354_52.res.st
def pcE_52 (b : Nat) : E := rebase blk354_52.res.pc (pcOf (b + 101)) (pcOf (b + 53))
theorem run_52 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_52 (pcOf (b + 52)) 200 =
      some ⟨st_52, pcE_52 b, blk354_52.res.stop, blk354_52.res.steps, blk354_52.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_52.trans (congrArg some (by kernel_rfl))
  · exact blk543_52.trans (congrArg some (by kernel_rfl))
def st_53 : SymState := blk354_53.res.st
def pcE_53 (b : Nat) : E := .c (pcOf (b + 7))
theorem run_53 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_53 (pcOf (b + 53)) 200 =
      some ⟨st_53, pcE_53 b, blk354_53.res.stop, blk354_53.res.steps, blk354_53.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_53.trans (congrArg some (by kernel_rfl))
  · exact blk543_53.trans (congrArg some (by kernel_rfl))
def st_97 : SymState := blk354_97.res.st
def pcE_97 (b : Nat) : E := rebase blk354_97.res.pc (pcOf (b + 101)) (pcOf (b + 99))
theorem run_97 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_97 (pcOf (b + 97)) 200 =
      some ⟨st_97, pcE_97 b, blk354_97.res.stop, blk354_97.res.steps, blk354_97.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_97.trans (congrArg some (by kernel_rfl))
  · exact blk543_97.trans (congrArg some (by kernel_rfl))
def st_99 : SymState := blk354_99.res.st
def pcE_99 (b : Nat) : E := blk354_99.res.pc
theorem run_99 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_99 (pcOf (b + 99)) 200 =
      some ⟨st_99, pcE_99 b, blk354_99.res.stop, blk354_99.res.steps, blk354_99.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_99.trans (congrArg some (by kernel_rfl))
  · exact blk543_99.trans (congrArg some (by kernel_rfl))
def st_101 : SymState := blk354_101.res.st
def pcE_101 (b : Nat) : E := blk354_101.res.pc
theorem run_101 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_101 (pcOf (b + 101)) 200 =
      some ⟨st_101, pcE_101 b, blk354_101.res.stop, blk354_101.res.steps, blk354_101.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_101.trans (congrArg some (by kernel_rfl))
  · exact blk543_101.trans (congrArg some (by kernel_rfl))
def st_103 : SymState := blk354_103.res.st
def pcE_103 (b : Nat) : E := .c (pcOf (b + 113))
theorem run_103 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_103 (pcOf (b + 103)) 200 =
      some ⟨st_103, pcE_103 b, blk354_103.res.stop, blk354_103.res.steps, blk354_103.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_103.trans (congrArg some (by kernel_rfl))
  · exact blk543_103.trans (congrArg some (by kernel_rfl))
def st_113 : SymState := blk354_113.res.st
def pcE_113 (b : Nat) : E := rebase blk354_113.res.pc (pcOf (b + 0)) (pcOf (b + 115))
theorem run_113 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_113 (pcOf (b + 113)) 200 =
      some ⟨st_113, pcE_113 b, blk354_113.res.stop, blk354_113.res.steps, blk354_113.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_113.trans (congrArg some (by kernel_rfl))
  · exact blk543_113.trans (congrArg some (by kernel_rfl))
def st_115 : SymState := blk354_115.res.st
def pcE_115 (b : Nat) : E := .c (pcOf (b + 123))
theorem run_115 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_115 (pcOf (b + 115)) 200 =
      some ⟨st_115, pcE_115 b, blk354_115.res.stop, blk354_115.res.steps, blk354_115.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_115.trans (congrArg some (by kernel_rfl))
  · exact blk543_115.trans (congrArg some (by kernel_rfl))
def st_124 : SymState := blk354_124.res.st
def pcE_124 (b : Nat) : E := rebase blk354_124.res.pc (pcOf (b + 263)) (pcOf (b + 130))
theorem run_124 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_124 (pcOf (b + 124)) 200 =
      some ⟨st_124, pcE_124 b, blk354_124.res.stop, blk354_124.res.steps, blk354_124.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_124.trans (congrArg some (by kernel_rfl))
  · exact blk543_124.trans (congrArg some (by kernel_rfl))
def st_130 : SymState := blk354_130.res.st
def pcE_130 (b : Nat) : E := rebase blk354_130.res.pc (pcOf (b + 468)) (pcOf (b + 132))
theorem run_130 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_130 (pcOf (b + 130)) 200 =
      some ⟨st_130, pcE_130 b, blk354_130.res.stop, blk354_130.res.steps, blk354_130.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_130.trans (congrArg some (by kernel_rfl))
  · exact blk543_130.trans (congrArg some (by kernel_rfl))
def st_132 : SymState := blk354_132.res.st
def pcE_132 (b : Nat) : E := rebase blk354_132.res.pc (pcOf (b + 468)) (pcOf (b + 262))
theorem run_132 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_132 (pcOf (b + 132)) 200 =
      some ⟨st_132, pcE_132 b, blk354_132.res.stop, blk354_132.res.steps, blk354_132.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_132.trans (congrArg some (by kernel_rfl))
  · exact blk543_132.trans (congrArg some (by kernel_rfl))
def st_262 : SymState := blk354_262.res.st
def pcE_262 (b : Nat) : E := .c (pcOf (b + 438))
theorem run_262 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_262 (pcOf (b + 262)) 200 =
      some ⟨st_262, pcE_262 b, blk354_262.res.stop, blk354_262.res.steps, blk354_262.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_262.trans (congrArg some (by kernel_rfl))
  · exact blk543_262.trans (congrArg some (by kernel_rfl))
def st_263 : SymState := blk354_263.res.st
def pcE_263 (b : Nat) : E := rebase blk354_263.res.pc (pcOf (b + 468)) (pcOf (b + 265))
theorem run_263 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_263 (pcOf (b + 263)) 200 =
      some ⟨st_263, pcE_263 b, blk354_263.res.stop, blk354_263.res.steps, blk354_263.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_263.trans (congrArg some (by kernel_rfl))
  · exact blk543_263.trans (congrArg some (by kernel_rfl))
def st_265 : SymState := blk354_265.res.st
def pcE_265 (b : Nat) : E := rebase blk354_265.res.pc (pcOf (b + 468)) (pcOf (b + 362))
theorem run_265 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_265 (pcOf (b + 265)) 200 =
      some ⟨st_265, pcE_265 b, blk354_265.res.stop, blk354_265.res.steps, blk354_265.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_265.trans (congrArg some (by kernel_rfl))
  · exact blk543_265.trans (congrArg some (by kernel_rfl))
def st_438 : SymState := blk354_438.res.st
def pcE_438 (b : Nat) : E := rebase blk354_438.res.pc (pcOf (b + 441)) (pcOf (b + 440))
theorem run_438 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_438 (pcOf (b + 438)) 200 =
      some ⟨st_438, pcE_438 b, blk354_438.res.stop, blk354_438.res.steps, blk354_438.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_438.trans (congrArg some (by kernel_rfl))
  · exact blk543_438.trans (congrArg some (by kernel_rfl))
def st_440 : SymState := blk354_440.res.st
def pcE_440 (b : Nat) : E := .c (pcOf (b + 441))
theorem run_440 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_440 (pcOf (b + 440)) 200 =
      some ⟨st_440, pcE_440 b, blk354_440.res.stop, blk354_440.res.steps, blk354_440.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_440.trans (congrArg some (by kernel_rfl))
  · exact blk543_440.trans (congrArg some (by kernel_rfl))
def st_441 : SymState := blk354_441.res.st
def pcE_441 (b : Nat) : E := .c (pcOf (b + 442))
theorem run_441 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_441 (pcOf (b + 441)) 200 =
      some ⟨st_441, pcE_441 b, blk354_441.res.stop, blk354_441.res.steps, blk354_441.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_441.trans (congrArg some (by kernel_rfl))
  · exact blk543_441.trans (congrArg some (by kernel_rfl))
def st_442 : SymState := blk354_442.res.st
def pcE_442 (b : Nat) : E := rebase blk354_442.res.pc (pcOf (b + 461)) (pcOf (b + 443))
theorem run_442 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_442 (pcOf (b + 442)) 200 =
      some ⟨st_442, pcE_442 b, blk354_442.res.stop, blk354_442.res.steps, blk354_442.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_442.trans (congrArg some (by kernel_rfl))
  · exact blk543_442.trans (congrArg some (by kernel_rfl))
def st_443 : SymState := blk354_443.res.st
def pcE_443 (b : Nat) : E := rebase blk354_443.res.pc (pcOf (b + 448)) (pcOf (b + 446))
theorem run_443 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_443 (pcOf (b + 443)) 200 =
      some ⟨st_443, pcE_443 b, blk354_443.res.stop, blk354_443.res.steps, blk354_443.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_443.trans (congrArg some (by kernel_rfl))
  · exact blk543_443.trans (congrArg some (by kernel_rfl))
def st_446 : SymState := blk354_446.res.st
def pcE_446 (b : Nat) : E := .c (pcOf (b + 448))
theorem run_446 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_446 (pcOf (b + 446)) 200 =
      some ⟨st_446, pcE_446 b, blk354_446.res.stop, blk354_446.res.steps, blk354_446.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_446.trans (congrArg some (by kernel_rfl))
  · exact blk543_446.trans (congrArg some (by kernel_rfl))
def st_448 : SymState := blk354_448.res.st
def pcE_448 (b : Nat) : E := .c (pcOf (b + 452))
theorem run_448 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_448 (pcOf (b + 448)) 200 =
      some ⟨st_448, pcE_448 b, blk354_448.res.stop, blk354_448.res.steps, blk354_448.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_448.trans (congrArg some (by kernel_rfl))
  · exact blk543_448.trans (congrArg some (by kernel_rfl))
def st_453 : SymState := blk354_453.res.st
def pcE_453 (b : Nat) : E := .c (pcOf (b + 442))
theorem run_453 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_453 (pcOf (b + 453)) 200 =
      some ⟨st_453, pcE_453 b, blk354_453.res.stop, blk354_453.res.steps, blk354_453.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_453.trans (congrArg some (by kernel_rfl))
  · exact blk543_453.trans (congrArg some (by kernel_rfl))
def st_461 : SymState := blk354_461.res.st
def pcE_461 (b : Nat) : E := rebase blk354_461.res.pc (pcOf (b + 467)) (pcOf (b + 462))
theorem run_461 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_461 (pcOf (b + 461)) 200 =
      some ⟨st_461, pcE_461 b, blk354_461.res.stop, blk354_461.res.steps, blk354_461.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_461.trans (congrArg some (by kernel_rfl))
  · exact blk543_461.trans (congrArg some (by kernel_rfl))
def st_462 : SymState := blk354_462.res.st
def pcE_462 (b : Nat) : E := .c (pcOf (b + 466))
theorem run_462 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_462 (pcOf (b + 462)) 200 =
      some ⟨st_462, pcE_462 b, blk354_462.res.stop, blk354_462.res.steps, blk354_462.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_462.trans (congrArg some (by kernel_rfl))
  · exact blk543_462.trans (congrArg some (by kernel_rfl))
def st_467 : SymState := blk354_467.res.st
def pcE_467 (b : Nat) : E := blk354_467.res.pc
theorem run_467 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_467 (pcOf (b + 467)) 200 =
      some ⟨st_467, pcE_467 b, blk354_467.res.stop, blk354_467.res.steps, blk354_467.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_467.trans (congrArg some (by kernel_rfl))
  · exact blk543_467.trans (congrArg some (by kernel_rfl))
def st_468 : SymState := blk354_468.res.st
def pcE_468 (b : Nat) : E := .c (pcOf (b + 113))
theorem run_468 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } k_468 (pcOf (b + 468)) 200 =
      some ⟨st_468, pcE_468 b, blk354_468.res.stop, blk354_468.res.steps, blk354_468.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk354_468.trans (congrArg some (by kernel_rfl))
  · exact blk543_468.trans (congrArg some (by kernel_rfl))
def gatePc (b : Nat) : Nat := if b = 354 then 1152 else 1221
def gateEHead : List (BitVec 32) := [131895,394474243,0xe35313,7566099,0xd0031663]
def gateEJump : List (BitVec 32) := [0xb80ff06f]
def gateSHead : List (BitVec 32) := [131895,394474243,0xe35313,7566099,0xee031663]
def gateSJump : List (BitVec 32) := [0xd60ff06f]
def gateHead (b : Nat) : List (BitVec 32) := if b = 354 then gateEHead else gateSHead
def gateJump (b : Nat) : List (BitVec 32) := if b = 354 then gateEJump else gateSJump
def gateL (b : Nat) : Rv.Layout := [(0, gateHead b), (5, gateJump b)]
def GateAt (image : Image) (b : Nat) : Prop := CodeAt image (pcOf (gatePc b)) (layoutCode (gateL b))
theorem gateL_ok (b : Nat) : layoutOk 0 (gateL b) = true := by
  unfold gateL; by_cases hb : b = 354 <;> simp [gateHead, gateJump, hb, gateEHead, gateSHead,
    gateEJump, gateSJump, layoutOk]
theorem codeAt_gateHead {image : Image} {b : Nat} (h : GateAt image b) :
    CodeAt image (pcOf (gatePc b)) (gateHead b) := by
  simpa using codeAt_sublayout h (gateL_ok b) (i := 0) rfl
theorem codeAt_gateJump {image : Image} {b : Nat} (h : GateAt image b) :
    CodeAt image (pcOf (gatePc b + 5)) (gateJump b) :=
  codeAt_sublayout h (gateL_ok b) (i := 1) rfl
theorem gateAt_expand : GateAt Images.expandImage 354 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide +kernel
theorem gateAt_sign : GateAt Images.signImage 543 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide +kernel
sym_block blkGateE := symRun { noAlias := true } gateEHead (pcOf 1152) 20
sym_block blkGateS := symRun { noAlias := true } gateSHead (pcOf 1221) 20
sym_block blkGateJE := symRun { noAlias := true } gateEJump (pcOf 1157) 20
sym_block blkGateJS := symRun { noAlias := true } gateSJump (pcOf 1226) 20
def gateSt : SymState := blkGateE.res.st
def gateEnd (b : Nat) : E := rebase blkGateE.res.pc (pcOf (b + 101)) (pcOf (gatePc b + 5))
theorem run_gate {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } (gateHead b) (pcOf (gatePc b)) 20 =
      some ⟨gateSt, gateEnd b, blkGateE.res.stop, blkGateE.res.steps, blkGateE.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blkGateE.trans (congrArg some (by kernel_rfl))
  · exact blkGateS.trans (congrArg some (by kernel_rfl))
theorem run_gateJump {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun { noAlias := true } (gateJump b) (pcOf (gatePc b + 5)) 20 =
      some ⟨blkGateJE.res.st, .c (pcOf (b + 3)), blkGateJE.res.stop,
        blkGateJE.res.steps, blkGateJE.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blkGateJE.trans (congrArg some (by kernel_rfl))
  · exact blkGateJS.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Search
