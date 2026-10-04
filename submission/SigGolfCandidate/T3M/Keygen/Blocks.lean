import SigGolfCandidate.T3M.Keygen.PackedBlocks
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Images.Keygen

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
def seg_0 : List (BitVec 32) := [659,0x8000e93,134967,963331,9352067,7286819,8336419,0x9000e93,134967,34541331,963331,9352067,7286819,8336419,134967,34551843,34552867,1043,1171,56626451,53480851,3987,133943,0x460b0b13,327991,2323]
def seg_26 : List (BitVec 32) := [4919,40456803]
def seg_28 : List (BitVec 32) := [138167,0xa00b8b93,6882227,4428691,2329779,465567983]
def seg_34 : List (BitVec 32) := [1640723,0xfddff06f]
def seg_36 : List (BitVec 32) := [0xc00793,806357651,805306607]
def seg_39 : List (BitVec 32) := [998244463,16855811,25244547,7286819,8336419,39991,34343955,0x40000a13,2098835]
def seg_48 : List (BitVec 32) := [1049363,0x86a0663]
def seg_50 : List (BitVec 32) := [2451]
def seg_51 : List (BitVec 32) := [0x749dc63]
def seg_52 : List (BitVec 32) := [4919,0xd0130313,33988371,31679283,34182035,134711,7223331,8272931,132407,67110291,132663,0x6060613]
def seg_64 : List (BitVec 32) := [115]
def seg_65 : List (BitVec 32) := [20581939,5119507,3018291,930563,9319299,134839,0x60e8e93,966147,9354883,29573939,30655411,7090211,8139811,17566739,1673619,0xf8dff06f]
def seg_81 : List (BitVec 32) := [1726995,1476243,0xf75ff06f]
def seg_84 : List (BitVec 32) := [0x8000e93,40759,0xfe0f0f13,963331,9352067,7286819,8336419,0x9000e93,40759,963331,9352067,7286819,8336419,40759,0xfe0f0f13,34551843,34552867,4919,0xe0130313,915,40503,0xfe0e0e13,7223331,8272931,38199,0xfe050513,34231,67470739,38455]
def seg_113 : List (BitVec 32) := [115]
def seg_114 : List (BitVec 32) := [1049235,1299]
def seg_116 : List (BitVec 32) := [115]
def seg_277 : List (BitVec 32) := [327991,65811,0xa000f13,16855811,25244547,7286819,8336419,527415,34343955,6711,657939,2835]
def seg_289 : List (BitVec 32) := [2963,1727763,4856467,327991,65811,2788019]
def seg_295 : List (BitVec 32) := [4919,0xd0130313,34280339,7562035,34313107,134711,921107,7223331,8272931,132407,328979,67110291,132663,0x6060613]
def seg_309 : List (BitVec 32) := [115]
def seg_310 : List (BitVec 32) := [701187,406403,7553843,7090211,9089795,8795011,7553843,7091235,17478403,17183619,7553843,7092259,25867011,25572227,7553843,7093283,34245267,34343955,1805203,0xf7abece3]
def seg_330 : List (BitVec 32) := [1726995,1772307,0xc00313,0xf46b68e3]
def seg_334 : List (BitVec 32) := [134711,921107,3767,0x80e8e93,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,0xe0130313,7223331,932899,132407,328979,67110291,460343,394771,115,1049363,33755923,7224355,460343,33949203,115,0xfff00913,3758355,657847,625043,461623,723731,527543,822419,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb023,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb423,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb823,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecbc23,1049235,1299,115]
def sub_0 : List (BitVec 32) := [2579]
def sub_1 : List (BitVec 32) := [18488931]
def sub_2 : List (BitVec 32) := [134839,487493267,963331,9352067,7057443,8107043]
def sub_8 : List (BitVec 32) := [89785443]
def sub_9 : List (BitVec 32) := [0x7340006f, 0x014383b3, 0x02039313, 0x01041f13, 0x01e36333, 0x10136313, 0x00020e37, 0x1a0e0e13, 0x006e3823, 0x00020537, 0x1a050513, 0x04000593, 0x00020637, 0x1d060613]
def sub_23 : List (BitVec 32) := [115]
def sub_24 : List (BitVec 32) := [1706515,0xfa1ff06f]
def sub_26 : List (BitVec 32) := [32871]
def sub_27 : List (BitVec 32) := [33171,295827,34152211,31712179,134711,437128723,8272931,134711,0x600e0e13,8272931,17044243,538141459,7223331,2451]
def sub_41 : List (BitVec 32) := [0xda9dc63]
def sub_42 : List (BitVec 32) := [1700627,67310179]
def sub_44 : List (BitVec 32) := [1695251,17044243,34479891,31679283,1270547,295827,34152211,31712179,134711,7223331,8272931,132407,67110291,132663,67503635]
def sub_59 : List (BitVec 32) := [115]
def sub_60 : List (BitVec 32) := [1703443,5119507,134839,68062867,31329843,134967,487526163,930563,9319299,7286819,8336419,20647475]
def sub_72 : List (BitVec 32) := [936067]
def sub_73 : List (BitVec 32) := [7342739,267363]
def sub_75 : List (BitVec 32) := [0x6750006f]
def sub_76 : List (BitVec 32) := [0xf8463]
def sub_77 : List (BitVec 32) := [559763]
def sub_78 : List (BitVec 32) := [0xec9ff0ef]
def sub_79 : List (BitVec 32) := [34576995]
def sub_80 : List (BitVec 32) := [4824595,623715]
def sub_82 : List (BitVec 32) := [17698323]
def sub_83 : List (BitVec 32) := [134839,0x600e8e93,31329843,134839,487493267,963331,9352067,7221283,8270883]
def sub_92 : List (BitVec 32) := [17533843,1673619,0xf2dff06f]
def sub_95 : List (BitVec 32) := [68129379]
def sub_96 : List (BitVec 32) := [1901331,4395795,66257683,0xfc037313,132407,0x60050513,198035,132663,0x3c060613]
def sub_105 : List (BitVec 32) := [115]
def sub_106 : List (BitVec 32) := [134839,0x3c0e8e93,963331,9352067,7122979,8172579]
def sub_112 : List (BitVec 32) := [98407]
def sub_113 : List (BitVec 32) := [1051155,0xfff78313,6953523]
def sub_116 : List (BitVec 32) := [0xa0a0663]
def sub_117 : List (BitVec 32) := [658451]
def sub_118 : List (BitVec 32) := [1708819,0x86c5c63]
def sub_120 : List (BitVec 32) := [6037011,3018291,134967,537857811,930563,9319299,7286819,8336419,134967,588189459,17707779,26096515,7286819,8336419,33857043,30073651,0xfe6f3023,55221779,787347,0x580e42e3]
def sub_140 : List (BitVec 32) := [0xfe7f3423,132407,537199891,67110291,132663,604374547]
def sub_146 : List (BitVec 32) := [115]
def sub_147 : List (BitVec 32) := [4988435,3018291,134839,604933779,963331,9352067,7221283,8270883,1838099,0xf69ff06f]
def sub_157 : List (BitVec 32) := [1726995,0xf59ff06f]
def sub_159 : List (BitVec 32) := [32871]
def revCode : List (BitVec 32) := [787347,0xff3f313,8590099,8639379,6546355,7735,0xf0fe0e13,29618995,4395795,4445075,29619123,6546355,15927,859704851,29618995,2298643,2347923,29619123,6546355,24119,0x555e0e13,29618995,1250067,1299347,29619123,6546355,50566035,0xa14ff06f]
def subL : Rv.Layout := [(0, sub_0), (1, sub_1), (2, sub_2), (8, sub_8), (9, sub_9), (23, sub_23), (24, sub_24), (26, sub_26), (27, sub_27), (41, sub_41), (42, sub_42), (44, sub_44), (59, sub_59), (60, sub_60), (72, sub_72), (73, sub_73), (75, sub_75), (76, sub_76), (77, sub_77), (78, sub_78), (79, sub_79), (80, sub_80), (82, sub_82), (83, sub_83), (92, sub_92), (95, sub_95), (96, sub_96), (105, sub_105), (106, sub_106), (112, sub_112), (113, sub_113), (116, sub_116), (117, sub_117), (118, sub_118), (120, sub_120), (140, sub_140), (146, sub_146), (147, sub_147), (157, sub_157), (159, sub_159)]
def subCode : List (BitVec 32) := layoutCode subL
theorem subL_ok : layoutOk 0 subL = true := by decide +kernel
def maxLow : List (BitVec 32) := [3148435,0x99b9d663]
def maxHigh : List (BitVec 32) := [4197011,0x984ff06f]
def maxLayout : Rv.Layout := [(0, maxLow), (2, maxHigh)]
def maxDigitCode : List (BitVec 32) := layoutCode maxLayout
theorem maxLayout_ok : layoutOk 0 maxLayout = true := by decide +kernel
def packedHelper : List (BitVec 32) :=
  PackedBlocks.keygen_layer0 ++ PackedBlocks.keygen_layer1 ++
    PackedBlocks.keygen_layer23 ++ PackedBlocks.keygen_body
def seg_542 : List (BitVec 32) :=
  List.replicate 45 0x00000013 ++ packedHelper ++ List.replicate 505 0x00000013
def mainL : Rv.Layout := [(0, seg_0), (26, seg_26), (28, seg_28), (34, seg_34), (36, seg_36), (39, seg_39), (48, seg_48), (50, seg_50), (51, seg_51), (52, seg_52), (64, seg_64), (65, seg_65), (81, seg_81), (84, seg_84), (113, seg_113), (114, seg_114), (116, seg_116), (117, subCode), (277, seg_277), (289, seg_289), (295, seg_295), (309, seg_309), (310, seg_310), (330, seg_330), (334, seg_334), (542, seg_542), (1117, maxDigitCode), (1121, revCode)]
theorem mainL_ok : layoutOk 0 mainL = true := by decide +kernel
abbrev image : Image := Images.keygenImage
theorem code_eq : image.code = layoutCode mainL := by decide +kernel
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_layout code_eq mainL_ok (i := 0) (by kernel_rfl) (by decide)
theorem codeAt_26 : CodeAt image (pcOf 26) seg_26 :=
  codeAt_layout code_eq mainL_ok (i := 1) (by kernel_rfl) (by decide)
theorem codeAt_28 : CodeAt image (pcOf 28) seg_28 :=
  codeAt_layout code_eq mainL_ok (i := 2) (by kernel_rfl) (by decide)
theorem codeAt_34 : CodeAt image (pcOf 34) seg_34 :=
  codeAt_layout code_eq mainL_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_36 : CodeAt image (pcOf 36) seg_36 :=
  codeAt_layout code_eq mainL_ok (i := 4) (by kernel_rfl) (by decide)
theorem codeAt_39 : CodeAt image (pcOf 39) seg_39 :=
  codeAt_layout code_eq mainL_ok (i := 5) (by kernel_rfl) (by decide)
theorem codeAt_48 : CodeAt image (pcOf 48) seg_48 :=
  codeAt_layout code_eq mainL_ok (i := 6) (by kernel_rfl) (by decide)
theorem codeAt_50 : CodeAt image (pcOf 50) seg_50 :=
  codeAt_layout code_eq mainL_ok (i := 7) (by kernel_rfl) (by decide)
theorem codeAt_51 : CodeAt image (pcOf 51) seg_51 :=
  codeAt_layout code_eq mainL_ok (i := 8) (by kernel_rfl) (by decide)
theorem codeAt_52 : CodeAt image (pcOf 52) seg_52 :=
  codeAt_layout code_eq mainL_ok (i := 9) (by kernel_rfl) (by decide)
theorem codeAt_64 : CodeAt image (pcOf 64) seg_64 :=
  codeAt_layout code_eq mainL_ok (i := 10) (by kernel_rfl) (by decide)
theorem codeAt_65 : CodeAt image (pcOf 65) seg_65 :=
  codeAt_layout code_eq mainL_ok (i := 11) (by kernel_rfl) (by decide)
theorem codeAt_81 : CodeAt image (pcOf 81) seg_81 :=
  codeAt_layout code_eq mainL_ok (i := 12) (by kernel_rfl) (by decide)
theorem codeAt_84 : CodeAt image (pcOf 84) seg_84 :=
  codeAt_layout code_eq mainL_ok (i := 13) (by kernel_rfl) (by decide)
theorem codeAt_113 : CodeAt image (pcOf 113) seg_113 :=
  codeAt_layout code_eq mainL_ok (i := 14) (by kernel_rfl) (by decide)
theorem codeAt_114 : CodeAt image (pcOf 114) seg_114 :=
  codeAt_layout code_eq mainL_ok (i := 15) (by kernel_rfl) (by decide)
theorem codeAt_116 : CodeAt image (pcOf 116) seg_116 :=
  codeAt_layout code_eq mainL_ok (i := 16) (by kernel_rfl) (by decide)
theorem codeAt_subCode : CodeAt image (pcOf 117) subCode :=
  codeAt_layout code_eq mainL_ok (i := 17) (by kernel_rfl) (by decide)
theorem codeAt_277 : CodeAt image (pcOf 277) seg_277 :=
  codeAt_layout code_eq mainL_ok (i := 18) (by kernel_rfl) (by decide)
theorem codeAt_289 : CodeAt image (pcOf 289) seg_289 :=
  codeAt_layout code_eq mainL_ok (i := 19) (by kernel_rfl) (by decide)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_layout code_eq mainL_ok (i := 20) (by kernel_rfl) (by decide)
theorem codeAt_309 : CodeAt image (pcOf 309) seg_309 :=
  codeAt_layout code_eq mainL_ok (i := 21) (by kernel_rfl) (by decide)
theorem codeAt_310 : CodeAt image (pcOf 310) seg_310 :=
  codeAt_layout code_eq mainL_ok (i := 22) (by kernel_rfl) (by decide)
theorem codeAt_330 : CodeAt image (pcOf 330) seg_330 :=
  codeAt_layout code_eq mainL_ok (i := 23) (by kernel_rfl) (by decide)
theorem codeAt_334 : CodeAt image (pcOf 334) seg_334 :=
  codeAt_layout code_eq mainL_ok (i := 24) (by kernel_rfl) (by decide)
def SubAt (image : Image) (b : Nat) : Prop := CodeAt image (pcOf b) subCode ∧ (b = 117 ∨ b = 1013) ∧
  (CodeAt image (pcOf (b + 1000)) maxDigitCode ∧ CodeAt image (pcOf (b + 1004)) revCode ∧
    ((image = Images.keygenImage ∧ b = 117) ∨ (image = Images.signImage ∧ b = 1013)))
theorem codeAt_max : CodeAt image (pcOf 1117) maxDigitCode :=
  codeAt_layout code_eq mainL_ok (i := 26) (by kernel_rfl) (by decide)
theorem codeAt_1121 : CodeAt image (pcOf 1121) revCode :=
  codeAt_layout code_eq mainL_ok (i := 27) (by kernel_rfl) (by decide)
theorem subAt_keygen : SubAt image 117 :=
  ⟨codeAt_subCode, Or.inl rfl, codeAt_max, codeAt_1121, Or.inl ⟨rfl, rfl⟩⟩
theorem codeAt_rev {image : Image} {b : Nat} (h : SubAt image b) : CodeAt image (pcOf (b + 1004)) revCode :=
  h.2.2.2.1
theorem codeAt_maxLow {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1000)) maxLow := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 0) (o := 0) (seg := maxLow) (by kernel_rfl)
  simpa only [Nat.add_zero] using q
theorem codeAt_maxHigh {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1002)) maxHigh := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 1) (o := 2) (seg := maxHigh) (by kernel_rfl)
  simpa [Nat.add_assoc] using q
theorem codeAt_sub_0 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 0)) sub_0 :=
  codeAt_sublayout h.1 subL_ok (i := 0) (by kernel_rfl)
theorem codeAt_sub_1 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1)) sub_1 :=
  codeAt_sublayout h.1 subL_ok (i := 1) (by kernel_rfl)
theorem codeAt_sub_2 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 2)) sub_2 :=
  codeAt_sublayout h.1 subL_ok (i := 2) (by kernel_rfl)
theorem codeAt_sub_8 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 8)) sub_8 :=
  codeAt_sublayout h.1 subL_ok (i := 3) (by kernel_rfl)
theorem codeAt_sub_9 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 9)) sub_9 :=
  codeAt_sublayout h.1 subL_ok (i := 4) (by kernel_rfl)
theorem codeAt_sub_23 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 23)) sub_23 :=
  codeAt_sublayout h.1 subL_ok (i := 5) (by kernel_rfl)
theorem codeAt_sub_24 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 24)) sub_24 :=
  codeAt_sublayout h.1 subL_ok (i := 6) (by kernel_rfl)
theorem codeAt_sub_26 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 26)) sub_26 :=
  codeAt_sublayout h.1 subL_ok (i := 7) (by kernel_rfl)
theorem codeAt_sub_27 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 27)) sub_27 :=
  codeAt_sublayout h.1 subL_ok (i := 8) (by kernel_rfl)
theorem codeAt_sub_41 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 41)) sub_41 :=
  codeAt_sublayout h.1 subL_ok (i := 9) (by kernel_rfl)
theorem codeAt_sub_42 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 42)) sub_42 :=
  codeAt_sublayout h.1 subL_ok (i := 10) (by kernel_rfl)
theorem codeAt_sub_44 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 44)) sub_44 :=
  codeAt_sublayout h.1 subL_ok (i := 11) (by kernel_rfl)
theorem codeAt_sub_59 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 59)) sub_59 :=
  codeAt_sublayout h.1 subL_ok (i := 12) (by kernel_rfl)
theorem codeAt_sub_60 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 60)) sub_60 :=
  codeAt_sublayout h.1 subL_ok (i := 13) (by kernel_rfl)
theorem codeAt_sub_72 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 72)) sub_72 :=
  codeAt_sublayout h.1 subL_ok (i := 14) (by kernel_rfl)
theorem codeAt_sub_73 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 73)) sub_73 :=
  codeAt_sublayout h.1 subL_ok (i := 15) (by kernel_rfl)
theorem codeAt_sub_75 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 75)) sub_75 :=
  codeAt_sublayout h.1 subL_ok (i := 16) (by kernel_rfl)
theorem codeAt_sub_76 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 76)) sub_76 :=
  codeAt_sublayout h.1 subL_ok (i := 17) (by kernel_rfl)
theorem codeAt_sub_77 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 77)) sub_77 :=
  codeAt_sublayout h.1 subL_ok (i := 18) (by kernel_rfl)
theorem codeAt_sub_78 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 78)) sub_78 :=
  codeAt_sublayout h.1 subL_ok (i := 19) (by kernel_rfl)
theorem codeAt_sub_79 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 79)) sub_79 :=
  codeAt_sublayout h.1 subL_ok (i := 20) (by kernel_rfl)
theorem codeAt_sub_80 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 80)) sub_80 :=
  codeAt_sublayout h.1 subL_ok (i := 21) (by kernel_rfl)
theorem codeAt_sub_82 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 82)) sub_82 :=
  codeAt_sublayout h.1 subL_ok (i := 22) (by kernel_rfl)
theorem codeAt_sub_83 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 83)) sub_83 :=
  codeAt_sublayout h.1 subL_ok (i := 23) (by kernel_rfl)
theorem codeAt_sub_92 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 92)) sub_92 :=
  codeAt_sublayout h.1 subL_ok (i := 24) (by kernel_rfl)
theorem codeAt_sub_95 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 95)) sub_95 :=
  codeAt_sublayout h.1 subL_ok (i := 25) (by kernel_rfl)
theorem codeAt_sub_96 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 96)) sub_96 :=
  codeAt_sublayout h.1 subL_ok (i := 26) (by kernel_rfl)
theorem codeAt_sub_105 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 105)) sub_105 :=
  codeAt_sublayout h.1 subL_ok (i := 27) (by kernel_rfl)
theorem codeAt_sub_106 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 106)) sub_106 :=
  codeAt_sublayout h.1 subL_ok (i := 28) (by kernel_rfl)
theorem codeAt_sub_112 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 112)) sub_112 :=
  codeAt_sublayout h.1 subL_ok (i := 29) (by kernel_rfl)
theorem codeAt_sub_113 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 113)) sub_113 :=
  codeAt_sublayout h.1 subL_ok (i := 30) (by kernel_rfl)
theorem codeAt_sub_116 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 116)) sub_116 :=
  codeAt_sublayout h.1 subL_ok (i := 31) (by kernel_rfl)
theorem codeAt_sub_117 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 117)) sub_117 :=
  codeAt_sublayout h.1 subL_ok (i := 32) (by kernel_rfl)
theorem codeAt_sub_118 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 118)) sub_118 :=
  codeAt_sublayout h.1 subL_ok (i := 33) (by kernel_rfl)
theorem codeAt_sub_120 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 120)) sub_120 :=
  codeAt_sublayout h.1 subL_ok (i := 34) (by kernel_rfl)
theorem codeAt_sub_140 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 140)) sub_140 :=
  codeAt_sublayout h.1 subL_ok (i := 35) (by kernel_rfl)
theorem codeAt_sub_146 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 146)) sub_146 :=
  codeAt_sublayout h.1 subL_ok (i := 36) (by kernel_rfl)
theorem codeAt_sub_147 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 147)) sub_147 :=
  codeAt_sublayout h.1 subL_ok (i := 37) (by kernel_rfl)
theorem codeAt_sub_157 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 157)) sub_157 :=
  codeAt_sublayout h.1 subL_ok (i := 38) (by kernel_rfl)
theorem codeAt_sub_159 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 159)) sub_159 :=
  codeAt_sublayout h.1 subL_ok (i := 39) (by kernel_rfl)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 100
sym_block blk_26 := symRun { noAlias := true } seg_26 (pcOf 26) 100
sym_block blk_28 := symRun { noAlias := true } seg_28 (pcOf 28) 100
sym_block blk_34 := symRun { noAlias := true } seg_34 (pcOf 34) 100
sym_block blk_36 := symRun { noAlias := true } seg_36 (pcOf 36) 100
sym_block blk_39 := symRun { noAlias := true } seg_39 (pcOf 39) 100
sym_block blk_48 := symRun { noAlias := true } seg_48 (pcOf 48) 100
sym_block blk_50 := symRun { noAlias := true } seg_50 (pcOf 50) 100
sym_block blk_51 := symRun { noAlias := true } seg_51 (pcOf 51) 100
sym_block blk_52 := symRun { noAlias := true } seg_52 (pcOf 52) 100
sym_block blk_65 := symRun { noAlias := true } seg_65 (pcOf 65) 100
sym_block blk_81 := symRun { noAlias := true } seg_81 (pcOf 81) 100
sym_block blk_84 := symRun { noAlias := true } seg_84 (pcOf 84) 100
sym_block blk_114 := symRun { noAlias := true } seg_114 (pcOf 114) 100
sym_block blk_277 := symRun { noAlias := true } seg_277 (pcOf 277) 100
sym_block blk_289 := symRun { noAlias := true } seg_289 (pcOf 289) 100
sym_block blk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 100
sym_block blk_310 := symRun { noAlias := true } seg_310 (pcOf 310) 100
sym_block blk_330 := symRun { noAlias := true } seg_330 (pcOf 330) 100
sym_block blk117_0 := symRun { noAlias := true } sub_0 (pcOf (117 + 0)) 100
sym_block blk1013_0 := symRun { noAlias := true } sub_0 (pcOf (1013 + 0)) 100
sym_block blk117_1 := symRun { noAlias := true } sub_1 (pcOf (117 + 1)) 100
sym_block blk1013_1 := symRun { noAlias := true } sub_1 (pcOf (1013 + 1)) 100
sym_block blk117_2 := symRun { noAlias := true } sub_2 (pcOf (117 + 2)) 100
sym_block blk1013_2 := symRun { noAlias := true } sub_2 (pcOf (1013 + 2)) 100
sym_block blk117_8 := symRun { noAlias := true } sub_8 (pcOf (117 + 8)) 100
sym_block blk1013_8 := symRun { noAlias := true } sub_8 (pcOf (1013 + 8)) 100
sym_block blk117_9 := symRun { noAlias := true } sub_9 (pcOf (117 + 9)) 100
sym_block blk1013_9 := symRun { noAlias := true } sub_9 (pcOf (1013 + 9)) 100
sym_block blk117_24 := symRun { noAlias := true } sub_24 (pcOf (117 + 24)) 100
sym_block blk1013_24 := symRun { noAlias := true } sub_24 (pcOf (1013 + 24)) 100
sym_block blk117_26 := symRun { noAlias := true } sub_26 (pcOf (117 + 26)) 100
sym_block blk1013_26 := symRun { noAlias := true } sub_26 (pcOf (1013 + 26)) 100
sym_block blk117_27 := symRun { noAlias := true } sub_27 (pcOf (117 + 27)) 100
sym_block blk1013_27 := symRun { noAlias := true } sub_27 (pcOf (1013 + 27)) 100
sym_block blk117_41 := symRun { noAlias := true } sub_41 (pcOf (117 + 41)) 100
sym_block blk1013_41 := symRun { noAlias := true } sub_41 (pcOf (1013 + 41)) 100
sym_block blk117_42 := symRun { noAlias := true } sub_42 (pcOf (117 + 42)) 100
sym_block blk1013_42 := symRun { noAlias := true } sub_42 (pcOf (1013 + 42)) 100
sym_block blk117_44 := symRun { noAlias := true } sub_44 (pcOf (117 + 44)) 100
sym_block blk1013_44 := symRun { noAlias := true } sub_44 (pcOf (1013 + 44)) 100
sym_block blk117_60 := symRun { noAlias := true } sub_60 (pcOf (117 + 60)) 100
sym_block blk1013_60 := symRun { noAlias := true } sub_60 (pcOf (1013 + 60)) 100
sym_block blk117_73 := symRun { noAlias := true } sub_73 (pcOf (117 + 73)) 100
sym_block blk1013_73 := symRun { noAlias := true } sub_73 (pcOf (1013 + 73)) 100
sym_block blk117_75 := symRun { noAlias := true } sub_75 (pcOf (117 + 75)) 100
sym_block blk1013_75 := symRun { noAlias := true } sub_75 (pcOf (1013 + 75)) 100
sym_block blk117_76 := symRun { noAlias := true } sub_76 (pcOf (117 + 76)) 100
sym_block blk1013_76 := symRun { noAlias := true } sub_76 (pcOf (1013 + 76)) 100
sym_block blk117_77 := symRun { noAlias := true } sub_77 (pcOf (117 + 77)) 100
sym_block blk1013_77 := symRun { noAlias := true } sub_77 (pcOf (1013 + 77)) 100
sym_block blk117_78 := symRun { noAlias := true } sub_78 (pcOf (117 + 78)) 100
sym_block blk1013_78 := symRun { noAlias := true } sub_78 (pcOf (1013 + 78)) 100
sym_block blk117_79 := symRun { noAlias := true } sub_79 (pcOf (117 + 79)) 100
sym_block blk1013_79 := symRun { noAlias := true } sub_79 (pcOf (1013 + 79)) 100
sym_block blk117_80 := symRun { noAlias := true } sub_80 (pcOf (117 + 80)) 100
sym_block blk1013_80 := symRun { noAlias := true } sub_80 (pcOf (1013 + 80)) 100
sym_block blk117_82 := symRun { noAlias := true } sub_82 (pcOf (117 + 82)) 100
sym_block blk1013_82 := symRun { noAlias := true } sub_82 (pcOf (1013 + 82)) 100
sym_block blk117_83 := symRun { noAlias := true } sub_83 (pcOf (117 + 83)) 100
sym_block blk1013_83 := symRun { noAlias := true } sub_83 (pcOf (1013 + 83)) 100
sym_block blk117_92 := symRun { noAlias := true } sub_92 (pcOf (117 + 92)) 100
sym_block blk1013_92 := symRun { noAlias := true } sub_92 (pcOf (1013 + 92)) 100
sym_block blk117_95 := symRun { noAlias := true } sub_95 (pcOf (117 + 95)) 100
sym_block blk1013_95 := symRun { noAlias := true } sub_95 (pcOf (1013 + 95)) 100
sym_block blk117_96 := symRun { noAlias := true } sub_96 (pcOf (117 + 96)) 100
sym_block blk1013_96 := symRun { noAlias := true } sub_96 (pcOf (1013 + 96)) 100
sym_block blk117_106 := symRun { noAlias := true } sub_106 (pcOf (117 + 106)) 100
sym_block blk1013_106 := symRun { noAlias := true } sub_106 (pcOf (1013 + 106)) 100
sym_block blk117_112 := symRun { noAlias := true } sub_112 (pcOf (117 + 112)) 100
sym_block blk1013_112 := symRun { noAlias := true } sub_112 (pcOf (1013 + 112)) 100
sym_block blk117_113 := symRun { noAlias := true } sub_113 (pcOf (117 + 113)) 100
sym_block blk1013_113 := symRun { noAlias := true } sub_113 (pcOf (1013 + 113)) 100
sym_block blk117_116 := symRun { noAlias := true } sub_116 (pcOf (117 + 116)) 100
sym_block blk1013_116 := symRun { noAlias := true } sub_116 (pcOf (1013 + 116)) 100
sym_block blk117_117 := symRun { noAlias := true } sub_117 (pcOf (117 + 117)) 100
sym_block blk1013_117 := symRun { noAlias := true } sub_117 (pcOf (1013 + 117)) 100
sym_block blk117_118 := symRun { noAlias := true } sub_118 (pcOf (117 + 118)) 100
sym_block blk1013_118 := symRun { noAlias := true } sub_118 (pcOf (1013 + 118)) 100
sym_block blk117_120 := symRun { noAlias := true } sub_120 (pcOf (117 + 120)) 100
sym_block blk1013_120 := symRun { noAlias := true } sub_120 (pcOf (1013 + 120)) 100
sym_block blk117_140 := symRun { noAlias := true } sub_140 (pcOf (117 + 140)) 100
sym_block blk1013_140 := symRun { noAlias := true } sub_140 (pcOf (1013 + 140)) 100
sym_block blk117_rev := symRun { noAlias := true } revCode (pcOf (117 + 1004)) 100
sym_block blk1013_rev := symRun { noAlias := true } revCode (pcOf (1013 + 1004)) 100
sym_block blk117_147 := symRun { noAlias := true } sub_147 (pcOf (117 + 147)) 100
sym_block blk1013_147 := symRun { noAlias := true } sub_147 (pcOf (1013 + 147)) 100
sym_block blk117_157 := symRun { noAlias := true } sub_157 (pcOf (117 + 157)) 100
sym_block blk1013_157 := symRun { noAlias := true } sub_157 (pcOf (1013 + 157)) 100
sym_block blk117_159 := symRun { noAlias := true } sub_159 (pcOf (117 + 159)) 100
sym_block blk1013_159 := symRun { noAlias := true } sub_159 (pcOf (1013 + 159)) 100
def st_0 : SymState := blk117_0.res.st
def pcE_0 (b : Nat) : E := .c (pcOf (b + 1))
theorem run_0 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_0 (pcOf (b + 0)) 100 =
      some ⟨st_0, pcE_0 b, blk117_0.res.stop, blk117_0.res.steps, blk117_0.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_0.trans (congrArg some (by kernel_rfl))
  · exact blk1013_0.trans (congrArg some (by kernel_rfl))
def st_1 : SymState := blk117_1.res.st
def pcE_1 (b : Nat) : E := rebase blk117_1.res.pc (pcOf (b + 8)) (pcOf (b + 2))
theorem run_1 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_1 (pcOf (b + 1)) 100 =
      some ⟨st_1, pcE_1 b, blk117_1.res.stop, blk117_1.res.steps, blk117_1.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_1.trans (congrArg some (by kernel_rfl))
  · exact blk1013_1.trans (congrArg some (by kernel_rfl))
def st_2 : SymState := blk117_2.res.st
def pcE_2 (b : Nat) : E := .c (pcOf (b + 8))
theorem run_2 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_2 (pcOf (b + 2)) 100 =
      some ⟨st_2, pcE_2 b, blk117_2.res.stop, blk117_2.res.steps, blk117_2.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_2.trans (congrArg some (by kernel_rfl))
  · exact blk1013_2.trans (congrArg some (by kernel_rfl))
def st_8 : SymState := blk117_8.res.st
def pcE_8 (b : Nat) : E := rebase blk117_8.res.pc (pcOf (b + 26)) (pcOf (b + 9))
theorem run_8 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_8 (pcOf (b + 8)) 100 =
      some ⟨st_8, pcE_8 b, blk117_8.res.stop, blk117_8.res.steps, blk117_8.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_8.trans (congrArg some (by kernel_rfl))
  · exact blk1013_8.trans (congrArg some (by kernel_rfl))
def st_9 : SymState := blk117_9.res.st
def pcE_9 (b : Nat) : E := .c (pcOf (b + 470))
theorem run_9 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_9 (pcOf (b + 9)) 100 =
      some ⟨st_9, pcE_9 b, blk117_9.res.stop, blk117_9.res.steps, blk117_9.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_9.trans (congrArg some (by kernel_rfl))
  · exact blk1013_9.trans (congrArg some (by kernel_rfl))
def st_24 : SymState := blk117_24.res.st
def pcE_24 (b : Nat) : E := .c (pcOf (b + 1))
theorem run_24 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_24 (pcOf (b + 24)) 100 =
      some ⟨st_24, pcE_24 b, blk117_24.res.stop, blk117_24.res.steps, blk117_24.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_24.trans (congrArg some (by kernel_rfl))
  · exact blk1013_24.trans (congrArg some (by kernel_rfl))
def st_26 : SymState := blk117_26.res.st
def pcE_26 (b : Nat) : E := blk117_26.res.pc
theorem run_26 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_26 (pcOf (b + 26)) 100 =
      some ⟨st_26, pcE_26 b, blk117_26.res.stop, blk117_26.res.steps, blk117_26.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_26.trans (congrArg some (by kernel_rfl))
  · exact blk1013_26.trans (congrArg some (by kernel_rfl))
def st_27 : SymState := blk117_27.res.st
def pcE_27 (b : Nat) : E := .c (pcOf (b + 41))
theorem run_27 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_27 (pcOf (b + 27)) 100 =
      some ⟨st_27, pcE_27 b, blk117_27.res.stop, blk117_27.res.steps, blk117_27.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_27.trans (congrArg some (by kernel_rfl))
  · exact blk1013_27.trans (congrArg some (by kernel_rfl))
def st_41 : SymState := blk117_41.res.st
def pcE_41 (b : Nat) : E := rebase blk117_41.res.pc (pcOf (b + 95)) (pcOf (b + 42))
theorem run_41 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_41 (pcOf (b + 41)) 100 =
      some ⟨st_41, pcE_41 b, blk117_41.res.stop, blk117_41.res.steps, blk117_41.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_41.trans (congrArg some (by kernel_rfl))
  · exact blk1013_41.trans (congrArg some (by kernel_rfl))
def st_42 : SymState := blk117_42.res.st
def pcE_42 (b : Nat) : E := rebase blk117_42.res.pc (pcOf (b + 60)) (pcOf (b + 44))
theorem run_42 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_42 (pcOf (b + 42)) 100 =
      some ⟨st_42, pcE_42 b, blk117_42.res.stop, blk117_42.res.steps, blk117_42.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_42.trans (congrArg some (by kernel_rfl))
  · exact blk1013_42.trans (congrArg some (by kernel_rfl))
def st_44 : SymState := blk117_44.res.st
def pcE_44 (b : Nat) : E := .c (pcOf (b + 59))
theorem run_44 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_44 (pcOf (b + 44)) 100 =
      some ⟨st_44, pcE_44 b, blk117_44.res.stop, blk117_44.res.steps, blk117_44.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_44.trans (congrArg some (by kernel_rfl))
  · exact blk1013_44.trans (congrArg some (by kernel_rfl))
def st_60 : SymState := blk117_60.res.st
def pcE_60 (b : Nat) : E := .c (pcOf (b + 72))
theorem run_60 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_60 (pcOf (b + 60)) 100 =
      some ⟨st_60, pcE_60 b, blk117_60.res.stop, blk117_60.res.steps, blk117_60.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_60.trans (congrArg some (by kernel_rfl))
  · exact blk1013_60.trans (congrArg some (by kernel_rfl))
def st_73 : SymState := blk117_73.res.st
def pcE_73 (b : Nat) : E := rebase blk117_73.res.pc (pcOf (b + 76)) (pcOf (b + 75))
theorem run_73 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_73 (pcOf (b + 73)) 100 =
      some ⟨st_73, pcE_73 b, blk117_73.res.stop, blk117_73.res.steps, blk117_73.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_73.trans (congrArg some (by kernel_rfl))
  · exact blk1013_73.trans (congrArg some (by kernel_rfl))
def st_75 : SymState := blk117_75.res.st
def pcE_75 (b : Nat) : E := .c (pcOf (b + 1000))
theorem run_75 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_75 (pcOf (b + 75)) 100 =
      some ⟨st_75, pcE_75 b, blk117_75.res.stop, blk117_75.res.steps, blk117_75.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_75.trans (congrArg some (by kernel_rfl))
  · exact blk1013_75.trans (congrArg some (by kernel_rfl))
def st_76 : SymState := blk117_76.res.st
def pcE_76 (b : Nat) : E := rebase blk117_76.res.pc (pcOf (b + 78)) (pcOf (b + 77))
theorem run_76 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_76 (pcOf (b + 76)) 100 =
      some ⟨st_76, pcE_76 b, blk117_76.res.stop, blk117_76.res.steps, blk117_76.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_76.trans (congrArg some (by kernel_rfl))
  · exact blk1013_76.trans (congrArg some (by kernel_rfl))
def st_77 : SymState := blk117_77.res.st
def pcE_77 (b : Nat) : E := .c (pcOf (b + 78))
theorem run_77 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_77 (pcOf (b + 77)) 100 =
      some ⟨st_77, pcE_77 b, blk117_77.res.stop, blk117_77.res.steps, blk117_77.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_77.trans (congrArg some (by kernel_rfl))
  · exact blk1013_77.trans (congrArg some (by kernel_rfl))
def st_78 (b : Nat) : SymState := { blk117_78.res.st with regs := blk117_78.res.st.regs.set Reg.x1 (.c (pcOf (b + 79))) }
def pcE_78 (b : Nat) : E := .c (pcOf (b + 0))
theorem run_78 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_78 (pcOf (b + 78)) 100 =
      some ⟨st_78 b, pcE_78 b, blk117_78.res.stop, blk117_78.res.steps, blk117_78.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_78.trans (congrArg some (by kernel_rfl))
  · exact blk1013_78.trans (congrArg some (by kernel_rfl))
def st_79 : SymState := blk117_79.res.st
def pcE_79 (b : Nat) : E := rebase blk117_79.res.pc (pcOf (b + 92)) (pcOf (b + 80))
theorem run_79 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_79 (pcOf (b + 79)) 100 =
      some ⟨st_79, pcE_79 b, blk117_79.res.stop, blk117_79.res.steps, blk117_79.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_79.trans (congrArg some (by kernel_rfl))
  · exact blk1013_79.trans (congrArg some (by kernel_rfl))
def st_80 : SymState := blk117_80.res.st
def pcE_80 (b : Nat) : E := rebase blk117_80.res.pc (pcOf (b + 83)) (pcOf (b + 82))
theorem run_80 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_80 (pcOf (b + 80)) 100 =
      some ⟨st_80, pcE_80 b, blk117_80.res.stop, blk117_80.res.steps, blk117_80.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_80.trans (congrArg some (by kernel_rfl))
  · exact blk1013_80.trans (congrArg some (by kernel_rfl))
def st_82 : SymState := blk117_82.res.st
def pcE_82 (b : Nat) : E := .c (pcOf (b + 83))
theorem run_82 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_82 (pcOf (b + 82)) 100 =
      some ⟨st_82, pcE_82 b, blk117_82.res.stop, blk117_82.res.steps, blk117_82.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_82.trans (congrArg some (by kernel_rfl))
  · exact blk1013_82.trans (congrArg some (by kernel_rfl))
def st_83 : SymState := blk117_83.res.st
def pcE_83 (b : Nat) : E := .c (pcOf (b + 92))
theorem run_83 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_83 (pcOf (b + 83)) 100 =
      some ⟨st_83, pcE_83 b, blk117_83.res.stop, blk117_83.res.steps, blk117_83.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_83.trans (congrArg some (by kernel_rfl))
  · exact blk1013_83.trans (congrArg some (by kernel_rfl))
def st_92 : SymState := blk117_92.res.st
def pcE_92 (b : Nat) : E := .c (pcOf (b + 41))
theorem run_92 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_92 (pcOf (b + 92)) 100 =
      some ⟨st_92, pcE_92 b, blk117_92.res.stop, blk117_92.res.steps, blk117_92.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_92.trans (congrArg some (by kernel_rfl))
  · exact blk1013_92.trans (congrArg some (by kernel_rfl))
def st_95 : SymState := blk117_95.res.st
def pcE_95 (b : Nat) : E := rebase blk117_95.res.pc (pcOf (b + 112)) (pcOf (b + 96))
theorem run_95 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_95 (pcOf (b + 95)) 100 =
      some ⟨st_95, pcE_95 b, blk117_95.res.stop, blk117_95.res.steps, blk117_95.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_95.trans (congrArg some (by kernel_rfl))
  · exact blk1013_95.trans (congrArg some (by kernel_rfl))
def st_96 : SymState := blk117_96.res.st
def pcE_96 (b : Nat) : E := .c (pcOf (b + 105))
theorem run_96 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_96 (pcOf (b + 96)) 100 =
      some ⟨st_96, pcE_96 b, blk117_96.res.stop, blk117_96.res.steps, blk117_96.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_96.trans (congrArg some (by kernel_rfl))
  · exact blk1013_96.trans (congrArg some (by kernel_rfl))
def st_106 : SymState := blk117_106.res.st
def pcE_106 (b : Nat) : E := .c (pcOf (b + 112))
theorem run_106 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_106 (pcOf (b + 106)) 100 =
      some ⟨st_106, pcE_106 b, blk117_106.res.stop, blk117_106.res.steps, blk117_106.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_106.trans (congrArg some (by kernel_rfl))
  · exact blk1013_106.trans (congrArg some (by kernel_rfl))
def st_112 : SymState := blk117_112.res.st
def pcE_112 (b : Nat) : E := blk117_112.res.pc
theorem run_112 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_112 (pcOf (b + 112)) 100 =
      some ⟨st_112, pcE_112 b, blk117_112.res.stop, blk117_112.res.steps, blk117_112.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_112.trans (congrArg some (by kernel_rfl))
  · exact blk1013_112.trans (congrArg some (by kernel_rfl))
def st_113 : SymState := blk117_113.res.st
def pcE_113 (b : Nat) : E := .c (pcOf (b + 116))
theorem run_113 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_113 (pcOf (b + 113)) 100 =
      some ⟨st_113, pcE_113 b, blk117_113.res.stop, blk117_113.res.steps, blk117_113.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_113.trans (congrArg some (by kernel_rfl))
  · exact blk1013_113.trans (congrArg some (by kernel_rfl))
def st_116 : SymState := blk117_116.res.st
def pcE_116 (b : Nat) : E := rebase blk117_116.res.pc (pcOf (b + 159)) (pcOf (b + 117))
theorem run_116 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_116 (pcOf (b + 116)) 100 =
      some ⟨st_116, pcE_116 b, blk117_116.res.stop, blk117_116.res.steps, blk117_116.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_116.trans (congrArg some (by kernel_rfl))
  · exact blk1013_116.trans (congrArg some (by kernel_rfl))
def st_117 : SymState := blk117_117.res.st
def pcE_117 (b : Nat) : E := .c (pcOf (b + 118))
theorem run_117 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_117 (pcOf (b + 117)) 100 =
      some ⟨st_117, pcE_117 b, blk117_117.res.stop, blk117_117.res.steps, blk117_117.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_117.trans (congrArg some (by kernel_rfl))
  · exact blk1013_117.trans (congrArg some (by kernel_rfl))
def st_118 : SymState := blk117_118.res.st
def pcE_118 (b : Nat) : E := rebase blk117_118.res.pc (pcOf (b + 157)) (pcOf (b + 120))
theorem run_118 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_118 (pcOf (b + 118)) 100 =
      some ⟨st_118, pcE_118 b, blk117_118.res.stop, blk117_118.res.steps, blk117_118.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_118.trans (congrArg some (by kernel_rfl))
  · exact blk1013_118.trans (congrArg some (by kernel_rfl))
def st_120 : SymState := blk117_120.res.st
def pcE_120 (b : Nat) : E := rebase blk117_120.res.pc (pcOf (b + 1004)) (pcOf (b + 140))
theorem run_120 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_120 (pcOf (b + 120)) 100 =
      some ⟨st_120, pcE_120 b, blk117_120.res.stop, blk117_120.res.steps, blk117_120.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_120.trans (congrArg some (by kernel_rfl))
  · exact blk1013_120.trans (congrArg some (by kernel_rfl))
def st_140 : SymState := blk117_140.res.st
def pcE_140 (b : Nat) : E := .c (pcOf (b + 146))
theorem run_140 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_140 (pcOf (b + 140)) 100 =
      some ⟨st_140, pcE_140 b, blk117_140.res.stop, blk117_140.res.steps, blk117_140.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_140.trans (congrArg some (by kernel_rfl))
  · exact blk1013_140.trans (congrArg some (by kernel_rfl))
def st_rev : SymState := blk117_rev.res.st
def pcE_rev (b : Nat) : E := .c (pcOf (b + 140))
theorem run_rev {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } revCode (pcOf (b + 1004)) 100 =
      some ⟨st_rev, pcE_rev b, blk117_rev.res.stop, blk117_rev.res.steps, blk117_rev.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_rev.trans (congrArg some (by kernel_rfl))
  · exact blk1013_rev.trans (congrArg some (by kernel_rfl))
def st_147 : SymState := blk117_147.res.st
def pcE_147 (b : Nat) : E := .c (pcOf (b + 118))
theorem run_147 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_147 (pcOf (b + 147)) 100 =
      some ⟨st_147, pcE_147 b, blk117_147.res.stop, blk117_147.res.steps, blk117_147.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_147.trans (congrArg some (by kernel_rfl))
  · exact blk1013_147.trans (congrArg some (by kernel_rfl))
def st_157 : SymState := blk117_157.res.st
def pcE_157 (b : Nat) : E := .c (pcOf (b + 116))
theorem run_157 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_157 (pcOf (b + 157)) 100 =
      some ⟨st_157, pcE_157 b, blk117_157.res.stop, blk117_157.res.steps, blk117_157.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_157.trans (congrArg some (by kernel_rfl))
  · exact blk1013_157.trans (congrArg some (by kernel_rfl))
def st_159 : SymState := blk117_159.res.st
def pcE_159 (b : Nat) : E := blk117_159.res.pc
theorem run_159 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_159 (pcOf (b + 159)) 100 =
      some ⟨st_159, pcE_159 b, blk117_159.res.stop, blk117_159.res.steps, blk117_159.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_159.trans (congrArg some (by kernel_rfl))
  · exact blk1013_159.trans (congrArg some (by kernel_rfl))
sym_block max117Low := symRun { noAlias := true } maxLow (pcOf (117 + 1000)) 100
sym_block max1013Low := symRun { noAlias := true } maxLow (pcOf (1013 + 1000)) 100
sym_block max117High := symRun { noAlias := true } maxHigh (pcOf (117 + 1002)) 100
sym_block max1013High := symRun { noAlias := true } maxHigh (pcOf (1013 + 1002)) 100
def maxLowState : SymState := max117Low.res.st
def maxLowPC (b : Nat) : E := rebase max117Low.res.pc (pcOf (b + 76)) (pcOf (b + 1002))
theorem run_maxLow {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } maxLow (pcOf (b + 1000)) 100 =
      some ⟨maxLowState, maxLowPC b, max117Low.res.stop, max117Low.res.steps, max117Low.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact max117Low.trans (congrArg some (by kernel_rfl))
  · exact max1013Low.trans (congrArg some (by kernel_rfl))
def maxHighState : SymState := max117High.res.st
def maxHighPC (b : Nat) : E := .c (pcOf (b + 76))
theorem run_maxHigh {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } maxHigh (pcOf (b + 1002)) 100 =
      some ⟨maxHighState, maxHighPC b, max117High.res.stop, max117High.res.steps, max117High.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact max117High.trans (congrArg some (by kernel_rfl))
  · exact max1013High.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Keygen
