import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Search.Blocks

section


namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def expandCodeChunks : List (List (BitVec 32)) := [Images.expandCode_0, Images.expandCode_1, Images.expandCode_2, Images.expandCode_3, Images.expandCode_4, Images.expandCode_5, Images.expandCode_6, Images.expandCode_7, Images.expandCode_8, Images.expandCode_9, Images.expandCode_10, Images.expandCode_11, Images.expandCode_12, Images.expandCode_13, Images.expandCode_14, Images.expandCode_15, Images.expandCode_16, Images.expandCode_17, Images.expandCode_18, Images.expandCode_19, Images.expandCode_20, Images.expandCode_21, Images.expandCode_22, Images.expandCode_23, Images.expandCode_24, Images.expandCode_25, Images.expandCode_26, Images.expandCode_27, Images.expandCode_28, Images.expandCode_29, Images.expandCode_30, Images.expandCode_31, Images.expandCode_32, Images.expandCode_33, Images.expandCode_34, Images.expandCode_35, Images.expandCode_36, Images.expandCode_37, Images.expandCode_38, Images.expandCode_39, Images.expandCode_40, Images.expandCode_41, Images.expandCode_42, Images.expandCode_43, Images.expandCode_44, Images.expandCode_45, Images.expandCode_46, Images.expandCode_47, Images.expandCode_48, Images.expandCode_49, Images.expandCode_50, Images.expandCode_51, Images.expandCode_52, Images.expandCode_53, Images.expandCode_54, Images.expandCode_55, Images.expandCode_56, Images.expandCode_57, Images.expandCode_58, Images.expandCode_59, Images.expandCode_60, Images.expandCode_61, Images.expandCode_62, Images.expandCode_63, Images.expandCode_64, Images.expandCode_65, Images.expandCode_66, Images.expandCode_67, Images.expandCode_68, Images.expandCode_69, Images.expandCode_70, Images.expandCode_71, Images.expandCode_72, Images.expandCode_73, Images.expandCode_74, Images.expandCode_75, Images.expandCode_76, Images.expandCode_77, Images.expandCode_78, Images.expandCode_79, Images.expandCode_80, Images.expandCode_81, Images.expandCode_82, Images.expandCode_83, Images.expandCode_84, Images.expandCode_85, Images.expandCode_86, Images.expandCode_87, Images.expandCode_88, Images.expandCode_89, Images.expandCode_90, Images.expandCode_91, Images.expandCode_92, Images.expandCode_93, Images.expandCode_94, Images.expandCode_95, Images.expandCode_96, Images.expandCode_97, Images.expandCode_98, Images.expandCode_99, Images.expandCode_100, Images.expandCode_101, Images.expandCode_102, Images.expandCode_103, Images.expandCode_104, Images.expandCode_105, Images.expandCode_106, Images.expandCode_107, Images.expandCode_108, Images.expandCode_109, Images.expandCode_110, Images.expandCode_111, Images.expandCode_112, Images.expandCode_113, Images.expandCode_114, Images.expandCode_115, Images.expandCode_116, Images.expandCode_117, Images.expandCode_118, Images.expandCode_119, Images.expandCode_120, Images.expandCode_121, Images.expandCode_122, Images.expandCode_123, Images.expandCode_124, Images.expandCode_125, Images.expandCode_126, Images.expandCode_127, Images.expandCode_128, Images.expandCode_129, Images.expandCode_130, Images.expandCode_131, Images.expandCode_132, Images.expandCode_133, Images.expandCode_134, Images.expandCode_135, Images.expandCode_136, Images.expandCode_137, Images.expandCode_138, Images.expandCode_139, Images.expandCode_140, Images.expandCode_141, Images.expandCode_142, Images.expandCode_143, Images.expandCode_144, Images.expandCode_145, Images.expandCode_146, Images.expandCode_147, Images.expandCode_148, Images.expandCode_149, Images.expandCode_150, Images.expandCode_151, Images.expandCode_152, Images.expandCode_153, Images.expandCode_154, Images.expandCode_155, Images.expandCode_156, Images.expandCode_157, Images.expandCode_158, Images.expandCode_159, Images.expandCode_160, Images.expandCode_161, Images.expandCode_162]
private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
theorem expandCode_flatten : Images.expandCode = expandCodeChunks.flatten := by
  change expandCodeChunks.foldl (· ++ ·) [] = expandCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_expand_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.expandCode.drop b).take code.length = code
  rw [expandCode_flatten]
  exact h
end SigGolfCandidate.T3M
end

section


namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedVariables false
def seg_0 : List (BitVec 32) := [659,32439,7991,0x800f0f13,963331,9352067,7286819,8336419,32439,134967,302976787,963331,9352067,7286819,8336419,67112595,134967,336531219,963331,9352067,7286819,8336419,83889811,134967,353308435,963331,9352067,7286819,8336419,2451]
def seg_49 : List (BitVec 32) := [134711,370019859,930947,34903187,34919571,134711,0x550e0e13,0x9e3023,7735,0x810e0e13,20848675,139575,2323,6967,0xc40b0b13,1043]
def seg_65 : List (BitVec 32) := [7340819,610556515]
def seg_67 : List (BitVec 32) := [2451]
def seg_68 : List (BitVec 32) := [3146515,74045539]
def seg_70 : List (BitVec 32) := [1316627,8849203,20383539,4660755,32439,17731219,31329843,5707411,4658963,0xe686b3,7863,0x860e8e93,30836403,930563,9319299,6729763,7779363,1673619,0xfb1ff06f]
def seg_89 : List (BitVec 32) := [4462355,3415571,29820723,134711,0x4a0e0e13,29820723,472451,7722387,7341331,898629871]
def seg_99 : List (BitVec 32) := [2451]
def seg_100 : List (BitVec 32) := [4195091,376035427]
def seg_102 : List (BitVec 32) := [0x7300313,0x3e695663]
def seg_104 : List (BitVec 32) := [4789907,32311,370019859,29787827,1640723,4462355,3415571,29820723,134711,0x4a0e0e13,29820723,472835,7821075,20405811,1998355,0x60e0263]
def seg_120 : List (BitVec 32) := [134967,537857811,439043,8827779,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,7052819,4955923,32378419,23989811,439043,8827779,7222307,8271907,1805203,0x600006f]
def seg_144 : List (BitVec 32) := [134839,604933779,134967,537857811,963331,9352067,7286819,8336419,134967,588189459,439043,8827779,7286819,8336419,7052819,4955923,32378419,23989811,439043,8827779,40778787,75378723,1805203]
def seg_167 : List (BitVec 32) := [3149331,0x413e0e33,1050259,29791923,1674771,29842995,29787827,4919,0xa0130313,17047315,31679283,0x7610006f]
def seg_179 : List (BitVec 32) := [33857299,31679283,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_190 : List (BitVec 32) := [115]
def seg_191 : List (BitVec 32) := [1673619,0xe91ff06f]
def seg_193 : List (BitVec 32) := [6037011,25062963,30081059,7052819,4955923,32378419,30083891,9112339,4464147,263267]
def seg_203 : List (BitVec 32) := [17698323]
def seg_204 : List (BitVec 32) := [134839,839814803,31329843,134839,604933779,963331,9352067,7221283,8270883,1311763,0xdadff06f]
def seg_215 : List (BitVec 32) := [591507]
def seg_216 : List (BitVec 32) := [0x7300313,40293987]
def seg_218 : List (BitVec 32) := [4627987,32439,370052755,31329843,930563,537073251]
def seg_224 : List (BitVec 32) := [9319171,537072227]
def seg_226 : List (BitVec 32) := [1476243,0xfd5ff06f]
def seg_228 : List (BitVec 32) := [4919,0xb0130313,295827,134711,839781907,7223331,8272931,132407,839189779,0x8000593,132663,973473299]
def seg_240 : List (BitVec 32) := [115]
def seg_241 : List (BitVec 32) := [134839,974032531,134967,638521107,963331,9352067,7286819,8336419]
def seg_249 : List (BitVec 32) := [3146771,6293395,45092115,3475,0xc200893,134711,0x550e0e13,930563,218003,66063891,29620531,6509715,822083823]
def seg_262 : List (BitVec 32) := [7735,0x820e0e13,20848675,34871,772278291,31671,0xa58b8b93,27703,0xf98c0c13,898629871]
def seg_272 : List (BitVec 32) := [2098195,6293395,45092115,3475,0xc300893,134711,0x550e0e13,930563,6509459,66063891,29620531,0xc35493,725614831]
def seg_285 : List (BitVec 32) := [7735,0x81ce0e13,20848675,34871,0xfd080813,27575,0xe18b8b93,23607,898370579,802160879]
def seg_295 : List (BitVec 32) := [1049619,7341971,45092115,3475,0xc300893,134711,0x550e0e13,930563,0xc35393,0x7f00e13,29620531,20141203,629145839]
def seg_308 : List (BitVec 32) := [7735,0x818e0e13,20848675,34871,0xcb080813,23479,495684499,19511,0x718c0c13,705691887]
def seg_318 : List (BitVec 32) := [1043,0xc00793,56626451,53480851,0x7e00893,134711,0x550e0e13,930563,20140947,7735,0xfffe0e13,29620531,32724115,528482543]
def seg_332 : List (BitVec 32) := [7735,0x814e0e13,20848675,34871,0x89080813,19383,0x458b8b93,15415,0x6d8c0c13,605028591]
def seg_342 : List (BitVec 32) := [134711,638455315,0xa000e93,930563,963459,7544419]
def seg_348 : List (BitVec 32) := [9319171,9352067,7542883]
def seg_351 : List (BitVec 32) := [1049235,1299]
def seg_353 : List (BitVec 32) := [115]
def seg_824 : List (BitVec 32) := [0xfd010113,1126435,0xa13423,0xb13823,4462355,3415571,29820723,134711,0x4a0e0e13,29820723,2579]
def seg_835 : List (BitVec 32) := [3808787,0xee0e33,933507,0xaedf33,79627875]
def seg_840 : List (BitVec 32) := [1706515,3149331,0xffca12e3]
def seg_843 : List (BitVec 32) := [0x7300e13,0x85c95ce3]
def seg_845 : List (BitVec 32) := [4791827,32439,370052755,31329843,134967,604966675,930563,9319299,7286819,8336419,1640723,1299,574619759]
def seg_858 : List (BitVec 32) := [0xa051863]
def seg_859 : List (BitVec 32) := [34210403]
def seg_860 : List (BitVec 32) := [6037011,25062963,30081059,7052819,4955923,32378419,30083891,9112339]
def seg_868 : List (BitVec 32) := [2963,2030611,1316627,8849203,21432115,4658963,32311,17698323,29820723,134967,772738835,471811,8860547,7286819,8336419,4919,0x90130313,17047315,31679283,0x52c0006f]
def seg_888 : List (BitVec 32) := [33857299,31679283,134711,739118611,7223331,8272931,132407,738526483,67110291,132663,604374547]
def seg_899 : List (BitVec 32) := [115]
def seg_900 : List (BitVec 32) := [1049875,390070383]
def seg_902 : List (BitVec 32) := [0xfff50513,1414547,0xec1ff0ef]
def seg_905 : List (BitVec 32) := [0xa13c23,134839,604933779,963331,9352067,39923747,40973347,8467715,16856451,0xfff50513,1414547,1410451,0xe8dff0ef]
def seg_918 : List (BitVec 32) := [134967,537857811,33633027,42021763,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,8470019,0xb00693,0x41c686b3,1052179,0xde16b3,16858627,29787827,4919,0xa0130313,17047315,31679283,0x3dc0006f]
def seg_944 : List (BitVec 32) := [33857299,31679283,134711,537792019,7223331,8272931,25247235,34477667]
def seg_952 : List (BitVec 32) := [7052819,4955923,32378419,23989811,33633027,42021763,7222307,8271907,1805203,0x680006f]
def seg_962 : List (BitVec 32) := [33888867]
def seg_963 : List (BitVec 32) := [7052819,4955923,32378419,23989811,134839,604933779,963331,9352067,40778787,75378723,1805203,54526063]
def seg_975 : List (BitVec 32) := [6037011,25062963,17722899,30081059,7052819,4955923,32378419,30083891,9112339,2963,16858627,1997843]
def seg_987 : List (BitVec 32) := [132407,537199891,67110291,132663,604374547]
def seg_992 : List (BitVec 32) := [115]
def seg_993 : List (BitVec 32) := [1049875]
def seg_994 : List (BitVec 32) := [77955,50397459,32871]
def seg_997 : List (BitVec 32) := [295827,34152211,31712179,134711,437128723,8272931,134711,0x600e0e13,8272931,17044243,538141459,7223331,2451]
def seg_1010 : List (BitVec 32) := [0xda9da63]
def seg_1011 : List (BitVec 32) := [4824595,17698355,134967,487526163,930563,9319299,7286819,8336419,930563,9319299,40613923,41663523,0xfc0b8b93,134711,0x420e0e13,20844083]
def seg_1027 : List (BitVec 32) := [936451]
def seg_1028 : List (BitVec 32) := [7342739,267363]
def seg_1030 : List (BitVec 32) := [536871023]
def seg_1031 : List (BitVec 32) := [89805923]
def seg_1032 : List (BitVec 32) := [9016211,21201843,33788691,17047315,31679283,269706003,134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
def seg_1046 : List (BitVec 32) := [115]
def seg_1047 : List (BitVec 32) := [1706515,0xfbdff06f]
def seg_1049 : List (BitVec 32) := [4824595,623715]
def seg_1051 : List (BitVec 32) := [17698323]
def seg_1052 : List (BitVec 32) := [134839,0x600e8e93,31329843,134839,487493267,963331,9352067,7221283,8270883,1673619,0xf31ff06f]
def seg_1063 : List (BitVec 32) := [1901331,4395795,66257683,0xfc037313,132407,0x60050513,198035,132663,604374547]
def seg_1072 : List (BitVec 32) := [115]
def seg_1073 : List (BitVec 32) := [2579,5053971,29887283]
def seg_1076 : List (BitVec 32) := [284841571]
def seg_1077 : List (BitVec 32) := [21585459,1998355,68028515]
def seg_1080 : List (BitVec 32) := [733955,9122691,7090211,8139811,134967,537857811,733955,9122691,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,79691887]
def seg_1099 : List (BitVec 32) := [733955,9122691,40646691,41696291,134839,604933779,134967,537857811,963331,9352067,7286819,8336419,134967,588189459,733955,9122691,7286819,8336419]
def seg_1117 : List (BitVec 32) := [0x41478e33,0xfffe0e13,1050259,29791923,1707539,29974067,29787827,17044243,806576915,426899,33857299,31679283,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_1138 : List (BitVec 32) := [115]
def seg_1139 : List (BitVec 32) := [17500947,0xfc0c0c13,1706515,0xef9ff06f]
def seg_1143 : List (BitVec 32) := [134839,604933779,134967,638521107,963331,9352067,7286819,8336419,32871]
def seg_1152 : List (BitVec 32) := [131895,394474243,0xe35313,7566099,0xd0031663,0xb80ff06f]
def seg_1158 : List (BitVec 32) := [3148435,0xe1b9d0e3]
def seg_1160 : List (BitVec 32) := [4197011,0xdf9ff06f]
def seg_1162 : List (BitVec 32) := [426899,0xff3ff13,9379603,8639379,31712179,7735,0xf0fe0e13,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,0x555e0e13,29622067,2039571,1299347,29619123,31712179,50566035,0x838ff06f]
def seg_1190 : List (BitVec 32) := [426899,0xff3ff13,9379603,8639379,31712179,7735,0xf0fe0e13,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,0x555e0e13,29622067,2039571,1299347,29619123,31712179,50566035,0xbbdff06f]
def seg_1218 : List (BitVec 32) := [0x400e8393,0x40038393,0xff3ff13,9379603,8639379,31712179,7735,0xf0fe0e13,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,0x555e0e13,29622067,2039571,1299347,29619123,31712179,50566035,0xa69ff06f]
def expL : Rv.Layout := [(0, seg_0), (30, layoutCode (Search.dsL 30)), (49, seg_49), (65, seg_65), (67, seg_67), (68, seg_68), (70, seg_70), (89, seg_89), (99, seg_99), (100, seg_100), (102, seg_102), (104, seg_104), (120, seg_120), (144, seg_144), (167, seg_167), (179, seg_179), (190, seg_190), (191, seg_191), (193, seg_193), (203, seg_203), (204, seg_204), (215, seg_215), (216, seg_216), (218, seg_218), (224, seg_224), (226, seg_226), (228, seg_228), (240, seg_240), (241, seg_241), (249, seg_249), (262, seg_262), (272, seg_272), (285, seg_285), (295, seg_295), (308, seg_308), (318, seg_318), (332, seg_332), (342, seg_342), (348, seg_348), (351, seg_351), (353, seg_353), (354, Search.kernCode), (824, seg_824), (835, seg_835), (840, seg_840), (843, seg_843), (845, seg_845), (858, seg_858), (859, seg_859), (860, seg_860), (868, seg_868), (888, seg_888), (899, seg_899), (900, seg_900), (902, seg_902), (905, seg_905), (918, seg_918), (944, seg_944), (952, seg_952), (962, seg_962), (963, seg_963), (975, seg_975), (987, seg_987), (992, seg_992), (993, seg_993), (994, seg_994), (997, seg_997), (1010, seg_1010), (1011, seg_1011), (1027, seg_1027), (1028, seg_1028), (1030, seg_1030), (1031, seg_1031), (1032, seg_1032), (1046, seg_1046), (1047, seg_1047), (1049, seg_1049), (1051, seg_1051), (1052, seg_1052), (1063, seg_1063), (1072, seg_1072), (1073, seg_1073), (1076, seg_1076), (1077, seg_1077), (1080, seg_1080), (1099, seg_1099), (1117, seg_1117), (1138, seg_1138), (1139, seg_1139), (1143, seg_1143), (1152, seg_1152), (1158, seg_1158), (1160, seg_1160), (1162, seg_1162), (1190, seg_1190), (1218, seg_1218)]
theorem expL_ok : layoutOk 0 expL = true := by decide +kernel
abbrev image : Image := Images.expandImage
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_49 : CodeAt image (pcOf 49) seg_49 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_65 : CodeAt image (pcOf 65) seg_65 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_67 : CodeAt image (pcOf 67) seg_67 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_68 : CodeAt image (pcOf 68) seg_68 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_70 : CodeAt image (pcOf 70) seg_70 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_89 : CodeAt image (pcOf 89) seg_89 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_99 : CodeAt image (pcOf 99) seg_99 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_100 : CodeAt image (pcOf 100) seg_100 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_102 : CodeAt image (pcOf 102) seg_102 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_104 : CodeAt image (pcOf 104) seg_104 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_120 : CodeAt image (pcOf 120) seg_120 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_144 : CodeAt image (pcOf 144) seg_144 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_167 : CodeAt image (pcOf 167) seg_167 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_179 : CodeAt image (pcOf 179) seg_179 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_190 : CodeAt image (pcOf 190) seg_190 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_191 : CodeAt image (pcOf 191) seg_191 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_193 : CodeAt image (pcOf 193) seg_193 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_203 : CodeAt image (pcOf 203) seg_203 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_204 : CodeAt image (pcOf 204) seg_204 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_215 : CodeAt image (pcOf 215) seg_215 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_216 : CodeAt image (pcOf 216) seg_216 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_218 : CodeAt image (pcOf 218) seg_218 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_224 : CodeAt image (pcOf 224) seg_224 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_226 : CodeAt image (pcOf 226) seg_226 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_228 : CodeAt image (pcOf 228) seg_228 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_240 : CodeAt image (pcOf 240) seg_240 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_241 : CodeAt image (pcOf 241) seg_241 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_249 : CodeAt image (pcOf 249) seg_249 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_262 : CodeAt image (pcOf 262) seg_262 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_272 : CodeAt image (pcOf 272) seg_272 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_285 : CodeAt image (pcOf 285) seg_285 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_308 : CodeAt image (pcOf 308) seg_308 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_318 : CodeAt image (pcOf 318) seg_318 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_332 : CodeAt image (pcOf 332) seg_332 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_342 : CodeAt image (pcOf 342) seg_342 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_348 : CodeAt image (pcOf 348) seg_348 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_351 : CodeAt image (pcOf 351) seg_351 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_353 : CodeAt image (pcOf 353) seg_353 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_824 : CodeAt image (pcOf 824) seg_824 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_835 : CodeAt image (pcOf 835) seg_835 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_840 : CodeAt image (pcOf 840) seg_840 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_843 : CodeAt image (pcOf 843) seg_843 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_845 : CodeAt image (pcOf 845) seg_845 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_858 : CodeAt image (pcOf 858) seg_858 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_859 : CodeAt image (pcOf 859) seg_859 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_860 : CodeAt image (pcOf 860) seg_860 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_868 : CodeAt image (pcOf 868) seg_868 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_888 : CodeAt image (pcOf 888) seg_888 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_899 : CodeAt image (pcOf 899) seg_899 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_900 : CodeAt image (pcOf 900) seg_900 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_902 : CodeAt image (pcOf 902) seg_902 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_905 : CodeAt image (pcOf 905) seg_905 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_918 : CodeAt image (pcOf 918) seg_918 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_944 : CodeAt image (pcOf 944) seg_944 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_952 : CodeAt image (pcOf 952) seg_952 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_962 : CodeAt image (pcOf 962) seg_962 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_963 : CodeAt image (pcOf 963) seg_963 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_975 : CodeAt image (pcOf 975) seg_975 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_987 : CodeAt image (pcOf 987) seg_987 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_992 : CodeAt image (pcOf 992) seg_992 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_993 : CodeAt image (pcOf 993) seg_993 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_994 : CodeAt image (pcOf 994) seg_994 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_997 : CodeAt image (pcOf 997) seg_997 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1010 : CodeAt image (pcOf 1010) seg_1010 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1011 : CodeAt image (pcOf 1011) seg_1011 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1027 : CodeAt image (pcOf 1027) seg_1027 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1028 : CodeAt image (pcOf 1028) seg_1028 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1030 : CodeAt image (pcOf 1030) seg_1030 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1031 : CodeAt image (pcOf 1031) seg_1031 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1032 : CodeAt image (pcOf 1032) seg_1032 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1046 : CodeAt image (pcOf 1046) seg_1046 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1047 : CodeAt image (pcOf 1047) seg_1047 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1049 : CodeAt image (pcOf 1049) seg_1049 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1051 : CodeAt image (pcOf 1051) seg_1051 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1052 : CodeAt image (pcOf 1052) seg_1052 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1063 : CodeAt image (pcOf 1063) seg_1063 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1072 : CodeAt image (pcOf 1072) seg_1072 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1073 : CodeAt image (pcOf 1073) seg_1073 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1076 : CodeAt image (pcOf 1076) seg_1076 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1077 : CodeAt image (pcOf 1077) seg_1077 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1080 : CodeAt image (pcOf 1080) seg_1080 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1099 : CodeAt image (pcOf 1099) seg_1099 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1117 : CodeAt image (pcOf 1117) seg_1117 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1138 : CodeAt image (pcOf 1138) seg_1138 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1139 : CodeAt image (pcOf 1139) seg_1139 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1143 : CodeAt image (pcOf 1143) seg_1143 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1158 : CodeAt image (pcOf 1158) seg_1158 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1160 : CodeAt image (pcOf 1160) seg_1160 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1162 : CodeAt image (pcOf 1162) seg_1162 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1190 : CodeAt image (pcOf 1190) seg_1190 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1218 : CodeAt image (pcOf 1218) seg_1218 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eblk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 200
sym_block eblk_49 := symRun { noAlias := true } seg_49 (pcOf 49) 200
sym_block eblk_65 := symRun { noAlias := true } seg_65 (pcOf 65) 200
sym_block eblk_67 := symRun { noAlias := true } seg_67 (pcOf 67) 200
sym_block eblk_68 := symRun { noAlias := true } seg_68 (pcOf 68) 200
sym_block eblk_70 := symRun { noAlias := true } seg_70 (pcOf 70) 200
sym_block eblk_89 := symRun { noAlias := true } seg_89 (pcOf 89) 200
sym_block eblk_99 := symRun { noAlias := true } seg_99 (pcOf 99) 200
sym_block eblk_100 := symRun { noAlias := true } seg_100 (pcOf 100) 200
sym_block eblk_102 := symRun { noAlias := true } seg_102 (pcOf 102) 200
sym_block eblk_104 := symRun { noAlias := true } seg_104 (pcOf 104) 200
sym_block eblk_120 := symRun { noAlias := true } seg_120 (pcOf 120) 200
sym_block eblk_144 := symRun { noAlias := true } seg_144 (pcOf 144) 200
sym_block eblk_167 := symRun { noAlias := true } seg_167 (pcOf 167) 200
sym_block eblk_179 := symRun { noAlias := true } seg_179 (pcOf 179) 200
sym_block eblk_191 := symRun { noAlias := true } seg_191 (pcOf 191) 200
sym_block eblk_193 := symRun { noAlias := true } seg_193 (pcOf 193) 200
sym_block eblk_203 := symRun { noAlias := true } seg_203 (pcOf 203) 200
sym_block eblk_204 := symRun { noAlias := true } seg_204 (pcOf 204) 200
sym_block eblk_215 := symRun { noAlias := true } seg_215 (pcOf 215) 200
sym_block eblk_216 := symRun { noAlias := true } seg_216 (pcOf 216) 200
sym_block eblk_218 := symRun { noAlias := true } seg_218 (pcOf 218) 200
sym_block eblk_224 := symRun { noAlias := true } seg_224 (pcOf 224) 200
sym_block eblk_226 := symRun { noAlias := true } seg_226 (pcOf 226) 200
sym_block eblk_228 := symRun { noAlias := true } seg_228 (pcOf 228) 200
sym_block eblk_241 := symRun { noAlias := true } seg_241 (pcOf 241) 200
sym_block eblk_249 := symRun { noAlias := true } seg_249 (pcOf 249) 200
sym_block eblk_262 := symRun { noAlias := true } seg_262 (pcOf 262) 200
sym_block eblk_272 := symRun { noAlias := true } seg_272 (pcOf 272) 200
sym_block eblk_285 := symRun { noAlias := true } seg_285 (pcOf 285) 200
sym_block eblk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 200
sym_block eblk_308 := symRun { noAlias := true } seg_308 (pcOf 308) 200
sym_block eblk_318 := symRun { noAlias := true } seg_318 (pcOf 318) 200
sym_block eblk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 200
sym_block eblk_342 := symRun { noAlias := true } seg_342 (pcOf 342) 200
sym_block eblk_348 := symRun { noAlias := true } seg_348 (pcOf 348) 200
sym_block eblk_351 := symRun { noAlias := true } seg_351 (pcOf 351) 200
sym_block eblk_824 := symRun { noAlias := true } seg_824 (pcOf 824) 200
sym_block eblk_835 := symRun { noAlias := true } seg_835 (pcOf 835) 200
sym_block eblk_840 := symRun { noAlias := true } seg_840 (pcOf 840) 200
sym_block eblk_843 := symRun { noAlias := true } seg_843 (pcOf 843) 200
sym_block eblk_845 := symRun { noAlias := true } seg_845 (pcOf 845) 200
sym_block eblk_858 := symRun { noAlias := true } seg_858 (pcOf 858) 200
sym_block eblk_859 := symRun { noAlias := true } seg_859 (pcOf 859) 200
sym_block eblk_860 := symRun { noAlias := true } seg_860 (pcOf 860) 200
sym_block eblk_868 := symRun { noAlias := true } seg_868 (pcOf 868) 200
sym_block eblk_888 := symRun { noAlias := true } seg_888 (pcOf 888) 200
sym_block eblk_900 := symRun { noAlias := true } seg_900 (pcOf 900) 200
sym_block eblk_902 := symRun { noAlias := true } seg_902 (pcOf 902) 200
sym_block eblk_905 := symRun { noAlias := true } seg_905 (pcOf 905) 200
sym_block eblk_918 := symRun { noAlias := true } seg_918 (pcOf 918) 200
sym_block eblk_944 := symRun { noAlias := true } seg_944 (pcOf 944) 200
sym_block eblk_952 := symRun { noAlias := true } seg_952 (pcOf 952) 200
sym_block eblk_962 := symRun { noAlias := true } seg_962 (pcOf 962) 200
sym_block eblk_963 := symRun { noAlias := true } seg_963 (pcOf 963) 200
sym_block eblk_975 := symRun { noAlias := true } seg_975 (pcOf 975) 200
sym_block eblk_987 := symRun { noAlias := true } seg_987 (pcOf 987) 200
sym_block eblk_993 := symRun { noAlias := true } seg_993 (pcOf 993) 200
sym_block eblk_994 := symRun { noAlias := true } seg_994 (pcOf 994) 200
sym_block eblk_997 := symRun { noAlias := true } seg_997 (pcOf 997) 200
sym_block eblk_1010 := symRun { noAlias := true } seg_1010 (pcOf 1010) 200
sym_block eblk_1011 := symRun { noAlias := true } seg_1011 (pcOf 1011) 200
sym_block eblk_1027 := symRun { noAlias := true } seg_1027 (pcOf 1027) 200
sym_block eblk_1028 := symRun { noAlias := true } seg_1028 (pcOf 1028) 200
sym_block eblk_1030 := symRun { noAlias := true } seg_1030 (pcOf 1030) 200
sym_block eblk_1031 := symRun { noAlias := true } seg_1031 (pcOf 1031) 200
sym_block eblk_1032 := symRun { noAlias := true } seg_1032 (pcOf 1032) 200
sym_block eblk_1047 := symRun { noAlias := true } seg_1047 (pcOf 1047) 200
sym_block eblk_1049 := symRun { noAlias := true } seg_1049 (pcOf 1049) 200
sym_block eblk_1051 := symRun { noAlias := true } seg_1051 (pcOf 1051) 200
sym_block eblk_1052 := symRun { noAlias := true } seg_1052 (pcOf 1052) 200
sym_block eblk_1063 := symRun { noAlias := true } seg_1063 (pcOf 1063) 200
sym_block eblk_1073 := symRun { noAlias := true } seg_1073 (pcOf 1073) 200
sym_block eblk_1076 := symRun { noAlias := true } seg_1076 (pcOf 1076) 200
sym_block eblk_1077 := symRun { noAlias := true } seg_1077 (pcOf 1077) 200
sym_block eblk_1080 := symRun { noAlias := true } seg_1080 (pcOf 1080) 200
sym_block eblk_1099 := symRun { noAlias := true } seg_1099 (pcOf 1099) 200
sym_block eblk_1117 := symRun { noAlias := true } seg_1117 (pcOf 1117) 200
sym_block eblk_1139 := symRun { noAlias := true } seg_1139 (pcOf 1139) 200
sym_block eblk_1143 := symRun { noAlias := true } seg_1143 (pcOf 1143) 200
sym_block eblk_1158 := symRun { noAlias := true } seg_1158 (pcOf 1158) 200
sym_block eblk_1160 := symRun { noAlias := true } seg_1160 (pcOf 1160) 200
sym_block eblk_1162 := symRun { noAlias := true } seg_1162 (pcOf 1162) 200
sym_block eblk_1190 := symRun { noAlias := true } seg_1190 (pcOf 1190) 200
sym_block eblk_1218 := symRun { noAlias := true } seg_1218 (pcOf 1218) 200
end SigGolfCandidate.T3M.Expand
end
