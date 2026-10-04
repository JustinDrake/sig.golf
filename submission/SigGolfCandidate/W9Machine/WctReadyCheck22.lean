import SigGolfCandidate.W9Machine.WctRoutineCheck21
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine704 : ChainRoutine :=
  ⟨704, [3, 0, 2, 0, 1, 0, 0], [piece241908, piece241914, piece241916, piece241918, piece235870, piece235876, piece235878, piece235882, piece235275, piece2726, piece2732, piece2736, piece1585, piece966]⟩
def routine705 : ChainRoutine :=
  ⟨705, [3, 0, 2, 1, 0, 0, 0], [piece241919, piece241925, piece241927, piece241929, piece235894, piece235900, piece235903, piece235296, piece235302, piece235306, piece3101, piece1585, piece966]⟩
def routine706 : ChainRoutine :=
  ⟨706, [3, 0, 3, 0, 0, 0, 0], [piece241930, piece241936, piece241938, piece241940, piece235915, piece235921, piece235923, piece235925, piece235929, piece3101, piece1585, piece966]⟩
def routine707 : ChainRoutine :=
  ⟨707, [3, 1, 0, 0, 0, 0, 2], [piece241941, piece241947, piece241949, piece241951, piece241957, piece241961, piece239386, piece4391, piece2078, piece1120, piece805, piece811, piece814]⟩
def routine708 : ChainRoutine :=
  ⟨708, [3, 1, 0, 0, 0, 1, 1], [piece241962, piece241968, piece241970, piece241972, piece241978, piece241982, piece239407, piece4412, piece2099, piece1138, piece1144, piece875, piece881]⟩
def routine709 : ChainRoutine :=
  ⟨709, [3, 1, 0, 0, 0, 2, 0], [piece241983, piece241989, piece241991, piece241993, piece241999, piece242003, piece239428, piece4433, piece2120, piece1162, piece1168, piece1170, piece1174, piece966]⟩
def routine710 : ChainRoutine :=
  ⟨710, [3, 1, 0, 0, 1, 0, 1], [piece242004, piece242010, piece242012, piece242014, piece242020, piece242024, piece239449, piece4454, piece2138, piece2144, piece2148, piece1365, piece875, piece881]⟩
def routine711 : ChainRoutine :=
  ⟨711, [3, 1, 0, 0, 1, 1, 0], [piece242025, piece242031, piece242033, piece242035, piece242041, piece242045, piece239470, piece4475, piece2166, piece2172, piece1386, piece1392, piece1396, piece966]⟩
def routine712 : ChainRoutine :=
  ⟨712, [3, 1, 0, 0, 2, 0, 0], [piece242046, piece242052, piece242054, piece242056, piece242062, piece242066, piece239491, piece4496, piece2190, piece2196, piece2198, piece2202, piece1585, piece966]⟩
def routine713 : ChainRoutine :=
  ⟨713, [3, 1, 0, 1, 0, 0, 1], [piece242067, piece242073, piece242075, piece242077, piece242083, piece242087, piece239512, piece4514, piece4520, piece4524, piece2681, piece1365, piece875, piece881]⟩
def routine714 : ChainRoutine :=
  ⟨714, [3, 1, 0, 1, 0, 1, 0], [piece242088, piece242094, piece242096, piece242098, piece242104, piece242108, piece242114, piece242118, piece242124, piece242128, piece966]⟩
def routine715 : ChainRoutine :=
  ⟨715, [3, 1, 0, 1, 1, 0, 0], [piece242129, piece242135, piece242137, piece242139, piece242145, piece242149, piece239574, piece4570, piece4576, piece2726, piece2732, piece2736, piece1585, piece966]⟩
def routine716 : ChainRoutine :=
  ⟨716, [3, 1, 0, 2, 0, 0, 0], [piece242150, piece242156, piece242158, piece242160, piece242166, piece242170, piece239595, piece4594, piece4600, piece4602, piece4606, piece3101, piece1585, piece966]⟩
def routine717 : ChainRoutine :=
  ⟨717, [3, 1, 1, 0, 0, 0, 1], [piece242171, piece242177, piece242179, piece242181, piece242187, piece239613, piece239619, piece239623, piece235227, piece2681, piece1365, piece875, piece881]⟩
def routine718 : ChainRoutine :=
  ⟨718, [3, 1, 1, 0, 0, 1, 0], [piece242188, piece242194, piece242196, piece242198, piece242204, piece239641, piece239647, piece239651, piece235251, piece2705, piece1386, piece1392, piece1396, piece966]⟩
def routine719 : ChainRoutine :=
  ⟨719, [3, 1, 1, 0, 1, 0, 0], [piece242205, piece242211, piece242213, piece242215, piece242221, piece239669, piece239675, piece239679, piece235275, piece2726, piece2732, piece2736, piece1585, piece966]⟩
def routine720 : ChainRoutine :=
  ⟨720, [3, 1, 1, 1, 0, 0, 0], [piece242222, piece242228, piece242230, piece242232, piece242238, piece239697, piece239703, piece235296, piece235302, piece235306, piece3101, piece1585, piece966]⟩
def routine721 : ChainRoutine :=
  ⟨721, [3, 1, 2, 0, 0, 0, 0], [piece242239, piece242245, piece242247, piece242249, piece242255, piece239721, piece239727, piece239729, piece239733, piece235929, piece3101, piece1585, piece966]⟩
def routine722 : ChainRoutine :=
  ⟨722, [3, 2, 0, 0, 0, 0, 1], [piece242256, piece242262, piece242264, piece242266, piece242272, piece242274, piece242278, piece241456, piece235227, piece2681, piece1365, piece875, piece881]⟩
def routine723 : ChainRoutine :=
  ⟨723, [3, 2, 0, 0, 0, 1, 0], [piece242279, piece242285, piece242287, piece242289, piece242295, piece242297, piece242301, piece241479, piece235251, piece2705, piece1386, piece1392, piece1396, piece966]⟩
def routine724 : ChainRoutine :=
  ⟨724, [3, 2, 0, 0, 1, 0, 0], [piece242302, piece242308, piece242310, piece242312, piece242318, piece242320, piece242324, piece241502, piece235275, piece2726, piece2732, piece2736, piece1585, piece966]⟩
def routine725 : ChainRoutine :=
  ⟨725, [3, 2, 0, 1, 0, 0, 0], [piece242325, piece242331, piece242333, piece242335, piece242341, piece242343, piece242347, piece241525, piece235296, piece235302, piece235306, piece3101, piece1585, piece966]⟩
def routine726 : ChainRoutine :=
  ⟨726, [3, 2, 1, 0, 0, 0, 0], [piece242348, piece242354, piece242356, piece242358, piece242364, piece242367, piece241545, piece241551, piece241555, piece235929, piece3101, piece1585, piece966]⟩
def routine727 : ChainRoutine :=
  ⟨727, [3, 3, 0, 0, 0, 0, 0], [piece242368, piece242374, piece242376, piece242378, piece242384, piece242386, piece242388, piece242392, piece235929, piece3101, piece1585, piece966]⟩
def routineBatch22 : List ChainRoutine := [routine704, routine705, routine706, routine707, routine708, routine709, routine710, routine711, routine712, routine713, routine714, routine715, routine716, routine717, routine718, routine719, routine720, routine721, routine722, routine723, routine724, routine725, routine726, routine727]
theorem routineBatch22_checked :
    (routineBatch22.all ChainRoutine.checked) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch22_checked :
    (routineBatch22.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch22_checked :
    (routineBatch22.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine704_ready : RoutineReady ⟨704, by decide⟩ routine704 := by
  wct_ready_start 704 22 0
  wct_cases [241908,241914,241916,241918,235870,235876,235878,235882,235275,2726,2732,2736,1585,966]
  · wct_piece 48 241908 3
  · wct_piece 48 241914 4
  · wct_piece 48 241916 5
  · wct_piece 48 241918 6
  · wct_piece 23 235870 30
  · wct_piece 23 235876 31
  · wct_piece 23 235878 32
  · wct_piece 23 235882 33
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine705_ready : RoutineReady ⟨705, by decide⟩ routine705 := by
  wct_ready_start 705 22 1
  wct_cases [241919,241925,241927,241929,235894,235900,235903,235296,235302,235306,3101,1585,966]
  · wct_piece 48 241919 7
  · wct_piece 48 241925 8
  · wct_piece 48 241927 9
  · wct_piece 48 241929 10
  · wct_piece 23 235894 37
  · wct_piece 23 235900 38
  · wct_piece 23 235903 39
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine706_ready : RoutineReady ⟨706, by decide⟩ routine706 := by
  wct_ready_start 706 22 2
  wct_cases [241930,241936,241938,241940,235915,235921,235923,235925,235929,3101,1585,966]
  · wct_piece 48 241930 11
  · wct_piece 48 241936 12
  · wct_piece 48 241938 13
  · wct_piece 48 241940 14
  · wct_piece 23 235915 43
  · wct_piece 23 235921 44
  · wct_piece 23 235923 45
  · wct_piece 23 235925 46
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine707_ready : RoutineReady ⟨707, by decide⟩ routine707 := by
  wct_ready_start 707 22 3
  wct_cases [241941,241947,241949,241951,241957,241961,239386,4391,2078,1120,805,811,814]
  · wct_piece 48 241941 15
  · wct_piece 48 241947 16
  · wct_piece 48 241949 17
  · wct_piece 48 241951 18
  · wct_piece 48 241957 19
  · wct_piece 48 241961 20
  · wct_piece 36 239386 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine708_ready : RoutineReady ⟨708, by decide⟩ routine708 := by
  wct_ready_start 708 22 4
  wct_cases [241962,241968,241970,241972,241978,241982,239407,4412,2099,1138,1144,875,881]
  · wct_piece 48 241962 21
  · wct_piece 48 241968 22
  · wct_piece 48 241970 23
  · wct_piece 48 241972 24
  · wct_piece 48 241978 25
  · wct_piece 48 241982 26
  · wct_piece 36 239407 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine709_ready : RoutineReady ⟨709, by decide⟩ routine709 := by
  wct_ready_start 709 22 5
  wct_cases [241983,241989,241991,241993,241999,242003,239428,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 48 241983 27
  · wct_piece 48 241989 28
  · wct_piece 48 241991 29
  · wct_piece 48 241993 30
  · wct_piece 48 241999 31
  · wct_piece 48 242003 32
  · wct_piece 36 239428 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine710_ready : RoutineReady ⟨710, by decide⟩ routine710 := by
  wct_ready_start 710 22 6
  wct_cases [242004,242010,242012,242014,242020,242024,239449,4454,2138,2144,2148,1365,875,881]
  · wct_piece 48 242004 33
  · wct_piece 48 242010 34
  · wct_piece 48 242012 35
  · wct_piece 48 242014 36
  · wct_piece 48 242020 37
  · wct_piece 48 242024 38
  · wct_piece 36 239449 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine711_ready : RoutineReady ⟨711, by decide⟩ routine711 := by
  wct_ready_start 711 22 7
  wct_cases [242025,242031,242033,242035,242041,242045,239470,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 48 242025 39
  · wct_piece 48 242031 40
  · wct_piece 48 242033 41
  · wct_piece 48 242035 42
  · wct_piece 48 242041 43
  · wct_piece 48 242045 44
  · wct_piece 36 239470 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine712_ready : RoutineReady ⟨712, by decide⟩ routine712 := by
  wct_ready_start 712 22 8
  wct_cases [242046,242052,242054,242056,242062,242066,239491,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 48 242046 45
  · wct_piece 48 242052 46
  · wct_piece 48 242054 47
  · wct_piece 48 242056 48
  · wct_piece 48 242062 49
  · wct_piece 48 242066 50
  · wct_piece 36 239491 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine713_ready : RoutineReady ⟨713, by decide⟩ routine713 := by
  wct_ready_start 713 22 9
  wct_cases [242067,242073,242075,242077,242083,242087,239512,4514,4520,4524,2681,1365,875,881]
  · wct_piece 48 242067 51
  · wct_piece 48 242073 52
  · wct_piece 48 242075 53
  · wct_piece 48 242077 54
  · wct_piece 48 242083 55
  · wct_piece 48 242087 56
  · wct_piece 37 239512 3
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine714_ready : RoutineReady ⟨714, by decide⟩ routine714 := by
  wct_ready_start 714 22 10
  wct_cases [242088,242094,242096,242098,242104,242108,242114,242118,242124,242128,966]
  · wct_piece 48 242088 57
  · wct_piece 48 242094 58
  · wct_piece 48 242096 59
  · wct_piece 48 242098 60
  · wct_piece 48 242104 61
  · wct_piece 48 242108 62
  · wct_piece 48 242114 63
  · wct_piece 49 242118 0
  · wct_piece 49 242124 1
  · wct_piece 49 242128 2
  · wct_piece 0 966 57
theorem routine715_ready : RoutineReady ⟨715, by decide⟩ routine715 := by
  wct_ready_start 715 22 11
  wct_cases [242129,242135,242137,242139,242145,242149,239574,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 49 242129 3
  · wct_piece 49 242135 4
  · wct_piece 49 242137 5
  · wct_piece 49 242139 6
  · wct_piece 49 242145 7
  · wct_piece 49 242149 8
  · wct_piece 37 239574 19
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine716_ready : RoutineReady ⟨716, by decide⟩ routine716 := by
  wct_ready_start 716 22 12
  wct_cases [242150,242156,242158,242160,242166,242170,239595,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 49 242150 9
  · wct_piece 49 242156 10
  · wct_piece 49 242158 11
  · wct_piece 49 242160 12
  · wct_piece 49 242166 13
  · wct_piece 49 242170 14
  · wct_piece 37 239595 25
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine717_ready : RoutineReady ⟨717, by decide⟩ routine717 := by
  wct_ready_start 717 22 13
  wct_cases [242171,242177,242179,242181,242187,239613,239619,239623,235227,2681,1365,875,881]
  · wct_piece 49 242171 15
  · wct_piece 49 242177 16
  · wct_piece 49 242179 17
  · wct_piece 49 242181 18
  · wct_piece 49 242187 19
  · wct_piece 37 239613 30
  · wct_piece 37 239619 31
  · wct_piece 37 239623 32
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine718_ready : RoutineReady ⟨718, by decide⟩ routine718 := by
  wct_ready_start 718 22 14
  wct_cases [242188,242194,242196,242198,242204,239641,239647,239651,235251,2705,1386,1392,1396,966]
  · wct_piece 49 242188 20
  · wct_piece 49 242194 21
  · wct_piece 49 242196 22
  · wct_piece 49 242198 23
  · wct_piece 49 242204 24
  · wct_piece 37 239641 37
  · wct_piece 37 239647 38
  · wct_piece 37 239651 39
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine719_ready : RoutineReady ⟨719, by decide⟩ routine719 := by
  wct_ready_start 719 22 15
  wct_cases [242205,242211,242213,242215,242221,239669,239675,239679,235275,2726,2732,2736,1585,966]
  · wct_piece 49 242205 25
  · wct_piece 49 242211 26
  · wct_piece 49 242213 27
  · wct_piece 49 242215 28
  · wct_piece 49 242221 29
  · wct_piece 37 239669 44
  · wct_piece 37 239675 45
  · wct_piece 37 239679 46
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine720_ready : RoutineReady ⟨720, by decide⟩ routine720 := by
  wct_ready_start 720 22 16
  wct_cases [242222,242228,242230,242232,242238,239697,239703,235296,235302,235306,3101,1585,966]
  · wct_piece 49 242222 30
  · wct_piece 49 242228 31
  · wct_piece 49 242230 32
  · wct_piece 49 242232 33
  · wct_piece 49 242238 34
  · wct_piece 37 239697 51
  · wct_piece 37 239703 52
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine721_ready : RoutineReady ⟨721, by decide⟩ routine721 := by
  wct_ready_start 721 22 17
  wct_cases [242239,242245,242247,242249,242255,239721,239727,239729,239733,235929,3101,1585,966]
  · wct_piece 49 242239 35
  · wct_piece 49 242245 36
  · wct_piece 49 242247 37
  · wct_piece 49 242249 38
  · wct_piece 49 242255 39
  · wct_piece 37 239721 57
  · wct_piece 37 239727 58
  · wct_piece 37 239729 59
  · wct_piece 37 239733 60
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine722_ready : RoutineReady ⟨722, by decide⟩ routine722 := by
  wct_ready_start 722 22 18
  wct_cases [242256,242262,242264,242266,242272,242274,242278,241456,235227,2681,1365,875,881]
  · wct_piece 49 242256 40
  · wct_piece 49 242262 41
  · wct_piece 49 242264 42
  · wct_piece 49 242266 43
  · wct_piece 49 242272 44
  · wct_piece 49 242274 45
  · wct_piece 49 242278 46
  · wct_piece 45 241456 37
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine723_ready : RoutineReady ⟨723, by decide⟩ routine723 := by
  wct_ready_start 723 22 19
  wct_cases [242279,242285,242287,242289,242295,242297,242301,241479,235251,2705,1386,1392,1396,966]
  · wct_piece 49 242279 47
  · wct_piece 49 242285 48
  · wct_piece 49 242287 49
  · wct_piece 49 242289 50
  · wct_piece 49 242295 51
  · wct_piece 49 242297 52
  · wct_piece 49 242301 53
  · wct_piece 45 241479 44
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine724_ready : RoutineReady ⟨724, by decide⟩ routine724 := by
  wct_ready_start 724 22 20
  wct_cases [242302,242308,242310,242312,242318,242320,242324,241502,235275,2726,2732,2736,1585,966]
  · wct_piece 49 242302 54
  · wct_piece 49 242308 55
  · wct_piece 49 242310 56
  · wct_piece 49 242312 57
  · wct_piece 49 242318 58
  · wct_piece 49 242320 59
  · wct_piece 49 242324 60
  · wct_piece 45 241502 51
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine725_ready : RoutineReady ⟨725, by decide⟩ routine725 := by
  wct_ready_start 725 22 21
  wct_cases [242325,242331,242333,242335,242341,242343,242347,241525,235296,235302,235306,3101,1585,966]
  · wct_piece 49 242325 61
  · wct_piece 49 242331 62
  · wct_piece 49 242333 63
  · wct_piece 50 242335 0
  · wct_piece 50 242341 1
  · wct_piece 50 242343 2
  · wct_piece 50 242347 3
  · wct_piece 45 241525 58
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine726_ready : RoutineReady ⟨726, by decide⟩ routine726 := by
  wct_ready_start 726 22 22
  wct_cases [242348,242354,242356,242358,242364,242367,241545,241551,241555,235929,3101,1585,966]
  · wct_piece 50 242348 4
  · wct_piece 50 242354 5
  · wct_piece 50 242356 6
  · wct_piece 50 242358 7
  · wct_piece 50 242364 8
  · wct_piece 50 242367 9
  · wct_piece 46 241545 0
  · wct_piece 46 241551 1
  · wct_piece 46 241555 2
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine727_ready : RoutineReady ⟨727, by decide⟩ routine727 := by
  wct_ready_start 727 22 23
  wct_cases [242368,242374,242376,242378,242384,242386,242388,242392,235929,3101,1585,966]
  · wct_piece 50 242368 10
  · wct_piece 50 242374 11
  · wct_piece 50 242376 12
  · wct_piece 50 242378 13
  · wct_piece 50 242384 14
  · wct_piece 50 242386 15
  · wct_piece 50 242388 16
  · wct_piece 50 242392 17
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end
