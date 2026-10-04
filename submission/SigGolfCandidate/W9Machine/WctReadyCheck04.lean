import SigGolfCandidate.W9Machine.WctRoutineModel
import SigGolfCandidate.W9Machine.WctChainCheck12
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine128 : ChainRoutine := ⟨128, [0, 0, 3, 1, 1, 0, 1], [piece2732, piece2737, piece2739, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine129 : ChainRoutine := ⟨129, [0, 0, 3, 1, 1, 1, 0], [piece2748, piece2753, piece2755, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine130 : ChainRoutine := ⟨130, [0, 0, 3, 1, 2, 0, 0], [piece2764, piece2769, piece2771, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine131 : ChainRoutine := ⟨131, [0, 0, 3, 2, 0, 0, 1], [piece2780, piece2785, piece2787, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine132 : ChainRoutine := ⟨132, [0, 0, 3, 2, 0, 1, 0], [piece2802, piece2807, piece2809, piece2812, piece2817, piece2819, piece2823, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine133 : ChainRoutine := ⟨133, [0, 0, 3, 2, 1, 0, 0], [piece2824, piece2829, piece2831, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine134 : ChainRoutine := ⟨134, [0, 0, 3, 3, 0, 0, 0], [piece2843, piece2848, piece2850, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine135 : ChainRoutine := ⟨135, [0, 1, 0, 0, 0, 2, 3], [piece2867, piece2872, piece2876, piece1512, piece960, piece775, piece780, piece783, piece754, piece759, piece761, piece764]⟩
def routine136 : ChainRoutine := ⟨136, [0, 1, 0, 0, 0, 3, 2], [piece2877, piece2882, piece2886, piece1522, piece970, piece789, piece794, piece796, piece799, piece804, piece807]⟩
def routine137 : ChainRoutine := ⟨137, [0, 1, 0, 0, 1, 1, 3], [piece2887, piece2892, piece2896, piece1532, piece976, piece981, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine138 : ChainRoutine := ⟨138, [0, 1, 0, 0, 1, 2, 2], [piece2897, piece2902, piece2906, piece1542, piece987, piece992, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine139 : ChainRoutine := ⟨139, [0, 1, 0, 0, 1, 3, 1], [piece2907, piece2912, piece2916, piece1552, piece998, piece1003, piece852, piece857, piece859, piece862, piece867]⟩
def routine140 : ChainRoutine := ⟨140, [0, 1, 0, 0, 2, 0, 3], [piece2917, piece2922, piece2926, piece1562, piece1009, piece1014, piece1016, piece1020, piece886, piece754, piece759, piece761, piece764]⟩
def routine141 : ChainRoutine := ⟨141, [0, 1, 0, 0, 2, 1, 2], [piece2927, piece2932, piece2936, piece1572, piece1026, piece1031, piece1034, piece897, piece902, piece799, piece804, piece807]⟩
def routine142 : ChainRoutine := ⟨142, [0, 1, 0, 0, 2, 2, 1], [piece2937, piece2942, piece2946, piece1582, piece1040, piece1045, piece1048, piece913, piece918, piece921, piece862, piece867]⟩
def routine143 : ChainRoutine := ⟨143, [0, 1, 0, 0, 2, 3, 0], [piece2947, piece2952, piece2956, piece1592, piece1054, piece1059, piece1062, piece932, piece937, piece939, piece941, piece945]⟩
def routine144 : ChainRoutine := ⟨144, [0, 1, 0, 0, 3, 0, 2], [piece2957, piece2962, piece2966, piece1602, piece1068, piece1073, piece1075, piece1077, piece1081, piece799, piece804, piece807]⟩
def routine145 : ChainRoutine := ⟨145, [0, 1, 0, 0, 3, 1, 1], [piece2967, piece2972, piece2976, piece1612, piece1087, piece1092, piece1094, piece1097, piece1102, piece862, piece867]⟩
def routine146 : ChainRoutine := ⟨146, [0, 1, 0, 0, 3, 2, 0], [piece2977, piece2982, piece2986, piece1622, piece1108, piece1113, piece1115, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine147 : ChainRoutine := ⟨147, [0, 1, 0, 1, 0, 1, 3], [piece2987, piece2992, piece2996, piece3001, piece3005, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine148 : ChainRoutine := ⟨148, [0, 1, 0, 1, 0, 2, 2], [piece3006, piece3011, piece3015, piece3020, piece3024, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine149 : ChainRoutine := ⟨149, [0, 1, 0, 1, 0, 3, 1], [piece3025, piece3030, piece3034, piece1658, piece1663, piece1667, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine150 : ChainRoutine := ⟨150, [0, 1, 0, 1, 1, 0, 3], [piece3035, piece3040, piece3044, piece3049, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine151 : ChainRoutine := ⟨151, [0, 1, 0, 1, 1, 1, 2], [piece3050, piece3055, piece3059, piece1684, piece1689, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine152 : ChainRoutine := ⟨152, [0, 1, 0, 1, 1, 2, 1], [piece3060, piece3065, piece3069, piece1695, piece1700, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine153 : ChainRoutine := ⟨153, [0, 1, 0, 1, 1, 3, 0], [piece3070, piece3075, piece3079, piece1706, piece1711, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine154 : ChainRoutine := ⟨154, [0, 1, 0, 1, 2, 0, 2], [piece3080, piece3085, piece3089, piece3094, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine155 : ChainRoutine := ⟨155, [0, 1, 0, 1, 2, 1, 1], [piece3095, piece3100, piece3104, piece1728, piece1733, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine156 : ChainRoutine := ⟨156, [0, 1, 0, 1, 2, 2, 0], [piece3105, piece3110, piece3114, piece3119, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine157 : ChainRoutine := ⟨157, [0, 1, 0, 1, 3, 0, 1], [piece3120, piece3125, piece3129, piece1750, piece1755, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine158 : ChainRoutine := ⟨158, [0, 1, 0, 1, 3, 1, 0], [piece3130, piece3135, piece3139, piece1761, piece1766, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine159 : ChainRoutine := ⟨159, [0, 1, 0, 2, 0, 0, 3], [piece3140, piece3145, piece3149, piece1772, piece1777, piece1779, piece1783, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routineBatch04 : List ChainRoutine := [routine128, routine129, routine130, routine131, routine132, routine133, routine134, routine135, routine136, routine137, routine138, routine139, routine140, routine141, routine142, routine143, routine144, routine145, routine146, routine147, routine148, routine149, routine150, routine151, routine152, routine153, routine154, routine155, routine156, routine157, routine158, routine159]
theorem routineBatch04_checked : (routineBatch04.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch04_checked :
    (routineBatch04.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch04_checked :
    (routineBatch04.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine128_ready : RoutineReady ⟨128, by decide⟩ routine128 := by
  wct_ready_start 128 4 0
  wct_cases [2732,2737,2739,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 9 2732 24
  · wct_piece 9 2737 25
  · wct_piece 9 2739 26
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine129_ready : RoutineReady ⟨129, by decide⟩ routine129 := by
  wct_ready_start 129 4 1
  wct_cases [2748,2753,2755,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 9 2748 29
  · wct_piece 9 2753 30
  · wct_piece 9 2755 31
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine130_ready : RoutineReady ⟨130, by decide⟩ routine130 := by
  wct_ready_start 130 4 2
  wct_cases [2764,2769,2771,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 9 2764 34
  · wct_piece 9 2769 35
  · wct_piece 9 2771 36
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine131_ready : RoutineReady ⟨131, by decide⟩ routine131 := by
  wct_ready_start 131 4 3
  wct_cases [2780,2785,2787,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 9 2780 39
  · wct_piece 9 2785 40
  · wct_piece 9 2787 41
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine132_ready : RoutineReady ⟨132, by decide⟩ routine132 := by
  wct_ready_start 132 4 4
  wct_cases [2802,2807,2809,2812,2817,2819,2823,2503,1320,1325,1329,945]
  · wct_piece 9 2802 46
  · wct_piece 9 2807 47
  · wct_piece 9 2809 48
  · wct_piece 9 2812 49
  · wct_piece 9 2817 50
  · wct_piece 9 2819 51
  · wct_piece 9 2823 52
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine133_ready : RoutineReady ⟨133, by decide⟩ routine133 := by
  wct_ready_start 133 4 5
  wct_cases [2824,2829,2831,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 9 2824 53
  · wct_piece 9 2829 54
  · wct_piece 9 2831 55
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine134_ready : RoutineReady ⟨134, by decide⟩ routine134 := by
  wct_ready_start 134 4 6
  wct_cases [2843,2848,2850,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 9 2843 59
  · wct_piece 9 2848 60
  · wct_piece 9 2850 61
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine135_ready : RoutineReady ⟨135, by decide⟩ routine135 := by
  wct_ready_start 135 4 7
  wct_cases [2867,2872,2876,1512,960,775,780,783,754,759,761,764]
  · wct_piece 10 2867 3
  · wct_piece 10 2872 4
  · wct_piece 10 2876 5
  · wct_piece 3 1512 37
  · wct_piece 0 960 60
  · wct_piece 0 775 8
  · wct_piece 0 780 9
  · wct_piece 0 783 10
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine136_ready : RoutineReady ⟨136, by decide⟩ routine136 := by
  wct_ready_start 136 4 8
  wct_cases [2877,2882,2886,1522,970,789,794,796,799,804,807]
  · wct_piece 10 2877 6
  · wct_piece 10 2882 7
  · wct_piece 10 2886 8
  · wct_piece 3 1522 40
  · wct_piece 0 970 63
  · wct_piece 0 789 12
  · wct_piece 0 794 13
  · wct_piece 0 796 14
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine137_ready : RoutineReady ⟨137, by decide⟩ routine137 := by
  wct_ready_start 137 4 9
  wct_cases [2887,2892,2896,1532,976,981,821,826,754,759,761,764]
  · wct_piece 10 2887 9
  · wct_piece 10 2892 10
  · wct_piece 10 2896 11
  · wct_piece 3 1532 43
  · wct_piece 1 976 1
  · wct_piece 1 981 2
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine138_ready : RoutineReady ⟨138, by decide⟩ routine138 := by
  wct_ready_start 138 4 10
  wct_cases [2897,2902,2906,1542,987,992,835,840,843,799,804,807]
  · wct_piece 10 2897 12
  · wct_piece 10 2902 13
  · wct_piece 10 2906 14
  · wct_piece 3 1542 46
  · wct_piece 1 987 4
  · wct_piece 1 992 5
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine139_ready : RoutineReady ⟨139, by decide⟩ routine139 := by
  wct_ready_start 139 4 11
  wct_cases [2907,2912,2916,1552,998,1003,852,857,859,862,867]
  · wct_piece 10 2907 15
  · wct_piece 10 2912 16
  · wct_piece 10 2916 17
  · wct_piece 3 1552 49
  · wct_piece 1 998 7
  · wct_piece 1 1003 8
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine140_ready : RoutineReady ⟨140, by decide⟩ routine140 := by
  wct_ready_start 140 4 12
  wct_cases [2917,2922,2926,1562,1009,1014,1016,1020,886,754,759,761,764]
  · wct_piece 10 2917 18
  · wct_piece 10 2922 19
  · wct_piece 10 2926 20
  · wct_piece 3 1562 52
  · wct_piece 1 1009 10
  · wct_piece 1 1014 11
  · wct_piece 1 1016 12
  · wct_piece 1 1020 13
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine141_ready : RoutineReady ⟨141, by decide⟩ routine141 := by
  wct_ready_start 141 4 13
  wct_cases [2927,2932,2936,1572,1026,1031,1034,897,902,799,804,807]
  · wct_piece 10 2927 21
  · wct_piece 10 2932 22
  · wct_piece 10 2936 23
  · wct_piece 3 1572 55
  · wct_piece 1 1026 15
  · wct_piece 1 1031 16
  · wct_piece 1 1034 17
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine142_ready : RoutineReady ⟨142, by decide⟩ routine142 := by
  wct_ready_start 142 4 14
  wct_cases [2937,2942,2946,1582,1040,1045,1048,913,918,921,862,867]
  · wct_piece 10 2937 24
  · wct_piece 10 2942 25
  · wct_piece 10 2946 26
  · wct_piece 3 1582 58
  · wct_piece 1 1040 19
  · wct_piece 1 1045 20
  · wct_piece 1 1048 21
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine143_ready : RoutineReady ⟨143, by decide⟩ routine143 := by
  wct_ready_start 143 4 15
  wct_cases [2947,2952,2956,1592,1054,1059,1062,932,937,939,941,945]
  · wct_piece 10 2947 27
  · wct_piece 10 2952 28
  · wct_piece 10 2956 29
  · wct_piece 3 1592 61
  · wct_piece 1 1054 23
  · wct_piece 1 1059 24
  · wct_piece 1 1062 25
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine144_ready : RoutineReady ⟨144, by decide⟩ routine144 := by
  wct_ready_start 144 4 16
  wct_cases [2957,2962,2966,1602,1068,1073,1075,1077,1081,799,804,807]
  · wct_piece 10 2957 30
  · wct_piece 10 2962 31
  · wct_piece 10 2966 32
  · wct_piece 4 1602 0
  · wct_piece 1 1068 27
  · wct_piece 1 1073 28
  · wct_piece 1 1075 29
  · wct_piece 1 1077 30
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine145_ready : RoutineReady ⟨145, by decide⟩ routine145 := by
  wct_ready_start 145 4 17
  wct_cases [2967,2972,2976,1612,1087,1092,1094,1097,1102,862,867]
  · wct_piece 10 2967 33
  · wct_piece 10 2972 34
  · wct_piece 10 2976 35
  · wct_piece 4 1612 3
  · wct_piece 1 1087 33
  · wct_piece 1 1092 34
  · wct_piece 1 1094 35
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine146_ready : RoutineReady ⟨146, by decide⟩ routine146 := by
  wct_ready_start 146 4 18
  wct_cases [2977,2982,2986,1622,1108,1113,1115,1118,1123,1125,1129,945]
  · wct_piece 10 2977 36
  · wct_piece 10 2982 37
  · wct_piece 10 2986 38
  · wct_piece 4 1622 6
  · wct_piece 1 1108 39
  · wct_piece 1 1113 40
  · wct_piece 1 1115 41
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine147_ready : RoutineReady ⟨147, by decide⟩ routine147 := by
  wct_ready_start 147 4 19
  wct_cases [2987,2992,2996,3001,3005,1141,821,826,754,759,761,764]
  · wct_piece 10 2987 39
  · wct_piece 10 2992 40
  · wct_piece 10 2996 41
  · wct_piece 10 3001 42
  · wct_piece 10 3005 43
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine148_ready : RoutineReady ⟨148, by decide⟩ routine148 := by
  wct_ready_start 148 4 20
  wct_cases [3006,3011,3015,3020,3024,835,840,843,799,804,807]
  · wct_piece 10 3006 44
  · wct_piece 10 3011 45
  · wct_piece 10 3015 46
  · wct_piece 10 3020 47
  · wct_piece 10 3024 48
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine149_ready : RoutineReady ⟨149, by decide⟩ routine149 := by
  wct_ready_start 149 4 21
  wct_cases [3025,3030,3034,1658,1663,1667,1165,852,857,859,862,867]
  · wct_piece 10 3025 49
  · wct_piece 10 3030 50
  · wct_piece 10 3034 51
  · wct_piece 4 1658 16
  · wct_piece 4 1663 17
  · wct_piece 4 1667 18
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine150_ready : RoutineReady ⟨150, by decide⟩ routine150 := by
  wct_ready_start 150 4 22
  wct_cases [3035,3040,3044,3049,1174,1179,1183,886,754,759,761,764]
  · wct_piece 10 3035 52
  · wct_piece 10 3040 53
  · wct_piece 10 3044 54
  · wct_piece 10 3049 55
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine151_ready : RoutineReady ⟨151, by decide⟩ routine151 := by
  wct_ready_start 151 4 23
  wct_cases [3050,3055,3059,1684,1689,1192,1197,897,902,799,804,807]
  · wct_piece 10 3050 56
  · wct_piece 10 3055 57
  · wct_piece 10 3059 58
  · wct_piece 4 1684 23
  · wct_piece 4 1689 24
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine152_ready : RoutineReady ⟨152, by decide⟩ routine152 := by
  wct_ready_start 152 4 24
  wct_cases [3060,3065,3069,1695,1700,1206,1211,913,918,921,862,867]
  · wct_piece 10 3060 59
  · wct_piece 10 3065 60
  · wct_piece 10 3069 61
  · wct_piece 4 1695 26
  · wct_piece 4 1700 27
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine153_ready : RoutineReady ⟨153, by decide⟩ routine153 := by
  wct_ready_start 153 4 25
  wct_cases [3070,3075,3079,1706,1711,1220,1225,932,937,939,941,945]
  · wct_piece 10 3070 62
  · wct_piece 10 3075 63
  · wct_piece 11 3079 0
  · wct_piece 4 1706 29
  · wct_piece 4 1711 30
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine154_ready : RoutineReady ⟨154, by decide⟩ routine154 := by
  wct_ready_start 154 4 26
  wct_cases [3080,3085,3089,3094,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 11 3080 1
  · wct_piece 11 3085 2
  · wct_piece 11 3089 3
  · wct_piece 11 3094 4
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine155_ready : RoutineReady ⟨155, by decide⟩ routine155 := by
  wct_ready_start 155 4 27
  wct_cases [3095,3100,3104,1728,1733,1254,1259,1262,1097,1102,862,867]
  · wct_piece 11 3095 5
  · wct_piece 11 3100 6
  · wct_piece 11 3104 7
  · wct_piece 4 1728 35
  · wct_piece 4 1733 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine156_ready : RoutineReady ⟨156, by decide⟩ routine156 := by
  wct_ready_start 156 4 28
  wct_cases [3105,3110,3114,3119,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 11 3105 8
  · wct_piece 11 3110 9
  · wct_piece 11 3114 10
  · wct_piece 11 3119 11
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine157_ready : RoutineReady ⟨157, by decide⟩ routine157 := by
  wct_ready_start 157 4 29
  wct_cases [3120,3125,3129,1750,1755,1288,1293,1295,1297,1301,862,867]
  · wct_piece 11 3120 12
  · wct_piece 11 3125 13
  · wct_piece 11 3129 14
  · wct_piece 4 1750 41
  · wct_piece 4 1755 42
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine158_ready : RoutineReady ⟨158, by decide⟩ routine158 := by
  wct_ready_start 158 4 30
  wct_cases [3130,3135,3139,1761,1766,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 11 3130 15
  · wct_piece 11 3135 16
  · wct_piece 11 3139 17
  · wct_piece 4 1761 44
  · wct_piece 4 1766 45
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine159_ready : RoutineReady ⟨159, by decide⟩ routine159 := by
  wct_ready_start 159 4 31
  wct_cases [3140,3145,3149,1772,1777,1779,1783,1343,886,754,759,761,764]
  · wct_piece 11 3140 18
  · wct_piece 11 3145 19
  · wct_piece 11 3149 20
  · wct_piece 4 1772 47
  · wct_piece 4 1777 48
  · wct_piece 4 1779 49
  · wct_piece 4 1783 50
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
end W9Machine.Chain
end
