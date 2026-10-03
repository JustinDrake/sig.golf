import SigGolfCandidate.W9Machine.WctRoutineCheck04
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

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
  wct_cases [2953,2959,2961,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 9 2953 24
  · wct_piece 9 2959 25
  · wct_piece 9 2961 26
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine129_ready : RoutineReady ⟨129, by decide⟩ routine129 := by
  wct_ready_start 129 4 1
  wct_cases [2971,2977,2979,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 9 2971 29
  · wct_piece 9 2977 30
  · wct_piece 9 2979 31
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine130_ready : RoutineReady ⟨130, by decide⟩ routine130 := by
  wct_ready_start 130 4 2
  wct_cases [2989,2995,2997,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 9 2989 34
  · wct_piece 9 2995 35
  · wct_piece 9 2997 36
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine131_ready : RoutineReady ⟨131, by decide⟩ routine131 := by
  wct_ready_start 131 4 3
  wct_cases [3007,3013,3015,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 9 3007 39
  · wct_piece 9 3013 40
  · wct_piece 9 3015 41
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine132_ready : RoutineReady ⟨132, by decide⟩ routine132 := by
  wct_ready_start 132 4 4
  wct_cases [3031,3037,3039,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 9 3031 46
  · wct_piece 9 3037 47
  · wct_piece 9 3039 48
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine133_ready : RoutineReady ⟨133, by decide⟩ routine133 := by
  wct_ready_start 133 4 5
  wct_cases [3055,3061,3063,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 9 3055 53
  · wct_piece 9 3061 54
  · wct_piece 9 3063 55
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine134_ready : RoutineReady ⟨134, by decide⟩ routine134 := by
  wct_ready_start 134 4 6
  wct_cases [3076,3082,3084,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 9 3076 59
  · wct_piece 9 3082 60
  · wct_piece 9 3084 61
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine135_ready : RoutineReady ⟨135, by decide⟩ routine135 := by
  wct_ready_start 135 4 7
  wct_cases [3102,3108,3112,1596,982,778,784,787,755,761,763,766]
  · wct_piece 10 3102 3
  · wct_piece 10 3108 4
  · wct_piece 10 3112 5
  · wct_piece 3 1596 37
  · wct_piece 0 982 60
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine136_ready : RoutineReady ⟨136, by decide⟩ routine136 := by
  wct_ready_start 136 4 8
  wct_cases [3113,3119,3123,1607,993,794,800,802,805,811,814]
  · wct_piece 10 3113 6
  · wct_piece 10 3119 7
  · wct_piece 10 3123 8
  · wct_piece 3 1607 40
  · wct_piece 0 993 63
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine137_ready : RoutineReady ⟨137, by decide⟩ routine137 := by
  wct_ready_start 137 4 9
  wct_cases [3124,3130,3134,1618,1000,1006,829,835,755,761,763,766]
  · wct_piece 10 3124 9
  · wct_piece 10 3130 10
  · wct_piece 10 3134 11
  · wct_piece 3 1618 43
  · wct_piece 1 1000 1
  · wct_piece 1 1006 2
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine138_ready : RoutineReady ⟨138, by decide⟩ routine138 := by
  wct_ready_start 138 4 10
  wct_cases [3135,3141,3145,1629,1013,1019,845,851,854,805,811,814]
  · wct_piece 10 3135 12
  · wct_piece 10 3141 13
  · wct_piece 10 3145 14
  · wct_piece 3 1629 46
  · wct_piece 1 1013 4
  · wct_piece 1 1019 5
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine139_ready : RoutineReady ⟨139, by decide⟩ routine139 := by
  wct_ready_start 139 4 11
  wct_cases [3146,3152,3156,1640,1026,1032,864,870,872,875,881]
  · wct_piece 10 3146 15
  · wct_piece 10 3152 16
  · wct_piece 10 3156 17
  · wct_piece 3 1640 49
  · wct_piece 1 1026 7
  · wct_piece 1 1032 8
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine140_ready : RoutineReady ⟨140, by decide⟩ routine140 := by
  wct_ready_start 140 4 12
  wct_cases [3157,3163,3167,1651,1039,1045,1047,1051,901,755,761,763,766]
  · wct_piece 10 3157 18
  · wct_piece 10 3163 19
  · wct_piece 10 3167 20
  · wct_piece 3 1651 52
  · wct_piece 1 1039 10
  · wct_piece 1 1045 11
  · wct_piece 1 1047 12
  · wct_piece 1 1051 13
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine141_ready : RoutineReady ⟨141, by decide⟩ routine141 := by
  wct_ready_start 141 4 13
  wct_cases [3168,3174,3178,1662,1058,1064,1067,913,919,805,811,814]
  · wct_piece 10 3168 21
  · wct_piece 10 3174 22
  · wct_piece 10 3178 23
  · wct_piece 3 1662 55
  · wct_piece 1 1058 15
  · wct_piece 1 1064 16
  · wct_piece 1 1067 17
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine142_ready : RoutineReady ⟨142, by decide⟩ routine142 := by
  wct_ready_start 142 4 14
  wct_cases [3179,3185,3189,1673,1074,1080,1083,931,937,940,875,881]
  · wct_piece 10 3179 24
  · wct_piece 10 3185 25
  · wct_piece 10 3189 26
  · wct_piece 3 1673 58
  · wct_piece 1 1074 19
  · wct_piece 1 1080 20
  · wct_piece 1 1083 21
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine143_ready : RoutineReady ⟨143, by decide⟩ routine143 := by
  wct_ready_start 143 4 15
  wct_cases [3190,3196,3200,1684,1090,1096,1099,952,958,960,962,966]
  · wct_piece 10 3190 27
  · wct_piece 10 3196 28
  · wct_piece 10 3200 29
  · wct_piece 3 1684 61
  · wct_piece 1 1090 23
  · wct_piece 1 1096 24
  · wct_piece 1 1099 25
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine144_ready : RoutineReady ⟨144, by decide⟩ routine144 := by
  wct_ready_start 144 4 16
  wct_cases [3201,3207,3211,1695,1106,1112,1114,1116,1120,805,811,814]
  · wct_piece 10 3201 30
  · wct_piece 10 3207 31
  · wct_piece 10 3211 32
  · wct_piece 4 1695 0
  · wct_piece 1 1106 27
  · wct_piece 1 1112 28
  · wct_piece 1 1114 29
  · wct_piece 1 1116 30
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine145_ready : RoutineReady ⟨145, by decide⟩ routine145 := by
  wct_ready_start 145 4 17
  wct_cases [3212,3218,3222,1706,1127,1133,1135,1138,1144,875,881]
  · wct_piece 10 3212 33
  · wct_piece 10 3218 34
  · wct_piece 10 3222 35
  · wct_piece 4 1706 3
  · wct_piece 1 1127 33
  · wct_piece 1 1133 34
  · wct_piece 1 1135 35
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine146_ready : RoutineReady ⟨146, by decide⟩ routine146 := by
  wct_ready_start 146 4 18
  wct_cases [3223,3229,3233,1717,1151,1157,1159,1162,1168,1170,1174,966]
  · wct_piece 10 3223 36
  · wct_piece 10 3229 37
  · wct_piece 10 3233 38
  · wct_piece 4 1717 6
  · wct_piece 1 1151 39
  · wct_piece 1 1157 40
  · wct_piece 1 1159 41
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine147_ready : RoutineReady ⟨147, by decide⟩ routine147 := by
  wct_ready_start 147 4 19
  wct_cases [3234,3240,3244,1724,1730,1734,1187,829,835,755,761,763,766]
  · wct_piece 10 3234 39
  · wct_piece 10 3240 40
  · wct_piece 10 3244 41
  · wct_piece 4 1724 8
  · wct_piece 4 1730 9
  · wct_piece 4 1734 10
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine148_ready : RoutineReady ⟨148, by decide⟩ routine148 := by
  wct_ready_start 148 4 20
  wct_cases [3245,3251,3255,3261,3265,1200,845,851,854,805,811,814]
  · wct_piece 10 3245 42
  · wct_piece 10 3251 43
  · wct_piece 10 3255 44
  · wct_piece 10 3261 45
  · wct_piece 10 3265 46
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine149_ready : RoutineReady ⟨149, by decide⟩ routine149 := by
  wct_ready_start 149 4 21
  wct_cases [3266,3272,3276,1758,1764,1768,1213,864,870,872,875,881]
  · wct_piece 10 3266 47
  · wct_piece 10 3272 48
  · wct_piece 10 3276 49
  · wct_piece 4 1758 16
  · wct_piece 4 1764 17
  · wct_piece 4 1768 18
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine150_ready : RoutineReady ⟨150, by decide⟩ routine150 := by
  wct_ready_start 150 4 22
  wct_cases [3277,3283,3287,1775,1781,1223,1229,1233,901,755,761,763,766]
  · wct_piece 10 3277 50
  · wct_piece 10 3283 51
  · wct_piece 10 3287 52
  · wct_piece 4 1775 20
  · wct_piece 4 1781 21
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine151_ready : RoutineReady ⟨151, by decide⟩ routine151 := by
  wct_ready_start 151 4 23
  wct_cases [3288,3294,3298,1788,1794,1243,1249,913,919,805,811,814]
  · wct_piece 10 3288 53
  · wct_piece 10 3294 54
  · wct_piece 10 3298 55
  · wct_piece 4 1788 23
  · wct_piece 4 1794 24
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine152_ready : RoutineReady ⟨152, by decide⟩ routine152 := by
  wct_ready_start 152 4 24
  wct_cases [3299,3305,3309,1801,1807,1259,1265,931,937,940,875,881]
  · wct_piece 10 3299 56
  · wct_piece 10 3305 57
  · wct_piece 10 3309 58
  · wct_piece 4 1801 26
  · wct_piece 4 1807 27
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine153_ready : RoutineReady ⟨153, by decide⟩ routine153 := by
  wct_ready_start 153 4 25
  wct_cases [3310,3316,3320,1814,1820,1275,1281,952,958,960,962,966]
  · wct_piece 10 3310 59
  · wct_piece 10 3316 60
  · wct_piece 10 3320 61
  · wct_piece 4 1814 29
  · wct_piece 4 1820 30
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine154_ready : RoutineReady ⟨154, by decide⟩ routine154 := by
  wct_ready_start 154 4 26
  wct_cases [3321,3327,3331,1827,1833,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 10 3321 62
  · wct_piece 10 3327 63
  · wct_piece 11 3331 0
  · wct_piece 4 1827 32
  · wct_piece 4 1833 33
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine155_ready : RoutineReady ⟨155, by decide⟩ routine155 := by
  wct_ready_start 155 4 27
  wct_cases [3332,3338,3342,1840,1846,1313,1319,1322,1138,1144,875,881]
  · wct_piece 11 3332 1
  · wct_piece 11 3338 2
  · wct_piece 11 3342 3
  · wct_piece 4 1840 35
  · wct_piece 4 1846 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine156_ready : RoutineReady ⟨156, by decide⟩ routine156 := by
  wct_ready_start 156 4 28
  wct_cases [3343,3349,3353,1853,1859,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 11 3343 4
  · wct_piece 11 3349 5
  · wct_piece 11 3353 6
  · wct_piece 4 1853 38
  · wct_piece 4 1859 39
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine157_ready : RoutineReady ⟨157, by decide⟩ routine157 := by
  wct_ready_start 157 4 29
  wct_cases [3354,3360,3364,1866,1872,1351,1357,1359,1361,1365,875,881]
  · wct_piece 11 3354 7
  · wct_piece 11 3360 8
  · wct_piece 11 3364 9
  · wct_piece 4 1866 41
  · wct_piece 4 1872 42
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine158_ready : RoutineReady ⟨158, by decide⟩ routine158 := by
  wct_ready_start 158 4 30
  wct_cases [3365,3371,3375,1879,1885,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 11 3365 10
  · wct_piece 11 3371 11
  · wct_piece 11 3375 12
  · wct_piece 4 1879 44
  · wct_piece 4 1885 45
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine159_ready : RoutineReady ⟨159, by decide⟩ routine159 := by
  wct_ready_start 159 4 31
  wct_cases [3376,3382,3386,1892,1898,1900,1904,1411,901,755,761,763,766]
  · wct_piece 11 3376 13
  · wct_piece 11 3382 14
  · wct_piece 11 3386 15
  · wct_piece 4 1892 47
  · wct_piece 4 1898 48
  · wct_piece 4 1900 49
  · wct_piece 4 1904 50
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
end W9Machine.Chain
end
