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
def routine160 : ChainRoutine := ⟨160, [0, 1, 0, 2, 0, 1, 2], [piece3150, piece3155, piece3159, piece3164, piece3166, piece3170, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine161 : ChainRoutine := ⟨161, [0, 1, 0, 2, 0, 2, 1], [piece3171, piece3176, piece3180, piece3185, piece3187, piece3191, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine162 : ChainRoutine := ⟨162, [0, 1, 0, 2, 0, 3, 0], [piece3192, piece3197, piece3201, piece1823, piece1828, piece1830, piece1834, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine163 : ChainRoutine := ⟨163, [0, 1, 0, 2, 1, 0, 2], [piece3202, piece3207, piece3211, piece3216, piece3219, piece3224, piece3228, piece1081, piece799, piece804, piece807]⟩
def routine164 : ChainRoutine := ⟨164, [0, 1, 0, 2, 1, 1, 1], [piece3229, piece3234, piece3238, piece1854, piece1859, piece1862, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine165 : ChainRoutine := ⟨165, [0, 1, 0, 2, 1, 2, 0], [piece3239, piece3244, piece3248, piece3253, piece3256, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine166 : ChainRoutine := ⟨166, [0, 1, 0, 2, 2, 0, 1], [piece3257, piece3262, piece3266, piece3271, piece3274, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine167 : ChainRoutine := ⟨167, [0, 1, 0, 2, 2, 1, 0], [piece3275, piece3280, piece3284, piece3289, piece3292, piece3297, piece3300, piece1320, piece1325, piece1329, piece945]⟩
def routine168 : ChainRoutine := ⟨168, [0, 1, 0, 2, 3, 0, 0], [piece3301, piece3306, piece3310, piece1910, piece1915, piece1918, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine169 : ChainRoutine := ⟨169, [0, 1, 0, 3, 0, 0, 2], [piece3311, piece3316, piece3320, piece1924, piece1929, piece1931, piece1933, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine170 : ChainRoutine := ⟨170, [0, 1, 0, 3, 0, 1, 1], [piece3321, piece3326, piece3330, piece1943, piece1948, piece1950, piece1952, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine171 : ChainRoutine := ⟨171, [0, 1, 0, 3, 0, 2, 0], [piece3331, piece3336, piece3340, piece1962, piece1967, piece1969, piece1971, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine172 : ChainRoutine := ⟨172, [0, 1, 0, 3, 1, 0, 1], [piece3341, piece3346, piece3350, piece1981, piece1986, piece1988, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine173 : ChainRoutine := ⟨173, [0, 1, 0, 3, 1, 1, 0], [piece3351, piece3356, piece3360, piece2006, piece2011, piece2013, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine174 : ChainRoutine := ⟨174, [0, 1, 0, 3, 2, 0, 0], [piece3361, piece3366, piece3370, piece2027, piece2032, piece2034, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine175 : ChainRoutine := ⟨175, [0, 1, 1, 0, 0, 1, 3], [piece3371, piece3376, piece3381, piece3385, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine176 : ChainRoutine := ⟨176, [0, 1, 1, 0, 0, 2, 2], [piece3386, piece3391, piece3396, piece3400, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine177 : ChainRoutine := ⟨177, [0, 1, 1, 0, 0, 3, 1], [piece3401, piece3406, piece3411, piece3415, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine178 : ChainRoutine := ⟨178, [0, 1, 1, 0, 1, 0, 3], [piece3416, piece3421, piece3426, piece3430, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine179 : ChainRoutine := ⟨179, [0, 1, 1, 0, 1, 1, 2], [piece3431, piece3436, piece3441, piece3445, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine180 : ChainRoutine := ⟨180, [0, 1, 1, 0, 1, 2, 1], [piece3446, piece3451, piece3456, piece3460, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine181 : ChainRoutine := ⟨181, [0, 1, 1, 0, 1, 3, 0], [piece3461, piece3466, piece3471, piece3475, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine182 : ChainRoutine := ⟨182, [0, 1, 1, 0, 2, 0, 2], [piece3476, piece3481, piece3486, piece3490, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine183 : ChainRoutine := ⟨183, [0, 1, 1, 0, 2, 1, 1], [piece3491, piece3496, piece3501, piece3505, piece2156, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine184 : ChainRoutine := ⟨184, [0, 1, 1, 0, 2, 2, 0], [piece3506, piece3511, piece3516, piece3520, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine185 : ChainRoutine := ⟨185, [0, 1, 1, 0, 3, 0, 1], [piece3521, piece3526, piece3531, piece3535, piece2180, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine186 : ChainRoutine := ⟨186, [0, 1, 1, 0, 3, 1, 0], [piece3536, piece3541, piece3546, piece3550, piece2192, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine187 : ChainRoutine := ⟨187, [0, 1, 1, 1, 0, 0, 3], [piece3551, piece3556, piece3561, piece2201, piece2206, piece2210, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine188 : ChainRoutine := ⟨188, [0, 1, 1, 1, 0, 1, 2], [piece3562, piece3567, piece3572, piece2219, piece2224, piece2228, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine189 : ChainRoutine := ⟨189, [0, 1, 1, 1, 0, 2, 1], [piece3573, piece3578, piece3583, piece2237, piece2242, piece2246, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine190 : ChainRoutine := ⟨190, [0, 1, 1, 1, 0, 3, 0], [piece3584, piece3589, piece3594, piece2255, piece2260, piece2264, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine191 : ChainRoutine := ⟨191, [0, 1, 1, 1, 1, 0, 2], [piece3595, piece3600, piece3605, piece2273, piece2278, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routineBatch05 : List ChainRoutine := [routine160, routine161, routine162, routine163, routine164, routine165, routine166, routine167, routine168, routine169, routine170, routine171, routine172, routine173, routine174, routine175, routine176, routine177, routine178, routine179, routine180, routine181, routine182, routine183, routine184, routine185, routine186, routine187, routine188, routine189, routine190, routine191]
theorem routineBatch05_checked : (routineBatch05.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch05_checked :
    (routineBatch05.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch05_checked :
    (routineBatch05.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine160_ready : RoutineReady ⟨160, by decide⟩ routine160 := by
  wct_ready_start 160 5 0
  wct_cases [3150,3155,3159,3164,3166,3170,1357,897,902,799,804,807]
  · wct_piece 11 3150 21
  · wct_piece 11 3155 22
  · wct_piece 11 3159 23
  · wct_piece 11 3164 24
  · wct_piece 11 3166 25
  · wct_piece 11 3170 26
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine161_ready : RoutineReady ⟨161, by decide⟩ routine161 := by
  wct_ready_start 161 5 1
  wct_cases [3171,3176,3180,3185,3187,3191,1371,913,918,921,862,867]
  · wct_piece 11 3171 27
  · wct_piece 11 3176 28
  · wct_piece 11 3180 29
  · wct_piece 11 3185 30
  · wct_piece 11 3187 31
  · wct_piece 11 3191 32
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine162_ready : RoutineReady ⟨162, by decide⟩ routine162 := by
  wct_ready_start 162 5 2
  wct_cases [3192,3197,3201,1823,1828,1830,1834,1385,932,937,939,941,945]
  · wct_piece 11 3192 33
  · wct_piece 11 3197 34
  · wct_piece 11 3201 35
  · wct_piece 4 1823 62
  · wct_piece 4 1828 63
  · wct_piece 5 1830 0
  · wct_piece 5 1834 1
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine163_ready : RoutineReady ⟨163, by decide⟩ routine163 := by
  wct_ready_start 163 5 3
  wct_cases [3202,3207,3211,3216,3219,3224,3228,1081,799,804,807]
  · wct_piece 11 3202 36
  · wct_piece 11 3207 37
  · wct_piece 11 3211 38
  · wct_piece 11 3216 39
  · wct_piece 11 3219 40
  · wct_piece 11 3224 41
  · wct_piece 11 3228 42
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine164_ready : RoutineReady ⟨164, by decide⟩ routine164 := by
  wct_ready_start 164 5 4
  wct_cases [3229,3234,3238,1854,1859,1862,1416,1421,1097,1102,862,867]
  · wct_piece 11 3229 43
  · wct_piece 11 3234 44
  · wct_piece 11 3238 45
  · wct_piece 5 1854 7
  · wct_piece 5 1859 8
  · wct_piece 5 1862 9
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine165_ready : RoutineReady ⟨165, by decide⟩ routine165 := by
  wct_ready_start 165 5 5
  wct_cases [3239,3244,3248,3253,3256,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 11 3239 46
  · wct_piece 11 3244 47
  · wct_piece 11 3248 48
  · wct_piece 11 3253 49
  · wct_piece 11 3256 50
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine166_ready : RoutineReady ⟨166, by decide⟩ routine166 := by
  wct_ready_start 166 5 6
  wct_cases [3257,3262,3266,3271,3274,1448,1453,1455,1459,1301,862,867]
  · wct_piece 11 3257 51
  · wct_piece 11 3262 52
  · wct_piece 11 3266 53
  · wct_piece 11 3271 54
  · wct_piece 11 3274 55
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine167_ready : RoutineReady ⟨167, by decide⟩ routine167 := by
  wct_ready_start 167 5 7
  wct_cases [3275,3280,3284,3289,3292,3297,3300,1320,1325,1329,945]
  · wct_piece 11 3275 56
  · wct_piece 11 3280 57
  · wct_piece 11 3284 58
  · wct_piece 11 3289 59
  · wct_piece 11 3292 60
  · wct_piece 11 3297 61
  · wct_piece 11 3300 62
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine168_ready : RoutineReady ⟨168, by decide⟩ routine168 := by
  wct_ready_start 168 5 8
  wct_cases [3301,3306,3310,1910,1915,1918,1489,1494,1496,1498,1502,945]
  · wct_piece 11 3301 63
  · wct_piece 12 3306 0
  · wct_piece 12 3310 1
  · wct_piece 5 1910 23
  · wct_piece 5 1915 24
  · wct_piece 5 1918 25
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine169_ready : RoutineReady ⟨169, by decide⟩ routine169 := by
  wct_ready_start 169 5 9
  wct_cases [3311,3316,3320,1924,1929,1931,1933,1937,1081,799,804,807]
  · wct_piece 12 3311 2
  · wct_piece 12 3316 3
  · wct_piece 12 3320 4
  · wct_piece 5 1924 27
  · wct_piece 5 1929 28
  · wct_piece 5 1931 29
  · wct_piece 5 1933 30
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine170_ready : RoutineReady ⟨170, by decide⟩ routine170 := by
  wct_ready_start 170 5 10
  wct_cases [3321,3326,3330,1943,1948,1950,1952,1956,1097,1102,862,867]
  · wct_piece 12 3321 5
  · wct_piece 12 3326 6
  · wct_piece 12 3330 7
  · wct_piece 5 1943 33
  · wct_piece 5 1948 34
  · wct_piece 5 1950 35
  · wct_piece 5 1952 36
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine171_ready : RoutineReady ⟨171, by decide⟩ routine171 := by
  wct_ready_start 171 5 11
  wct_cases [3331,3336,3340,1962,1967,1969,1971,1975,1118,1123,1125,1129,945]
  · wct_piece 12 3331 8
  · wct_piece 12 3336 9
  · wct_piece 12 3340 10
  · wct_piece 5 1962 39
  · wct_piece 5 1967 40
  · wct_piece 5 1969 41
  · wct_piece 5 1971 42
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine172_ready : RoutineReady ⟨172, by decide⟩ routine172 := by
  wct_ready_start 172 5 12
  wct_cases [3341,3346,3350,1981,1986,1988,1991,1996,2000,1301,862,867]
  · wct_piece 12 3341 11
  · wct_piece 12 3346 12
  · wct_piece 12 3350 13
  · wct_piece 5 1981 45
  · wct_piece 5 1986 46
  · wct_piece 5 1988 47
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine173_ready : RoutineReady ⟨173, by decide⟩ routine173 := by
  wct_ready_start 173 5 13
  wct_cases [3351,3356,3360,2006,2011,2013,2016,2021,1320,1325,1329,945]
  · wct_piece 12 3351 14
  · wct_piece 12 3356 15
  · wct_piece 12 3360 16
  · wct_piece 5 2006 52
  · wct_piece 5 2011 53
  · wct_piece 5 2013 54
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine174_ready : RoutineReady ⟨174, by decide⟩ routine174 := by
  wct_ready_start 174 5 14
  wct_cases [3361,3366,3370,2027,2032,2034,2037,2042,2044,2048,1502,945]
  · wct_piece 12 3361 17
  · wct_piece 12 3366 18
  · wct_piece 12 3370 19
  · wct_piece 5 2027 58
  · wct_piece 5 2032 59
  · wct_piece 5 2034 60
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine175_ready : RoutineReady ⟨175, by decide⟩ routine175 := by
  wct_ready_start 175 5 15
  wct_cases [3371,3376,3381,3385,2060,1141,821,826,754,759,761,764]
  · wct_piece 12 3371 20
  · wct_piece 12 3376 21
  · wct_piece 12 3381 22
  · wct_piece 12 3385 23
  · wct_piece 6 2060 4
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine176_ready : RoutineReady ⟨176, by decide⟩ routine176 := by
  wct_ready_start 176 5 16
  wct_cases [3386,3391,3396,3400,2072,1153,835,840,843,799,804,807]
  · wct_piece 12 3386 24
  · wct_piece 12 3391 25
  · wct_piece 12 3396 26
  · wct_piece 12 3400 27
  · wct_piece 6 2072 8
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine177_ready : RoutineReady ⟨177, by decide⟩ routine177 := by
  wct_ready_start 177 5 17
  wct_cases [3401,3406,3411,3415,2084,1165,852,857,859,862,867]
  · wct_piece 12 3401 28
  · wct_piece 12 3406 29
  · wct_piece 12 3411 30
  · wct_piece 12 3415 31
  · wct_piece 6 2084 12
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine178_ready : RoutineReady ⟨178, by decide⟩ routine178 := by
  wct_ready_start 178 5 18
  wct_cases [3416,3421,3426,3430,1174,1179,1183,886,754,759,761,764]
  · wct_piece 12 3416 32
  · wct_piece 12 3421 33
  · wct_piece 12 3426 34
  · wct_piece 12 3430 35
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine179_ready : RoutineReady ⟨179, by decide⟩ routine179 := by
  wct_ready_start 179 5 19
  wct_cases [3431,3436,3441,3445,2108,1192,1197,897,902,799,804,807]
  · wct_piece 12 3431 36
  · wct_piece 12 3436 37
  · wct_piece 12 3441 38
  · wct_piece 12 3445 39
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine180_ready : RoutineReady ⟨180, by decide⟩ routine180 := by
  wct_ready_start 180 5 20
  wct_cases [3446,3451,3456,3460,2120,1206,1211,913,918,921,862,867]
  · wct_piece 12 3446 40
  · wct_piece 12 3451 41
  · wct_piece 12 3456 42
  · wct_piece 12 3460 43
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine181_ready : RoutineReady ⟨181, by decide⟩ routine181 := by
  wct_ready_start 181 5 21
  wct_cases [3461,3466,3471,3475,2132,1220,1225,932,937,939,941,945]
  · wct_piece 12 3461 44
  · wct_piece 12 3466 45
  · wct_piece 12 3471 46
  · wct_piece 12 3475 47
  · wct_piece 6 2132 28
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine182_ready : RoutineReady ⟨182, by decide⟩ routine182 := by
  wct_ready_start 182 5 22
  wct_cases [3476,3481,3486,3490,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 12 3476 48
  · wct_piece 12 3481 49
  · wct_piece 12 3486 50
  · wct_piece 12 3490 51
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine183_ready : RoutineReady ⟨183, by decide⟩ routine183 := by
  wct_ready_start 183 5 23
  wct_cases [3491,3496,3501,3505,2156,1254,1259,1262,1097,1102,862,867]
  · wct_piece 12 3491 52
  · wct_piece 12 3496 53
  · wct_piece 12 3501 54
  · wct_piece 12 3505 55
  · wct_piece 6 2156 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine184_ready : RoutineReady ⟨184, by decide⟩ routine184 := by
  wct_ready_start 184 5 24
  wct_cases [3506,3511,3516,3520,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 12 3506 56
  · wct_piece 12 3511 57
  · wct_piece 12 3516 58
  · wct_piece 12 3520 59
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine185_ready : RoutineReady ⟨185, by decide⟩ routine185 := by
  wct_ready_start 185 5 25
  wct_cases [3521,3526,3531,3535,2180,1288,1293,1295,1297,1301,862,867]
  · wct_piece 12 3521 60
  · wct_piece 12 3526 61
  · wct_piece 12 3531 62
  · wct_piece 12 3535 63
  · wct_piece 6 2180 44
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine186_ready : RoutineReady ⟨186, by decide⟩ routine186 := by
  wct_ready_start 186 5 26
  wct_cases [3536,3541,3546,3550,2192,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 13 3536 0
  · wct_piece 13 3541 1
  · wct_piece 13 3546 2
  · wct_piece 13 3550 3
  · wct_piece 6 2192 48
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine187_ready : RoutineReady ⟨187, by decide⟩ routine187 := by
  wct_ready_start 187 5 27
  wct_cases [3551,3556,3561,2201,2206,2210,1343,886,754,759,761,764]
  · wct_piece 13 3551 4
  · wct_piece 13 3556 5
  · wct_piece 13 3561 6
  · wct_piece 6 2201 51
  · wct_piece 6 2206 52
  · wct_piece 6 2210 53
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine188_ready : RoutineReady ⟨188, by decide⟩ routine188 := by
  wct_ready_start 188 5 28
  wct_cases [3562,3567,3572,2219,2224,2228,1357,897,902,799,804,807]
  · wct_piece 13 3562 7
  · wct_piece 13 3567 8
  · wct_piece 13 3572 9
  · wct_piece 6 2219 56
  · wct_piece 6 2224 57
  · wct_piece 6 2228 58
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine189_ready : RoutineReady ⟨189, by decide⟩ routine189 := by
  wct_ready_start 189 5 29
  wct_cases [3573,3578,3583,2237,2242,2246,1371,913,918,921,862,867]
  · wct_piece 13 3573 10
  · wct_piece 13 3578 11
  · wct_piece 13 3583 12
  · wct_piece 6 2237 61
  · wct_piece 6 2242 62
  · wct_piece 6 2246 63
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine190_ready : RoutineReady ⟨190, by decide⟩ routine190 := by
  wct_ready_start 190 5 30
  wct_cases [3584,3589,3594,2255,2260,2264,1385,932,937,939,941,945]
  · wct_piece 13 3584 13
  · wct_piece 13 3589 14
  · wct_piece 13 3594 15
  · wct_piece 7 2255 2
  · wct_piece 7 2260 3
  · wct_piece 7 2264 4
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine191_ready : RoutineReady ⟨191, by decide⟩ routine191 := by
  wct_ready_start 191 5 31
  wct_cases [3595,3600,3605,2273,2278,1396,1401,1405,1081,799,804,807]
  · wct_piece 13 3595 16
  · wct_piece 13 3600 17
  · wct_piece 13 3605 18
  · wct_piece 7 2273 7
  · wct_piece 7 2278 8
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
end W9Machine.Chain
end
