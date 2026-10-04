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
def routine352 : ChainRoutine := ⟨352, [1, 0, 0, 1, 1, 1, 2], [piece236336, piece236341, piece3059, piece1684, piece1689, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine353 : ChainRoutine := ⟨353, [1, 0, 0, 1, 1, 2, 1], [piece236342, piece236347, piece3069, piece1695, piece1700, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine354 : ChainRoutine := ⟨354, [1, 0, 0, 1, 1, 3, 0], [piece236348, piece236353, piece3079, piece1706, piece1711, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine355 : ChainRoutine := ⟨355, [1, 0, 0, 1, 2, 0, 2], [piece236354, piece236359, piece3089, piece3094, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine356 : ChainRoutine := ⟨356, [1, 0, 0, 1, 2, 1, 1], [piece236360, piece236365, piece3104, piece1728, piece1733, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine357 : ChainRoutine := ⟨357, [1, 0, 0, 1, 2, 2, 0], [piece236366, piece236371, piece3114, piece3119, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine358 : ChainRoutine := ⟨358, [1, 0, 0, 1, 3, 0, 1], [piece236372, piece236377, piece3129, piece1750, piece1755, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine359 : ChainRoutine := ⟨359, [1, 0, 0, 1, 3, 1, 0], [piece236378, piece236383, piece3139, piece1761, piece1766, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine360 : ChainRoutine := ⟨360, [1, 0, 0, 2, 0, 0, 3], [piece236384, piece236389, piece3149, piece1772, piece1777, piece1779, piece1783, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine361 : ChainRoutine := ⟨361, [1, 0, 0, 2, 0, 1, 2], [piece236390, piece236395, piece3159, piece3164, piece3166, piece3170, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine362 : ChainRoutine := ⟨362, [1, 0, 0, 2, 0, 2, 1], [piece236396, piece236401, piece3180, piece3185, piece3187, piece3191, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine363 : ChainRoutine := ⟨363, [1, 0, 0, 2, 0, 3, 0], [piece236402, piece236407, piece3201, piece1823, piece1828, piece1830, piece1834, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine364 : ChainRoutine := ⟨364, [1, 0, 0, 2, 1, 0, 2], [piece236408, piece236413, piece3211, piece3216, piece3219, piece3224, piece3228, piece1081, piece799, piece804, piece807]⟩
def routine365 : ChainRoutine := ⟨365, [1, 0, 0, 2, 1, 1, 1], [piece236414, piece236419, piece3238, piece1854, piece1859, piece1862, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine366 : ChainRoutine := ⟨366, [1, 0, 0, 2, 1, 2, 0], [piece236420, piece236425, piece3248, piece3253, piece3256, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine367 : ChainRoutine := ⟨367, [1, 0, 0, 2, 2, 0, 1], [piece236426, piece236431, piece3266, piece3271, piece3274, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine368 : ChainRoutine := ⟨368, [1, 0, 0, 2, 2, 1, 0], [piece236432, piece236437, piece3284, piece3289, piece3292, piece3297, piece3300, piece1320, piece1325, piece1329, piece945]⟩
def routine369 : ChainRoutine := ⟨369, [1, 0, 0, 2, 3, 0, 0], [piece236438, piece236443, piece3310, piece1910, piece1915, piece1918, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine370 : ChainRoutine := ⟨370, [1, 0, 0, 3, 0, 0, 2], [piece236444, piece236449, piece3320, piece1924, piece1929, piece1931, piece1933, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine371 : ChainRoutine := ⟨371, [1, 0, 0, 3, 0, 1, 1], [piece236450, piece236455, piece3330, piece1943, piece1948, piece1950, piece1952, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine372 : ChainRoutine := ⟨372, [1, 0, 0, 3, 0, 2, 0], [piece236456, piece236461, piece3340, piece1962, piece1967, piece1969, piece1971, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine373 : ChainRoutine := ⟨373, [1, 0, 0, 3, 1, 0, 1], [piece236462, piece236467, piece3350, piece1981, piece1986, piece1988, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine374 : ChainRoutine := ⟨374, [1, 0, 0, 3, 1, 1, 0], [piece236468, piece236473, piece3360, piece2006, piece2011, piece2013, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine375 : ChainRoutine := ⟨375, [1, 0, 0, 3, 2, 0, 0], [piece236474, piece236479, piece3370, piece2027, piece2032, piece2034, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine376 : ChainRoutine := ⟨376, [1, 0, 1, 0, 0, 1, 3], [piece236480, piece236485, piece3376, piece3381, piece3385, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine377 : ChainRoutine := ⟨377, [1, 0, 1, 0, 0, 2, 2], [piece236486, piece236491, piece3391, piece3396, piece3400, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine378 : ChainRoutine := ⟨378, [1, 0, 1, 0, 0, 3, 1], [piece236492, piece236497, piece3406, piece3411, piece3415, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine379 : ChainRoutine := ⟨379, [1, 0, 1, 0, 1, 0, 3], [piece236498, piece236503, piece236508, piece236512, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine380 : ChainRoutine := ⟨380, [1, 0, 1, 0, 1, 1, 2], [piece236513, piece236518, piece236523, piece236527, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine381 : ChainRoutine := ⟨381, [1, 0, 1, 0, 1, 2, 1], [piece236528, piece236533, piece236538, piece236542, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine382 : ChainRoutine := ⟨382, [1, 0, 1, 0, 1, 3, 0], [piece236543, piece236548, piece3466, piece3471, piece3475, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine383 : ChainRoutine := ⟨383, [1, 0, 1, 0, 2, 0, 2], [piece236549, piece236554, piece236559, piece236563, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routineBatch11 : List ChainRoutine := [routine352, routine353, routine354, routine355, routine356, routine357, routine358, routine359, routine360, routine361, routine362, routine363, routine364, routine365, routine366, routine367, routine368, routine369, routine370, routine371, routine372, routine373, routine374, routine375, routine376, routine377, routine378, routine379, routine380, routine381, routine382, routine383]
theorem routineBatch11_checked : (routineBatch11.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch11_checked :
    (routineBatch11.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch11_checked :
    (routineBatch11.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine352_ready : RoutineReady ⟨352, by decide⟩ routine352 := by
  wct_ready_start 352 11 0
  wct_cases [236336,236341,3059,1684,1689,1192,1197,897,902,799,804,807]
  · wct_piece 25 236336 5
  · wct_piece 25 236341 6
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
theorem routine353_ready : RoutineReady ⟨353, by decide⟩ routine353 := by
  wct_ready_start 353 11 1
  wct_cases [236342,236347,3069,1695,1700,1206,1211,913,918,921,862,867]
  · wct_piece 25 236342 7
  · wct_piece 25 236347 8
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
theorem routine354_ready : RoutineReady ⟨354, by decide⟩ routine354 := by
  wct_ready_start 354 11 2
  wct_cases [236348,236353,3079,1706,1711,1220,1225,932,937,939,941,945]
  · wct_piece 25 236348 9
  · wct_piece 25 236353 10
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
theorem routine355_ready : RoutineReady ⟨355, by decide⟩ routine355 := by
  wct_ready_start 355 11 3
  wct_cases [236354,236359,3089,3094,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 25 236354 11
  · wct_piece 25 236359 12
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
theorem routine356_ready : RoutineReady ⟨356, by decide⟩ routine356 := by
  wct_ready_start 356 11 4
  wct_cases [236360,236365,3104,1728,1733,1254,1259,1262,1097,1102,862,867]
  · wct_piece 25 236360 13
  · wct_piece 25 236365 14
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
theorem routine357_ready : RoutineReady ⟨357, by decide⟩ routine357 := by
  wct_ready_start 357 11 5
  wct_cases [236366,236371,3114,3119,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 25 236366 15
  · wct_piece 25 236371 16
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
theorem routine358_ready : RoutineReady ⟨358, by decide⟩ routine358 := by
  wct_ready_start 358 11 6
  wct_cases [236372,236377,3129,1750,1755,1288,1293,1295,1297,1301,862,867]
  · wct_piece 25 236372 17
  · wct_piece 25 236377 18
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
theorem routine359_ready : RoutineReady ⟨359, by decide⟩ routine359 := by
  wct_ready_start 359 11 7
  wct_cases [236378,236383,3139,1761,1766,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 25 236378 19
  · wct_piece 25 236383 20
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
theorem routine360_ready : RoutineReady ⟨360, by decide⟩ routine360 := by
  wct_ready_start 360 11 8
  wct_cases [236384,236389,3149,1772,1777,1779,1783,1343,886,754,759,761,764]
  · wct_piece 25 236384 21
  · wct_piece 25 236389 22
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
theorem routine361_ready : RoutineReady ⟨361, by decide⟩ routine361 := by
  wct_ready_start 361 11 9
  wct_cases [236390,236395,3159,3164,3166,3170,1357,897,902,799,804,807]
  · wct_piece 25 236390 23
  · wct_piece 25 236395 24
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
theorem routine362_ready : RoutineReady ⟨362, by decide⟩ routine362 := by
  wct_ready_start 362 11 10
  wct_cases [236396,236401,3180,3185,3187,3191,1371,913,918,921,862,867]
  · wct_piece 25 236396 25
  · wct_piece 25 236401 26
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
theorem routine363_ready : RoutineReady ⟨363, by decide⟩ routine363 := by
  wct_ready_start 363 11 11
  wct_cases [236402,236407,3201,1823,1828,1830,1834,1385,932,937,939,941,945]
  · wct_piece 25 236402 27
  · wct_piece 25 236407 28
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
theorem routine364_ready : RoutineReady ⟨364, by decide⟩ routine364 := by
  wct_ready_start 364 11 12
  wct_cases [236408,236413,3211,3216,3219,3224,3228,1081,799,804,807]
  · wct_piece 25 236408 29
  · wct_piece 25 236413 30
  · wct_piece 11 3211 38
  · wct_piece 11 3216 39
  · wct_piece 11 3219 40
  · wct_piece 11 3224 41
  · wct_piece 11 3228 42
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine365_ready : RoutineReady ⟨365, by decide⟩ routine365 := by
  wct_ready_start 365 11 13
  wct_cases [236414,236419,3238,1854,1859,1862,1416,1421,1097,1102,862,867]
  · wct_piece 25 236414 31
  · wct_piece 25 236419 32
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
theorem routine366_ready : RoutineReady ⟨366, by decide⟩ routine366 := by
  wct_ready_start 366 11 14
  wct_cases [236420,236425,3248,3253,3256,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 25 236420 33
  · wct_piece 25 236425 34
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
theorem routine367_ready : RoutineReady ⟨367, by decide⟩ routine367 := by
  wct_ready_start 367 11 15
  wct_cases [236426,236431,3266,3271,3274,1448,1453,1455,1459,1301,862,867]
  · wct_piece 25 236426 35
  · wct_piece 25 236431 36
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
theorem routine368_ready : RoutineReady ⟨368, by decide⟩ routine368 := by
  wct_ready_start 368 11 16
  wct_cases [236432,236437,3284,3289,3292,3297,3300,1320,1325,1329,945]
  · wct_piece 25 236432 37
  · wct_piece 25 236437 38
  · wct_piece 11 3284 58
  · wct_piece 11 3289 59
  · wct_piece 11 3292 60
  · wct_piece 11 3297 61
  · wct_piece 11 3300 62
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine369_ready : RoutineReady ⟨369, by decide⟩ routine369 := by
  wct_ready_start 369 11 17
  wct_cases [236438,236443,3310,1910,1915,1918,1489,1494,1496,1498,1502,945]
  · wct_piece 25 236438 39
  · wct_piece 25 236443 40
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
theorem routine370_ready : RoutineReady ⟨370, by decide⟩ routine370 := by
  wct_ready_start 370 11 18
  wct_cases [236444,236449,3320,1924,1929,1931,1933,1937,1081,799,804,807]
  · wct_piece 25 236444 41
  · wct_piece 25 236449 42
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
theorem routine371_ready : RoutineReady ⟨371, by decide⟩ routine371 := by
  wct_ready_start 371 11 19
  wct_cases [236450,236455,3330,1943,1948,1950,1952,1956,1097,1102,862,867]
  · wct_piece 25 236450 43
  · wct_piece 25 236455 44
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
theorem routine372_ready : RoutineReady ⟨372, by decide⟩ routine372 := by
  wct_ready_start 372 11 20
  wct_cases [236456,236461,3340,1962,1967,1969,1971,1975,1118,1123,1125,1129,945]
  · wct_piece 25 236456 45
  · wct_piece 25 236461 46
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
theorem routine373_ready : RoutineReady ⟨373, by decide⟩ routine373 := by
  wct_ready_start 373 11 21
  wct_cases [236462,236467,3350,1981,1986,1988,1991,1996,2000,1301,862,867]
  · wct_piece 25 236462 47
  · wct_piece 25 236467 48
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
theorem routine374_ready : RoutineReady ⟨374, by decide⟩ routine374 := by
  wct_ready_start 374 11 22
  wct_cases [236468,236473,3360,2006,2011,2013,2016,2021,1320,1325,1329,945]
  · wct_piece 25 236468 49
  · wct_piece 25 236473 50
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
theorem routine375_ready : RoutineReady ⟨375, by decide⟩ routine375 := by
  wct_ready_start 375 11 23
  wct_cases [236474,236479,3370,2027,2032,2034,2037,2042,2044,2048,1502,945]
  · wct_piece 25 236474 51
  · wct_piece 25 236479 52
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
theorem routine376_ready : RoutineReady ⟨376, by decide⟩ routine376 := by
  wct_ready_start 376 11 24
  wct_cases [236480,236485,3376,3381,3385,2060,1141,821,826,754,759,761,764]
  · wct_piece 25 236480 53
  · wct_piece 25 236485 54
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
theorem routine377_ready : RoutineReady ⟨377, by decide⟩ routine377 := by
  wct_ready_start 377 11 25
  wct_cases [236486,236491,3391,3396,3400,2072,1153,835,840,843,799,804,807]
  · wct_piece 25 236486 55
  · wct_piece 25 236491 56
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
theorem routine378_ready : RoutineReady ⟨378, by decide⟩ routine378 := by
  wct_ready_start 378 11 26
  wct_cases [236492,236497,3406,3411,3415,2084,1165,852,857,859,862,867]
  · wct_piece 25 236492 57
  · wct_piece 25 236497 58
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
theorem routine379_ready : RoutineReady ⟨379, by decide⟩ routine379 := by
  wct_ready_start 379 11 27
  wct_cases [236498,236503,236508,236512,1174,1179,1183,886,754,759,761,764]
  · wct_piece 25 236498 59
  · wct_piece 25 236503 60
  · wct_piece 25 236508 61
  · wct_piece 25 236512 62
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine380_ready : RoutineReady ⟨380, by decide⟩ routine380 := by
  wct_ready_start 380 11 28
  wct_cases [236513,236518,236523,236527,2108,1192,1197,897,902,799,804,807]
  · wct_piece 25 236513 63
  · wct_piece 26 236518 0
  · wct_piece 26 236523 1
  · wct_piece 26 236527 2
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine381_ready : RoutineReady ⟨381, by decide⟩ routine381 := by
  wct_ready_start 381 11 29
  wct_cases [236528,236533,236538,236542,2120,1206,1211,913,918,921,862,867]
  · wct_piece 26 236528 3
  · wct_piece 26 236533 4
  · wct_piece 26 236538 5
  · wct_piece 26 236542 6
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine382_ready : RoutineReady ⟨382, by decide⟩ routine382 := by
  wct_ready_start 382 11 30
  wct_cases [236543,236548,3466,3471,3475,2132,1220,1225,932,937,939,941,945]
  · wct_piece 26 236543 7
  · wct_piece 26 236548 8
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
theorem routine383_ready : RoutineReady ⟨383, by decide⟩ routine383 := by
  wct_ready_start 383 11 31
  wct_cases [236549,236554,236559,236563,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 26 236549 9
  · wct_piece 26 236554 10
  · wct_piece 26 236559 11
  · wct_piece 26 236563 12
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage11 (rank : Fin 728) (hlo : 352 ≤ rank.val) (hhi : rank.val < 384) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 352 ≤ n at hlo
  change n < 384 at hhi
  interval_cases n
  · exact ⟨routine352, routine352_ready⟩
  · exact ⟨routine353, routine353_ready⟩
  · exact ⟨routine354, routine354_ready⟩
  · exact ⟨routine355, routine355_ready⟩
  · exact ⟨routine356, routine356_ready⟩
  · exact ⟨routine357, routine357_ready⟩
  · exact ⟨routine358, routine358_ready⟩
  · exact ⟨routine359, routine359_ready⟩
  · exact ⟨routine360, routine360_ready⟩
  · exact ⟨routine361, routine361_ready⟩
  · exact ⟨routine362, routine362_ready⟩
  · exact ⟨routine363, routine363_ready⟩
  · exact ⟨routine364, routine364_ready⟩
  · exact ⟨routine365, routine365_ready⟩
  · exact ⟨routine366, routine366_ready⟩
  · exact ⟨routine367, routine367_ready⟩
  · exact ⟨routine368, routine368_ready⟩
  · exact ⟨routine369, routine369_ready⟩
  · exact ⟨routine370, routine370_ready⟩
  · exact ⟨routine371, routine371_ready⟩
  · exact ⟨routine372, routine372_ready⟩
  · exact ⟨routine373, routine373_ready⟩
  · exact ⟨routine374, routine374_ready⟩
  · exact ⟨routine375, routine375_ready⟩
  · exact ⟨routine376, routine376_ready⟩
  · exact ⟨routine377, routine377_ready⟩
  · exact ⟨routine378, routine378_ready⟩
  · exact ⟨routine379, routine379_ready⟩
  · exact ⟨routine380, routine380_ready⟩
  · exact ⟨routine381, routine381_ready⟩
  · exact ⟨routine382, routine382_ready⟩
  · exact ⟨routine383, routine383_ready⟩
end W9Machine.Chain
end
