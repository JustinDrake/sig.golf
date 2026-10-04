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
def routine320 : ChainRoutine := ⟨320, [0, 3, 0, 3, 0, 0, 0], [piece235924, piece235929, piece235931, piece235933, piece235937, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine321 : ChainRoutine := ⟨321, [0, 3, 1, 0, 0, 0, 2], [piece235938, piece235943, piece235945, piece235948, piece235953, piece235957, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine322 : ChainRoutine := ⟨322, [0, 3, 1, 0, 0, 1, 1], [piece235958, piece235963, piece235965, piece235968, piece235973, piece235977, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine323 : ChainRoutine := ⟨323, [0, 3, 1, 0, 0, 2, 0], [piece235978, piece235983, piece235985, piece235988, piece235993, piece235997, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine324 : ChainRoutine := ⟨324, [0, 3, 1, 0, 1, 0, 1], [piece235998, piece236003, piece236005, piece236008, piece236013, piece236017, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine325 : ChainRoutine := ⟨325, [0, 3, 1, 0, 1, 1, 0], [piece236018, piece236023, piece236025, piece236028, piece236033, piece236037, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine326 : ChainRoutine := ⟨326, [0, 3, 1, 0, 2, 0, 0], [piece236038, piece236043, piece236045, piece236048, piece236053, piece236057, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine327 : ChainRoutine := ⟨327, [0, 3, 1, 1, 0, 0, 1], [piece236058, piece236063, piece236065, piece236068, piece236073, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine328 : ChainRoutine := ⟨328, [0, 3, 1, 1, 0, 1, 0], [piece236074, piece236079, piece236081, piece236084, piece236089, piece236094, piece236098, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine329 : ChainRoutine := ⟨329, [0, 3, 1, 1, 1, 0, 0], [piece236099, piece236104, piece236106, piece236109, piece236114, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine330 : ChainRoutine := ⟨330, [0, 3, 1, 2, 0, 0, 0], [piece236115, piece236120, piece236122, piece236125, piece236130, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine331 : ChainRoutine := ⟨331, [0, 3, 2, 0, 0, 0, 1], [piece236131, piece236136, piece236138, piece236141, piece236146, piece236148, piece236152, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine332 : ChainRoutine := ⟨332, [0, 3, 2, 0, 0, 1, 0], [piece236153, piece236158, piece236160, piece236163, piece236168, piece236170, piece236174, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine333 : ChainRoutine := ⟨333, [0, 3, 2, 0, 1, 0, 0], [piece236175, piece236180, piece236182, piece236185, piece236190, piece236192, piece236196, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine334 : ChainRoutine := ⟨334, [0, 3, 2, 1, 0, 0, 0], [piece236197, piece236202, piece236204, piece236207, piece236212, piece236215, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine335 : ChainRoutine := ⟨335, [0, 3, 3, 0, 0, 0, 0], [piece236216, piece236221, piece236223, piece236226, piece236231, piece236233, piece236235, piece236239, piece2866, piece1502, piece945]⟩
def routine336 : ChainRoutine := ⟨336, [1, 0, 0, 0, 0, 2, 3], [piece236240, piece236245, piece2876, piece1512, piece960, piece775, piece780, piece783, piece754, piece759, piece761, piece764]⟩
def routine337 : ChainRoutine := ⟨337, [1, 0, 0, 0, 0, 3, 2], [piece236246, piece236251, piece2886, piece1522, piece970, piece789, piece794, piece796, piece799, piece804, piece807]⟩
def routine338 : ChainRoutine := ⟨338, [1, 0, 0, 0, 1, 1, 3], [piece236252, piece236257, piece2896, piece1532, piece976, piece981, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine339 : ChainRoutine := ⟨339, [1, 0, 0, 0, 1, 2, 2], [piece236258, piece236263, piece2906, piece1542, piece987, piece992, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine340 : ChainRoutine := ⟨340, [1, 0, 0, 0, 1, 3, 1], [piece236264, piece236269, piece2916, piece1552, piece998, piece1003, piece852, piece857, piece859, piece862, piece867]⟩
def routine341 : ChainRoutine := ⟨341, [1, 0, 0, 0, 2, 0, 3], [piece236270, piece236275, piece2926, piece1562, piece1009, piece1014, piece1016, piece1020, piece886, piece754, piece759, piece761, piece764]⟩
def routine342 : ChainRoutine := ⟨342, [1, 0, 0, 0, 2, 1, 2], [piece236276, piece236281, piece2936, piece1572, piece1026, piece1031, piece1034, piece897, piece902, piece799, piece804, piece807]⟩
def routine343 : ChainRoutine := ⟨343, [1, 0, 0, 0, 2, 2, 1], [piece236282, piece236287, piece2946, piece1582, piece1040, piece1045, piece1048, piece913, piece918, piece921, piece862, piece867]⟩
def routine344 : ChainRoutine := ⟨344, [1, 0, 0, 0, 2, 3, 0], [piece236288, piece236293, piece2956, piece1592, piece1054, piece1059, piece1062, piece932, piece937, piece939, piece941, piece945]⟩
def routine345 : ChainRoutine := ⟨345, [1, 0, 0, 0, 3, 0, 2], [piece236294, piece236299, piece2966, piece1602, piece1068, piece1073, piece1075, piece1077, piece1081, piece799, piece804, piece807]⟩
def routine346 : ChainRoutine := ⟨346, [1, 0, 0, 0, 3, 1, 1], [piece236300, piece236305, piece2976, piece1612, piece1087, piece1092, piece1094, piece1097, piece1102, piece862, piece867]⟩
def routine347 : ChainRoutine := ⟨347, [1, 0, 0, 0, 3, 2, 0], [piece236306, piece236311, piece2986, piece1622, piece1108, piece1113, piece1115, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine348 : ChainRoutine := ⟨348, [1, 0, 0, 1, 0, 1, 3], [piece236312, piece236317, piece2996, piece3001, piece3005, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine349 : ChainRoutine := ⟨349, [1, 0, 0, 1, 0, 2, 2], [piece236318, piece236323, piece3015, piece3020, piece3024, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine350 : ChainRoutine := ⟨350, [1, 0, 0, 1, 0, 3, 1], [piece236324, piece236329, piece3034, piece1658, piece1663, piece1667, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine351 : ChainRoutine := ⟨351, [1, 0, 0, 1, 1, 0, 3], [piece236330, piece236335, piece3044, piece3049, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routineBatch10 : List ChainRoutine := [routine320, routine321, routine322, routine323, routine324, routine325, routine326, routine327, routine328, routine329, routine330, routine331, routine332, routine333, routine334, routine335, routine336, routine337, routine338, routine339, routine340, routine341, routine342, routine343, routine344, routine345, routine346, routine347, routine348, routine349, routine350, routine351]
theorem routineBatch10_checked : (routineBatch10.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch10_checked :
    (routineBatch10.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch10_checked :
    (routineBatch10.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine320_ready : RoutineReady ⟨320, by decide⟩ routine320 := by
  wct_ready_start 320 10 0
  wct_cases [235924,235929,235931,235933,235937,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 23 235924 3
  · wct_piece 23 235929 4
  · wct_piece 23 235931 5
  · wct_piece 23 235933 6
  · wct_piece 23 235937 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine321_ready : RoutineReady ⟨321, by decide⟩ routine321 := by
  wct_ready_start 321 10 1
  wct_cases [235938,235943,235945,235948,235953,235957,4108,1937,1081,799,804,807]
  · wct_piece 23 235938 8
  · wct_piece 23 235943 9
  · wct_piece 23 235945 10
  · wct_piece 23 235948 11
  · wct_piece 23 235953 12
  · wct_piece 23 235957 13
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine322_ready : RoutineReady ⟨322, by decide⟩ routine322 := by
  wct_ready_start 322 10 2
  wct_cases [235958,235963,235965,235968,235973,235977,4127,1956,1097,1102,862,867]
  · wct_piece 23 235958 14
  · wct_piece 23 235963 15
  · wct_piece 23 235965 16
  · wct_piece 23 235968 17
  · wct_piece 23 235973 18
  · wct_piece 23 235977 19
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine323_ready : RoutineReady ⟨323, by decide⟩ routine323 := by
  wct_ready_start 323 10 3
  wct_cases [235978,235983,235985,235988,235993,235997,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 23 235978 20
  · wct_piece 23 235983 21
  · wct_piece 23 235985 22
  · wct_piece 23 235988 23
  · wct_piece 23 235993 24
  · wct_piece 23 235997 25
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine324_ready : RoutineReady ⟨324, by decide⟩ routine324 := by
  wct_ready_start 324 10 4
  wct_cases [235998,236003,236005,236008,236013,236017,1991,1996,2000,1301,862,867]
  · wct_piece 23 235998 26
  · wct_piece 23 236003 27
  · wct_piece 23 236005 28
  · wct_piece 23 236008 29
  · wct_piece 23 236013 30
  · wct_piece 23 236017 31
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine325_ready : RoutineReady ⟨325, by decide⟩ routine325 := by
  wct_ready_start 325 10 5
  wct_cases [236018,236023,236025,236028,236033,236037,2016,2021,1320,1325,1329,945]
  · wct_piece 23 236018 32
  · wct_piece 23 236023 33
  · wct_piece 23 236025 34
  · wct_piece 23 236028 35
  · wct_piece 23 236033 36
  · wct_piece 23 236037 37
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine326_ready : RoutineReady ⟨326, by decide⟩ routine326 := by
  wct_ready_start 326 10 6
  wct_cases [236038,236043,236045,236048,236053,236057,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 23 236038 38
  · wct_piece 23 236043 39
  · wct_piece 23 236045 40
  · wct_piece 23 236048 41
  · wct_piece 23 236053 42
  · wct_piece 23 236057 43
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine327_ready : RoutineReady ⟨327, by decide⟩ routine327 := by
  wct_ready_start 327 10 7
  wct_cases [236058,236063,236065,236068,236073,4219,4224,4228,2481,1301,862,867]
  · wct_piece 23 236058 44
  · wct_piece 23 236063 45
  · wct_piece 23 236065 46
  · wct_piece 23 236068 47
  · wct_piece 23 236073 48
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine328_ready : RoutineReady ⟨328, by decide⟩ routine328 := by
  wct_ready_start 328 10 8
  wct_cases [236074,236079,236081,236084,236089,236094,236098,2503,1320,1325,1329,945]
  · wct_piece 23 236074 49
  · wct_piece 23 236079 50
  · wct_piece 23 236081 51
  · wct_piece 23 236084 52
  · wct_piece 23 236089 53
  · wct_piece 23 236094 54
  · wct_piece 23 236098 55
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine329_ready : RoutineReady ⟨329, by decide⟩ routine329 := by
  wct_ready_start 329 10 9
  wct_cases [236099,236104,236106,236109,236114,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 23 236099 56
  · wct_piece 23 236104 57
  · wct_piece 23 236106 58
  · wct_piece 23 236109 59
  · wct_piece 23 236114 60
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine330_ready : RoutineReady ⟨330, by decide⟩ routine330 := by
  wct_ready_start 330 10 10
  wct_cases [236115,236120,236122,236125,236130,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 23 236115 61
  · wct_piece 23 236120 62
  · wct_piece 23 236122 63
  · wct_piece 24 236125 0
  · wct_piece 24 236130 1
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine331_ready : RoutineReady ⟨331, by decide⟩ routine331 := by
  wct_ready_start 331 10 11
  wct_cases [236131,236136,236138,236141,236146,236148,236152,235565,2481,1301,862,867]
  · wct_piece 24 236131 2
  · wct_piece 24 236136 3
  · wct_piece 24 236138 4
  · wct_piece 24 236141 5
  · wct_piece 24 236146 6
  · wct_piece 24 236148 7
  · wct_piece 24 236152 8
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine332_ready : RoutineReady ⟨332, by decide⟩ routine332 := by
  wct_ready_start 332 10 12
  wct_cases [236153,236158,236160,236163,236168,236170,236174,235587,2503,1320,1325,1329,945]
  · wct_piece 24 236153 9
  · wct_piece 24 236158 10
  · wct_piece 24 236160 11
  · wct_piece 24 236163 12
  · wct_piece 24 236168 13
  · wct_piece 24 236170 14
  · wct_piece 24 236174 15
  · wct_piece 21 235587 15
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine333_ready : RoutineReady ⟨333, by decide⟩ routine333 := by
  wct_ready_start 333 10 13
  wct_cases [236175,236180,236182,236185,236190,236192,236196,235609,2522,2527,2531,1502,945]
  · wct_piece 24 236175 16
  · wct_piece 24 236180 17
  · wct_piece 24 236182 18
  · wct_piece 24 236185 19
  · wct_piece 24 236190 20
  · wct_piece 24 236192 21
  · wct_piece 24 236196 22
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine334_ready : RoutineReady ⟨334, by decide⟩ routine334 := by
  wct_ready_start 334 10 14
  wct_cases [236197,236202,236204,236207,236212,236215,235628,235633,235637,2866,1502,945]
  · wct_piece 24 236197 23
  · wct_piece 24 236202 24
  · wct_piece 24 236204 25
  · wct_piece 24 236207 26
  · wct_piece 24 236212 27
  · wct_piece 24 236215 28
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine335_ready : RoutineReady ⟨335, by decide⟩ routine335 := by
  wct_ready_start 335 10 15
  wct_cases [236216,236221,236223,236226,236231,236233,236235,236239,2866,1502,945]
  · wct_piece 24 236216 29
  · wct_piece 24 236221 30
  · wct_piece 24 236223 31
  · wct_piece 24 236226 32
  · wct_piece 24 236231 33
  · wct_piece 24 236233 34
  · wct_piece 24 236235 35
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine336_ready : RoutineReady ⟨336, by decide⟩ routine336 := by
  wct_ready_start 336 10 16
  wct_cases [236240,236245,2876,1512,960,775,780,783,754,759,761,764]
  · wct_piece 24 236240 37
  · wct_piece 24 236245 38
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
theorem routine337_ready : RoutineReady ⟨337, by decide⟩ routine337 := by
  wct_ready_start 337 10 17
  wct_cases [236246,236251,2886,1522,970,789,794,796,799,804,807]
  · wct_piece 24 236246 39
  · wct_piece 24 236251 40
  · wct_piece 10 2886 8
  · wct_piece 3 1522 40
  · wct_piece 0 970 63
  · wct_piece 0 789 12
  · wct_piece 0 794 13
  · wct_piece 0 796 14
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine338_ready : RoutineReady ⟨338, by decide⟩ routine338 := by
  wct_ready_start 338 10 18
  wct_cases [236252,236257,2896,1532,976,981,821,826,754,759,761,764]
  · wct_piece 24 236252 41
  · wct_piece 24 236257 42
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
theorem routine339_ready : RoutineReady ⟨339, by decide⟩ routine339 := by
  wct_ready_start 339 10 19
  wct_cases [236258,236263,2906,1542,987,992,835,840,843,799,804,807]
  · wct_piece 24 236258 43
  · wct_piece 24 236263 44
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
theorem routine340_ready : RoutineReady ⟨340, by decide⟩ routine340 := by
  wct_ready_start 340 10 20
  wct_cases [236264,236269,2916,1552,998,1003,852,857,859,862,867]
  · wct_piece 24 236264 45
  · wct_piece 24 236269 46
  · wct_piece 10 2916 17
  · wct_piece 3 1552 49
  · wct_piece 1 998 7
  · wct_piece 1 1003 8
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine341_ready : RoutineReady ⟨341, by decide⟩ routine341 := by
  wct_ready_start 341 10 21
  wct_cases [236270,236275,2926,1562,1009,1014,1016,1020,886,754,759,761,764]
  · wct_piece 24 236270 47
  · wct_piece 24 236275 48
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
theorem routine342_ready : RoutineReady ⟨342, by decide⟩ routine342 := by
  wct_ready_start 342 10 22
  wct_cases [236276,236281,2936,1572,1026,1031,1034,897,902,799,804,807]
  · wct_piece 24 236276 49
  · wct_piece 24 236281 50
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
theorem routine343_ready : RoutineReady ⟨343, by decide⟩ routine343 := by
  wct_ready_start 343 10 23
  wct_cases [236282,236287,2946,1582,1040,1045,1048,913,918,921,862,867]
  · wct_piece 24 236282 51
  · wct_piece 24 236287 52
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
theorem routine344_ready : RoutineReady ⟨344, by decide⟩ routine344 := by
  wct_ready_start 344 10 24
  wct_cases [236288,236293,2956,1592,1054,1059,1062,932,937,939,941,945]
  · wct_piece 24 236288 53
  · wct_piece 24 236293 54
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
theorem routine345_ready : RoutineReady ⟨345, by decide⟩ routine345 := by
  wct_ready_start 345 10 25
  wct_cases [236294,236299,2966,1602,1068,1073,1075,1077,1081,799,804,807]
  · wct_piece 24 236294 55
  · wct_piece 24 236299 56
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
theorem routine346_ready : RoutineReady ⟨346, by decide⟩ routine346 := by
  wct_ready_start 346 10 26
  wct_cases [236300,236305,2976,1612,1087,1092,1094,1097,1102,862,867]
  · wct_piece 24 236300 57
  · wct_piece 24 236305 58
  · wct_piece 10 2976 35
  · wct_piece 4 1612 3
  · wct_piece 1 1087 33
  · wct_piece 1 1092 34
  · wct_piece 1 1094 35
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine347_ready : RoutineReady ⟨347, by decide⟩ routine347 := by
  wct_ready_start 347 10 27
  wct_cases [236306,236311,2986,1622,1108,1113,1115,1118,1123,1125,1129,945]
  · wct_piece 24 236306 59
  · wct_piece 24 236311 60
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
theorem routine348_ready : RoutineReady ⟨348, by decide⟩ routine348 := by
  wct_ready_start 348 10 28
  wct_cases [236312,236317,2996,3001,3005,1141,821,826,754,759,761,764]
  · wct_piece 24 236312 61
  · wct_piece 24 236317 62
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
theorem routine349_ready : RoutineReady ⟨349, by decide⟩ routine349 := by
  wct_ready_start 349 10 29
  wct_cases [236318,236323,3015,3020,3024,835,840,843,799,804,807]
  · wct_piece 24 236318 63
  · wct_piece 25 236323 0
  · wct_piece 10 3015 46
  · wct_piece 10 3020 47
  · wct_piece 10 3024 48
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine350_ready : RoutineReady ⟨350, by decide⟩ routine350 := by
  wct_ready_start 350 10 30
  wct_cases [236324,236329,3034,1658,1663,1667,1165,852,857,859,862,867]
  · wct_piece 25 236324 1
  · wct_piece 25 236329 2
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
theorem routine351_ready : RoutineReady ⟨351, by decide⟩ routine351 := by
  wct_ready_start 351 10 31
  wct_cases [236330,236335,3044,3049,1174,1179,1183,886,754,759,761,764]
  · wct_piece 25 236330 3
  · wct_piece 25 236335 4
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
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage10 (rank : Fin 728) (hlo : 320 ≤ rank.val) (hhi : rank.val < 352) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 320 ≤ n at hlo
  change n < 352 at hhi
  interval_cases n
  · exact ⟨routine320, routine320_ready⟩
  · exact ⟨routine321, routine321_ready⟩
  · exact ⟨routine322, routine322_ready⟩
  · exact ⟨routine323, routine323_ready⟩
  · exact ⟨routine324, routine324_ready⟩
  · exact ⟨routine325, routine325_ready⟩
  · exact ⟨routine326, routine326_ready⟩
  · exact ⟨routine327, routine327_ready⟩
  · exact ⟨routine328, routine328_ready⟩
  · exact ⟨routine329, routine329_ready⟩
  · exact ⟨routine330, routine330_ready⟩
  · exact ⟨routine331, routine331_ready⟩
  · exact ⟨routine332, routine332_ready⟩
  · exact ⟨routine333, routine333_ready⟩
  · exact ⟨routine334, routine334_ready⟩
  · exact ⟨routine335, routine335_ready⟩
  · exact ⟨routine336, routine336_ready⟩
  · exact ⟨routine337, routine337_ready⟩
  · exact ⟨routine338, routine338_ready⟩
  · exact ⟨routine339, routine339_ready⟩
  · exact ⟨routine340, routine340_ready⟩
  · exact ⟨routine341, routine341_ready⟩
  · exact ⟨routine342, routine342_ready⟩
  · exact ⟨routine343, routine343_ready⟩
  · exact ⟨routine344, routine344_ready⟩
  · exact ⟨routine345, routine345_ready⟩
  · exact ⟨routine346, routine346_ready⟩
  · exact ⟨routine347, routine347_ready⟩
  · exact ⟨routine348, routine348_ready⟩
  · exact ⟨routine349, routine349_ready⟩
  · exact ⟨routine350, routine350_ready⟩
  · exact ⟨routine351, routine351_ready⟩
end W9Machine.Chain
end
