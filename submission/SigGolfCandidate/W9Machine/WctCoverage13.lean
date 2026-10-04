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
def routine416 : ChainRoutine := ⟨416, [1, 0, 2, 0, 3, 0, 0], [piece236862, piece236867, piece3918, piece3923, piece3925, piece3929, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine417 : ChainRoutine := ⟨417, [1, 0, 2, 1, 0, 0, 2], [piece236868, piece236873, piece3935, piece3940, piece3943, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine418 : ChainRoutine := ⟨418, [1, 0, 2, 1, 0, 1, 1], [piece236874, piece236879, piece236884, piece236887, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine419 : ChainRoutine := ⟨419, [1, 0, 2, 1, 0, 2, 0], [piece236888, piece236893, piece236898, piece236901, piece236906, piece236910, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine420 : ChainRoutine := ⟨420, [1, 0, 2, 1, 1, 0, 1], [piece236911, piece236916, piece236921, piece236924, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine421 : ChainRoutine := ⟨421, [1, 0, 2, 1, 1, 1, 0], [piece236925, piece236930, piece236935, piece236938, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine422 : ChainRoutine := ⟨422, [1, 0, 2, 1, 2, 0, 0], [piece236939, piece236944, piece4014, piece4019, piece4022, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine423 : ChainRoutine := ⟨423, [1, 0, 2, 2, 0, 0, 1], [piece236945, piece236950, piece4028, piece4033, piece4036, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine424 : ChainRoutine := ⟨424, [1, 0, 2, 2, 0, 1, 0], [piece236951, piece236956, piece236961, piece236964, piece236969, piece236971, piece236975, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine425 : ChainRoutine := ⟨425, [1, 0, 2, 2, 1, 0, 0], [piece236976, piece236981, piece4067, piece4072, piece4075, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine426 : ChainRoutine := ⟨426, [1, 0, 2, 3, 0, 0, 0], [piece236982, piece236987, piece4081, piece4086, piece4089, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine427 : ChainRoutine := ⟨427, [1, 0, 3, 0, 0, 0, 2], [piece236988, piece236993, piece4095, piece4100, piece4102, piece4104, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine428 : ChainRoutine := ⟨428, [1, 0, 3, 0, 0, 1, 1], [piece236994, piece236999, piece4114, piece4119, piece4121, piece4123, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine429 : ChainRoutine := ⟨429, [1, 0, 3, 0, 0, 2, 0], [piece237000, piece237005, piece4133, piece4138, piece4140, piece4142, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine430 : ChainRoutine := ⟨430, [1, 0, 3, 0, 1, 0, 1], [piece237006, piece237011, piece4152, piece4157, piece4159, piece4161, piece4165, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine431 : ChainRoutine := ⟨431, [1, 0, 3, 0, 1, 1, 0], [piece237012, piece237017, piece4171, piece4176, piece4178, piece4180, piece4184, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine432 : ChainRoutine := ⟨432, [1, 0, 3, 0, 2, 0, 0], [piece237018, piece237023, piece4190, piece4195, piece4197, piece4199, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine433 : ChainRoutine := ⟨433, [1, 0, 3, 1, 0, 0, 1], [piece237024, piece237029, piece4209, piece4214, piece4216, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine434 : ChainRoutine := ⟨434, [1, 0, 3, 1, 0, 1, 0], [piece237030, piece237035, piece237040, piece237042, piece237045, piece237050, piece237054, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine435 : ChainRoutine := ⟨435, [1, 0, 3, 1, 1, 0, 0], [piece237055, piece237060, piece4259, piece4264, piece4266, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine436 : ChainRoutine := ⟨436, [1, 0, 3, 2, 0, 0, 0], [piece237061, piece237066, piece4280, piece4285, piece4287, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine437 : ChainRoutine := ⟨437, [1, 1, 0, 0, 0, 1, 3], [piece237067, piece237072, piece237077, piece237081, piece4313, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine438 : ChainRoutine := ⟨438, [1, 1, 0, 0, 0, 2, 2], [piece237082, piece237087, piece237092, piece237096, piece4325, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine439 : ChainRoutine := ⟨439, [1, 1, 0, 0, 0, 3, 1], [piece237097, piece237102, piece237107, piece237111, piece4337, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine440 : ChainRoutine := ⟨440, [1, 1, 0, 0, 1, 0, 3], [piece237112, piece237117, piece237122, piece237126, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine441 : ChainRoutine := ⟨441, [1, 1, 0, 0, 1, 1, 2], [piece237127, piece237132, piece237137, piece237141, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine442 : ChainRoutine := ⟨442, [1, 1, 0, 0, 1, 2, 1], [piece237142, piece237147, piece237152, piece237156, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine443 : ChainRoutine := ⟨443, [1, 1, 0, 0, 1, 3, 0], [piece237157, piece237162, piece237167, piece237171, piece4385, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine444 : ChainRoutine := ⟨444, [1, 1, 0, 0, 2, 0, 2], [piece237172, piece237177, piece237182, piece237186, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine445 : ChainRoutine := ⟨445, [1, 1, 0, 0, 2, 1, 1], [piece237187, piece237192, piece237197, piece237201, piece2156, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine446 : ChainRoutine := ⟨446, [1, 1, 0, 0, 2, 2, 0], [piece237202, piece237207, piece237212, piece237216, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine447 : ChainRoutine := ⟨447, [1, 1, 0, 0, 3, 0, 1], [piece237217, piece237222, piece237227, piece237231, piece4433, piece2180, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routineBatch13 : List ChainRoutine := [routine416, routine417, routine418, routine419, routine420, routine421, routine422, routine423, routine424, routine425, routine426, routine427, routine428, routine429, routine430, routine431, routine432, routine433, routine434, routine435, routine436, routine437, routine438, routine439, routine440, routine441, routine442, routine443, routine444, routine445, routine446, routine447]
theorem routineBatch13_checked : (routineBatch13.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch13_checked :
    (routineBatch13.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch13_checked :
    (routineBatch13.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine416_ready : RoutineReady ⟨416, by decide⟩ routine416 := by
  wct_ready_start 416 13 0
  wct_cases [236862,236867,3918,3923,3925,3929,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 27 236862 38
  · wct_piece 27 236867 39
  · wct_piece 14 3918 43
  · wct_piece 14 3923 44
  · wct_piece 14 3925 45
  · wct_piece 14 3929 46
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine417_ready : RoutineReady ⟨417, by decide⟩ routine417 := by
  wct_ready_start 417 13 1
  wct_cases [236868,236873,3935,3940,3943,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 27 236868 40
  · wct_piece 27 236873 41
  · wct_piece 14 3935 48
  · wct_piece 14 3940 49
  · wct_piece 14 3943 50
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine418_ready : RoutineReady ⟨418, by decide⟩ routine418 := by
  wct_ready_start 418 13 2
  wct_cases [236874,236879,236884,236887,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 27 236874 42
  · wct_piece 27 236879 43
  · wct_piece 27 236884 44
  · wct_piece 27 236887 45
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine419_ready : RoutineReady ⟨419, by decide⟩ routine419 := by
  wct_ready_start 419 13 3
  wct_cases [236888,236893,236898,236901,236906,236910,1975,1118,1123,1125,1129,945]
  · wct_piece 27 236888 46
  · wct_piece 27 236893 47
  · wct_piece 27 236898 48
  · wct_piece 27 236901 49
  · wct_piece 27 236906 50
  · wct_piece 27 236910 51
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine420_ready : RoutineReady ⟨420, by decide⟩ routine420 := by
  wct_ready_start 420 13 4
  wct_cases [236911,236916,236921,236924,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 27 236911 52
  · wct_piece 27 236916 53
  · wct_piece 27 236921 54
  · wct_piece 27 236924 55
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine421_ready : RoutineReady ⟨421, by decide⟩ routine421 := by
  wct_ready_start 421 13 5
  wct_cases [236925,236930,236935,236938,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 27 236925 56
  · wct_piece 27 236930 57
  · wct_piece 27 236935 58
  · wct_piece 27 236938 59
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine422_ready : RoutineReady ⟨422, by decide⟩ routine422 := by
  wct_ready_start 422 13 6
  wct_cases [236939,236944,4014,4019,4022,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 27 236939 60
  · wct_piece 27 236944 61
  · wct_piece 15 4014 6
  · wct_piece 15 4019 7
  · wct_piece 15 4022 8
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine423_ready : RoutineReady ⟨423, by decide⟩ routine423 := by
  wct_ready_start 423 13 7
  wct_cases [236945,236950,4028,4033,4036,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 27 236945 62
  · wct_piece 27 236950 63
  · wct_piece 15 4028 10
  · wct_piece 15 4033 11
  · wct_piece 15 4036 12
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine424_ready : RoutineReady ⟨424, by decide⟩ routine424 := by
  wct_ready_start 424 13 8
  wct_cases [236951,236956,236961,236964,236969,236971,236975,2503,1320,1325,1329,945]
  · wct_piece 28 236951 0
  · wct_piece 28 236956 1
  · wct_piece 28 236961 2
  · wct_piece 28 236964 3
  · wct_piece 28 236969 4
  · wct_piece 28 236971 5
  · wct_piece 28 236975 6
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine425_ready : RoutineReady ⟨425, by decide⟩ routine425 := by
  wct_ready_start 425 13 9
  wct_cases [236976,236981,4067,4072,4075,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 28 236976 7
  · wct_piece 28 236981 8
  · wct_piece 15 4067 21
  · wct_piece 15 4072 22
  · wct_piece 15 4075 23
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine426_ready : RoutineReady ⟨426, by decide⟩ routine426 := by
  wct_ready_start 426 13 10
  wct_cases [236982,236987,4081,4086,4089,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 28 236982 9
  · wct_piece 28 236987 10
  · wct_piece 15 4081 25
  · wct_piece 15 4086 26
  · wct_piece 15 4089 27
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine427_ready : RoutineReady ⟨427, by decide⟩ routine427 := by
  wct_ready_start 427 13 11
  wct_cases [236988,236993,4095,4100,4102,4104,4108,1937,1081,799,804,807]
  · wct_piece 28 236988 11
  · wct_piece 28 236993 12
  · wct_piece 15 4095 29
  · wct_piece 15 4100 30
  · wct_piece 15 4102 31
  · wct_piece 15 4104 32
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine428_ready : RoutineReady ⟨428, by decide⟩ routine428 := by
  wct_ready_start 428 13 12
  wct_cases [236994,236999,4114,4119,4121,4123,4127,1956,1097,1102,862,867]
  · wct_piece 28 236994 13
  · wct_piece 28 236999 14
  · wct_piece 15 4114 35
  · wct_piece 15 4119 36
  · wct_piece 15 4121 37
  · wct_piece 15 4123 38
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine429_ready : RoutineReady ⟨429, by decide⟩ routine429 := by
  wct_ready_start 429 13 13
  wct_cases [237000,237005,4133,4138,4140,4142,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 28 237000 15
  · wct_piece 28 237005 16
  · wct_piece 15 4133 41
  · wct_piece 15 4138 42
  · wct_piece 15 4140 43
  · wct_piece 15 4142 44
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine430_ready : RoutineReady ⟨430, by decide⟩ routine430 := by
  wct_ready_start 430 13 14
  wct_cases [237006,237011,4152,4157,4159,4161,4165,1991,1996,2000,1301,862,867]
  · wct_piece 28 237006 17
  · wct_piece 28 237011 18
  · wct_piece 15 4152 47
  · wct_piece 15 4157 48
  · wct_piece 15 4159 49
  · wct_piece 15 4161 50
  · wct_piece 15 4165 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine431_ready : RoutineReady ⟨431, by decide⟩ routine431 := by
  wct_ready_start 431 13 15
  wct_cases [237012,237017,4171,4176,4178,4180,4184,2016,2021,1320,1325,1329,945]
  · wct_piece 28 237012 19
  · wct_piece 28 237017 20
  · wct_piece 15 4171 53
  · wct_piece 15 4176 54
  · wct_piece 15 4178 55
  · wct_piece 15 4180 56
  · wct_piece 15 4184 57
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine432_ready : RoutineReady ⟨432, by decide⟩ routine432 := by
  wct_ready_start 432 13 16
  wct_cases [237018,237023,4190,4195,4197,4199,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 28 237018 21
  · wct_piece 28 237023 22
  · wct_piece 15 4190 59
  · wct_piece 15 4195 60
  · wct_piece 15 4197 61
  · wct_piece 15 4199 62
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine433_ready : RoutineReady ⟨433, by decide⟩ routine433 := by
  wct_ready_start 433 13 17
  wct_cases [237024,237029,4209,4214,4216,4219,4224,4228,2481,1301,862,867]
  · wct_piece 28 237024 23
  · wct_piece 28 237029 24
  · wct_piece 16 4209 1
  · wct_piece 16 4214 2
  · wct_piece 16 4216 3
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine434_ready : RoutineReady ⟨434, by decide⟩ routine434 := by
  wct_ready_start 434 13 18
  wct_cases [237030,237035,237040,237042,237045,237050,237054,2503,1320,1325,1329,945]
  · wct_piece 28 237030 25
  · wct_piece 28 237035 26
  · wct_piece 28 237040 27
  · wct_piece 28 237042 28
  · wct_piece 28 237045 29
  · wct_piece 28 237050 30
  · wct_piece 28 237054 31
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine435_ready : RoutineReady ⟨435, by decide⟩ routine435 := by
  wct_ready_start 435 13 19
  wct_cases [237055,237060,4259,4264,4266,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 28 237055 32
  · wct_piece 28 237060 33
  · wct_piece 16 4259 15
  · wct_piece 16 4264 16
  · wct_piece 16 4266 17
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine436_ready : RoutineReady ⟨436, by decide⟩ routine436 := by
  wct_ready_start 436 13 20
  wct_cases [237061,237066,4280,4285,4287,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 28 237061 34
  · wct_piece 28 237066 35
  · wct_piece 16 4280 21
  · wct_piece 16 4285 22
  · wct_piece 16 4287 23
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine437_ready : RoutineReady ⟨437, by decide⟩ routine437 := by
  wct_ready_start 437 13 21
  wct_cases [237067,237072,237077,237081,4313,2060,1141,821,826,754,759,761,764]
  · wct_piece 28 237067 36
  · wct_piece 28 237072 37
  · wct_piece 28 237077 38
  · wct_piece 28 237081 39
  · wct_piece 16 4313 31
  · wct_piece 6 2060 4
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine438_ready : RoutineReady ⟨438, by decide⟩ routine438 := by
  wct_ready_start 438 13 22
  wct_cases [237082,237087,237092,237096,4325,2072,1153,835,840,843,799,804,807]
  · wct_piece 28 237082 40
  · wct_piece 28 237087 41
  · wct_piece 28 237092 42
  · wct_piece 28 237096 43
  · wct_piece 16 4325 35
  · wct_piece 6 2072 8
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine439_ready : RoutineReady ⟨439, by decide⟩ routine439 := by
  wct_ready_start 439 13 23
  wct_cases [237097,237102,237107,237111,4337,2084,1165,852,857,859,862,867]
  · wct_piece 28 237097 44
  · wct_piece 28 237102 45
  · wct_piece 28 237107 46
  · wct_piece 28 237111 47
  · wct_piece 16 4337 39
  · wct_piece 6 2084 12
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine440_ready : RoutineReady ⟨440, by decide⟩ routine440 := by
  wct_ready_start 440 13 24
  wct_cases [237112,237117,237122,237126,1174,1179,1183,886,754,759,761,764]
  · wct_piece 28 237112 48
  · wct_piece 28 237117 49
  · wct_piece 28 237122 50
  · wct_piece 28 237126 51
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine441_ready : RoutineReady ⟨441, by decide⟩ routine441 := by
  wct_ready_start 441 13 25
  wct_cases [237127,237132,237137,237141,2108,1192,1197,897,902,799,804,807]
  · wct_piece 28 237127 52
  · wct_piece 28 237132 53
  · wct_piece 28 237137 54
  · wct_piece 28 237141 55
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine442_ready : RoutineReady ⟨442, by decide⟩ routine442 := by
  wct_ready_start 442 13 26
  wct_cases [237142,237147,237152,237156,2120,1206,1211,913,918,921,862,867]
  · wct_piece 28 237142 56
  · wct_piece 28 237147 57
  · wct_piece 28 237152 58
  · wct_piece 28 237156 59
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine443_ready : RoutineReady ⟨443, by decide⟩ routine443 := by
  wct_ready_start 443 13 27
  wct_cases [237157,237162,237167,237171,4385,2132,1220,1225,932,937,939,941,945]
  · wct_piece 28 237157 60
  · wct_piece 28 237162 61
  · wct_piece 28 237167 62
  · wct_piece 28 237171 63
  · wct_piece 16 4385 55
  · wct_piece 6 2132 28
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine444_ready : RoutineReady ⟨444, by decide⟩ routine444 := by
  wct_ready_start 444 13 28
  wct_cases [237172,237177,237182,237186,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 29 237172 0
  · wct_piece 29 237177 1
  · wct_piece 29 237182 2
  · wct_piece 29 237186 3
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine445_ready : RoutineReady ⟨445, by decide⟩ routine445 := by
  wct_ready_start 445 13 29
  wct_cases [237187,237192,237197,237201,2156,1254,1259,1262,1097,1102,862,867]
  · wct_piece 29 237187 4
  · wct_piece 29 237192 5
  · wct_piece 29 237197 6
  · wct_piece 29 237201 7
  · wct_piece 6 2156 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine446_ready : RoutineReady ⟨446, by decide⟩ routine446 := by
  wct_ready_start 446 13 30
  wct_cases [237202,237207,237212,237216,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 29 237202 8
  · wct_piece 29 237207 9
  · wct_piece 29 237212 10
  · wct_piece 29 237216 11
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine447_ready : RoutineReady ⟨447, by decide⟩ routine447 := by
  wct_ready_start 447 13 31
  wct_cases [237217,237222,237227,237231,4433,2180,1288,1293,1295,1297,1301,862,867]
  · wct_piece 29 237217 12
  · wct_piece 29 237222 13
  · wct_piece 29 237227 14
  · wct_piece 29 237231 15
  · wct_piece 17 4433 7
  · wct_piece 6 2180 44
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage13 (rank : Fin 728) (hlo : 416 ≤ rank.val) (hhi : rank.val < 448) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 416 ≤ n at hlo
  change n < 448 at hhi
  interval_cases n
  · exact ⟨routine416, routine416_ready⟩
  · exact ⟨routine417, routine417_ready⟩
  · exact ⟨routine418, routine418_ready⟩
  · exact ⟨routine419, routine419_ready⟩
  · exact ⟨routine420, routine420_ready⟩
  · exact ⟨routine421, routine421_ready⟩
  · exact ⟨routine422, routine422_ready⟩
  · exact ⟨routine423, routine423_ready⟩
  · exact ⟨routine424, routine424_ready⟩
  · exact ⟨routine425, routine425_ready⟩
  · exact ⟨routine426, routine426_ready⟩
  · exact ⟨routine427, routine427_ready⟩
  · exact ⟨routine428, routine428_ready⟩
  · exact ⟨routine429, routine429_ready⟩
  · exact ⟨routine430, routine430_ready⟩
  · exact ⟨routine431, routine431_ready⟩
  · exact ⟨routine432, routine432_ready⟩
  · exact ⟨routine433, routine433_ready⟩
  · exact ⟨routine434, routine434_ready⟩
  · exact ⟨routine435, routine435_ready⟩
  · exact ⟨routine436, routine436_ready⟩
  · exact ⟨routine437, routine437_ready⟩
  · exact ⟨routine438, routine438_ready⟩
  · exact ⟨routine439, routine439_ready⟩
  · exact ⟨routine440, routine440_ready⟩
  · exact ⟨routine441, routine441_ready⟩
  · exact ⟨routine442, routine442_ready⟩
  · exact ⟨routine443, routine443_ready⟩
  · exact ⟨routine444, routine444_ready⟩
  · exact ⟨routine445, routine445_ready⟩
  · exact ⟨routine446, routine446_ready⟩
  · exact ⟨routine447, routine447_ready⟩
end W9Machine.Chain
end
