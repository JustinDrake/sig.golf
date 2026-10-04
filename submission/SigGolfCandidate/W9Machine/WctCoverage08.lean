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
def routine256 : ChainRoutine := ⟨256, [0, 2, 0, 1, 2, 1, 0], [piece4565, piece4570, piece4572, piece4576, piece4581, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine257 : ChainRoutine := ⟨257, [0, 2, 0, 1, 3, 0, 0], [piece4582, piece4587, piece4589, piece4593, piece2343, piece2348, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine258 : ChainRoutine := ⟨258, [0, 2, 0, 2, 0, 0, 2], [piece4594, piece4599, piece4601, piece4605, piece2357, piece2362, piece2364, piece2368, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine259 : ChainRoutine := ⟨259, [0, 2, 0, 2, 0, 1, 1], [piece4606, piece4611, piece4613, piece4617, piece2377, piece2382, piece2384, piece2388, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine260 : ChainRoutine := ⟨260, [0, 2, 0, 2, 0, 2, 0], [piece4618, piece4623, piece4625, piece4629, piece4634, piece4636, piece4640, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine261 : ChainRoutine := ⟨261, [0, 2, 0, 2, 1, 0, 1], [piece4641, piece4646, piece4648, piece4652, piece4657, piece4660, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine262 : ChainRoutine := ⟨262, [0, 2, 0, 2, 1, 1, 0], [piece4661, piece4666, piece4668, piece4672, piece4677, piece4680, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine263 : ChainRoutine := ⟨263, [0, 2, 0, 2, 2, 0, 0], [piece4681, piece4686, piece4688, piece4692, piece2451, piece2456, piece2459, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine264 : ChainRoutine := ⟨264, [0, 2, 0, 3, 0, 0, 1], [piece4693, piece4698, piece4700, piece4704, piece2468, piece2473, piece2475, piece2477, piece2481, piece1301, piece862, piece867]⟩
def routine265 : ChainRoutine := ⟨265, [0, 2, 0, 3, 0, 1, 0], [piece4705, piece4710, piece4712, piece4716, piece2490, piece2495, piece2497, piece2499, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine266 : ChainRoutine := ⟨266, [0, 2, 0, 3, 1, 0, 0], [piece4717, piece4722, piece4724, piece4728, piece2512, piece2517, piece2519, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine267 : ChainRoutine := ⟨267, [0, 2, 1, 0, 0, 0, 3], [piece4729, piece4734, piece4737, piece4742, piece4746, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine268 : ChainRoutine := ⟨268, [0, 2, 1, 0, 0, 1, 2], [piece235008, piece235013, piece235016, piece235021, piece235025, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine269 : ChainRoutine := ⟨269, [0, 2, 1, 0, 0, 2, 1], [piece235026, piece235031, piece235034, piece235039, piece235043, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine270 : ChainRoutine := ⟨270, [0, 2, 1, 0, 0, 3, 0], [piece235044, piece235049, piece235052, piece235057, piece235061, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine271 : ChainRoutine := ⟨271, [0, 2, 1, 0, 1, 0, 2], [piece235062, piece235067, piece235070, piece235075, piece235079, piece235084, piece235088, piece1081, piece799, piece804, piece807]⟩
def routine272 : ChainRoutine := ⟨272, [0, 2, 1, 0, 1, 1, 1], [piece235089, piece235094, piece235097, piece235102, piece235106, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine273 : ChainRoutine := ⟨273, [0, 2, 1, 0, 1, 2, 0], [piece235107, piece235112, piece235115, piece235120, piece235124, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine274 : ChainRoutine := ⟨274, [0, 2, 1, 0, 2, 0, 1], [piece235125, piece235130, piece235133, piece235138, piece235142, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine275 : ChainRoutine := ⟨275, [0, 2, 1, 0, 2, 1, 0], [piece235143, piece235148, piece235151, piece235156, piece235160, piece235165, piece235168, piece1320, piece1325, piece1329, piece945]⟩
def routine276 : ChainRoutine := ⟨276, [0, 2, 1, 0, 3, 0, 0], [piece235169, piece235174, piece235177, piece235182, piece235186, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine277 : ChainRoutine := ⟨277, [0, 2, 1, 1, 0, 0, 2], [piece235187, piece235192, piece235195, piece235200, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine278 : ChainRoutine := ⟨278, [0, 2, 1, 1, 0, 1, 1], [piece235201, piece235206, piece235209, piece235214, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine279 : ChainRoutine := ⟨279, [0, 2, 1, 1, 0, 2, 0], [piece235215, piece235220, piece235223, piece235228, piece235233, piece235237, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine280 : ChainRoutine := ⟨280, [0, 2, 1, 1, 1, 0, 1], [piece235238, piece235243, piece235246, piece235251, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine281 : ChainRoutine := ⟨281, [0, 2, 1, 1, 1, 1, 0], [piece235252, piece235257, piece235260, piece235265, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine282 : ChainRoutine := ⟨282, [0, 2, 1, 1, 2, 0, 0], [piece235266, piece235271, piece235274, piece235279, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine283 : ChainRoutine := ⟨283, [0, 2, 1, 2, 0, 0, 1], [piece235280, piece235285, piece235288, piece235293, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine284 : ChainRoutine := ⟨284, [0, 2, 1, 2, 0, 1, 0], [piece235294, piece235299, piece235302, piece235307, piece235312, piece235314, piece235318, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine285 : ChainRoutine := ⟨285, [0, 2, 1, 2, 1, 0, 0], [piece235319, piece235324, piece235327, piece235332, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine286 : ChainRoutine := ⟨286, [0, 2, 1, 3, 0, 0, 0], [piece235333, piece235338, piece235341, piece235346, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine287 : ChainRoutine := ⟨287, [0, 2, 2, 0, 0, 0, 2], [piece235347, piece235352, piece235355, piece235360, piece235362, piece235366, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routineBatch08 : List ChainRoutine := [routine256, routine257, routine258, routine259, routine260, routine261, routine262, routine263, routine264, routine265, routine266, routine267, routine268, routine269, routine270, routine271, routine272, routine273, routine274, routine275, routine276, routine277, routine278, routine279, routine280, routine281, routine282, routine283, routine284, routine285, routine286, routine287]
theorem routineBatch08_checked : (routineBatch08.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch08_checked :
    (routineBatch08.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch08_checked :
    (routineBatch08.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine256_ready : RoutineReady ⟨256, by decide⟩ routine256 := by
  wct_ready_start 256 8 0
  wct_cases [4565,4570,4572,4576,4581,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 17 4565 49
  · wct_piece 17 4570 50
  · wct_piece 17 4572 51
  · wct_piece 17 4576 52
  · wct_piece 17 4581 53
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine257_ready : RoutineReady ⟨257, by decide⟩ routine257 := by
  wct_ready_start 257 8 1
  wct_cases [4582,4587,4589,4593,2343,2348,1489,1494,1496,1498,1502,945]
  · wct_piece 17 4582 54
  · wct_piece 17 4587 55
  · wct_piece 17 4589 56
  · wct_piece 17 4593 57
  · wct_piece 7 2343 27
  · wct_piece 7 2348 28
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine258_ready : RoutineReady ⟨258, by decide⟩ routine258 := by
  wct_ready_start 258 8 2
  wct_cases [4594,4599,4601,4605,2357,2362,2364,2368,1937,1081,799,804,807]
  · wct_piece 17 4594 58
  · wct_piece 17 4599 59
  · wct_piece 17 4601 60
  · wct_piece 17 4605 61
  · wct_piece 7 2357 31
  · wct_piece 7 2362 32
  · wct_piece 7 2364 33
  · wct_piece 7 2368 34
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine259_ready : RoutineReady ⟨259, by decide⟩ routine259 := by
  wct_ready_start 259 8 3
  wct_cases [4606,4611,4613,4617,2377,2382,2384,2388,1956,1097,1102,862,867]
  · wct_piece 17 4606 62
  · wct_piece 17 4611 63
  · wct_piece 18 4613 0
  · wct_piece 18 4617 1
  · wct_piece 7 2377 37
  · wct_piece 7 2382 38
  · wct_piece 7 2384 39
  · wct_piece 7 2388 40
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine260_ready : RoutineReady ⟨260, by decide⟩ routine260 := by
  wct_ready_start 260 8 4
  wct_cases [4618,4623,4625,4629,4634,4636,4640,1975,1118,1123,1125,1129,945]
  · wct_piece 18 4618 2
  · wct_piece 18 4623 3
  · wct_piece 18 4625 4
  · wct_piece 18 4629 5
  · wct_piece 18 4634 6
  · wct_piece 18 4636 7
  · wct_piece 18 4640 8
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine261_ready : RoutineReady ⟨261, by decide⟩ routine261 := by
  wct_ready_start 261 8 5
  wct_cases [4641,4646,4648,4652,4657,4660,1991,1996,2000,1301,862,867]
  · wct_piece 18 4641 9
  · wct_piece 18 4646 10
  · wct_piece 18 4648 11
  · wct_piece 18 4652 12
  · wct_piece 18 4657 13
  · wct_piece 18 4660 14
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine262_ready : RoutineReady ⟨262, by decide⟩ routine262 := by
  wct_ready_start 262 8 6
  wct_cases [4661,4666,4668,4672,4677,4680,2016,2021,1320,1325,1329,945]
  · wct_piece 18 4661 15
  · wct_piece 18 4666 16
  · wct_piece 18 4668 17
  · wct_piece 18 4672 18
  · wct_piece 18 4677 19
  · wct_piece 18 4680 20
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine263_ready : RoutineReady ⟨263, by decide⟩ routine263 := by
  wct_ready_start 263 8 7
  wct_cases [4681,4686,4688,4692,2451,2456,2459,2037,2042,2044,2048,1502,945]
  · wct_piece 18 4681 21
  · wct_piece 18 4686 22
  · wct_piece 18 4688 23
  · wct_piece 18 4692 24
  · wct_piece 7 2451 59
  · wct_piece 7 2456 60
  · wct_piece 7 2459 61
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine264_ready : RoutineReady ⟨264, by decide⟩ routine264 := by
  wct_ready_start 264 8 8
  wct_cases [4693,4698,4700,4704,2468,2473,2475,2477,2481,1301,862,867]
  · wct_piece 18 4693 25
  · wct_piece 18 4698 26
  · wct_piece 18 4700 27
  · wct_piece 18 4704 28
  · wct_piece 8 2468 0
  · wct_piece 8 2473 1
  · wct_piece 8 2475 2
  · wct_piece 8 2477 3
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine265_ready : RoutineReady ⟨265, by decide⟩ routine265 := by
  wct_ready_start 265 8 9
  wct_cases [4705,4710,4712,4716,2490,2495,2497,2499,2503,1320,1325,1329,945]
  · wct_piece 18 4705 29
  · wct_piece 18 4710 30
  · wct_piece 18 4712 31
  · wct_piece 18 4716 32
  · wct_piece 8 2490 7
  · wct_piece 8 2495 8
  · wct_piece 8 2497 9
  · wct_piece 8 2499 10
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine266_ready : RoutineReady ⟨266, by decide⟩ routine266 := by
  wct_ready_start 266 8 10
  wct_cases [4717,4722,4724,4728,2512,2517,2519,2522,2527,2531,1502,945]
  · wct_piece 18 4717 33
  · wct_piece 18 4722 34
  · wct_piece 18 4724 35
  · wct_piece 18 4728 36
  · wct_piece 8 2512 14
  · wct_piece 8 2517 15
  · wct_piece 8 2519 16
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine267_ready : RoutineReady ⟨267, by decide⟩ routine267 := by
  wct_ready_start 267 8 11
  wct_cases [4729,4734,4737,4742,4746,2545,1343,886,754,759,761,764]
  · wct_piece 18 4729 37
  · wct_piece 18 4734 38
  · wct_piece 18 4737 39
  · wct_piece 18 4742 40
  · wct_piece 18 4746 41
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine268_ready : RoutineReady ⟨268, by decide⟩ routine268 := by
  wct_ready_start 268 8 12
  wct_cases [235008,235013,235016,235021,235025,2559,1357,897,902,799,804,807]
  · wct_piece 18 235008 42
  · wct_piece 18 235013 43
  · wct_piece 18 235016 44
  · wct_piece 18 235021 45
  · wct_piece 18 235025 46
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine269_ready : RoutineReady ⟨269, by decide⟩ routine269 := by
  wct_ready_start 269 8 13
  wct_cases [235026,235031,235034,235039,235043,2573,1371,913,918,921,862,867]
  · wct_piece 18 235026 47
  · wct_piece 18 235031 48
  · wct_piece 18 235034 49
  · wct_piece 18 235039 50
  · wct_piece 18 235043 51
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine270_ready : RoutineReady ⟨270, by decide⟩ routine270 := by
  wct_ready_start 270 8 14
  wct_cases [235044,235049,235052,235057,235061,2587,1385,932,937,939,941,945]
  · wct_piece 18 235044 52
  · wct_piece 18 235049 53
  · wct_piece 18 235052 54
  · wct_piece 18 235057 55
  · wct_piece 18 235061 56
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine271_ready : RoutineReady ⟨271, by decide⟩ routine271 := by
  wct_ready_start 271 8 15
  wct_cases [235062,235067,235070,235075,235079,235084,235088,1081,799,804,807]
  · wct_piece 18 235062 57
  · wct_piece 18 235067 58
  · wct_piece 18 235070 59
  · wct_piece 18 235075 60
  · wct_piece 18 235079 61
  · wct_piece 18 235084 62
  · wct_piece 18 235088 63
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine272_ready : RoutineReady ⟨272, by decide⟩ routine272 := by
  wct_ready_start 272 8 16
  wct_cases [235089,235094,235097,235102,235106,2615,1416,1421,1097,1102,862,867]
  · wct_piece 19 235089 0
  · wct_piece 19 235094 1
  · wct_piece 19 235097 2
  · wct_piece 19 235102 3
  · wct_piece 19 235106 4
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine273_ready : RoutineReady ⟨273, by decide⟩ routine273 := by
  wct_ready_start 273 8 17
  wct_cases [235107,235112,235115,235120,235124,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 19 235107 5
  · wct_piece 19 235112 6
  · wct_piece 19 235115 7
  · wct_piece 19 235120 8
  · wct_piece 19 235124 9
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine274_ready : RoutineReady ⟨274, by decide⟩ routine274 := by
  wct_ready_start 274 8 18
  wct_cases [235125,235130,235133,235138,235142,1448,1453,1455,1459,1301,862,867]
  · wct_piece 19 235125 10
  · wct_piece 19 235130 11
  · wct_piece 19 235133 12
  · wct_piece 19 235138 13
  · wct_piece 19 235142 14
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine275_ready : RoutineReady ⟨275, by decide⟩ routine275 := by
  wct_ready_start 275 8 19
  wct_cases [235143,235148,235151,235156,235160,235165,235168,1320,1325,1329,945]
  · wct_piece 19 235143 15
  · wct_piece 19 235148 16
  · wct_piece 19 235151 17
  · wct_piece 19 235156 18
  · wct_piece 19 235160 19
  · wct_piece 19 235165 20
  · wct_piece 19 235168 21
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine276_ready : RoutineReady ⟨276, by decide⟩ routine276 := by
  wct_ready_start 276 8 20
  wct_cases [235169,235174,235177,235182,235186,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 19 235169 22
  · wct_piece 19 235174 23
  · wct_piece 19 235177 24
  · wct_piece 19 235182 25
  · wct_piece 19 235186 26
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine277_ready : RoutineReady ⟨277, by decide⟩ routine277 := by
  wct_ready_start 277 8 21
  wct_cases [235187,235192,235195,235200,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 19 235187 27
  · wct_piece 19 235192 28
  · wct_piece 19 235195 29
  · wct_piece 19 235200 30
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine278_ready : RoutineReady ⟨278, by decide⟩ routine278 := by
  wct_ready_start 278 8 22
  wct_cases [235201,235206,235209,235214,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 19 235201 31
  · wct_piece 19 235206 32
  · wct_piece 19 235209 33
  · wct_piece 19 235214 34
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine279_ready : RoutineReady ⟨279, by decide⟩ routine279 := by
  wct_ready_start 279 8 23
  wct_cases [235215,235220,235223,235228,235233,235237,1975,1118,1123,1125,1129,945]
  · wct_piece 19 235215 35
  · wct_piece 19 235220 36
  · wct_piece 19 235223 37
  · wct_piece 19 235228 38
  · wct_piece 19 235233 39
  · wct_piece 19 235237 40
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine280_ready : RoutineReady ⟨280, by decide⟩ routine280 := by
  wct_ready_start 280 8 24
  wct_cases [235238,235243,235246,235251,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 19 235238 41
  · wct_piece 19 235243 42
  · wct_piece 19 235246 43
  · wct_piece 19 235251 44
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine281_ready : RoutineReady ⟨281, by decide⟩ routine281 := by
  wct_ready_start 281 8 25
  wct_cases [235252,235257,235260,235265,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 19 235252 45
  · wct_piece 19 235257 46
  · wct_piece 19 235260 47
  · wct_piece 19 235265 48
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine282_ready : RoutineReady ⟨282, by decide⟩ routine282 := by
  wct_ready_start 282 8 26
  wct_cases [235266,235271,235274,235279,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 19 235266 49
  · wct_piece 19 235271 50
  · wct_piece 19 235274 51
  · wct_piece 19 235279 52
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine283_ready : RoutineReady ⟨283, by decide⟩ routine283 := by
  wct_ready_start 283 8 27
  wct_cases [235280,235285,235288,235293,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 19 235280 53
  · wct_piece 19 235285 54
  · wct_piece 19 235288 55
  · wct_piece 19 235293 56
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine284_ready : RoutineReady ⟨284, by decide⟩ routine284 := by
  wct_ready_start 284 8 28
  wct_cases [235294,235299,235302,235307,235312,235314,235318,2503,1320,1325,1329,945]
  · wct_piece 19 235294 57
  · wct_piece 19 235299 58
  · wct_piece 19 235302 59
  · wct_piece 19 235307 60
  · wct_piece 19 235312 61
  · wct_piece 19 235314 62
  · wct_piece 19 235318 63
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine285_ready : RoutineReady ⟨285, by decide⟩ routine285 := by
  wct_ready_start 285 8 29
  wct_cases [235319,235324,235327,235332,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 20 235319 0
  · wct_piece 20 235324 1
  · wct_piece 20 235327 2
  · wct_piece 20 235332 3
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine286_ready : RoutineReady ⟨286, by decide⟩ routine286 := by
  wct_ready_start 286 8 30
  wct_cases [235333,235338,235341,235346,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 20 235333 4
  · wct_piece 20 235338 5
  · wct_piece 20 235341 6
  · wct_piece 20 235346 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine287_ready : RoutineReady ⟨287, by decide⟩ routine287 := by
  wct_ready_start 287 8 31
  wct_cases [235347,235352,235355,235360,235362,235366,4108,1937,1081,799,804,807]
  · wct_piece 20 235347 8
  · wct_piece 20 235352 9
  · wct_piece 20 235355 10
  · wct_piece 20 235360 11
  · wct_piece 20 235362 12
  · wct_piece 20 235366 13
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
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
theorem coverage08 (rank : Fin 728) (hlo : 256 ≤ rank.val) (hhi : rank.val < 288) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 256 ≤ n at hlo
  change n < 288 at hhi
  interval_cases n
  · exact ⟨routine256, routine256_ready⟩
  · exact ⟨routine257, routine257_ready⟩
  · exact ⟨routine258, routine258_ready⟩
  · exact ⟨routine259, routine259_ready⟩
  · exact ⟨routine260, routine260_ready⟩
  · exact ⟨routine261, routine261_ready⟩
  · exact ⟨routine262, routine262_ready⟩
  · exact ⟨routine263, routine263_ready⟩
  · exact ⟨routine264, routine264_ready⟩
  · exact ⟨routine265, routine265_ready⟩
  · exact ⟨routine266, routine266_ready⟩
  · exact ⟨routine267, routine267_ready⟩
  · exact ⟨routine268, routine268_ready⟩
  · exact ⟨routine269, routine269_ready⟩
  · exact ⟨routine270, routine270_ready⟩
  · exact ⟨routine271, routine271_ready⟩
  · exact ⟨routine272, routine272_ready⟩
  · exact ⟨routine273, routine273_ready⟩
  · exact ⟨routine274, routine274_ready⟩
  · exact ⟨routine275, routine275_ready⟩
  · exact ⟨routine276, routine276_ready⟩
  · exact ⟨routine277, routine277_ready⟩
  · exact ⟨routine278, routine278_ready⟩
  · exact ⟨routine279, routine279_ready⟩
  · exact ⟨routine280, routine280_ready⟩
  · exact ⟨routine281, routine281_ready⟩
  · exact ⟨routine282, routine282_ready⟩
  · exact ⟨routine283, routine283_ready⟩
  · exact ⟨routine284, routine284_ready⟩
  · exact ⟨routine285, routine285_ready⟩
  · exact ⟨routine286, routine286_ready⟩
  · exact ⟨routine287, routine287_ready⟩
end W9Machine.Chain
end
