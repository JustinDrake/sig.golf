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
def routine576 : ChainRoutine := ⟨576, [2, 0, 0, 2, 0, 2, 0], [piece239936, piece239941, piece239943, piece4629, piece4634, piece4636, piece4640, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine577 : ChainRoutine := ⟨577, [2, 0, 0, 2, 1, 0, 1], [piece239944, piece239949, piece239951, piece4652, piece4657, piece4660, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine578 : ChainRoutine := ⟨578, [2, 0, 0, 2, 1, 1, 0], [piece239952, piece239957, piece239959, piece4672, piece4677, piece4680, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine579 : ChainRoutine := ⟨579, [2, 0, 0, 2, 2, 0, 0], [piece239960, piece239965, piece239967, piece4692, piece2451, piece2456, piece2459, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine580 : ChainRoutine := ⟨580, [2, 0, 0, 3, 0, 0, 1], [piece239968, piece239973, piece239975, piece4704, piece2468, piece2473, piece2475, piece2477, piece2481, piece1301, piece862, piece867]⟩
def routine581 : ChainRoutine := ⟨581, [2, 0, 0, 3, 0, 1, 0], [piece239976, piece239981, piece239983, piece4716, piece2490, piece2495, piece2497, piece2499, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine582 : ChainRoutine := ⟨582, [2, 0, 0, 3, 1, 0, 0], [piece239984, piece239989, piece239991, piece4728, piece2512, piece2517, piece2519, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine583 : ChainRoutine := ⟨583, [2, 0, 1, 0, 0, 0, 3], [piece239992, piece239997, piece239999, piece4737, piece4742, piece4746, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine584 : ChainRoutine := ⟨584, [2, 0, 1, 0, 0, 1, 2], [piece240000, piece240005, piece240007, piece235016, piece235021, piece235025, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine585 : ChainRoutine := ⟨585, [2, 0, 1, 0, 0, 2, 1], [piece240008, piece240013, piece240015, piece235034, piece235039, piece235043, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine586 : ChainRoutine := ⟨586, [2, 0, 1, 0, 0, 3, 0], [piece240016, piece240021, piece240023, piece235052, piece235057, piece235061, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine587 : ChainRoutine := ⟨587, [2, 0, 1, 0, 1, 0, 2], [piece240024, piece240029, piece240031, piece235070, piece235075, piece235079, piece235084, piece235088, piece1081, piece799, piece804, piece807]⟩
def routine588 : ChainRoutine := ⟨588, [2, 0, 1, 0, 1, 1, 1], [piece240032, piece240037, piece240039, piece235097, piece235102, piece235106, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine589 : ChainRoutine := ⟨589, [2, 0, 1, 0, 1, 2, 0], [piece240040, piece240045, piece240047, piece235115, piece235120, piece235124, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine590 : ChainRoutine := ⟨590, [2, 0, 1, 0, 2, 0, 1], [piece240048, piece240053, piece240055, piece235133, piece235138, piece235142, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine591 : ChainRoutine := ⟨591, [2, 0, 1, 0, 2, 1, 0], [piece240056, piece240061, piece240063, piece235151, piece235156, piece235160, piece235165, piece235168, piece1320, piece1325, piece1329, piece945]⟩
def routine592 : ChainRoutine := ⟨592, [2, 0, 1, 0, 3, 0, 0], [piece240064, piece240069, piece240071, piece235177, piece235182, piece235186, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine593 : ChainRoutine := ⟨593, [2, 0, 1, 1, 0, 0, 2], [piece240072, piece240077, piece240079, piece235195, piece235200, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine594 : ChainRoutine := ⟨594, [2, 0, 1, 1, 0, 1, 1], [piece240080, piece240085, piece240087, piece235209, piece235214, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine595 : ChainRoutine := ⟨595, [2, 0, 1, 1, 0, 2, 0], [piece240088, piece240093, piece240095, piece235223, piece235228, piece235233, piece235237, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine596 : ChainRoutine := ⟨596, [2, 0, 1, 1, 1, 0, 1], [piece240096, piece240101, piece240103, piece235246, piece235251, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine597 : ChainRoutine := ⟨597, [2, 0, 1, 1, 1, 1, 0], [piece240104, piece240109, piece240111, piece235260, piece235265, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine598 : ChainRoutine := ⟨598, [2, 0, 1, 1, 2, 0, 0], [piece240112, piece240117, piece240119, piece235274, piece235279, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine599 : ChainRoutine := ⟨599, [2, 0, 1, 2, 0, 0, 1], [piece240120, piece240125, piece240127, piece235288, piece235293, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine600 : ChainRoutine := ⟨600, [2, 0, 1, 2, 0, 1, 0], [piece240128, piece240133, piece240135, piece235302, piece235307, piece235312, piece235314, piece235318, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine601 : ChainRoutine := ⟨601, [2, 0, 1, 2, 1, 0, 0], [piece240136, piece240141, piece240143, piece235327, piece235332, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine602 : ChainRoutine := ⟨602, [2, 0, 1, 3, 0, 0, 0], [piece240144, piece240149, piece240151, piece235341, piece235346, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine603 : ChainRoutine := ⟨603, [2, 0, 2, 0, 0, 0, 2], [piece240152, piece240157, piece240159, piece235355, piece235360, piece235362, piece235366, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine604 : ChainRoutine := ⟨604, [2, 0, 2, 0, 0, 1, 1], [piece240160, piece240165, piece240167, piece235375, piece235380, piece235382, piece235386, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine605 : ChainRoutine := ⟨605, [2, 0, 2, 0, 0, 2, 0], [piece240168, piece240173, piece240175, piece235395, piece235400, piece235402, piece235406, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine606 : ChainRoutine := ⟨606, [2, 0, 2, 0, 1, 0, 1], [piece240176, piece240181, piece240183, piece235415, piece235420, piece235422, piece235426, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine607 : ChainRoutine := ⟨607, [2, 0, 2, 0, 1, 1, 0], [piece240184, piece240189, piece240191, piece235435, piece235440, piece235442, piece235446, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routineBatch18 : List ChainRoutine := [routine576, routine577, routine578, routine579, routine580, routine581, routine582, routine583, routine584, routine585, routine586, routine587, routine588, routine589, routine590, routine591, routine592, routine593, routine594, routine595, routine596, routine597, routine598, routine599, routine600, routine601, routine602, routine603, routine604, routine605, routine606, routine607]
theorem routineBatch18_checked : (routineBatch18.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch18_checked :
    (routineBatch18.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch18_checked :
    (routineBatch18.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine576_ready : RoutineReady ⟨576, by decide⟩ routine576 := by
  wct_ready_start 576 18 0
  wct_cases [239936,239941,239943,4629,4634,4636,4640,1975,1118,1123,1125,1129,945]
  · wct_piece 40 239936 29
  · wct_piece 40 239941 30
  · wct_piece 40 239943 31
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
theorem routine577_ready : RoutineReady ⟨577, by decide⟩ routine577 := by
  wct_ready_start 577 18 1
  wct_cases [239944,239949,239951,4652,4657,4660,1991,1996,2000,1301,862,867]
  · wct_piece 40 239944 32
  · wct_piece 40 239949 33
  · wct_piece 40 239951 34
  · wct_piece 18 4652 12
  · wct_piece 18 4657 13
  · wct_piece 18 4660 14
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine578_ready : RoutineReady ⟨578, by decide⟩ routine578 := by
  wct_ready_start 578 18 2
  wct_cases [239952,239957,239959,4672,4677,4680,2016,2021,1320,1325,1329,945]
  · wct_piece 40 239952 35
  · wct_piece 40 239957 36
  · wct_piece 40 239959 37
  · wct_piece 18 4672 18
  · wct_piece 18 4677 19
  · wct_piece 18 4680 20
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine579_ready : RoutineReady ⟨579, by decide⟩ routine579 := by
  wct_ready_start 579 18 3
  wct_cases [239960,239965,239967,4692,2451,2456,2459,2037,2042,2044,2048,1502,945]
  · wct_piece 40 239960 38
  · wct_piece 40 239965 39
  · wct_piece 40 239967 40
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
theorem routine580_ready : RoutineReady ⟨580, by decide⟩ routine580 := by
  wct_ready_start 580 18 4
  wct_cases [239968,239973,239975,4704,2468,2473,2475,2477,2481,1301,862,867]
  · wct_piece 40 239968 41
  · wct_piece 40 239973 42
  · wct_piece 40 239975 43
  · wct_piece 18 4704 28
  · wct_piece 8 2468 0
  · wct_piece 8 2473 1
  · wct_piece 8 2475 2
  · wct_piece 8 2477 3
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine581_ready : RoutineReady ⟨581, by decide⟩ routine581 := by
  wct_ready_start 581 18 5
  wct_cases [239976,239981,239983,4716,2490,2495,2497,2499,2503,1320,1325,1329,945]
  · wct_piece 40 239976 44
  · wct_piece 40 239981 45
  · wct_piece 40 239983 46
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
theorem routine582_ready : RoutineReady ⟨582, by decide⟩ routine582 := by
  wct_ready_start 582 18 6
  wct_cases [239984,239989,239991,4728,2512,2517,2519,2522,2527,2531,1502,945]
  · wct_piece 40 239984 47
  · wct_piece 40 239989 48
  · wct_piece 40 239991 49
  · wct_piece 18 4728 36
  · wct_piece 8 2512 14
  · wct_piece 8 2517 15
  · wct_piece 8 2519 16
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine583_ready : RoutineReady ⟨583, by decide⟩ routine583 := by
  wct_ready_start 583 18 7
  wct_cases [239992,239997,239999,4737,4742,4746,2545,1343,886,754,759,761,764]
  · wct_piece 40 239992 50
  · wct_piece 40 239997 51
  · wct_piece 40 239999 52
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
theorem routine584_ready : RoutineReady ⟨584, by decide⟩ routine584 := by
  wct_ready_start 584 18 8
  wct_cases [240000,240005,240007,235016,235021,235025,2559,1357,897,902,799,804,807]
  · wct_piece 40 240000 53
  · wct_piece 40 240005 54
  · wct_piece 40 240007 55
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
theorem routine585_ready : RoutineReady ⟨585, by decide⟩ routine585 := by
  wct_ready_start 585 18 9
  wct_cases [240008,240013,240015,235034,235039,235043,2573,1371,913,918,921,862,867]
  · wct_piece 40 240008 56
  · wct_piece 40 240013 57
  · wct_piece 40 240015 58
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
theorem routine586_ready : RoutineReady ⟨586, by decide⟩ routine586 := by
  wct_ready_start 586 18 10
  wct_cases [240016,240021,240023,235052,235057,235061,2587,1385,932,937,939,941,945]
  · wct_piece 40 240016 59
  · wct_piece 40 240021 60
  · wct_piece 40 240023 61
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
theorem routine587_ready : RoutineReady ⟨587, by decide⟩ routine587 := by
  wct_ready_start 587 18 11
  wct_cases [240024,240029,240031,235070,235075,235079,235084,235088,1081,799,804,807]
  · wct_piece 40 240024 62
  · wct_piece 40 240029 63
  · wct_piece 41 240031 0
  · wct_piece 18 235070 59
  · wct_piece 18 235075 60
  · wct_piece 18 235079 61
  · wct_piece 18 235084 62
  · wct_piece 18 235088 63
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine588_ready : RoutineReady ⟨588, by decide⟩ routine588 := by
  wct_ready_start 588 18 12
  wct_cases [240032,240037,240039,235097,235102,235106,2615,1416,1421,1097,1102,862,867]
  · wct_piece 41 240032 1
  · wct_piece 41 240037 2
  · wct_piece 41 240039 3
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
theorem routine589_ready : RoutineReady ⟨589, by decide⟩ routine589 := by
  wct_ready_start 589 18 13
  wct_cases [240040,240045,240047,235115,235120,235124,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 41 240040 4
  · wct_piece 41 240045 5
  · wct_piece 41 240047 6
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
theorem routine590_ready : RoutineReady ⟨590, by decide⟩ routine590 := by
  wct_ready_start 590 18 14
  wct_cases [240048,240053,240055,235133,235138,235142,1448,1453,1455,1459,1301,862,867]
  · wct_piece 41 240048 7
  · wct_piece 41 240053 8
  · wct_piece 41 240055 9
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
theorem routine591_ready : RoutineReady ⟨591, by decide⟩ routine591 := by
  wct_ready_start 591 18 15
  wct_cases [240056,240061,240063,235151,235156,235160,235165,235168,1320,1325,1329,945]
  · wct_piece 41 240056 10
  · wct_piece 41 240061 11
  · wct_piece 41 240063 12
  · wct_piece 19 235151 17
  · wct_piece 19 235156 18
  · wct_piece 19 235160 19
  · wct_piece 19 235165 20
  · wct_piece 19 235168 21
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine592_ready : RoutineReady ⟨592, by decide⟩ routine592 := by
  wct_ready_start 592 18 16
  wct_cases [240064,240069,240071,235177,235182,235186,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 41 240064 13
  · wct_piece 41 240069 14
  · wct_piece 41 240071 15
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
theorem routine593_ready : RoutineReady ⟨593, by decide⟩ routine593 := by
  wct_ready_start 593 18 17
  wct_cases [240072,240077,240079,235195,235200,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 41 240072 16
  · wct_piece 41 240077 17
  · wct_piece 41 240079 18
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
theorem routine594_ready : RoutineReady ⟨594, by decide⟩ routine594 := by
  wct_ready_start 594 18 18
  wct_cases [240080,240085,240087,235209,235214,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 41 240080 19
  · wct_piece 41 240085 20
  · wct_piece 41 240087 21
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
theorem routine595_ready : RoutineReady ⟨595, by decide⟩ routine595 := by
  wct_ready_start 595 18 19
  wct_cases [240088,240093,240095,235223,235228,235233,235237,1975,1118,1123,1125,1129,945]
  · wct_piece 41 240088 22
  · wct_piece 41 240093 23
  · wct_piece 41 240095 24
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
theorem routine596_ready : RoutineReady ⟨596, by decide⟩ routine596 := by
  wct_ready_start 596 18 20
  wct_cases [240096,240101,240103,235246,235251,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 41 240096 25
  · wct_piece 41 240101 26
  · wct_piece 41 240103 27
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
theorem routine597_ready : RoutineReady ⟨597, by decide⟩ routine597 := by
  wct_ready_start 597 18 21
  wct_cases [240104,240109,240111,235260,235265,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 41 240104 28
  · wct_piece 41 240109 29
  · wct_piece 41 240111 30
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
theorem routine598_ready : RoutineReady ⟨598, by decide⟩ routine598 := by
  wct_ready_start 598 18 22
  wct_cases [240112,240117,240119,235274,235279,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 41 240112 31
  · wct_piece 41 240117 32
  · wct_piece 41 240119 33
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
theorem routine599_ready : RoutineReady ⟨599, by decide⟩ routine599 := by
  wct_ready_start 599 18 23
  wct_cases [240120,240125,240127,235288,235293,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 41 240120 34
  · wct_piece 41 240125 35
  · wct_piece 41 240127 36
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
theorem routine600_ready : RoutineReady ⟨600, by decide⟩ routine600 := by
  wct_ready_start 600 18 24
  wct_cases [240128,240133,240135,235302,235307,235312,235314,235318,2503,1320,1325,1329,945]
  · wct_piece 41 240128 37
  · wct_piece 41 240133 38
  · wct_piece 41 240135 39
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
theorem routine601_ready : RoutineReady ⟨601, by decide⟩ routine601 := by
  wct_ready_start 601 18 25
  wct_cases [240136,240141,240143,235327,235332,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 41 240136 40
  · wct_piece 41 240141 41
  · wct_piece 41 240143 42
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
theorem routine602_ready : RoutineReady ⟨602, by decide⟩ routine602 := by
  wct_ready_start 602 18 26
  wct_cases [240144,240149,240151,235341,235346,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 41 240144 43
  · wct_piece 41 240149 44
  · wct_piece 41 240151 45
  · wct_piece 20 235341 6
  · wct_piece 20 235346 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine603_ready : RoutineReady ⟨603, by decide⟩ routine603 := by
  wct_ready_start 603 18 27
  wct_cases [240152,240157,240159,235355,235360,235362,235366,4108,1937,1081,799,804,807]
  · wct_piece 41 240152 46
  · wct_piece 41 240157 47
  · wct_piece 41 240159 48
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
theorem routine604_ready : RoutineReady ⟨604, by decide⟩ routine604 := by
  wct_ready_start 604 18 28
  wct_cases [240160,240165,240167,235375,235380,235382,235386,4127,1956,1097,1102,862,867]
  · wct_piece 41 240160 49
  · wct_piece 41 240165 50
  · wct_piece 41 240167 51
  · wct_piece 20 235375 16
  · wct_piece 20 235380 17
  · wct_piece 20 235382 18
  · wct_piece 20 235386 19
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine605_ready : RoutineReady ⟨605, by decide⟩ routine605 := by
  wct_ready_start 605 18 29
  wct_cases [240168,240173,240175,235395,235400,235402,235406,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 41 240168 52
  · wct_piece 41 240173 53
  · wct_piece 41 240175 54
  · wct_piece 20 235395 22
  · wct_piece 20 235400 23
  · wct_piece 20 235402 24
  · wct_piece 20 235406 25
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine606_ready : RoutineReady ⟨606, by decide⟩ routine606 := by
  wct_ready_start 606 18 30
  wct_cases [240176,240181,240183,235415,235420,235422,235426,1991,1996,2000,1301,862,867]
  · wct_piece 41 240176 55
  · wct_piece 41 240181 56
  · wct_piece 41 240183 57
  · wct_piece 20 235415 28
  · wct_piece 20 235420 29
  · wct_piece 20 235422 30
  · wct_piece 20 235426 31
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine607_ready : RoutineReady ⟨607, by decide⟩ routine607 := by
  wct_ready_start 607 18 31
  wct_cases [240184,240189,240191,235435,235440,235442,235446,2016,2021,1320,1325,1329,945]
  · wct_piece 41 240184 58
  · wct_piece 41 240189 59
  · wct_piece 41 240191 60
  · wct_piece 20 235435 34
  · wct_piece 20 235440 35
  · wct_piece 20 235442 36
  · wct_piece 20 235446 37
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
end W9Machine.Chain
end
