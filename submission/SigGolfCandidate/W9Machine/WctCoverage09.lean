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
def routine288 : ChainRoutine := ⟨288, [0, 2, 2, 0, 0, 1, 1], [piece235367, piece235372, piece235375, piece235380, piece235382, piece235386, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine289 : ChainRoutine := ⟨289, [0, 2, 2, 0, 0, 2, 0], [piece235387, piece235392, piece235395, piece235400, piece235402, piece235406, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine290 : ChainRoutine := ⟨290, [0, 2, 2, 0, 1, 0, 1], [piece235407, piece235412, piece235415, piece235420, piece235422, piece235426, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine291 : ChainRoutine := ⟨291, [0, 2, 2, 0, 1, 1, 0], [piece235427, piece235432, piece235435, piece235440, piece235442, piece235446, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine292 : ChainRoutine := ⟨292, [0, 2, 2, 0, 2, 0, 0], [piece235447, piece235452, piece235455, piece235460, piece235462, piece235466, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine293 : ChainRoutine := ⟨293, [0, 2, 2, 1, 0, 0, 1], [piece235467, piece235472, piece235475, piece235480, piece235483, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine294 : ChainRoutine := ⟨294, [0, 2, 2, 1, 0, 1, 0], [piece235484, piece235489, piece235492, piece235497, piece235500, piece235505, piece235509, piece1320, piece1325, piece1329, piece945]⟩
def routine295 : ChainRoutine := ⟨295, [0, 2, 2, 1, 1, 0, 0], [piece235510, piece235515, piece235518, piece235523, piece235526, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine296 : ChainRoutine := ⟨296, [0, 2, 2, 2, 0, 0, 0], [piece235527, piece235532, piece235535, piece235540, piece235543, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine297 : ChainRoutine := ⟨297, [0, 2, 3, 0, 0, 0, 1], [piece235544, piece235549, piece235552, piece235557, piece235559, piece235561, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine298 : ChainRoutine := ⟨298, [0, 2, 3, 0, 0, 1, 0], [piece235566, piece235571, piece235574, piece235579, piece235581, piece235583, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine299 : ChainRoutine := ⟨299, [0, 2, 3, 0, 1, 0, 0], [piece235588, piece235593, piece235596, piece235601, piece235603, piece235605, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine300 : ChainRoutine := ⟨300, [0, 2, 3, 1, 0, 0, 0], [piece235610, piece235615, piece235618, piece235623, piece235625, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine301 : ChainRoutine := ⟨301, [0, 3, 0, 0, 0, 0, 3], [piece235638, piece235643, piece235645, piece235647, piece235651, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine302 : ChainRoutine := ⟨302, [0, 3, 0, 0, 0, 1, 2], [piece235652, piece235657, piece235659, piece235661, piece235665, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine303 : ChainRoutine := ⟨303, [0, 3, 0, 0, 0, 2, 1], [piece235666, piece235671, piece235673, piece235675, piece235679, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine304 : ChainRoutine := ⟨304, [0, 3, 0, 0, 0, 3, 0], [piece235680, piece235685, piece235687, piece235689, piece235693, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine305 : ChainRoutine := ⟨305, [0, 3, 0, 0, 1, 0, 2], [piece235694, piece235699, piece235701, piece235703, piece235707, piece2601, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine306 : ChainRoutine := ⟨306, [0, 3, 0, 0, 1, 1, 1], [piece235708, piece235713, piece235715, piece235717, piece235721, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine307 : ChainRoutine := ⟨307, [0, 3, 0, 0, 1, 2, 0], [piece235722, piece235727, piece235729, piece235731, piece235735, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine308 : ChainRoutine := ⟨308, [0, 3, 0, 0, 2, 0, 1], [piece235736, piece235741, piece235743, piece235745, piece235749, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine309 : ChainRoutine := ⟨309, [0, 3, 0, 0, 2, 1, 0], [piece235750, piece235755, piece235757, piece235759, piece235763, piece2657, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine310 : ChainRoutine := ⟨310, [0, 3, 0, 0, 3, 0, 0], [piece235764, piece235769, piece235771, piece235773, piece235777, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine311 : ChainRoutine := ⟨311, [0, 3, 0, 1, 0, 0, 2], [piece235778, piece235783, piece235785, piece235787, piece235791, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine312 : ChainRoutine := ⟨312, [0, 3, 0, 1, 0, 1, 1], [piece235792, piece235797, piece235799, piece235801, piece235805, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine313 : ChainRoutine := ⟨313, [0, 3, 0, 1, 0, 2, 0], [piece235806, piece235811, piece235813, piece235815, piece235819, piece235824, piece235828, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine314 : ChainRoutine := ⟨314, [0, 3, 0, 1, 1, 0, 1], [piece235829, piece235834, piece235836, piece235838, piece235842, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine315 : ChainRoutine := ⟨315, [0, 3, 0, 1, 1, 1, 0], [piece235843, piece235848, piece235850, piece235852, piece235856, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine316 : ChainRoutine := ⟨316, [0, 3, 0, 1, 2, 0, 0], [piece235857, piece235862, piece235864, piece235866, piece235870, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine317 : ChainRoutine := ⟨317, [0, 3, 0, 2, 0, 0, 1], [piece235871, piece235876, piece235878, piece235880, piece235884, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine318 : ChainRoutine := ⟨318, [0, 3, 0, 2, 0, 1, 0], [piece235885, piece235890, piece235892, piece235894, piece235898, piece235903, piece235905, piece235909, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine319 : ChainRoutine := ⟨319, [0, 3, 0, 2, 1, 0, 0], [piece235910, piece235915, piece235917, piece235919, piece235923, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routineBatch09 : List ChainRoutine := [routine288, routine289, routine290, routine291, routine292, routine293, routine294, routine295, routine296, routine297, routine298, routine299, routine300, routine301, routine302, routine303, routine304, routine305, routine306, routine307, routine308, routine309, routine310, routine311, routine312, routine313, routine314, routine315, routine316, routine317, routine318, routine319]
theorem routineBatch09_checked : (routineBatch09.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch09_checked :
    (routineBatch09.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch09_checked :
    (routineBatch09.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine288_ready : RoutineReady ⟨288, by decide⟩ routine288 := by
  wct_ready_start 288 9 0
  wct_cases [235367,235372,235375,235380,235382,235386,4127,1956,1097,1102,862,867]
  · wct_piece 20 235367 14
  · wct_piece 20 235372 15
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
theorem routine289_ready : RoutineReady ⟨289, by decide⟩ routine289 := by
  wct_ready_start 289 9 1
  wct_cases [235387,235392,235395,235400,235402,235406,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 20 235387 20
  · wct_piece 20 235392 21
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
theorem routine290_ready : RoutineReady ⟨290, by decide⟩ routine290 := by
  wct_ready_start 290 9 2
  wct_cases [235407,235412,235415,235420,235422,235426,1991,1996,2000,1301,862,867]
  · wct_piece 20 235407 26
  · wct_piece 20 235412 27
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
theorem routine291_ready : RoutineReady ⟨291, by decide⟩ routine291 := by
  wct_ready_start 291 9 3
  wct_cases [235427,235432,235435,235440,235442,235446,2016,2021,1320,1325,1329,945]
  · wct_piece 20 235427 32
  · wct_piece 20 235432 33
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
theorem routine292_ready : RoutineReady ⟨292, by decide⟩ routine292 := by
  wct_ready_start 292 9 4
  wct_cases [235447,235452,235455,235460,235462,235466,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 20 235447 38
  · wct_piece 20 235452 39
  · wct_piece 20 235455 40
  · wct_piece 20 235460 41
  · wct_piece 20 235462 42
  · wct_piece 20 235466 43
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine293_ready : RoutineReady ⟨293, by decide⟩ routine293 := by
  wct_ready_start 293 9 5
  wct_cases [235467,235472,235475,235480,235483,4219,4224,4228,2481,1301,862,867]
  · wct_piece 20 235467 44
  · wct_piece 20 235472 45
  · wct_piece 20 235475 46
  · wct_piece 20 235480 47
  · wct_piece 20 235483 48
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine294_ready : RoutineReady ⟨294, by decide⟩ routine294 := by
  wct_ready_start 294 9 6
  wct_cases [235484,235489,235492,235497,235500,235505,235509,1320,1325,1329,945]
  · wct_piece 20 235484 49
  · wct_piece 20 235489 50
  · wct_piece 20 235492 51
  · wct_piece 20 235497 52
  · wct_piece 20 235500 53
  · wct_piece 20 235505 54
  · wct_piece 20 235509 55
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine295_ready : RoutineReady ⟨295, by decide⟩ routine295 := by
  wct_ready_start 295 9 7
  wct_cases [235510,235515,235518,235523,235526,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 20 235510 56
  · wct_piece 20 235515 57
  · wct_piece 20 235518 58
  · wct_piece 20 235523 59
  · wct_piece 20 235526 60
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine296_ready : RoutineReady ⟨296, by decide⟩ routine296 := by
  wct_ready_start 296 9 8
  wct_cases [235527,235532,235535,235540,235543,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 20 235527 61
  · wct_piece 20 235532 62
  · wct_piece 20 235535 63
  · wct_piece 21 235540 0
  · wct_piece 21 235543 1
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine297_ready : RoutineReady ⟨297, by decide⟩ routine297 := by
  wct_ready_start 297 9 9
  wct_cases [235544,235549,235552,235557,235559,235561,235565,2481,1301,862,867]
  · wct_piece 21 235544 2
  · wct_piece 21 235549 3
  · wct_piece 21 235552 4
  · wct_piece 21 235557 5
  · wct_piece 21 235559 6
  · wct_piece 21 235561 7
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine298_ready : RoutineReady ⟨298, by decide⟩ routine298 := by
  wct_ready_start 298 9 10
  wct_cases [235566,235571,235574,235579,235581,235583,235587,2503,1320,1325,1329,945]
  · wct_piece 21 235566 9
  · wct_piece 21 235571 10
  · wct_piece 21 235574 11
  · wct_piece 21 235579 12
  · wct_piece 21 235581 13
  · wct_piece 21 235583 14
  · wct_piece 21 235587 15
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine299_ready : RoutineReady ⟨299, by decide⟩ routine299 := by
  wct_ready_start 299 9 11
  wct_cases [235588,235593,235596,235601,235603,235605,235609,2522,2527,2531,1502,945]
  · wct_piece 21 235588 16
  · wct_piece 21 235593 17
  · wct_piece 21 235596 18
  · wct_piece 21 235601 19
  · wct_piece 21 235603 20
  · wct_piece 21 235605 21
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine300_ready : RoutineReady ⟨300, by decide⟩ routine300 := by
  wct_ready_start 300 9 12
  wct_cases [235610,235615,235618,235623,235625,235628,235633,235637,2866,1502,945]
  · wct_piece 21 235610 23
  · wct_piece 21 235615 24
  · wct_piece 21 235618 25
  · wct_piece 21 235623 26
  · wct_piece 21 235625 27
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine301_ready : RoutineReady ⟨301, by decide⟩ routine301 := by
  wct_ready_start 301 9 13
  wct_cases [235638,235643,235645,235647,235651,2545,1343,886,754,759,761,764]
  · wct_piece 21 235638 31
  · wct_piece 21 235643 32
  · wct_piece 21 235645 33
  · wct_piece 21 235647 34
  · wct_piece 21 235651 35
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine302_ready : RoutineReady ⟨302, by decide⟩ routine302 := by
  wct_ready_start 302 9 14
  wct_cases [235652,235657,235659,235661,235665,2559,1357,897,902,799,804,807]
  · wct_piece 21 235652 36
  · wct_piece 21 235657 37
  · wct_piece 21 235659 38
  · wct_piece 21 235661 39
  · wct_piece 21 235665 40
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine303_ready : RoutineReady ⟨303, by decide⟩ routine303 := by
  wct_ready_start 303 9 15
  wct_cases [235666,235671,235673,235675,235679,2573,1371,913,918,921,862,867]
  · wct_piece 21 235666 41
  · wct_piece 21 235671 42
  · wct_piece 21 235673 43
  · wct_piece 21 235675 44
  · wct_piece 21 235679 45
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine304_ready : RoutineReady ⟨304, by decide⟩ routine304 := by
  wct_ready_start 304 9 16
  wct_cases [235680,235685,235687,235689,235693,2587,1385,932,937,939,941,945]
  · wct_piece 21 235680 46
  · wct_piece 21 235685 47
  · wct_piece 21 235687 48
  · wct_piece 21 235689 49
  · wct_piece 21 235693 50
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine305_ready : RoutineReady ⟨305, by decide⟩ routine305 := by
  wct_ready_start 305 9 17
  wct_cases [235694,235699,235701,235703,235707,2601,1396,1401,1405,1081,799,804,807]
  · wct_piece 21 235694 51
  · wct_piece 21 235699 52
  · wct_piece 21 235701 53
  · wct_piece 21 235703 54
  · wct_piece 21 235707 55
  · wct_piece 8 2601 44
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine306_ready : RoutineReady ⟨306, by decide⟩ routine306 := by
  wct_ready_start 306 9 18
  wct_cases [235708,235713,235715,235717,235721,2615,1416,1421,1097,1102,862,867]
  · wct_piece 21 235708 56
  · wct_piece 21 235713 57
  · wct_piece 21 235715 58
  · wct_piece 21 235717 59
  · wct_piece 21 235721 60
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine307_ready : RoutineReady ⟨307, by decide⟩ routine307 := by
  wct_ready_start 307 9 19
  wct_cases [235722,235727,235729,235731,235735,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 21 235722 61
  · wct_piece 21 235727 62
  · wct_piece 21 235729 63
  · wct_piece 22 235731 0
  · wct_piece 22 235735 1
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine308_ready : RoutineReady ⟨308, by decide⟩ routine308 := by
  wct_ready_start 308 9 20
  wct_cases [235736,235741,235743,235745,235749,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 22 235736 2
  · wct_piece 22 235741 3
  · wct_piece 22 235743 4
  · wct_piece 22 235745 5
  · wct_piece 22 235749 6
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine309_ready : RoutineReady ⟨309, by decide⟩ routine309 := by
  wct_ready_start 309 9 21
  wct_cases [235750,235755,235757,235759,235763,2657,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 22 235750 7
  · wct_piece 22 235755 8
  · wct_piece 22 235757 9
  · wct_piece 22 235759 10
  · wct_piece 22 235763 11
  · wct_piece 9 2657 0
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine310_ready : RoutineReady ⟨310, by decide⟩ routine310 := by
  wct_ready_start 310 9 22
  wct_cases [235764,235769,235771,235773,235777,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 22 235764 12
  · wct_piece 22 235769 13
  · wct_piece 22 235771 14
  · wct_piece 22 235773 15
  · wct_piece 22 235777 16
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine311_ready : RoutineReady ⟨311, by decide⟩ routine311 := by
  wct_ready_start 311 9 23
  wct_cases [235778,235783,235785,235787,235791,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 22 235778 17
  · wct_piece 22 235783 18
  · wct_piece 22 235785 19
  · wct_piece 22 235787 20
  · wct_piece 22 235791 21
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine312_ready : RoutineReady ⟨312, by decide⟩ routine312 := by
  wct_ready_start 312 9 24
  wct_cases [235792,235797,235799,235801,235805,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 22 235792 22
  · wct_piece 22 235797 23
  · wct_piece 22 235799 24
  · wct_piece 22 235801 25
  · wct_piece 22 235805 26
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine313_ready : RoutineReady ⟨313, by decide⟩ routine313 := by
  wct_ready_start 313 9 25
  wct_cases [235806,235811,235813,235815,235819,235824,235828,1975,1118,1123,1125,1129,945]
  · wct_piece 22 235806 27
  · wct_piece 22 235811 28
  · wct_piece 22 235813 29
  · wct_piece 22 235815 30
  · wct_piece 22 235819 31
  · wct_piece 22 235824 32
  · wct_piece 22 235828 33
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine314_ready : RoutineReady ⟨314, by decide⟩ routine314 := by
  wct_ready_start 314 9 26
  wct_cases [235829,235834,235836,235838,235842,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 22 235829 34
  · wct_piece 22 235834 35
  · wct_piece 22 235836 36
  · wct_piece 22 235838 37
  · wct_piece 22 235842 38
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine315_ready : RoutineReady ⟨315, by decide⟩ routine315 := by
  wct_ready_start 315 9 27
  wct_cases [235843,235848,235850,235852,235856,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 22 235843 39
  · wct_piece 22 235848 40
  · wct_piece 22 235850 41
  · wct_piece 22 235852 42
  · wct_piece 22 235856 43
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine316_ready : RoutineReady ⟨316, by decide⟩ routine316 := by
  wct_ready_start 316 9 28
  wct_cases [235857,235862,235864,235866,235870,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 22 235857 44
  · wct_piece 22 235862 45
  · wct_piece 22 235864 46
  · wct_piece 22 235866 47
  · wct_piece 22 235870 48
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine317_ready : RoutineReady ⟨317, by decide⟩ routine317 := by
  wct_ready_start 317 9 29
  wct_cases [235871,235876,235878,235880,235884,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 22 235871 49
  · wct_piece 22 235876 50
  · wct_piece 22 235878 51
  · wct_piece 22 235880 52
  · wct_piece 22 235884 53
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine318_ready : RoutineReady ⟨318, by decide⟩ routine318 := by
  wct_ready_start 318 9 30
  wct_cases [235885,235890,235892,235894,235898,235903,235905,235909,2503,1320,1325,1329,945]
  · wct_piece 22 235885 54
  · wct_piece 22 235890 55
  · wct_piece 22 235892 56
  · wct_piece 22 235894 57
  · wct_piece 22 235898 58
  · wct_piece 22 235903 59
  · wct_piece 22 235905 60
  · wct_piece 22 235909 61
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine319_ready : RoutineReady ⟨319, by decide⟩ routine319 := by
  wct_ready_start 319 9 31
  wct_cases [235910,235915,235917,235919,235923,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 22 235910 62
  · wct_piece 22 235915 63
  · wct_piece 23 235917 0
  · wct_piece 23 235919 1
  · wct_piece 23 235923 2
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage09 (rank : Fin 728) (hlo : 288 ≤ rank.val) (hhi : rank.val < 320) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 288 ≤ n at hlo
  change n < 320 at hhi
  interval_cases n
  · exact ⟨routine288, routine288_ready⟩
  · exact ⟨routine289, routine289_ready⟩
  · exact ⟨routine290, routine290_ready⟩
  · exact ⟨routine291, routine291_ready⟩
  · exact ⟨routine292, routine292_ready⟩
  · exact ⟨routine293, routine293_ready⟩
  · exact ⟨routine294, routine294_ready⟩
  · exact ⟨routine295, routine295_ready⟩
  · exact ⟨routine296, routine296_ready⟩
  · exact ⟨routine297, routine297_ready⟩
  · exact ⟨routine298, routine298_ready⟩
  · exact ⟨routine299, routine299_ready⟩
  · exact ⟨routine300, routine300_ready⟩
  · exact ⟨routine301, routine301_ready⟩
  · exact ⟨routine302, routine302_ready⟩
  · exact ⟨routine303, routine303_ready⟩
  · exact ⟨routine304, routine304_ready⟩
  · exact ⟨routine305, routine305_ready⟩
  · exact ⟨routine306, routine306_ready⟩
  · exact ⟨routine307, routine307_ready⟩
  · exact ⟨routine308, routine308_ready⟩
  · exact ⟨routine309, routine309_ready⟩
  · exact ⟨routine310, routine310_ready⟩
  · exact ⟨routine311, routine311_ready⟩
  · exact ⟨routine312, routine312_ready⟩
  · exact ⟨routine313, routine313_ready⟩
  · exact ⟨routine314, routine314_ready⟩
  · exact ⟨routine315, routine315_ready⟩
  · exact ⟨routine316, routine316_ready⟩
  · exact ⟨routine317, routine317_ready⟩
  · exact ⟨routine318, routine318_ready⟩
  · exact ⟨routine319, routine319_ready⟩
end W9Machine.Chain
end
