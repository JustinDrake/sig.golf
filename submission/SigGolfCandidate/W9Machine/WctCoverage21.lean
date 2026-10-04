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
def routine672 : ChainRoutine := ⟨672, [3, 0, 0, 0, 0, 0, 3], [piece241439, piece241444, piece241446, piece241448, piece235651, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine673 : ChainRoutine := ⟨673, [3, 0, 0, 0, 0, 1, 2], [piece241449, piece241454, piece241456, piece241458, piece235665, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine674 : ChainRoutine := ⟨674, [3, 0, 0, 0, 0, 2, 1], [piece241459, piece241464, piece241466, piece241468, piece235679, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine675 : ChainRoutine := ⟨675, [3, 0, 0, 0, 0, 3, 0], [piece241469, piece241474, piece241476, piece241478, piece235693, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine676 : ChainRoutine := ⟨676, [3, 0, 0, 0, 1, 0, 2], [piece241479, piece241484, piece241486, piece241488, piece235707, piece2601, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine677 : ChainRoutine := ⟨677, [3, 0, 0, 0, 1, 1, 1], [piece241489, piece241494, piece241496, piece241498, piece235721, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine678 : ChainRoutine := ⟨678, [3, 0, 0, 0, 1, 2, 0], [piece241499, piece241504, piece241506, piece241508, piece235735, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine679 : ChainRoutine := ⟨679, [3, 0, 0, 0, 2, 0, 1], [piece241509, piece241514, piece241516, piece241518, piece235749, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine680 : ChainRoutine := ⟨680, [3, 0, 0, 0, 2, 1, 0], [piece241519, piece241524, piece241526, piece241528, piece235763, piece2657, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine681 : ChainRoutine := ⟨681, [3, 0, 0, 0, 3, 0, 0], [piece241529, piece241534, piece241536, piece241538, piece235777, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine682 : ChainRoutine := ⟨682, [3, 0, 0, 1, 0, 0, 2], [piece241539, piece241544, piece241546, piece241548, piece235791, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine683 : ChainRoutine := ⟨683, [3, 0, 0, 1, 0, 1, 1], [piece241549, piece241554, piece241556, piece241558, piece235805, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine684 : ChainRoutine := ⟨684, [3, 0, 0, 1, 0, 2, 0], [piece241559, piece241564, piece241566, piece241568, piece235819, piece235824, piece235828, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine685 : ChainRoutine := ⟨685, [3, 0, 0, 1, 1, 0, 1], [piece241569, piece241574, piece241576, piece241578, piece235842, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine686 : ChainRoutine := ⟨686, [3, 0, 0, 1, 1, 1, 0], [piece241579, piece241584, piece241586, piece241588, piece235856, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine687 : ChainRoutine := ⟨687, [3, 0, 0, 1, 2, 0, 0], [piece241589, piece241594, piece241596, piece241598, piece235870, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine688 : ChainRoutine := ⟨688, [3, 0, 0, 2, 0, 0, 1], [piece241599, piece241604, piece241606, piece241608, piece235884, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine689 : ChainRoutine := ⟨689, [3, 0, 0, 2, 0, 1, 0], [piece241609, piece241614, piece241616, piece241618, piece235898, piece235903, piece235905, piece235909, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine690 : ChainRoutine := ⟨690, [3, 0, 0, 2, 1, 0, 0], [piece241619, piece241624, piece241626, piece241628, piece235923, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine691 : ChainRoutine := ⟨691, [3, 0, 0, 3, 0, 0, 0], [piece241629, piece241634, piece241636, piece241638, piece235937, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine692 : ChainRoutine := ⟨692, [3, 0, 1, 0, 0, 0, 2], [piece241639, piece241644, piece241646, piece241648, piece235948, piece235953, piece235957, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine693 : ChainRoutine := ⟨693, [3, 0, 1, 0, 0, 1, 1], [piece241649, piece241654, piece241656, piece241658, piece235968, piece235973, piece235977, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine694 : ChainRoutine := ⟨694, [3, 0, 1, 0, 0, 2, 0], [piece241659, piece241664, piece241666, piece241668, piece235988, piece235993, piece235997, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine695 : ChainRoutine := ⟨695, [3, 0, 1, 0, 1, 0, 1], [piece241669, piece241674, piece241676, piece241678, piece236008, piece236013, piece236017, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine696 : ChainRoutine := ⟨696, [3, 0, 1, 0, 1, 1, 0], [piece241679, piece241684, piece241686, piece241688, piece236028, piece236033, piece236037, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine697 : ChainRoutine := ⟨697, [3, 0, 1, 0, 2, 0, 0], [piece241689, piece241694, piece241696, piece241698, piece236048, piece236053, piece236057, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine698 : ChainRoutine := ⟨698, [3, 0, 1, 1, 0, 0, 1], [piece241699, piece241704, piece241706, piece241708, piece236068, piece236073, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine699 : ChainRoutine := ⟨699, [3, 0, 1, 1, 0, 1, 0], [piece241709, piece241714, piece241716, piece241718, piece236084, piece236089, piece236094, piece236098, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine700 : ChainRoutine := ⟨700, [3, 0, 1, 1, 1, 0, 0], [piece241719, piece241724, piece241726, piece241728, piece236109, piece236114, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine701 : ChainRoutine := ⟨701, [3, 0, 1, 2, 0, 0, 0], [piece241729, piece241734, piece241736, piece241738, piece236125, piece236130, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine702 : ChainRoutine := ⟨702, [3, 0, 2, 0, 0, 0, 1], [piece241739, piece241744, piece241746, piece241748, piece236141, piece236146, piece236148, piece236152, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine703 : ChainRoutine := ⟨703, [3, 0, 2, 0, 0, 1, 0], [piece241749, piece241754, piece241756, piece241758, piece236163, piece236168, piece236170, piece236174, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routineBatch21 : List ChainRoutine := [routine672, routine673, routine674, routine675, routine676, routine677, routine678, routine679, routine680, routine681, routine682, routine683, routine684, routine685, routine686, routine687, routine688, routine689, routine690, routine691, routine692, routine693, routine694, routine695, routine696, routine697, routine698, routine699, routine700, routine701, routine702, routine703]
theorem routineBatch21_checked : (routineBatch21.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch21_checked :
    (routineBatch21.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch21_checked :
    (routineBatch21.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine672_ready : RoutineReady ⟨672, by decide⟩ routine672 := by
  wct_ready_start 672 21 0
  wct_cases [241439,241444,241446,241448,235651,2545,1343,886,754,759,761,764]
  · wct_piece 47 241439 41
  · wct_piece 47 241444 42
  · wct_piece 47 241446 43
  · wct_piece 47 241448 44
  · wct_piece 21 235651 35
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine673_ready : RoutineReady ⟨673, by decide⟩ routine673 := by
  wct_ready_start 673 21 1
  wct_cases [241449,241454,241456,241458,235665,2559,1357,897,902,799,804,807]
  · wct_piece 47 241449 45
  · wct_piece 47 241454 46
  · wct_piece 47 241456 47
  · wct_piece 47 241458 48
  · wct_piece 21 235665 40
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine674_ready : RoutineReady ⟨674, by decide⟩ routine674 := by
  wct_ready_start 674 21 2
  wct_cases [241459,241464,241466,241468,235679,2573,1371,913,918,921,862,867]
  · wct_piece 47 241459 49
  · wct_piece 47 241464 50
  · wct_piece 47 241466 51
  · wct_piece 47 241468 52
  · wct_piece 21 235679 45
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine675_ready : RoutineReady ⟨675, by decide⟩ routine675 := by
  wct_ready_start 675 21 3
  wct_cases [241469,241474,241476,241478,235693,2587,1385,932,937,939,941,945]
  · wct_piece 47 241469 53
  · wct_piece 47 241474 54
  · wct_piece 47 241476 55
  · wct_piece 47 241478 56
  · wct_piece 21 235693 50
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine676_ready : RoutineReady ⟨676, by decide⟩ routine676 := by
  wct_ready_start 676 21 4
  wct_cases [241479,241484,241486,241488,235707,2601,1396,1401,1405,1081,799,804,807]
  · wct_piece 47 241479 57
  · wct_piece 47 241484 58
  · wct_piece 47 241486 59
  · wct_piece 47 241488 60
  · wct_piece 21 235707 55
  · wct_piece 8 2601 44
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine677_ready : RoutineReady ⟨677, by decide⟩ routine677 := by
  wct_ready_start 677 21 5
  wct_cases [241489,241494,241496,241498,235721,2615,1416,1421,1097,1102,862,867]
  · wct_piece 47 241489 61
  · wct_piece 47 241494 62
  · wct_piece 47 241496 63
  · wct_piece 48 241498 0
  · wct_piece 21 235721 60
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine678_ready : RoutineReady ⟨678, by decide⟩ routine678 := by
  wct_ready_start 678 21 6
  wct_cases [241499,241504,241506,241508,235735,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 48 241499 1
  · wct_piece 48 241504 2
  · wct_piece 48 241506 3
  · wct_piece 48 241508 4
  · wct_piece 22 235735 1
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine679_ready : RoutineReady ⟨679, by decide⟩ routine679 := by
  wct_ready_start 679 21 7
  wct_cases [241509,241514,241516,241518,235749,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 48 241509 5
  · wct_piece 48 241514 6
  · wct_piece 48 241516 7
  · wct_piece 48 241518 8
  · wct_piece 22 235749 6
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine680_ready : RoutineReady ⟨680, by decide⟩ routine680 := by
  wct_ready_start 680 21 8
  wct_cases [241519,241524,241526,241528,235763,2657,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 48 241519 9
  · wct_piece 48 241524 10
  · wct_piece 48 241526 11
  · wct_piece 48 241528 12
  · wct_piece 22 235763 11
  · wct_piece 9 2657 0
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine681_ready : RoutineReady ⟨681, by decide⟩ routine681 := by
  wct_ready_start 681 21 9
  wct_cases [241529,241534,241536,241538,235777,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 48 241529 13
  · wct_piece 48 241534 14
  · wct_piece 48 241536 15
  · wct_piece 48 241538 16
  · wct_piece 22 235777 16
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine682_ready : RoutineReady ⟨682, by decide⟩ routine682 := by
  wct_ready_start 682 21 10
  wct_cases [241539,241544,241546,241548,235791,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 48 241539 17
  · wct_piece 48 241544 18
  · wct_piece 48 241546 19
  · wct_piece 48 241548 20
  · wct_piece 22 235791 21
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine683_ready : RoutineReady ⟨683, by decide⟩ routine683 := by
  wct_ready_start 683 21 11
  wct_cases [241549,241554,241556,241558,235805,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 48 241549 21
  · wct_piece 48 241554 22
  · wct_piece 48 241556 23
  · wct_piece 48 241558 24
  · wct_piece 22 235805 26
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine684_ready : RoutineReady ⟨684, by decide⟩ routine684 := by
  wct_ready_start 684 21 12
  wct_cases [241559,241564,241566,241568,235819,235824,235828,1975,1118,1123,1125,1129,945]
  · wct_piece 48 241559 25
  · wct_piece 48 241564 26
  · wct_piece 48 241566 27
  · wct_piece 48 241568 28
  · wct_piece 22 235819 31
  · wct_piece 22 235824 32
  · wct_piece 22 235828 33
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine685_ready : RoutineReady ⟨685, by decide⟩ routine685 := by
  wct_ready_start 685 21 13
  wct_cases [241569,241574,241576,241578,235842,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 48 241569 29
  · wct_piece 48 241574 30
  · wct_piece 48 241576 31
  · wct_piece 48 241578 32
  · wct_piece 22 235842 38
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine686_ready : RoutineReady ⟨686, by decide⟩ routine686 := by
  wct_ready_start 686 21 14
  wct_cases [241579,241584,241586,241588,235856,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 48 241579 33
  · wct_piece 48 241584 34
  · wct_piece 48 241586 35
  · wct_piece 48 241588 36
  · wct_piece 22 235856 43
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine687_ready : RoutineReady ⟨687, by decide⟩ routine687 := by
  wct_ready_start 687 21 15
  wct_cases [241589,241594,241596,241598,235870,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 48 241589 37
  · wct_piece 48 241594 38
  · wct_piece 48 241596 39
  · wct_piece 48 241598 40
  · wct_piece 22 235870 48
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine688_ready : RoutineReady ⟨688, by decide⟩ routine688 := by
  wct_ready_start 688 21 16
  wct_cases [241599,241604,241606,241608,235884,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 48 241599 41
  · wct_piece 48 241604 42
  · wct_piece 48 241606 43
  · wct_piece 48 241608 44
  · wct_piece 22 235884 53
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine689_ready : RoutineReady ⟨689, by decide⟩ routine689 := by
  wct_ready_start 689 21 17
  wct_cases [241609,241614,241616,241618,235898,235903,235905,235909,2503,1320,1325,1329,945]
  · wct_piece 48 241609 45
  · wct_piece 48 241614 46
  · wct_piece 48 241616 47
  · wct_piece 48 241618 48
  · wct_piece 22 235898 58
  · wct_piece 22 235903 59
  · wct_piece 22 235905 60
  · wct_piece 22 235909 61
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine690_ready : RoutineReady ⟨690, by decide⟩ routine690 := by
  wct_ready_start 690 21 18
  wct_cases [241619,241624,241626,241628,235923,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 48 241619 49
  · wct_piece 48 241624 50
  · wct_piece 48 241626 51
  · wct_piece 48 241628 52
  · wct_piece 23 235923 2
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine691_ready : RoutineReady ⟨691, by decide⟩ routine691 := by
  wct_ready_start 691 21 19
  wct_cases [241629,241634,241636,241638,235937,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 48 241629 53
  · wct_piece 48 241634 54
  · wct_piece 48 241636 55
  · wct_piece 48 241638 56
  · wct_piece 23 235937 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine692_ready : RoutineReady ⟨692, by decide⟩ routine692 := by
  wct_ready_start 692 21 20
  wct_cases [241639,241644,241646,241648,235948,235953,235957,4108,1937,1081,799,804,807]
  · wct_piece 48 241639 57
  · wct_piece 48 241644 58
  · wct_piece 48 241646 59
  · wct_piece 48 241648 60
  · wct_piece 23 235948 11
  · wct_piece 23 235953 12
  · wct_piece 23 235957 13
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine693_ready : RoutineReady ⟨693, by decide⟩ routine693 := by
  wct_ready_start 693 21 21
  wct_cases [241649,241654,241656,241658,235968,235973,235977,4127,1956,1097,1102,862,867]
  · wct_piece 48 241649 61
  · wct_piece 48 241654 62
  · wct_piece 48 241656 63
  · wct_piece 49 241658 0
  · wct_piece 23 235968 17
  · wct_piece 23 235973 18
  · wct_piece 23 235977 19
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine694_ready : RoutineReady ⟨694, by decide⟩ routine694 := by
  wct_ready_start 694 21 22
  wct_cases [241659,241664,241666,241668,235988,235993,235997,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 49 241659 1
  · wct_piece 49 241664 2
  · wct_piece 49 241666 3
  · wct_piece 49 241668 4
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
theorem routine695_ready : RoutineReady ⟨695, by decide⟩ routine695 := by
  wct_ready_start 695 21 23
  wct_cases [241669,241674,241676,241678,236008,236013,236017,1991,1996,2000,1301,862,867]
  · wct_piece 49 241669 5
  · wct_piece 49 241674 6
  · wct_piece 49 241676 7
  · wct_piece 49 241678 8
  · wct_piece 23 236008 29
  · wct_piece 23 236013 30
  · wct_piece 23 236017 31
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine696_ready : RoutineReady ⟨696, by decide⟩ routine696 := by
  wct_ready_start 696 21 24
  wct_cases [241679,241684,241686,241688,236028,236033,236037,2016,2021,1320,1325,1329,945]
  · wct_piece 49 241679 9
  · wct_piece 49 241684 10
  · wct_piece 49 241686 11
  · wct_piece 49 241688 12
  · wct_piece 23 236028 35
  · wct_piece 23 236033 36
  · wct_piece 23 236037 37
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine697_ready : RoutineReady ⟨697, by decide⟩ routine697 := by
  wct_ready_start 697 21 25
  wct_cases [241689,241694,241696,241698,236048,236053,236057,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 49 241689 13
  · wct_piece 49 241694 14
  · wct_piece 49 241696 15
  · wct_piece 49 241698 16
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
theorem routine698_ready : RoutineReady ⟨698, by decide⟩ routine698 := by
  wct_ready_start 698 21 26
  wct_cases [241699,241704,241706,241708,236068,236073,4219,4224,4228,2481,1301,862,867]
  · wct_piece 49 241699 17
  · wct_piece 49 241704 18
  · wct_piece 49 241706 19
  · wct_piece 49 241708 20
  · wct_piece 23 236068 47
  · wct_piece 23 236073 48
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine699_ready : RoutineReady ⟨699, by decide⟩ routine699 := by
  wct_ready_start 699 21 27
  wct_cases [241709,241714,241716,241718,236084,236089,236094,236098,2503,1320,1325,1329,945]
  · wct_piece 49 241709 21
  · wct_piece 49 241714 22
  · wct_piece 49 241716 23
  · wct_piece 49 241718 24
  · wct_piece 23 236084 52
  · wct_piece 23 236089 53
  · wct_piece 23 236094 54
  · wct_piece 23 236098 55
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine700_ready : RoutineReady ⟨700, by decide⟩ routine700 := by
  wct_ready_start 700 21 28
  wct_cases [241719,241724,241726,241728,236109,236114,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 49 241719 25
  · wct_piece 49 241724 26
  · wct_piece 49 241726 27
  · wct_piece 49 241728 28
  · wct_piece 23 236109 59
  · wct_piece 23 236114 60
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine701_ready : RoutineReady ⟨701, by decide⟩ routine701 := by
  wct_ready_start 701 21 29
  wct_cases [241729,241734,241736,241738,236125,236130,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 49 241729 29
  · wct_piece 49 241734 30
  · wct_piece 49 241736 31
  · wct_piece 49 241738 32
  · wct_piece 24 236125 0
  · wct_piece 24 236130 1
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine702_ready : RoutineReady ⟨702, by decide⟩ routine702 := by
  wct_ready_start 702 21 30
  wct_cases [241739,241744,241746,241748,236141,236146,236148,236152,235565,2481,1301,862,867]
  · wct_piece 49 241739 33
  · wct_piece 49 241744 34
  · wct_piece 49 241746 35
  · wct_piece 49 241748 36
  · wct_piece 24 236141 5
  · wct_piece 24 236146 6
  · wct_piece 24 236148 7
  · wct_piece 24 236152 8
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine703_ready : RoutineReady ⟨703, by decide⟩ routine703 := by
  wct_ready_start 703 21 31
  wct_cases [241749,241754,241756,241758,236163,236168,236170,236174,235587,2503,1320,1325,1329,945]
  · wct_piece 49 241749 37
  · wct_piece 49 241754 38
  · wct_piece 49 241756 39
  · wct_piece 49 241758 40
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
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage21 (rank : Fin 728) (hlo : 672 ≤ rank.val) (hhi : rank.val < 704) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 672 ≤ n at hlo
  change n < 704 at hhi
  interval_cases n
  · exact ⟨routine672, routine672_ready⟩
  · exact ⟨routine673, routine673_ready⟩
  · exact ⟨routine674, routine674_ready⟩
  · exact ⟨routine675, routine675_ready⟩
  · exact ⟨routine676, routine676_ready⟩
  · exact ⟨routine677, routine677_ready⟩
  · exact ⟨routine678, routine678_ready⟩
  · exact ⟨routine679, routine679_ready⟩
  · exact ⟨routine680, routine680_ready⟩
  · exact ⟨routine681, routine681_ready⟩
  · exact ⟨routine682, routine682_ready⟩
  · exact ⟨routine683, routine683_ready⟩
  · exact ⟨routine684, routine684_ready⟩
  · exact ⟨routine685, routine685_ready⟩
  · exact ⟨routine686, routine686_ready⟩
  · exact ⟨routine687, routine687_ready⟩
  · exact ⟨routine688, routine688_ready⟩
  · exact ⟨routine689, routine689_ready⟩
  · exact ⟨routine690, routine690_ready⟩
  · exact ⟨routine691, routine691_ready⟩
  · exact ⟨routine692, routine692_ready⟩
  · exact ⟨routine693, routine693_ready⟩
  · exact ⟨routine694, routine694_ready⟩
  · exact ⟨routine695, routine695_ready⟩
  · exact ⟨routine696, routine696_ready⟩
  · exact ⟨routine697, routine697_ready⟩
  · exact ⟨routine698, routine698_ready⟩
  · exact ⟨routine699, routine699_ready⟩
  · exact ⟨routine700, routine700_ready⟩
  · exact ⟨routine701, routine701_ready⟩
  · exact ⟨routine702, routine702_ready⟩
  · exact ⟨routine703, routine703_ready⟩
end W9Machine.Chain
end
