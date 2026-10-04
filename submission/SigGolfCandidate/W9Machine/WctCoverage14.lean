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
def routine448 : ChainRoutine := ⟨448, [1, 1, 0, 0, 3, 1, 0], [piece237232, piece237237, piece237242, piece237246, piece2192, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine449 : ChainRoutine := ⟨449, [1, 1, 0, 1, 0, 0, 3], [piece237247, piece237252, piece237257, piece237261, piece237266, piece237270, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine450 : ChainRoutine := ⟨450, [1, 1, 0, 1, 0, 1, 2], [piece237271, piece237276, piece237281, piece237285, piece237290, piece237294, piece237299, piece237304, piece237307]⟩
def routine451 : ChainRoutine := ⟨451, [1, 1, 0, 1, 0, 2, 1], [piece237313, piece237318, piece237323, piece237327, piece237332, piece237336, piece237341, piece237344, piece237349]⟩
def routine452 : ChainRoutine := ⟨452, [1, 1, 0, 1, 0, 3, 0], [piece237355, piece237360, piece237365, piece237369, piece237374, piece237378, piece237383, piece237385, piece237387, piece237391]⟩
def routine453 : ChainRoutine := ⟨453, [1, 1, 0, 1, 1, 0, 2], [piece237397, piece237402, piece237407, piece237411, piece237416, piece237421, piece237425, piece237430, piece237433]⟩
def routine454 : ChainRoutine := ⟨454, [1, 1, 0, 1, 1, 1, 1], [piece237439, piece237444, piece237449, piece237453, piece237458, piece237463, piece1097, piece1102, piece862, piece867]⟩
def routine455 : ChainRoutine := ⟨455, [1, 1, 0, 1, 1, 2, 0], [piece237464, piece237469, piece237474, piece237478, piece237483, piece237488, piece237493, piece237495, piece237499, piece945]⟩
def routine456 : ChainRoutine := ⟨456, [1, 1, 0, 1, 2, 0, 1], [piece237500, piece237505, piece237510, piece237514, piece237519, piece237524, piece237526, piece237530, piece862, piece867]⟩
def routine457 : ChainRoutine := ⟨457, [1, 1, 0, 1, 2, 1, 0], [piece237531, piece237536, piece237541, piece237545, piece237550, piece237555, piece237558, piece237563, piece237567]⟩
def routine458 : ChainRoutine := ⟨458, [1, 1, 0, 1, 3, 0, 0], [piece237573, piece237578, piece237583, piece237587, piece4593, piece2343, piece2348, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine459 : ChainRoutine := ⟨459, [1, 1, 0, 2, 0, 0, 2], [piece237588, piece237593, piece237598, piece237602, piece237607, piece237609, piece237613, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine460 : ChainRoutine := ⟨460, [1, 1, 0, 2, 0, 1, 1], [piece237614, piece237619, piece237624, piece237628, piece237633, piece237635, piece237639, piece237644, piece862, piece867]⟩
def routine461 : ChainRoutine := ⟨461, [1, 1, 0, 2, 0, 2, 0], [piece237645, piece237650, piece237655, piece237659, piece237664, piece237666, piece237670, piece237675, piece237677, piece237681]⟩
def routine462 : ChainRoutine := ⟨462, [1, 1, 0, 2, 1, 0, 1], [piece237687, piece237692, piece237697, piece237701, piece237706, piece237709, piece237714, piece237718, piece237723]⟩
def routine463 : ChainRoutine := ⟨463, [1, 1, 0, 2, 1, 1, 0], [piece237729, piece237734, piece237739, piece237743, piece237748, piece237751, piece237756, piece237761, piece237765]⟩
def routine464 : ChainRoutine := ⟨464, [1, 1, 0, 2, 2, 0, 0], [piece237771, piece237776, piece237781, piece237785, piece237790, piece237793, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine465 : ChainRoutine := ⟨465, [1, 1, 0, 3, 0, 0, 1], [piece237794, piece237799, piece237804, piece237808, piece4704, piece2468, piece2473, piece2475, piece2477, piece2481, piece1301, piece862, piece867]⟩
def routine466 : ChainRoutine := ⟨466, [1, 1, 0, 3, 0, 1, 0], [piece237809, piece237814, piece237819, piece237823, piece237828, piece237830, piece237832, piece237836, piece237841, piece237845]⟩
def routine467 : ChainRoutine := ⟨467, [1, 1, 0, 3, 1, 0, 0], [piece237851, piece237856, piece237861, piece237865, piece2512, piece2517, piece2519, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine468 : ChainRoutine := ⟨468, [1, 1, 1, 0, 0, 0, 3], [piece237866, piece237871, piece237876, piece4737, piece4742, piece4746, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine469 : ChainRoutine := ⟨469, [1, 1, 1, 0, 0, 1, 2], [piece237877, piece237882, piece237887, piece237892, piece237896, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine470 : ChainRoutine := ⟨470, [1, 1, 1, 0, 0, 2, 1], [piece237897, piece237902, piece237907, piece237912, piece237916, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine471 : ChainRoutine := ⟨471, [1, 1, 1, 0, 0, 3, 0], [piece237917, piece237922, piece237927, piece235052, piece235057, piece235061, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine472 : ChainRoutine := ⟨472, [1, 1, 1, 0, 1, 0, 2], [piece237928, piece237933, piece237938, piece237943, piece237947, piece237952, piece237956, piece237961, piece237964]⟩
def routine473 : ChainRoutine := ⟨473, [1, 1, 1, 0, 1, 1, 1], [piece237970, piece237975, piece237980, piece237985, piece237989, piece237994, piece1097, piece1102, piece862, piece867]⟩
def routine474 : ChainRoutine := ⟨474, [1, 1, 1, 0, 1, 2, 0], [piece237995, piece238000, piece238005, piece238010, piece238014, piece238019, piece238024, piece238026, piece238030, piece945]⟩
def routine475 : ChainRoutine := ⟨475, [1, 1, 1, 0, 2, 0, 1], [piece238031, piece238036, piece238041, piece238046, piece238050, piece238055, piece238057, piece238061, piece862, piece867]⟩
def routine476 : ChainRoutine := ⟨476, [1, 1, 1, 0, 2, 1, 0], [piece238062, piece238067, piece238072, piece238077, piece238081, piece238086, piece238089, piece238094, piece238098]⟩
def routine477 : ChainRoutine := ⟨477, [1, 1, 1, 0, 3, 0, 0], [piece238104, piece238109, piece238114, piece235177, piece235182, piece235186, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine478 : ChainRoutine := ⟨478, [1, 1, 1, 1, 0, 0, 2], [piece238115, piece238120, piece238125, piece238130, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine479 : ChainRoutine := ⟨479, [1, 1, 1, 1, 0, 1, 1], [piece238131, piece238136, piece238141, piece238146, piece238151, piece238155, piece1097, piece1102, piece862, piece867]⟩
def routineBatch14 : List ChainRoutine := [routine448, routine449, routine450, routine451, routine452, routine453, routine454, routine455, routine456, routine457, routine458, routine459, routine460, routine461, routine462, routine463, routine464, routine465, routine466, routine467, routine468, routine469, routine470, routine471, routine472, routine473, routine474, routine475, routine476, routine477, routine478, routine479]
theorem routineBatch14_checked : (routineBatch14.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch14_checked :
    (routineBatch14.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch14_checked :
    (routineBatch14.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine448_ready : RoutineReady ⟨448, by decide⟩ routine448 := by
  wct_ready_start 448 14 0
  wct_cases [237232,237237,237242,237246,2192,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 29 237232 16
  · wct_piece 29 237237 17
  · wct_piece 29 237242 18
  · wct_piece 29 237246 19
  · wct_piece 6 2192 48
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine449_ready : RoutineReady ⟨449, by decide⟩ routine449 := by
  wct_ready_start 449 14 1
  wct_cases [237247,237252,237257,237261,237266,237270,1343,886,754,759,761,764]
  · wct_piece 29 237247 20
  · wct_piece 29 237252 21
  · wct_piece 29 237257 22
  · wct_piece 29 237261 23
  · wct_piece 29 237266 24
  · wct_piece 29 237270 25
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine450_ready : RoutineReady ⟨450, by decide⟩ routine450 := by
  wct_ready_start 450 14 2
  wct_cases [237271,237276,237281,237285,237290,237294,237299,237304,237307]
  · wct_piece 29 237271 26
  · wct_piece 29 237276 27
  · wct_piece 29 237281 28
  · wct_piece 29 237285 29
  · wct_piece 29 237290 30
  · wct_piece 29 237294 31
  · wct_piece 29 237299 32
  · wct_piece 29 237304 33
  · wct_piece 29 237307 34
theorem routine451_ready : RoutineReady ⟨451, by decide⟩ routine451 := by
  wct_ready_start 451 14 3
  wct_cases [237313,237318,237323,237327,237332,237336,237341,237344,237349]
  · wct_piece 29 237313 35
  · wct_piece 29 237318 36
  · wct_piece 29 237323 37
  · wct_piece 29 237327 38
  · wct_piece 29 237332 39
  · wct_piece 29 237336 40
  · wct_piece 29 237341 41
  · wct_piece 29 237344 42
  · wct_piece 29 237349 43
theorem routine452_ready : RoutineReady ⟨452, by decide⟩ routine452 := by
  wct_ready_start 452 14 4
  wct_cases [237355,237360,237365,237369,237374,237378,237383,237385,237387,237391]
  · wct_piece 29 237355 44
  · wct_piece 29 237360 45
  · wct_piece 29 237365 46
  · wct_piece 29 237369 47
  · wct_piece 29 237374 48
  · wct_piece 29 237378 49
  · wct_piece 29 237383 50
  · wct_piece 29 237385 51
  · wct_piece 29 237387 52
  · wct_piece 29 237391 53
theorem routine453_ready : RoutineReady ⟨453, by decide⟩ routine453 := by
  wct_ready_start 453 14 5
  wct_cases [237397,237402,237407,237411,237416,237421,237425,237430,237433]
  · wct_piece 29 237397 54
  · wct_piece 29 237402 55
  · wct_piece 29 237407 56
  · wct_piece 29 237411 57
  · wct_piece 29 237416 58
  · wct_piece 29 237421 59
  · wct_piece 29 237425 60
  · wct_piece 29 237430 61
  · wct_piece 29 237433 62
theorem routine454_ready : RoutineReady ⟨454, by decide⟩ routine454 := by
  wct_ready_start 454 14 6
  wct_cases [237439,237444,237449,237453,237458,237463,1097,1102,862,867]
  · wct_piece 29 237439 63
  · wct_piece 30 237444 0
  · wct_piece 30 237449 1
  · wct_piece 30 237453 2
  · wct_piece 30 237458 3
  · wct_piece 30 237463 4
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine455_ready : RoutineReady ⟨455, by decide⟩ routine455 := by
  wct_ready_start 455 14 7
  wct_cases [237464,237469,237474,237478,237483,237488,237493,237495,237499,945]
  · wct_piece 30 237464 5
  · wct_piece 30 237469 6
  · wct_piece 30 237474 7
  · wct_piece 30 237478 8
  · wct_piece 30 237483 9
  · wct_piece 30 237488 10
  · wct_piece 30 237493 11
  · wct_piece 30 237495 12
  · wct_piece 30 237499 13
  · wct_piece 0 945 57
theorem routine456_ready : RoutineReady ⟨456, by decide⟩ routine456 := by
  wct_ready_start 456 14 8
  wct_cases [237500,237505,237510,237514,237519,237524,237526,237530,862,867]
  · wct_piece 30 237500 14
  · wct_piece 30 237505 15
  · wct_piece 30 237510 16
  · wct_piece 30 237514 17
  · wct_piece 30 237519 18
  · wct_piece 30 237524 19
  · wct_piece 30 237526 20
  · wct_piece 30 237530 21
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine457_ready : RoutineReady ⟨457, by decide⟩ routine457 := by
  wct_ready_start 457 14 9
  wct_cases [237531,237536,237541,237545,237550,237555,237558,237563,237567]
  · wct_piece 30 237531 22
  · wct_piece 30 237536 23
  · wct_piece 30 237541 24
  · wct_piece 30 237545 25
  · wct_piece 30 237550 26
  · wct_piece 30 237555 27
  · wct_piece 30 237558 28
  · wct_piece 30 237563 29
  · wct_piece 30 237567 30
theorem routine458_ready : RoutineReady ⟨458, by decide⟩ routine458 := by
  wct_ready_start 458 14 10
  wct_cases [237573,237578,237583,237587,4593,2343,2348,1489,1494,1496,1498,1502,945]
  · wct_piece 30 237573 31
  · wct_piece 30 237578 32
  · wct_piece 30 237583 33
  · wct_piece 30 237587 34
  · wct_piece 17 4593 57
  · wct_piece 7 2343 27
  · wct_piece 7 2348 28
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine459_ready : RoutineReady ⟨459, by decide⟩ routine459 := by
  wct_ready_start 459 14 11
  wct_cases [237588,237593,237598,237602,237607,237609,237613,1937,1081,799,804,807]
  · wct_piece 30 237588 35
  · wct_piece 30 237593 36
  · wct_piece 30 237598 37
  · wct_piece 30 237602 38
  · wct_piece 30 237607 39
  · wct_piece 30 237609 40
  · wct_piece 30 237613 41
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine460_ready : RoutineReady ⟨460, by decide⟩ routine460 := by
  wct_ready_start 460 14 12
  wct_cases [237614,237619,237624,237628,237633,237635,237639,237644,862,867]
  · wct_piece 30 237614 42
  · wct_piece 30 237619 43
  · wct_piece 30 237624 44
  · wct_piece 30 237628 45
  · wct_piece 30 237633 46
  · wct_piece 30 237635 47
  · wct_piece 30 237639 48
  · wct_piece 30 237644 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine461_ready : RoutineReady ⟨461, by decide⟩ routine461 := by
  wct_ready_start 461 14 13
  wct_cases [237645,237650,237655,237659,237664,237666,237670,237675,237677,237681]
  · wct_piece 30 237645 50
  · wct_piece 30 237650 51
  · wct_piece 30 237655 52
  · wct_piece 30 237659 53
  · wct_piece 30 237664 54
  · wct_piece 30 237666 55
  · wct_piece 30 237670 56
  · wct_piece 30 237675 57
  · wct_piece 30 237677 58
  · wct_piece 30 237681 59
theorem routine462_ready : RoutineReady ⟨462, by decide⟩ routine462 := by
  wct_ready_start 462 14 14
  wct_cases [237687,237692,237697,237701,237706,237709,237714,237718,237723]
  · wct_piece 30 237687 60
  · wct_piece 30 237692 61
  · wct_piece 30 237697 62
  · wct_piece 30 237701 63
  · wct_piece 31 237706 0
  · wct_piece 31 237709 1
  · wct_piece 31 237714 2
  · wct_piece 31 237718 3
  · wct_piece 31 237723 4
theorem routine463_ready : RoutineReady ⟨463, by decide⟩ routine463 := by
  wct_ready_start 463 14 15
  wct_cases [237729,237734,237739,237743,237748,237751,237756,237761,237765]
  · wct_piece 31 237729 5
  · wct_piece 31 237734 6
  · wct_piece 31 237739 7
  · wct_piece 31 237743 8
  · wct_piece 31 237748 9
  · wct_piece 31 237751 10
  · wct_piece 31 237756 11
  · wct_piece 31 237761 12
  · wct_piece 31 237765 13
theorem routine464_ready : RoutineReady ⟨464, by decide⟩ routine464 := by
  wct_ready_start 464 14 16
  wct_cases [237771,237776,237781,237785,237790,237793,2037,2042,2044,2048,1502,945]
  · wct_piece 31 237771 14
  · wct_piece 31 237776 15
  · wct_piece 31 237781 16
  · wct_piece 31 237785 17
  · wct_piece 31 237790 18
  · wct_piece 31 237793 19
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine465_ready : RoutineReady ⟨465, by decide⟩ routine465 := by
  wct_ready_start 465 14 17
  wct_cases [237794,237799,237804,237808,4704,2468,2473,2475,2477,2481,1301,862,867]
  · wct_piece 31 237794 20
  · wct_piece 31 237799 21
  · wct_piece 31 237804 22
  · wct_piece 31 237808 23
  · wct_piece 18 4704 28
  · wct_piece 8 2468 0
  · wct_piece 8 2473 1
  · wct_piece 8 2475 2
  · wct_piece 8 2477 3
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine466_ready : RoutineReady ⟨466, by decide⟩ routine466 := by
  wct_ready_start 466 14 18
  wct_cases [237809,237814,237819,237823,237828,237830,237832,237836,237841,237845]
  · wct_piece 31 237809 24
  · wct_piece 31 237814 25
  · wct_piece 31 237819 26
  · wct_piece 31 237823 27
  · wct_piece 31 237828 28
  · wct_piece 31 237830 29
  · wct_piece 31 237832 30
  · wct_piece 31 237836 31
  · wct_piece 31 237841 32
  · wct_piece 31 237845 33
theorem routine467_ready : RoutineReady ⟨467, by decide⟩ routine467 := by
  wct_ready_start 467 14 19
  wct_cases [237851,237856,237861,237865,2512,2517,2519,2522,2527,2531,1502,945]
  · wct_piece 31 237851 34
  · wct_piece 31 237856 35
  · wct_piece 31 237861 36
  · wct_piece 31 237865 37
  · wct_piece 8 2512 14
  · wct_piece 8 2517 15
  · wct_piece 8 2519 16
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine468_ready : RoutineReady ⟨468, by decide⟩ routine468 := by
  wct_ready_start 468 14 20
  wct_cases [237866,237871,237876,4737,4742,4746,2545,1343,886,754,759,761,764]
  · wct_piece 31 237866 38
  · wct_piece 31 237871 39
  · wct_piece 31 237876 40
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
theorem routine469_ready : RoutineReady ⟨469, by decide⟩ routine469 := by
  wct_ready_start 469 14 21
  wct_cases [237877,237882,237887,237892,237896,2559,1357,897,902,799,804,807]
  · wct_piece 31 237877 41
  · wct_piece 31 237882 42
  · wct_piece 31 237887 43
  · wct_piece 31 237892 44
  · wct_piece 31 237896 45
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine470_ready : RoutineReady ⟨470, by decide⟩ routine470 := by
  wct_ready_start 470 14 22
  wct_cases [237897,237902,237907,237912,237916,2573,1371,913,918,921,862,867]
  · wct_piece 31 237897 46
  · wct_piece 31 237902 47
  · wct_piece 31 237907 48
  · wct_piece 31 237912 49
  · wct_piece 31 237916 50
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine471_ready : RoutineReady ⟨471, by decide⟩ routine471 := by
  wct_ready_start 471 14 23
  wct_cases [237917,237922,237927,235052,235057,235061,2587,1385,932,937,939,941,945]
  · wct_piece 31 237917 51
  · wct_piece 31 237922 52
  · wct_piece 31 237927 53
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
theorem routine472_ready : RoutineReady ⟨472, by decide⟩ routine472 := by
  wct_ready_start 472 14 24
  wct_cases [237928,237933,237938,237943,237947,237952,237956,237961,237964]
  · wct_piece 31 237928 54
  · wct_piece 31 237933 55
  · wct_piece 31 237938 56
  · wct_piece 31 237943 57
  · wct_piece 31 237947 58
  · wct_piece 31 237952 59
  · wct_piece 31 237956 60
  · wct_piece 31 237961 61
  · wct_piece 31 237964 62
theorem routine473_ready : RoutineReady ⟨473, by decide⟩ routine473 := by
  wct_ready_start 473 14 25
  wct_cases [237970,237975,237980,237985,237989,237994,1097,1102,862,867]
  · wct_piece 31 237970 63
  · wct_piece 32 237975 0
  · wct_piece 32 237980 1
  · wct_piece 32 237985 2
  · wct_piece 32 237989 3
  · wct_piece 32 237994 4
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine474_ready : RoutineReady ⟨474, by decide⟩ routine474 := by
  wct_ready_start 474 14 26
  wct_cases [237995,238000,238005,238010,238014,238019,238024,238026,238030,945]
  · wct_piece 32 237995 5
  · wct_piece 32 238000 6
  · wct_piece 32 238005 7
  · wct_piece 32 238010 8
  · wct_piece 32 238014 9
  · wct_piece 32 238019 10
  · wct_piece 32 238024 11
  · wct_piece 32 238026 12
  · wct_piece 32 238030 13
  · wct_piece 0 945 57
theorem routine475_ready : RoutineReady ⟨475, by decide⟩ routine475 := by
  wct_ready_start 475 14 27
  wct_cases [238031,238036,238041,238046,238050,238055,238057,238061,862,867]
  · wct_piece 32 238031 14
  · wct_piece 32 238036 15
  · wct_piece 32 238041 16
  · wct_piece 32 238046 17
  · wct_piece 32 238050 18
  · wct_piece 32 238055 19
  · wct_piece 32 238057 20
  · wct_piece 32 238061 21
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine476_ready : RoutineReady ⟨476, by decide⟩ routine476 := by
  wct_ready_start 476 14 28
  wct_cases [238062,238067,238072,238077,238081,238086,238089,238094,238098]
  · wct_piece 32 238062 22
  · wct_piece 32 238067 23
  · wct_piece 32 238072 24
  · wct_piece 32 238077 25
  · wct_piece 32 238081 26
  · wct_piece 32 238086 27
  · wct_piece 32 238089 28
  · wct_piece 32 238094 29
  · wct_piece 32 238098 30
theorem routine477_ready : RoutineReady ⟨477, by decide⟩ routine477 := by
  wct_ready_start 477 14 29
  wct_cases [238104,238109,238114,235177,235182,235186,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 32 238104 31
  · wct_piece 32 238109 32
  · wct_piece 32 238114 33
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
theorem routine478_ready : RoutineReady ⟨478, by decide⟩ routine478 := by
  wct_ready_start 478 14 30
  wct_cases [238115,238120,238125,238130,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 32 238115 34
  · wct_piece 32 238120 35
  · wct_piece 32 238125 36
  · wct_piece 32 238130 37
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine479_ready : RoutineReady ⟨479, by decide⟩ routine479 := by
  wct_ready_start 479 14 31
  wct_cases [238131,238136,238141,238146,238151,238155,1097,1102,862,867]
  · wct_piece 32 238131 38
  · wct_piece 32 238136 39
  · wct_piece 32 238141 40
  · wct_piece 32 238146 41
  · wct_piece 32 238151 42
  · wct_piece 32 238155 43
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage14 (rank : Fin 728) (hlo : 448 ≤ rank.val) (hhi : rank.val < 480) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 448 ≤ n at hlo
  change n < 480 at hhi
  interval_cases n
  · exact ⟨routine448, routine448_ready⟩
  · exact ⟨routine449, routine449_ready⟩
  · exact ⟨routine450, routine450_ready⟩
  · exact ⟨routine451, routine451_ready⟩
  · exact ⟨routine452, routine452_ready⟩
  · exact ⟨routine453, routine453_ready⟩
  · exact ⟨routine454, routine454_ready⟩
  · exact ⟨routine455, routine455_ready⟩
  · exact ⟨routine456, routine456_ready⟩
  · exact ⟨routine457, routine457_ready⟩
  · exact ⟨routine458, routine458_ready⟩
  · exact ⟨routine459, routine459_ready⟩
  · exact ⟨routine460, routine460_ready⟩
  · exact ⟨routine461, routine461_ready⟩
  · exact ⟨routine462, routine462_ready⟩
  · exact ⟨routine463, routine463_ready⟩
  · exact ⟨routine464, routine464_ready⟩
  · exact ⟨routine465, routine465_ready⟩
  · exact ⟨routine466, routine466_ready⟩
  · exact ⟨routine467, routine467_ready⟩
  · exact ⟨routine468, routine468_ready⟩
  · exact ⟨routine469, routine469_ready⟩
  · exact ⟨routine470, routine470_ready⟩
  · exact ⟨routine471, routine471_ready⟩
  · exact ⟨routine472, routine472_ready⟩
  · exact ⟨routine473, routine473_ready⟩
  · exact ⟨routine474, routine474_ready⟩
  · exact ⟨routine475, routine475_ready⟩
  · exact ⟨routine476, routine476_ready⟩
  · exact ⟨routine477, routine477_ready⟩
  · exact ⟨routine478, routine478_ready⟩
  · exact ⟨routine479, routine479_ready⟩
end W9Machine.Chain
end
