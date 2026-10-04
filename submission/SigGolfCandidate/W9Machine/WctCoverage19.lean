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
def routine608 : ChainRoutine := ⟨608, [2, 0, 2, 0, 2, 0, 0], [piece240192, piece240197, piece240199, piece235455, piece235460, piece235462, piece235466, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine609 : ChainRoutine := ⟨609, [2, 0, 2, 1, 0, 0, 1], [piece240200, piece240205, piece240207, piece235475, piece235480, piece235483, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine610 : ChainRoutine := ⟨610, [2, 0, 2, 1, 0, 1, 0], [piece240208, piece240213, piece240215, piece235492, piece235497, piece235500, piece235505, piece235509, piece1320, piece1325, piece1329, piece945]⟩
def routine611 : ChainRoutine := ⟨611, [2, 0, 2, 1, 1, 0, 0], [piece240216, piece240221, piece240223, piece235518, piece235523, piece235526, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine612 : ChainRoutine := ⟨612, [2, 0, 2, 2, 0, 0, 0], [piece240224, piece240229, piece240231, piece235535, piece235540, piece235543, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine613 : ChainRoutine := ⟨613, [2, 0, 3, 0, 0, 0, 1], [piece240232, piece240237, piece240239, piece235552, piece235557, piece235559, piece235561, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine614 : ChainRoutine := ⟨614, [2, 0, 3, 0, 0, 1, 0], [piece240240, piece240245, piece240247, piece235574, piece235579, piece235581, piece235583, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine615 : ChainRoutine := ⟨615, [2, 0, 3, 0, 1, 0, 0], [piece240248, piece240253, piece240255, piece235596, piece235601, piece235603, piece235605, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine616 : ChainRoutine := ⟨616, [2, 0, 3, 1, 0, 0, 0], [piece240256, piece240261, piece240263, piece235618, piece235623, piece235625, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine617 : ChainRoutine := ⟨617, [2, 1, 0, 0, 0, 0, 3], [piece240264, piece240269, piece240271, piece240276, piece240280, piece235651, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine618 : ChainRoutine := ⟨618, [2, 1, 0, 0, 0, 1, 2], [piece240281, piece240286, piece240288, piece240293, piece240297, piece235665, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine619 : ChainRoutine := ⟨619, [2, 1, 0, 0, 0, 2, 1], [piece240298, piece240303, piece240305, piece240310, piece240314, piece235679, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine620 : ChainRoutine := ⟨620, [2, 1, 0, 0, 0, 3, 0], [piece240315, piece240320, piece240322, piece240327, piece240331, piece235693, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine621 : ChainRoutine := ⟨621, [2, 1, 0, 0, 1, 0, 2], [piece240332, piece240337, piece240339, piece240344, piece240348, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine622 : ChainRoutine := ⟨622, [2, 1, 0, 0, 1, 1, 1], [piece240349, piece240354, piece240356, piece240361, piece240365, piece235721, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine623 : ChainRoutine := ⟨623, [2, 1, 0, 0, 1, 2, 0], [piece240366, piece240371, piece240373, piece240378, piece240382, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine624 : ChainRoutine := ⟨624, [2, 1, 0, 0, 2, 0, 1], [piece240383, piece240388, piece240390, piece240395, piece240399, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine625 : ChainRoutine := ⟨625, [2, 1, 0, 0, 2, 1, 0], [piece240400, piece240405, piece240407, piece240412, piece240416, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine626 : ChainRoutine := ⟨626, [2, 1, 0, 0, 3, 0, 0], [piece240417, piece240422, piece240424, piece240429, piece240433, piece235777, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine627 : ChainRoutine := ⟨627, [2, 1, 0, 1, 0, 0, 2], [piece240434, piece240439, piece240441, piece240446, piece240450, piece240455, piece240459, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine628 : ChainRoutine := ⟨628, [2, 1, 0, 1, 0, 1, 1], [piece240460, piece240465, piece240467, piece240472, piece240476, piece240481, piece240485, piece240490, piece862, piece867]⟩
def routine629 : ChainRoutine := ⟨629, [2, 1, 0, 1, 0, 2, 0], [piece240491, piece240496, piece240498, piece240503, piece240507, piece240512, piece240516, piece240521, piece240523, piece240527]⟩
def routine630 : ChainRoutine := ⟨630, [2, 1, 0, 1, 1, 0, 1], [piece240533, piece240538, piece240540, piece240545, piece240549, piece240554, piece240559, piece240563, piece862, piece867]⟩
def routine631 : ChainRoutine := ⟨631, [2, 1, 0, 1, 1, 1, 0], [piece240564, piece240569, piece240571, piece240576, piece240580, piece240585, piece240590, piece240595, piece240599, piece945]⟩
def routine632 : ChainRoutine := ⟨632, [2, 1, 0, 1, 2, 0, 0], [piece240600, piece240605, piece240607, piece240612, piece240616, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine633 : ChainRoutine := ⟨633, [2, 1, 0, 2, 0, 0, 1], [piece240617, piece240622, piece240624, piece240629, piece240633, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine634 : ChainRoutine := ⟨634, [2, 1, 0, 2, 0, 1, 0], [piece240634, piece240639, piece240641, piece240646, piece240650, piece240655, piece240657, piece240661, piece240666, piece240670]⟩
def routine635 : ChainRoutine := ⟨635, [2, 1, 0, 2, 1, 0, 0], [piece240676, piece240681, piece240683, piece240688, piece240692, piece240697, piece240700, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine636 : ChainRoutine := ⟨636, [2, 1, 0, 3, 0, 0, 0], [piece240701, piece240706, piece240708, piece240713, piece240717, piece235937, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine637 : ChainRoutine := ⟨637, [2, 1, 1, 0, 0, 0, 2], [piece240718, piece240723, piece240725, piece240730, piece235948, piece235953, piece235957, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine638 : ChainRoutine := ⟨638, [2, 1, 1, 0, 0, 1, 1], [piece240731, piece240736, piece240738, piece240743, piece235968, piece235973, piece235977, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine639 : ChainRoutine := ⟨639, [2, 1, 1, 0, 0, 2, 0], [piece240744, piece240749, piece240751, piece240756, piece240761, piece240765, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routineBatch19 : List ChainRoutine := [routine608, routine609, routine610, routine611, routine612, routine613, routine614, routine615, routine616, routine617, routine618, routine619, routine620, routine621, routine622, routine623, routine624, routine625, routine626, routine627, routine628, routine629, routine630, routine631, routine632, routine633, routine634, routine635, routine636, routine637, routine638, routine639]
theorem routineBatch19_checked : (routineBatch19.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch19_checked :
    (routineBatch19.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch19_checked :
    (routineBatch19.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine608_ready : RoutineReady ⟨608, by decide⟩ routine608 := by
  wct_ready_start 608 19 0
  wct_cases [240192,240197,240199,235455,235460,235462,235466,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 41 240192 61
  · wct_piece 41 240197 62
  · wct_piece 41 240199 63
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
theorem routine609_ready : RoutineReady ⟨609, by decide⟩ routine609 := by
  wct_ready_start 609 19 1
  wct_cases [240200,240205,240207,235475,235480,235483,4219,4224,4228,2481,1301,862,867]
  · wct_piece 42 240200 0
  · wct_piece 42 240205 1
  · wct_piece 42 240207 2
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
theorem routine610_ready : RoutineReady ⟨610, by decide⟩ routine610 := by
  wct_ready_start 610 19 2
  wct_cases [240208,240213,240215,235492,235497,235500,235505,235509,1320,1325,1329,945]
  · wct_piece 42 240208 3
  · wct_piece 42 240213 4
  · wct_piece 42 240215 5
  · wct_piece 20 235492 51
  · wct_piece 20 235497 52
  · wct_piece 20 235500 53
  · wct_piece 20 235505 54
  · wct_piece 20 235509 55
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine611_ready : RoutineReady ⟨611, by decide⟩ routine611 := by
  wct_ready_start 611 19 3
  wct_cases [240216,240221,240223,235518,235523,235526,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 42 240216 6
  · wct_piece 42 240221 7
  · wct_piece 42 240223 8
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
theorem routine612_ready : RoutineReady ⟨612, by decide⟩ routine612 := by
  wct_ready_start 612 19 4
  wct_cases [240224,240229,240231,235535,235540,235543,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 42 240224 9
  · wct_piece 42 240229 10
  · wct_piece 42 240231 11
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
theorem routine613_ready : RoutineReady ⟨613, by decide⟩ routine613 := by
  wct_ready_start 613 19 5
  wct_cases [240232,240237,240239,235552,235557,235559,235561,235565,2481,1301,862,867]
  · wct_piece 42 240232 12
  · wct_piece 42 240237 13
  · wct_piece 42 240239 14
  · wct_piece 21 235552 4
  · wct_piece 21 235557 5
  · wct_piece 21 235559 6
  · wct_piece 21 235561 7
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine614_ready : RoutineReady ⟨614, by decide⟩ routine614 := by
  wct_ready_start 614 19 6
  wct_cases [240240,240245,240247,235574,235579,235581,235583,235587,2503,1320,1325,1329,945]
  · wct_piece 42 240240 15
  · wct_piece 42 240245 16
  · wct_piece 42 240247 17
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
theorem routine615_ready : RoutineReady ⟨615, by decide⟩ routine615 := by
  wct_ready_start 615 19 7
  wct_cases [240248,240253,240255,235596,235601,235603,235605,235609,2522,2527,2531,1502,945]
  · wct_piece 42 240248 18
  · wct_piece 42 240253 19
  · wct_piece 42 240255 20
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
theorem routine616_ready : RoutineReady ⟨616, by decide⟩ routine616 := by
  wct_ready_start 616 19 8
  wct_cases [240256,240261,240263,235618,235623,235625,235628,235633,235637,2866,1502,945]
  · wct_piece 42 240256 21
  · wct_piece 42 240261 22
  · wct_piece 42 240263 23
  · wct_piece 21 235618 25
  · wct_piece 21 235623 26
  · wct_piece 21 235625 27
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine617_ready : RoutineReady ⟨617, by decide⟩ routine617 := by
  wct_ready_start 617 19 9
  wct_cases [240264,240269,240271,240276,240280,235651,2545,1343,886,754,759,761,764]
  · wct_piece 42 240264 24
  · wct_piece 42 240269 25
  · wct_piece 42 240271 26
  · wct_piece 42 240276 27
  · wct_piece 42 240280 28
  · wct_piece 21 235651 35
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine618_ready : RoutineReady ⟨618, by decide⟩ routine618 := by
  wct_ready_start 618 19 10
  wct_cases [240281,240286,240288,240293,240297,235665,2559,1357,897,902,799,804,807]
  · wct_piece 42 240281 29
  · wct_piece 42 240286 30
  · wct_piece 42 240288 31
  · wct_piece 42 240293 32
  · wct_piece 42 240297 33
  · wct_piece 21 235665 40
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine619_ready : RoutineReady ⟨619, by decide⟩ routine619 := by
  wct_ready_start 619 19 11
  wct_cases [240298,240303,240305,240310,240314,235679,2573,1371,913,918,921,862,867]
  · wct_piece 42 240298 34
  · wct_piece 42 240303 35
  · wct_piece 42 240305 36
  · wct_piece 42 240310 37
  · wct_piece 42 240314 38
  · wct_piece 21 235679 45
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine620_ready : RoutineReady ⟨620, by decide⟩ routine620 := by
  wct_ready_start 620 19 12
  wct_cases [240315,240320,240322,240327,240331,235693,2587,1385,932,937,939,941,945]
  · wct_piece 42 240315 39
  · wct_piece 42 240320 40
  · wct_piece 42 240322 41
  · wct_piece 42 240327 42
  · wct_piece 42 240331 43
  · wct_piece 21 235693 50
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine621_ready : RoutineReady ⟨621, by decide⟩ routine621 := by
  wct_ready_start 621 19 13
  wct_cases [240332,240337,240339,240344,240348,1396,1401,1405,1081,799,804,807]
  · wct_piece 42 240332 44
  · wct_piece 42 240337 45
  · wct_piece 42 240339 46
  · wct_piece 42 240344 47
  · wct_piece 42 240348 48
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine622_ready : RoutineReady ⟨622, by decide⟩ routine622 := by
  wct_ready_start 622 19 14
  wct_cases [240349,240354,240356,240361,240365,235721,2615,1416,1421,1097,1102,862,867]
  · wct_piece 42 240349 49
  · wct_piece 42 240354 50
  · wct_piece 42 240356 51
  · wct_piece 42 240361 52
  · wct_piece 42 240365 53
  · wct_piece 21 235721 60
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine623_ready : RoutineReady ⟨623, by decide⟩ routine623 := by
  wct_ready_start 623 19 15
  wct_cases [240366,240371,240373,240378,240382,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 42 240366 54
  · wct_piece 42 240371 55
  · wct_piece 42 240373 56
  · wct_piece 42 240378 57
  · wct_piece 42 240382 58
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine624_ready : RoutineReady ⟨624, by decide⟩ routine624 := by
  wct_ready_start 624 19 16
  wct_cases [240383,240388,240390,240395,240399,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 42 240383 59
  · wct_piece 42 240388 60
  · wct_piece 42 240390 61
  · wct_piece 42 240395 62
  · wct_piece 42 240399 63
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine625_ready : RoutineReady ⟨625, by decide⟩ routine625 := by
  wct_ready_start 625 19 17
  wct_cases [240400,240405,240407,240412,240416,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 43 240400 0
  · wct_piece 43 240405 1
  · wct_piece 43 240407 2
  · wct_piece 43 240412 3
  · wct_piece 43 240416 4
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine626_ready : RoutineReady ⟨626, by decide⟩ routine626 := by
  wct_ready_start 626 19 18
  wct_cases [240417,240422,240424,240429,240433,235777,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 43 240417 5
  · wct_piece 43 240422 6
  · wct_piece 43 240424 7
  · wct_piece 43 240429 8
  · wct_piece 43 240433 9
  · wct_piece 22 235777 16
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine627_ready : RoutineReady ⟨627, by decide⟩ routine627 := by
  wct_ready_start 627 19 19
  wct_cases [240434,240439,240441,240446,240450,240455,240459,1937,1081,799,804,807]
  · wct_piece 43 240434 10
  · wct_piece 43 240439 11
  · wct_piece 43 240441 12
  · wct_piece 43 240446 13
  · wct_piece 43 240450 14
  · wct_piece 43 240455 15
  · wct_piece 43 240459 16
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine628_ready : RoutineReady ⟨628, by decide⟩ routine628 := by
  wct_ready_start 628 19 20
  wct_cases [240460,240465,240467,240472,240476,240481,240485,240490,862,867]
  · wct_piece 43 240460 17
  · wct_piece 43 240465 18
  · wct_piece 43 240467 19
  · wct_piece 43 240472 20
  · wct_piece 43 240476 21
  · wct_piece 43 240481 22
  · wct_piece 43 240485 23
  · wct_piece 43 240490 24
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine629_ready : RoutineReady ⟨629, by decide⟩ routine629 := by
  wct_ready_start 629 19 21
  wct_cases [240491,240496,240498,240503,240507,240512,240516,240521,240523,240527]
  · wct_piece 43 240491 25
  · wct_piece 43 240496 26
  · wct_piece 43 240498 27
  · wct_piece 43 240503 28
  · wct_piece 43 240507 29
  · wct_piece 43 240512 30
  · wct_piece 43 240516 31
  · wct_piece 43 240521 32
  · wct_piece 43 240523 33
  · wct_piece 43 240527 34
theorem routine630_ready : RoutineReady ⟨630, by decide⟩ routine630 := by
  wct_ready_start 630 19 22
  wct_cases [240533,240538,240540,240545,240549,240554,240559,240563,862,867]
  · wct_piece 43 240533 35
  · wct_piece 43 240538 36
  · wct_piece 43 240540 37
  · wct_piece 43 240545 38
  · wct_piece 43 240549 39
  · wct_piece 43 240554 40
  · wct_piece 43 240559 41
  · wct_piece 43 240563 42
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine631_ready : RoutineReady ⟨631, by decide⟩ routine631 := by
  wct_ready_start 631 19 23
  wct_cases [240564,240569,240571,240576,240580,240585,240590,240595,240599,945]
  · wct_piece 43 240564 43
  · wct_piece 43 240569 44
  · wct_piece 43 240571 45
  · wct_piece 43 240576 46
  · wct_piece 43 240580 47
  · wct_piece 43 240585 48
  · wct_piece 43 240590 49
  · wct_piece 43 240595 50
  · wct_piece 43 240599 51
  · wct_piece 0 945 57
theorem routine632_ready : RoutineReady ⟨632, by decide⟩ routine632 := by
  wct_ready_start 632 19 24
  wct_cases [240600,240605,240607,240612,240616,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 43 240600 52
  · wct_piece 43 240605 53
  · wct_piece 43 240607 54
  · wct_piece 43 240612 55
  · wct_piece 43 240616 56
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine633_ready : RoutineReady ⟨633, by decide⟩ routine633 := by
  wct_ready_start 633 19 25
  wct_cases [240617,240622,240624,240629,240633,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 43 240617 57
  · wct_piece 43 240622 58
  · wct_piece 43 240624 59
  · wct_piece 43 240629 60
  · wct_piece 43 240633 61
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine634_ready : RoutineReady ⟨634, by decide⟩ routine634 := by
  wct_ready_start 634 19 26
  wct_cases [240634,240639,240641,240646,240650,240655,240657,240661,240666,240670]
  · wct_piece 43 240634 62
  · wct_piece 43 240639 63
  · wct_piece 44 240641 0
  · wct_piece 44 240646 1
  · wct_piece 44 240650 2
  · wct_piece 44 240655 3
  · wct_piece 44 240657 4
  · wct_piece 44 240661 5
  · wct_piece 44 240666 6
  · wct_piece 44 240670 7
theorem routine635_ready : RoutineReady ⟨635, by decide⟩ routine635 := by
  wct_ready_start 635 19 27
  wct_cases [240676,240681,240683,240688,240692,240697,240700,2522,2527,2531,1502,945]
  · wct_piece 44 240676 8
  · wct_piece 44 240681 9
  · wct_piece 44 240683 10
  · wct_piece 44 240688 11
  · wct_piece 44 240692 12
  · wct_piece 44 240697 13
  · wct_piece 44 240700 14
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine636_ready : RoutineReady ⟨636, by decide⟩ routine636 := by
  wct_ready_start 636 19 28
  wct_cases [240701,240706,240708,240713,240717,235937,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 44 240701 15
  · wct_piece 44 240706 16
  · wct_piece 44 240708 17
  · wct_piece 44 240713 18
  · wct_piece 44 240717 19
  · wct_piece 23 235937 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine637_ready : RoutineReady ⟨637, by decide⟩ routine637 := by
  wct_ready_start 637 19 29
  wct_cases [240718,240723,240725,240730,235948,235953,235957,4108,1937,1081,799,804,807]
  · wct_piece 44 240718 20
  · wct_piece 44 240723 21
  · wct_piece 44 240725 22
  · wct_piece 44 240730 23
  · wct_piece 23 235948 11
  · wct_piece 23 235953 12
  · wct_piece 23 235957 13
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine638_ready : RoutineReady ⟨638, by decide⟩ routine638 := by
  wct_ready_start 638 19 30
  wct_cases [240731,240736,240738,240743,235968,235973,235977,4127,1956,1097,1102,862,867]
  · wct_piece 44 240731 24
  · wct_piece 44 240736 25
  · wct_piece 44 240738 26
  · wct_piece 44 240743 27
  · wct_piece 23 235968 17
  · wct_piece 23 235973 18
  · wct_piece 23 235977 19
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine639_ready : RoutineReady ⟨639, by decide⟩ routine639 := by
  wct_ready_start 639 19 31
  wct_cases [240744,240749,240751,240756,240761,240765,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 44 240744 28
  · wct_piece 44 240749 29
  · wct_piece 44 240751 30
  · wct_piece 44 240756 31
  · wct_piece 44 240761 32
  · wct_piece 44 240765 33
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage19 (rank : Fin 728) (hlo : 608 ≤ rank.val) (hhi : rank.val < 640) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 608 ≤ n at hlo
  change n < 640 at hhi
  interval_cases n
  · exact ⟨routine608, routine608_ready⟩
  · exact ⟨routine609, routine609_ready⟩
  · exact ⟨routine610, routine610_ready⟩
  · exact ⟨routine611, routine611_ready⟩
  · exact ⟨routine612, routine612_ready⟩
  · exact ⟨routine613, routine613_ready⟩
  · exact ⟨routine614, routine614_ready⟩
  · exact ⟨routine615, routine615_ready⟩
  · exact ⟨routine616, routine616_ready⟩
  · exact ⟨routine617, routine617_ready⟩
  · exact ⟨routine618, routine618_ready⟩
  · exact ⟨routine619, routine619_ready⟩
  · exact ⟨routine620, routine620_ready⟩
  · exact ⟨routine621, routine621_ready⟩
  · exact ⟨routine622, routine622_ready⟩
  · exact ⟨routine623, routine623_ready⟩
  · exact ⟨routine624, routine624_ready⟩
  · exact ⟨routine625, routine625_ready⟩
  · exact ⟨routine626, routine626_ready⟩
  · exact ⟨routine627, routine627_ready⟩
  · exact ⟨routine628, routine628_ready⟩
  · exact ⟨routine629, routine629_ready⟩
  · exact ⟨routine630, routine630_ready⟩
  · exact ⟨routine631, routine631_ready⟩
  · exact ⟨routine632, routine632_ready⟩
  · exact ⟨routine633, routine633_ready⟩
  · exact ⟨routine634, routine634_ready⟩
  · exact ⟨routine635, routine635_ready⟩
  · exact ⟨routine636, routine636_ready⟩
  · exact ⟨routine637, routine637_ready⟩
  · exact ⟨routine638, routine638_ready⟩
  · exact ⟨routine639, routine639_ready⟩
end W9Machine.Chain
end
