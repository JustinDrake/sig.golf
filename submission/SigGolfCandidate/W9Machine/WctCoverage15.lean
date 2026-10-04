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
def routine480 : ChainRoutine := ⟨480, [1, 1, 1, 1, 0, 2, 0], [piece238156, piece238161, piece238166, piece238171, piece238176, piece238180, piece238185, piece238187, piece238191, piece945]⟩
def routine481 : ChainRoutine := ⟨481, [1, 1, 1, 1, 1, 0, 1], [piece238192, piece238197, piece238202, piece238207, piece238212, piece238217, piece238221, piece1301, piece862, piece867]⟩
def routine482 : ChainRoutine := ⟨482, [1, 1, 1, 1, 1, 1, 0], [piece238222, piece238227, piece238232, piece238237, piece238242, piece238247, piece1320, piece1325, piece1329, piece945]⟩
def routine483 : ChainRoutine := ⟨483, [1, 1, 1, 1, 2, 0, 0], [piece238248, piece238253, piece238258, piece235274, piece235279, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine484 : ChainRoutine := ⟨484, [1, 1, 1, 2, 0, 0, 1], [piece238259, piece238264, piece238269, piece235288, piece235293, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine485 : ChainRoutine := ⟨485, [1, 1, 1, 2, 0, 1, 0], [piece238270, piece238275, piece238280, piece238285, piece238290, piece238292, piece238296, piece238301, piece238305, piece945]⟩
def routine486 : ChainRoutine := ⟨486, [1, 1, 1, 2, 1, 0, 0], [piece238306, piece238311, piece238316, piece238321, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine487 : ChainRoutine := ⟨487, [1, 1, 1, 3, 0, 0, 0], [piece238322, piece238327, piece238332, piece235341, piece235346, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine488 : ChainRoutine := ⟨488, [1, 1, 2, 0, 0, 0, 2], [piece238333, piece238338, piece238343, piece235355, piece235360, piece235362, piece235366, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine489 : ChainRoutine := ⟨489, [1, 1, 2, 0, 0, 1, 1], [piece238344, piece238349, piece238354, piece235375, piece235380, piece235382, piece235386, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine490 : ChainRoutine := ⟨490, [1, 1, 2, 0, 0, 2, 0], [piece238355, piece238360, piece238365, piece238370, piece238372, piece238376, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine491 : ChainRoutine := ⟨491, [1, 1, 2, 0, 1, 0, 1], [piece238377, piece238382, piece238387, piece238392, piece238394, piece238398, piece238403, piece238407, piece862, piece867]⟩
def routine492 : ChainRoutine := ⟨492, [1, 1, 2, 0, 1, 1, 0], [piece238408, piece238413, piece238418, piece238423, piece238425, piece238429, piece238434, piece238439, piece238443, piece945]⟩
def routine493 : ChainRoutine := ⟨493, [1, 1, 2, 0, 2, 0, 0], [piece238444, piece238449, piece238454, piece238459, piece238461, piece238465, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine494 : ChainRoutine := ⟨494, [1, 1, 2, 1, 0, 0, 1], [piece238466, piece238471, piece238476, piece238481, piece238484, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine495 : ChainRoutine := ⟨495, [1, 1, 2, 1, 0, 1, 0], [piece238485, piece238490, piece238495, piece238500, piece238503, piece238508, piece238512, piece238517, piece238521]⟩
def routine496 : ChainRoutine := ⟨496, [1, 1, 2, 1, 1, 0, 0], [piece238527, piece238532, piece238537, piece238542, piece238545, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine497 : ChainRoutine := ⟨497, [1, 1, 2, 2, 0, 0, 0], [piece238546, piece238551, piece238556, piece235535, piece235540, piece235543, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine498 : ChainRoutine := ⟨498, [1, 1, 3, 0, 0, 0, 1], [piece238557, piece238562, piece238567, piece235552, piece235557, piece235559, piece235561, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine499 : ChainRoutine := ⟨499, [1, 1, 3, 0, 0, 1, 0], [piece238568, piece238573, piece238578, piece235574, piece235579, piece235581, piece235583, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine500 : ChainRoutine := ⟨500, [1, 1, 3, 0, 1, 0, 0], [piece238579, piece238584, piece238589, piece235596, piece235601, piece235603, piece235605, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine501 : ChainRoutine := ⟨501, [1, 1, 3, 1, 0, 0, 0], [piece238590, piece238595, piece238600, piece235618, piece235623, piece235625, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine502 : ChainRoutine := ⟨502, [1, 2, 0, 0, 0, 0, 3], [piece238601, piece238606, piece238611, piece238613, piece238617, piece235651, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine503 : ChainRoutine := ⟨503, [1, 2, 0, 0, 0, 1, 2], [piece238618, piece238623, piece238628, piece238630, piece238634, piece235665, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine504 : ChainRoutine := ⟨504, [1, 2, 0, 0, 0, 2, 1], [piece238635, piece238640, piece238645, piece238647, piece238651, piece235679, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine505 : ChainRoutine := ⟨505, [1, 2, 0, 0, 0, 3, 0], [piece238652, piece238657, piece238662, piece238664, piece238668, piece235693, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine506 : ChainRoutine := ⟨506, [1, 2, 0, 0, 1, 0, 2], [piece238669, piece238674, piece238679, piece238681, piece238685, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine507 : ChainRoutine := ⟨507, [1, 2, 0, 0, 1, 1, 1], [piece238686, piece238691, piece238696, piece238698, piece238702, piece235721, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine508 : ChainRoutine := ⟨508, [1, 2, 0, 0, 1, 2, 0], [piece238703, piece238708, piece238713, piece238715, piece238719, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine509 : ChainRoutine := ⟨509, [1, 2, 0, 0, 2, 0, 1], [piece238720, piece238725, piece238730, piece238732, piece238736, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine510 : ChainRoutine := ⟨510, [1, 2, 0, 0, 2, 1, 0], [piece238737, piece238742, piece238747, piece238749, piece238753, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine511 : ChainRoutine := ⟨511, [1, 2, 0, 0, 3, 0, 0], [piece238754, piece238759, piece238764, piece238766, piece238770, piece235777, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routineBatch15 : List ChainRoutine := [routine480, routine481, routine482, routine483, routine484, routine485, routine486, routine487, routine488, routine489, routine490, routine491, routine492, routine493, routine494, routine495, routine496, routine497, routine498, routine499, routine500, routine501, routine502, routine503, routine504, routine505, routine506, routine507, routine508, routine509, routine510, routine511]
theorem routineBatch15_checked : (routineBatch15.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch15_checked :
    (routineBatch15.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch15_checked :
    (routineBatch15.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine480_ready : RoutineReady ⟨480, by decide⟩ routine480 := by
  wct_ready_start 480 15 0
  wct_cases [238156,238161,238166,238171,238176,238180,238185,238187,238191,945]
  · wct_piece 32 238156 44
  · wct_piece 32 238161 45
  · wct_piece 32 238166 46
  · wct_piece 32 238171 47
  · wct_piece 32 238176 48
  · wct_piece 32 238180 49
  · wct_piece 32 238185 50
  · wct_piece 32 238187 51
  · wct_piece 32 238191 52
  · wct_piece 0 945 57
theorem routine481_ready : RoutineReady ⟨481, by decide⟩ routine481 := by
  wct_ready_start 481 15 1
  wct_cases [238192,238197,238202,238207,238212,238217,238221,1301,862,867]
  · wct_piece 32 238192 53
  · wct_piece 32 238197 54
  · wct_piece 32 238202 55
  · wct_piece 32 238207 56
  · wct_piece 32 238212 57
  · wct_piece 32 238217 58
  · wct_piece 32 238221 59
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine482_ready : RoutineReady ⟨482, by decide⟩ routine482 := by
  wct_ready_start 482 15 2
  wct_cases [238222,238227,238232,238237,238242,238247,1320,1325,1329,945]
  · wct_piece 32 238222 60
  · wct_piece 32 238227 61
  · wct_piece 32 238232 62
  · wct_piece 32 238237 63
  · wct_piece 33 238242 0
  · wct_piece 33 238247 1
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine483_ready : RoutineReady ⟨483, by decide⟩ routine483 := by
  wct_ready_start 483 15 3
  wct_cases [238248,238253,238258,235274,235279,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 33 238248 2
  · wct_piece 33 238253 3
  · wct_piece 33 238258 4
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
theorem routine484_ready : RoutineReady ⟨484, by decide⟩ routine484 := by
  wct_ready_start 484 15 4
  wct_cases [238259,238264,238269,235288,235293,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 33 238259 5
  · wct_piece 33 238264 6
  · wct_piece 33 238269 7
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
theorem routine485_ready : RoutineReady ⟨485, by decide⟩ routine485 := by
  wct_ready_start 485 15 5
  wct_cases [238270,238275,238280,238285,238290,238292,238296,238301,238305,945]
  · wct_piece 33 238270 8
  · wct_piece 33 238275 9
  · wct_piece 33 238280 10
  · wct_piece 33 238285 11
  · wct_piece 33 238290 12
  · wct_piece 33 238292 13
  · wct_piece 33 238296 14
  · wct_piece 33 238301 15
  · wct_piece 33 238305 16
  · wct_piece 0 945 57
theorem routine486_ready : RoutineReady ⟨486, by decide⟩ routine486 := by
  wct_ready_start 486 15 6
  wct_cases [238306,238311,238316,238321,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 33 238306 17
  · wct_piece 33 238311 18
  · wct_piece 33 238316 19
  · wct_piece 33 238321 20
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine487_ready : RoutineReady ⟨487, by decide⟩ routine487 := by
  wct_ready_start 487 15 7
  wct_cases [238322,238327,238332,235341,235346,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 33 238322 21
  · wct_piece 33 238327 22
  · wct_piece 33 238332 23
  · wct_piece 20 235341 6
  · wct_piece 20 235346 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine488_ready : RoutineReady ⟨488, by decide⟩ routine488 := by
  wct_ready_start 488 15 8
  wct_cases [238333,238338,238343,235355,235360,235362,235366,4108,1937,1081,799,804,807]
  · wct_piece 33 238333 24
  · wct_piece 33 238338 25
  · wct_piece 33 238343 26
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
theorem routine489_ready : RoutineReady ⟨489, by decide⟩ routine489 := by
  wct_ready_start 489 15 9
  wct_cases [238344,238349,238354,235375,235380,235382,235386,4127,1956,1097,1102,862,867]
  · wct_piece 33 238344 27
  · wct_piece 33 238349 28
  · wct_piece 33 238354 29
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
theorem routine490_ready : RoutineReady ⟨490, by decide⟩ routine490 := by
  wct_ready_start 490 15 10
  wct_cases [238355,238360,238365,238370,238372,238376,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 33 238355 30
  · wct_piece 33 238360 31
  · wct_piece 33 238365 32
  · wct_piece 33 238370 33
  · wct_piece 33 238372 34
  · wct_piece 33 238376 35
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine491_ready : RoutineReady ⟨491, by decide⟩ routine491 := by
  wct_ready_start 491 15 11
  wct_cases [238377,238382,238387,238392,238394,238398,238403,238407,862,867]
  · wct_piece 33 238377 36
  · wct_piece 33 238382 37
  · wct_piece 33 238387 38
  · wct_piece 33 238392 39
  · wct_piece 33 238394 40
  · wct_piece 33 238398 41
  · wct_piece 33 238403 42
  · wct_piece 33 238407 43
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine492_ready : RoutineReady ⟨492, by decide⟩ routine492 := by
  wct_ready_start 492 15 12
  wct_cases [238408,238413,238418,238423,238425,238429,238434,238439,238443,945]
  · wct_piece 33 238408 44
  · wct_piece 33 238413 45
  · wct_piece 33 238418 46
  · wct_piece 33 238423 47
  · wct_piece 33 238425 48
  · wct_piece 33 238429 49
  · wct_piece 33 238434 50
  · wct_piece 33 238439 51
  · wct_piece 33 238443 52
  · wct_piece 0 945 57
theorem routine493_ready : RoutineReady ⟨493, by decide⟩ routine493 := by
  wct_ready_start 493 15 13
  wct_cases [238444,238449,238454,238459,238461,238465,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 33 238444 53
  · wct_piece 33 238449 54
  · wct_piece 33 238454 55
  · wct_piece 33 238459 56
  · wct_piece 33 238461 57
  · wct_piece 33 238465 58
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine494_ready : RoutineReady ⟨494, by decide⟩ routine494 := by
  wct_ready_start 494 15 14
  wct_cases [238466,238471,238476,238481,238484,4219,4224,4228,2481,1301,862,867]
  · wct_piece 33 238466 59
  · wct_piece 33 238471 60
  · wct_piece 33 238476 61
  · wct_piece 33 238481 62
  · wct_piece 33 238484 63
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine495_ready : RoutineReady ⟨495, by decide⟩ routine495 := by
  wct_ready_start 495 15 15
  wct_cases [238485,238490,238495,238500,238503,238508,238512,238517,238521]
  · wct_piece 34 238485 0
  · wct_piece 34 238490 1
  · wct_piece 34 238495 2
  · wct_piece 34 238500 3
  · wct_piece 34 238503 4
  · wct_piece 34 238508 5
  · wct_piece 34 238512 6
  · wct_piece 34 238517 7
  · wct_piece 34 238521 8
theorem routine496_ready : RoutineReady ⟨496, by decide⟩ routine496 := by
  wct_ready_start 496 15 16
  wct_cases [238527,238532,238537,238542,238545,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 34 238527 9
  · wct_piece 34 238532 10
  · wct_piece 34 238537 11
  · wct_piece 34 238542 12
  · wct_piece 34 238545 13
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine497_ready : RoutineReady ⟨497, by decide⟩ routine497 := by
  wct_ready_start 497 15 17
  wct_cases [238546,238551,238556,235535,235540,235543,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 34 238546 14
  · wct_piece 34 238551 15
  · wct_piece 34 238556 16
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
theorem routine498_ready : RoutineReady ⟨498, by decide⟩ routine498 := by
  wct_ready_start 498 15 18
  wct_cases [238557,238562,238567,235552,235557,235559,235561,235565,2481,1301,862,867]
  · wct_piece 34 238557 17
  · wct_piece 34 238562 18
  · wct_piece 34 238567 19
  · wct_piece 21 235552 4
  · wct_piece 21 235557 5
  · wct_piece 21 235559 6
  · wct_piece 21 235561 7
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine499_ready : RoutineReady ⟨499, by decide⟩ routine499 := by
  wct_ready_start 499 15 19
  wct_cases [238568,238573,238578,235574,235579,235581,235583,235587,2503,1320,1325,1329,945]
  · wct_piece 34 238568 20
  · wct_piece 34 238573 21
  · wct_piece 34 238578 22
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
theorem routine500_ready : RoutineReady ⟨500, by decide⟩ routine500 := by
  wct_ready_start 500 15 20
  wct_cases [238579,238584,238589,235596,235601,235603,235605,235609,2522,2527,2531,1502,945]
  · wct_piece 34 238579 23
  · wct_piece 34 238584 24
  · wct_piece 34 238589 25
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
theorem routine501_ready : RoutineReady ⟨501, by decide⟩ routine501 := by
  wct_ready_start 501 15 21
  wct_cases [238590,238595,238600,235618,235623,235625,235628,235633,235637,2866,1502,945]
  · wct_piece 34 238590 26
  · wct_piece 34 238595 27
  · wct_piece 34 238600 28
  · wct_piece 21 235618 25
  · wct_piece 21 235623 26
  · wct_piece 21 235625 27
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine502_ready : RoutineReady ⟨502, by decide⟩ routine502 := by
  wct_ready_start 502 15 22
  wct_cases [238601,238606,238611,238613,238617,235651,2545,1343,886,754,759,761,764]
  · wct_piece 34 238601 29
  · wct_piece 34 238606 30
  · wct_piece 34 238611 31
  · wct_piece 34 238613 32
  · wct_piece 34 238617 33
  · wct_piece 21 235651 35
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine503_ready : RoutineReady ⟨503, by decide⟩ routine503 := by
  wct_ready_start 503 15 23
  wct_cases [238618,238623,238628,238630,238634,235665,2559,1357,897,902,799,804,807]
  · wct_piece 34 238618 34
  · wct_piece 34 238623 35
  · wct_piece 34 238628 36
  · wct_piece 34 238630 37
  · wct_piece 34 238634 38
  · wct_piece 21 235665 40
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine504_ready : RoutineReady ⟨504, by decide⟩ routine504 := by
  wct_ready_start 504 15 24
  wct_cases [238635,238640,238645,238647,238651,235679,2573,1371,913,918,921,862,867]
  · wct_piece 34 238635 39
  · wct_piece 34 238640 40
  · wct_piece 34 238645 41
  · wct_piece 34 238647 42
  · wct_piece 34 238651 43
  · wct_piece 21 235679 45
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine505_ready : RoutineReady ⟨505, by decide⟩ routine505 := by
  wct_ready_start 505 15 25
  wct_cases [238652,238657,238662,238664,238668,235693,2587,1385,932,937,939,941,945]
  · wct_piece 34 238652 44
  · wct_piece 34 238657 45
  · wct_piece 34 238662 46
  · wct_piece 34 238664 47
  · wct_piece 34 238668 48
  · wct_piece 21 235693 50
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine506_ready : RoutineReady ⟨506, by decide⟩ routine506 := by
  wct_ready_start 506 15 26
  wct_cases [238669,238674,238679,238681,238685,1396,1401,1405,1081,799,804,807]
  · wct_piece 34 238669 49
  · wct_piece 34 238674 50
  · wct_piece 34 238679 51
  · wct_piece 34 238681 52
  · wct_piece 34 238685 53
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine507_ready : RoutineReady ⟨507, by decide⟩ routine507 := by
  wct_ready_start 507 15 27
  wct_cases [238686,238691,238696,238698,238702,235721,2615,1416,1421,1097,1102,862,867]
  · wct_piece 34 238686 54
  · wct_piece 34 238691 55
  · wct_piece 34 238696 56
  · wct_piece 34 238698 57
  · wct_piece 34 238702 58
  · wct_piece 21 235721 60
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine508_ready : RoutineReady ⟨508, by decide⟩ routine508 := by
  wct_ready_start 508 15 28
  wct_cases [238703,238708,238713,238715,238719,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 34 238703 59
  · wct_piece 34 238708 60
  · wct_piece 34 238713 61
  · wct_piece 34 238715 62
  · wct_piece 34 238719 63
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine509_ready : RoutineReady ⟨509, by decide⟩ routine509 := by
  wct_ready_start 509 15 29
  wct_cases [238720,238725,238730,238732,238736,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 35 238720 0
  · wct_piece 35 238725 1
  · wct_piece 35 238730 2
  · wct_piece 35 238732 3
  · wct_piece 35 238736 4
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine510_ready : RoutineReady ⟨510, by decide⟩ routine510 := by
  wct_ready_start 510 15 30
  wct_cases [238737,238742,238747,238749,238753,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 35 238737 5
  · wct_piece 35 238742 6
  · wct_piece 35 238747 7
  · wct_piece 35 238749 8
  · wct_piece 35 238753 9
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine511_ready : RoutineReady ⟨511, by decide⟩ routine511 := by
  wct_ready_start 511 15 31
  wct_cases [238754,238759,238764,238766,238770,235777,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 35 238754 10
  · wct_piece 35 238759 11
  · wct_piece 35 238764 12
  · wct_piece 35 238766 13
  · wct_piece 35 238770 14
  · wct_piece 22 235777 16
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage15 (rank : Fin 728) (hlo : 480 ≤ rank.val) (hhi : rank.val < 512) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 480 ≤ n at hlo
  change n < 512 at hhi
  interval_cases n
  · exact ⟨routine480, routine480_ready⟩
  · exact ⟨routine481, routine481_ready⟩
  · exact ⟨routine482, routine482_ready⟩
  · exact ⟨routine483, routine483_ready⟩
  · exact ⟨routine484, routine484_ready⟩
  · exact ⟨routine485, routine485_ready⟩
  · exact ⟨routine486, routine486_ready⟩
  · exact ⟨routine487, routine487_ready⟩
  · exact ⟨routine488, routine488_ready⟩
  · exact ⟨routine489, routine489_ready⟩
  · exact ⟨routine490, routine490_ready⟩
  · exact ⟨routine491, routine491_ready⟩
  · exact ⟨routine492, routine492_ready⟩
  · exact ⟨routine493, routine493_ready⟩
  · exact ⟨routine494, routine494_ready⟩
  · exact ⟨routine495, routine495_ready⟩
  · exact ⟨routine496, routine496_ready⟩
  · exact ⟨routine497, routine497_ready⟩
  · exact ⟨routine498, routine498_ready⟩
  · exact ⟨routine499, routine499_ready⟩
  · exact ⟨routine500, routine500_ready⟩
  · exact ⟨routine501, routine501_ready⟩
  · exact ⟨routine502, routine502_ready⟩
  · exact ⟨routine503, routine503_ready⟩
  · exact ⟨routine504, routine504_ready⟩
  · exact ⟨routine505, routine505_ready⟩
  · exact ⟨routine506, routine506_ready⟩
  · exact ⟨routine507, routine507_ready⟩
  · exact ⟨routine508, routine508_ready⟩
  · exact ⟨routine509, routine509_ready⟩
  · exact ⟨routine510, routine510_ready⟩
  · exact ⟨routine511, routine511_ready⟩
end W9Machine.Chain
end
