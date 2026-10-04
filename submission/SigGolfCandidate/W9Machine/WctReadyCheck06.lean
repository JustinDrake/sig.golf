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
def routine192 : ChainRoutine := ⟨192, [0, 1, 1, 1, 1, 1, 1], [piece3606, piece3611, piece3616, piece2287, piece2292, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine193 : ChainRoutine := ⟨193, [0, 1, 1, 1, 1, 2, 0], [piece3617, piece3622, piece3627, piece2301, piece2306, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine194 : ChainRoutine := ⟨194, [0, 1, 1, 1, 2, 0, 1], [piece3628, piece3633, piece3638, piece2315, piece2320, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine195 : ChainRoutine := ⟨195, [0, 1, 1, 1, 2, 1, 0], [piece3639, piece3644, piece3649, piece2329, piece2334, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine196 : ChainRoutine := ⟨196, [0, 1, 1, 1, 3, 0, 0], [piece3650, piece3655, piece3660, piece2343, piece2348, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine197 : ChainRoutine := ⟨197, [0, 1, 1, 2, 0, 0, 2], [piece3661, piece3666, piece3671, piece2357, piece2362, piece2364, piece2368, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine198 : ChainRoutine := ⟨198, [0, 1, 1, 2, 0, 1, 1], [piece3672, piece3677, piece3682, piece2377, piece2382, piece2384, piece2388, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine199 : ChainRoutine := ⟨199, [0, 1, 1, 2, 0, 2, 0], [piece3683, piece3688, piece3693, piece2397, piece2402, piece2404, piece2408, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine200 : ChainRoutine := ⟨200, [0, 1, 1, 2, 1, 0, 1], [piece3694, piece3699, piece3704, piece2417, piece2422, piece2425, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine201 : ChainRoutine := ⟨201, [0, 1, 1, 2, 1, 1, 0], [piece3705, piece3710, piece3715, piece2434, piece2439, piece2442, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine202 : ChainRoutine := ⟨202, [0, 1, 1, 2, 2, 0, 0], [piece3716, piece3721, piece3726, piece2451, piece2456, piece2459, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine203 : ChainRoutine := ⟨203, [0, 1, 1, 3, 0, 0, 1], [piece3727, piece3732, piece3737, piece2468, piece2473, piece2475, piece2477, piece2481, piece1301, piece862, piece867]⟩
def routine204 : ChainRoutine := ⟨204, [0, 1, 1, 3, 0, 1, 0], [piece3738, piece3743, piece3748, piece2490, piece2495, piece2497, piece2499, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine205 : ChainRoutine := ⟨205, [0, 1, 1, 3, 1, 0, 0], [piece3749, piece3754, piece3759, piece2512, piece2517, piece2519, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine206 : ChainRoutine := ⟨206, [0, 1, 2, 0, 0, 0, 3], [piece3760, piece3765, piece3770, piece3772, piece3776, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine207 : ChainRoutine := ⟨207, [0, 1, 2, 0, 0, 1, 2], [piece3777, piece3782, piece3787, piece3789, piece3793, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine208 : ChainRoutine := ⟨208, [0, 1, 2, 0, 0, 2, 1], [piece3794, piece3799, piece3804, piece3806, piece3810, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine209 : ChainRoutine := ⟨209, [0, 1, 2, 0, 0, 3, 0], [piece3811, piece3816, piece3821, piece3823, piece3827, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine210 : ChainRoutine := ⟨210, [0, 1, 2, 0, 1, 0, 2], [piece3828, piece3833, piece3838, piece3840, piece3844, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine211 : ChainRoutine := ⟨211, [0, 1, 2, 0, 1, 1, 1], [piece3845, piece3850, piece3855, piece3857, piece3861, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine212 : ChainRoutine := ⟨212, [0, 1, 2, 0, 1, 2, 0], [piece3862, piece3867, piece3872, piece3874, piece3878, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine213 : ChainRoutine := ⟨213, [0, 1, 2, 0, 2, 0, 1], [piece3879, piece3884, piece3889, piece3891, piece3895, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine214 : ChainRoutine := ⟨214, [0, 1, 2, 0, 2, 1, 0], [piece3896, piece3901, piece3906, piece3908, piece3912, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine215 : ChainRoutine := ⟨215, [0, 1, 2, 0, 3, 0, 0], [piece3913, piece3918, piece3923, piece3925, piece3929, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine216 : ChainRoutine := ⟨216, [0, 1, 2, 1, 0, 0, 2], [piece3930, piece3935, piece3940, piece3943, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine217 : ChainRoutine := ⟨217, [0, 1, 2, 1, 0, 1, 1], [piece3944, piece3949, piece3954, piece3957, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine218 : ChainRoutine := ⟨218, [0, 1, 2, 1, 0, 2, 0], [piece3958, piece3963, piece3968, piece3971, piece3976, piece3980, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine219 : ChainRoutine := ⟨219, [0, 1, 2, 1, 1, 0, 1], [piece3981, piece3986, piece3991, piece3994, piece2742, piece2747, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine220 : ChainRoutine := ⟨220, [0, 1, 2, 1, 1, 1, 0], [piece3995, piece4000, piece4005, piece4008, piece2758, piece2763, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine221 : ChainRoutine := ⟨221, [0, 1, 2, 1, 2, 0, 0], [piece4009, piece4014, piece4019, piece4022, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine222 : ChainRoutine := ⟨222, [0, 1, 2, 2, 0, 0, 1], [piece4023, piece4028, piece4033, piece4036, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine223 : ChainRoutine := ⟨223, [0, 1, 2, 2, 0, 1, 0], [piece4037, piece4042, piece4047, piece4050, piece4055, piece4057, piece4061, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routineBatch06 : List ChainRoutine := [routine192, routine193, routine194, routine195, routine196, routine197, routine198, routine199, routine200, routine201, routine202, routine203, routine204, routine205, routine206, routine207, routine208, routine209, routine210, routine211, routine212, routine213, routine214, routine215, routine216, routine217, routine218, routine219, routine220, routine221, routine222, routine223]
theorem routineBatch06_checked : (routineBatch06.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch06_checked :
    (routineBatch06.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch06_checked :
    (routineBatch06.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine192_ready : RoutineReady ⟨192, by decide⟩ routine192 := by
  wct_ready_start 192 6 0
  wct_cases [3606,3611,3616,2287,2292,1416,1421,1097,1102,862,867]
  · wct_piece 13 3606 19
  · wct_piece 13 3611 20
  · wct_piece 13 3616 21
  · wct_piece 7 2287 11
  · wct_piece 7 2292 12
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine193_ready : RoutineReady ⟨193, by decide⟩ routine193 := by
  wct_ready_start 193 6 1
  wct_cases [3617,3622,3627,2301,2306,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 13 3617 22
  · wct_piece 13 3622 23
  · wct_piece 13 3627 24
  · wct_piece 7 2301 15
  · wct_piece 7 2306 16
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine194_ready : RoutineReady ⟨194, by decide⟩ routine194 := by
  wct_ready_start 194 6 2
  wct_cases [3628,3633,3638,2315,2320,1448,1453,1455,1459,1301,862,867]
  · wct_piece 13 3628 25
  · wct_piece 13 3633 26
  · wct_piece 13 3638 27
  · wct_piece 7 2315 19
  · wct_piece 7 2320 20
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine195_ready : RoutineReady ⟨195, by decide⟩ routine195 := by
  wct_ready_start 195 6 3
  wct_cases [3639,3644,3649,2329,2334,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 13 3639 28
  · wct_piece 13 3644 29
  · wct_piece 13 3649 30
  · wct_piece 7 2329 23
  · wct_piece 7 2334 24
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine196_ready : RoutineReady ⟨196, by decide⟩ routine196 := by
  wct_ready_start 196 6 4
  wct_cases [3650,3655,3660,2343,2348,1489,1494,1496,1498,1502,945]
  · wct_piece 13 3650 31
  · wct_piece 13 3655 32
  · wct_piece 13 3660 33
  · wct_piece 7 2343 27
  · wct_piece 7 2348 28
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine197_ready : RoutineReady ⟨197, by decide⟩ routine197 := by
  wct_ready_start 197 6 5
  wct_cases [3661,3666,3671,2357,2362,2364,2368,1937,1081,799,804,807]
  · wct_piece 13 3661 34
  · wct_piece 13 3666 35
  · wct_piece 13 3671 36
  · wct_piece 7 2357 31
  · wct_piece 7 2362 32
  · wct_piece 7 2364 33
  · wct_piece 7 2368 34
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine198_ready : RoutineReady ⟨198, by decide⟩ routine198 := by
  wct_ready_start 198 6 6
  wct_cases [3672,3677,3682,2377,2382,2384,2388,1956,1097,1102,862,867]
  · wct_piece 13 3672 37
  · wct_piece 13 3677 38
  · wct_piece 13 3682 39
  · wct_piece 7 2377 37
  · wct_piece 7 2382 38
  · wct_piece 7 2384 39
  · wct_piece 7 2388 40
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine199_ready : RoutineReady ⟨199, by decide⟩ routine199 := by
  wct_ready_start 199 6 7
  wct_cases [3683,3688,3693,2397,2402,2404,2408,1975,1118,1123,1125,1129,945]
  · wct_piece 13 3683 40
  · wct_piece 13 3688 41
  · wct_piece 13 3693 42
  · wct_piece 7 2397 43
  · wct_piece 7 2402 44
  · wct_piece 7 2404 45
  · wct_piece 7 2408 46
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine200_ready : RoutineReady ⟨200, by decide⟩ routine200 := by
  wct_ready_start 200 6 8
  wct_cases [3694,3699,3704,2417,2422,2425,1991,1996,2000,1301,862,867]
  · wct_piece 13 3694 43
  · wct_piece 13 3699 44
  · wct_piece 13 3704 45
  · wct_piece 7 2417 49
  · wct_piece 7 2422 50
  · wct_piece 7 2425 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine201_ready : RoutineReady ⟨201, by decide⟩ routine201 := by
  wct_ready_start 201 6 9
  wct_cases [3705,3710,3715,2434,2439,2442,2016,2021,1320,1325,1329,945]
  · wct_piece 13 3705 46
  · wct_piece 13 3710 47
  · wct_piece 13 3715 48
  · wct_piece 7 2434 54
  · wct_piece 7 2439 55
  · wct_piece 7 2442 56
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine202_ready : RoutineReady ⟨202, by decide⟩ routine202 := by
  wct_ready_start 202 6 10
  wct_cases [3716,3721,3726,2451,2456,2459,2037,2042,2044,2048,1502,945]
  · wct_piece 13 3716 49
  · wct_piece 13 3721 50
  · wct_piece 13 3726 51
  · wct_piece 7 2451 59
  · wct_piece 7 2456 60
  · wct_piece 7 2459 61
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine203_ready : RoutineReady ⟨203, by decide⟩ routine203 := by
  wct_ready_start 203 6 11
  wct_cases [3727,3732,3737,2468,2473,2475,2477,2481,1301,862,867]
  · wct_piece 13 3727 52
  · wct_piece 13 3732 53
  · wct_piece 13 3737 54
  · wct_piece 8 2468 0
  · wct_piece 8 2473 1
  · wct_piece 8 2475 2
  · wct_piece 8 2477 3
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine204_ready : RoutineReady ⟨204, by decide⟩ routine204 := by
  wct_ready_start 204 6 12
  wct_cases [3738,3743,3748,2490,2495,2497,2499,2503,1320,1325,1329,945]
  · wct_piece 13 3738 55
  · wct_piece 13 3743 56
  · wct_piece 13 3748 57
  · wct_piece 8 2490 7
  · wct_piece 8 2495 8
  · wct_piece 8 2497 9
  · wct_piece 8 2499 10
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine205_ready : RoutineReady ⟨205, by decide⟩ routine205 := by
  wct_ready_start 205 6 13
  wct_cases [3749,3754,3759,2512,2517,2519,2522,2527,2531,1502,945]
  · wct_piece 13 3749 58
  · wct_piece 13 3754 59
  · wct_piece 13 3759 60
  · wct_piece 8 2512 14
  · wct_piece 8 2517 15
  · wct_piece 8 2519 16
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine206_ready : RoutineReady ⟨206, by decide⟩ routine206 := by
  wct_ready_start 206 6 14
  wct_cases [3760,3765,3770,3772,3776,2545,1343,886,754,759,761,764]
  · wct_piece 13 3760 61
  · wct_piece 13 3765 62
  · wct_piece 13 3770 63
  · wct_piece 14 3772 0
  · wct_piece 14 3776 1
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine207_ready : RoutineReady ⟨207, by decide⟩ routine207 := by
  wct_ready_start 207 6 15
  wct_cases [3777,3782,3787,3789,3793,2559,1357,897,902,799,804,807]
  · wct_piece 14 3777 2
  · wct_piece 14 3782 3
  · wct_piece 14 3787 4
  · wct_piece 14 3789 5
  · wct_piece 14 3793 6
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine208_ready : RoutineReady ⟨208, by decide⟩ routine208 := by
  wct_ready_start 208 6 16
  wct_cases [3794,3799,3804,3806,3810,2573,1371,913,918,921,862,867]
  · wct_piece 14 3794 7
  · wct_piece 14 3799 8
  · wct_piece 14 3804 9
  · wct_piece 14 3806 10
  · wct_piece 14 3810 11
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine209_ready : RoutineReady ⟨209, by decide⟩ routine209 := by
  wct_ready_start 209 6 17
  wct_cases [3811,3816,3821,3823,3827,2587,1385,932,937,939,941,945]
  · wct_piece 14 3811 12
  · wct_piece 14 3816 13
  · wct_piece 14 3821 14
  · wct_piece 14 3823 15
  · wct_piece 14 3827 16
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine210_ready : RoutineReady ⟨210, by decide⟩ routine210 := by
  wct_ready_start 210 6 18
  wct_cases [3828,3833,3838,3840,3844,1396,1401,1405,1081,799,804,807]
  · wct_piece 14 3828 17
  · wct_piece 14 3833 18
  · wct_piece 14 3838 19
  · wct_piece 14 3840 20
  · wct_piece 14 3844 21
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine211_ready : RoutineReady ⟨211, by decide⟩ routine211 := by
  wct_ready_start 211 6 19
  wct_cases [3845,3850,3855,3857,3861,2615,1416,1421,1097,1102,862,867]
  · wct_piece 14 3845 22
  · wct_piece 14 3850 23
  · wct_piece 14 3855 24
  · wct_piece 14 3857 25
  · wct_piece 14 3861 26
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine212_ready : RoutineReady ⟨212, by decide⟩ routine212 := by
  wct_ready_start 212 6 20
  wct_cases [3862,3867,3872,3874,3878,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 14 3862 27
  · wct_piece 14 3867 28
  · wct_piece 14 3872 29
  · wct_piece 14 3874 30
  · wct_piece 14 3878 31
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine213_ready : RoutineReady ⟨213, by decide⟩ routine213 := by
  wct_ready_start 213 6 21
  wct_cases [3879,3884,3889,3891,3895,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 14 3879 32
  · wct_piece 14 3884 33
  · wct_piece 14 3889 34
  · wct_piece 14 3891 35
  · wct_piece 14 3895 36
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine214_ready : RoutineReady ⟨214, by decide⟩ routine214 := by
  wct_ready_start 214 6 22
  wct_cases [3896,3901,3906,3908,3912,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 14 3896 37
  · wct_piece 14 3901 38
  · wct_piece 14 3906 39
  · wct_piece 14 3908 40
  · wct_piece 14 3912 41
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine215_ready : RoutineReady ⟨215, by decide⟩ routine215 := by
  wct_ready_start 215 6 23
  wct_cases [3913,3918,3923,3925,3929,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 14 3913 42
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
theorem routine216_ready : RoutineReady ⟨216, by decide⟩ routine216 := by
  wct_ready_start 216 6 24
  wct_cases [3930,3935,3940,3943,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 14 3930 47
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
theorem routine217_ready : RoutineReady ⟨217, by decide⟩ routine217 := by
  wct_ready_start 217 6 25
  wct_cases [3944,3949,3954,3957,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 14 3944 51
  · wct_piece 14 3949 52
  · wct_piece 14 3954 53
  · wct_piece 14 3957 54
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine218_ready : RoutineReady ⟨218, by decide⟩ routine218 := by
  wct_ready_start 218 6 26
  wct_cases [3958,3963,3968,3971,3976,3980,1975,1118,1123,1125,1129,945]
  · wct_piece 14 3958 55
  · wct_piece 14 3963 56
  · wct_piece 14 3968 57
  · wct_piece 14 3971 58
  · wct_piece 14 3976 59
  · wct_piece 14 3980 60
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine219_ready : RoutineReady ⟨219, by decide⟩ routine219 := by
  wct_ready_start 219 6 27
  wct_cases [3981,3986,3991,3994,2742,2747,1991,1996,2000,1301,862,867]
  · wct_piece 14 3981 61
  · wct_piece 14 3986 62
  · wct_piece 14 3991 63
  · wct_piece 15 3994 0
  · wct_piece 9 2742 27
  · wct_piece 9 2747 28
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine220_ready : RoutineReady ⟨220, by decide⟩ routine220 := by
  wct_ready_start 220 6 28
  wct_cases [3995,4000,4005,4008,2758,2763,2016,2021,1320,1325,1329,945]
  · wct_piece 15 3995 1
  · wct_piece 15 4000 2
  · wct_piece 15 4005 3
  · wct_piece 15 4008 4
  · wct_piece 9 2758 32
  · wct_piece 9 2763 33
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine221_ready : RoutineReady ⟨221, by decide⟩ routine221 := by
  wct_ready_start 221 6 29
  wct_cases [4009,4014,4019,4022,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 15 4009 5
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
theorem routine222_ready : RoutineReady ⟨222, by decide⟩ routine222 := by
  wct_ready_start 222 6 30
  wct_cases [4023,4028,4033,4036,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 15 4023 9
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
theorem routine223_ready : RoutineReady ⟨223, by decide⟩ routine223 := by
  wct_ready_start 223 6 31
  wct_cases [4037,4042,4047,4050,4055,4057,4061,2503,1320,1325,1329,945]
  · wct_piece 15 4037 13
  · wct_piece 15 4042 14
  · wct_piece 15 4047 15
  · wct_piece 15 4050 16
  · wct_piece 15 4055 17
  · wct_piece 15 4057 18
  · wct_piece 15 4061 19
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
end W9Machine.Chain
end
