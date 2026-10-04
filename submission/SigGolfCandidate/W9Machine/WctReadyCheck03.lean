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
def routine96 : ChainRoutine := ⟨96, [0, 0, 2, 1, 0, 0, 3], [piece2193, piece2198, piece2201, piece2206, piece2210, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine97 : ChainRoutine := ⟨97, [0, 0, 2, 1, 0, 1, 2], [piece2211, piece2216, piece2219, piece2224, piece2228, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine98 : ChainRoutine := ⟨98, [0, 0, 2, 1, 0, 2, 1], [piece2229, piece2234, piece2237, piece2242, piece2246, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine99 : ChainRoutine := ⟨99, [0, 0, 2, 1, 0, 3, 0], [piece2247, piece2252, piece2255, piece2260, piece2264, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine100 : ChainRoutine := ⟨100, [0, 0, 2, 1, 1, 0, 2], [piece2265, piece2270, piece2273, piece2278, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine101 : ChainRoutine := ⟨101, [0, 0, 2, 1, 1, 1, 1], [piece2279, piece2284, piece2287, piece2292, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine102 : ChainRoutine := ⟨102, [0, 0, 2, 1, 1, 2, 0], [piece2293, piece2298, piece2301, piece2306, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine103 : ChainRoutine := ⟨103, [0, 0, 2, 1, 2, 0, 1], [piece2307, piece2312, piece2315, piece2320, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine104 : ChainRoutine := ⟨104, [0, 0, 2, 1, 2, 1, 0], [piece2321, piece2326, piece2329, piece2334, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine105 : ChainRoutine := ⟨105, [0, 0, 2, 1, 3, 0, 0], [piece2335, piece2340, piece2343, piece2348, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine106 : ChainRoutine := ⟨106, [0, 0, 2, 2, 0, 0, 2], [piece2349, piece2354, piece2357, piece2362, piece2364, piece2368, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine107 : ChainRoutine := ⟨107, [0, 0, 2, 2, 0, 1, 1], [piece2369, piece2374, piece2377, piece2382, piece2384, piece2388, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine108 : ChainRoutine := ⟨108, [0, 0, 2, 2, 0, 2, 0], [piece2389, piece2394, piece2397, piece2402, piece2404, piece2408, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine109 : ChainRoutine := ⟨109, [0, 0, 2, 2, 1, 0, 1], [piece2409, piece2414, piece2417, piece2422, piece2425, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine110 : ChainRoutine := ⟨110, [0, 0, 2, 2, 1, 1, 0], [piece2426, piece2431, piece2434, piece2439, piece2442, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine111 : ChainRoutine := ⟨111, [0, 0, 2, 2, 2, 0, 0], [piece2443, piece2448, piece2451, piece2456, piece2459, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine112 : ChainRoutine := ⟨112, [0, 0, 2, 3, 0, 0, 1], [piece2460, piece2465, piece2468, piece2473, piece2475, piece2477, piece2481, piece1301, piece862, piece867]⟩
def routine113 : ChainRoutine := ⟨113, [0, 0, 2, 3, 0, 1, 0], [piece2482, piece2487, piece2490, piece2495, piece2497, piece2499, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine114 : ChainRoutine := ⟨114, [0, 0, 2, 3, 1, 0, 0], [piece2504, piece2509, piece2512, piece2517, piece2519, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine115 : ChainRoutine := ⟨115, [0, 0, 3, 0, 0, 0, 3], [piece2532, piece2537, piece2539, piece2541, piece2545, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine116 : ChainRoutine := ⟨116, [0, 0, 3, 0, 0, 1, 2], [piece2546, piece2551, piece2553, piece2555, piece2559, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine117 : ChainRoutine := ⟨117, [0, 0, 3, 0, 0, 2, 1], [piece2560, piece2565, piece2567, piece2569, piece2573, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine118 : ChainRoutine := ⟨118, [0, 0, 3, 0, 0, 3, 0], [piece2574, piece2579, piece2581, piece2583, piece2587, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine119 : ChainRoutine := ⟨119, [0, 0, 3, 0, 1, 0, 2], [piece2588, piece2593, piece2595, piece2597, piece2601, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine120 : ChainRoutine := ⟨120, [0, 0, 3, 0, 1, 1, 1], [piece2602, piece2607, piece2609, piece2611, piece2615, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine121 : ChainRoutine := ⟨121, [0, 0, 3, 0, 1, 2, 0], [piece2616, piece2621, piece2623, piece2625, piece2629, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine122 : ChainRoutine := ⟨122, [0, 0, 3, 0, 2, 0, 1], [piece2630, piece2635, piece2637, piece2639, piece2643, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine123 : ChainRoutine := ⟨123, [0, 0, 3, 0, 2, 1, 0], [piece2644, piece2649, piece2651, piece2653, piece2657, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine124 : ChainRoutine := ⟨124, [0, 0, 3, 0, 3, 0, 0], [piece2658, piece2663, piece2665, piece2667, piece2671, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine125 : ChainRoutine := ⟨125, [0, 0, 3, 1, 0, 0, 2], [piece2672, piece2677, piece2679, piece2682, piece2687, piece2691, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine126 : ChainRoutine := ⟨126, [0, 0, 3, 1, 0, 1, 1], [piece2692, piece2697, piece2699, piece2702, piece2707, piece2711, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine127 : ChainRoutine := ⟨127, [0, 0, 3, 1, 0, 2, 0], [piece2712, piece2717, piece2719, piece2722, piece2727, piece2731, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routineBatch03 : List ChainRoutine := [routine96, routine97, routine98, routine99, routine100, routine101, routine102, routine103, routine104, routine105, routine106, routine107, routine108, routine109, routine110, routine111, routine112, routine113, routine114, routine115, routine116, routine117, routine118, routine119, routine120, routine121, routine122, routine123, routine124, routine125, routine126, routine127]
theorem routineBatch03_checked : (routineBatch03.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch03_checked :
    (routineBatch03.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch03_checked :
    (routineBatch03.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine96_ready : RoutineReady ⟨96, by decide⟩ routine96 := by
  wct_ready_start 96 3 0
  wct_cases [2193,2198,2201,2206,2210,1343,886,754,759,761,764]
  · wct_piece 6 2193 49
  · wct_piece 6 2198 50
  · wct_piece 6 2201 51
  · wct_piece 6 2206 52
  · wct_piece 6 2210 53
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine97_ready : RoutineReady ⟨97, by decide⟩ routine97 := by
  wct_ready_start 97 3 1
  wct_cases [2211,2216,2219,2224,2228,1357,897,902,799,804,807]
  · wct_piece 6 2211 54
  · wct_piece 6 2216 55
  · wct_piece 6 2219 56
  · wct_piece 6 2224 57
  · wct_piece 6 2228 58
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine98_ready : RoutineReady ⟨98, by decide⟩ routine98 := by
  wct_ready_start 98 3 2
  wct_cases [2229,2234,2237,2242,2246,1371,913,918,921,862,867]
  · wct_piece 6 2229 59
  · wct_piece 6 2234 60
  · wct_piece 6 2237 61
  · wct_piece 6 2242 62
  · wct_piece 6 2246 63
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine99_ready : RoutineReady ⟨99, by decide⟩ routine99 := by
  wct_ready_start 99 3 3
  wct_cases [2247,2252,2255,2260,2264,1385,932,937,939,941,945]
  · wct_piece 7 2247 0
  · wct_piece 7 2252 1
  · wct_piece 7 2255 2
  · wct_piece 7 2260 3
  · wct_piece 7 2264 4
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine100_ready : RoutineReady ⟨100, by decide⟩ routine100 := by
  wct_ready_start 100 3 4
  wct_cases [2265,2270,2273,2278,1396,1401,1405,1081,799,804,807]
  · wct_piece 7 2265 5
  · wct_piece 7 2270 6
  · wct_piece 7 2273 7
  · wct_piece 7 2278 8
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine101_ready : RoutineReady ⟨101, by decide⟩ routine101 := by
  wct_ready_start 101 3 5
  wct_cases [2279,2284,2287,2292,1416,1421,1097,1102,862,867]
  · wct_piece 7 2279 9
  · wct_piece 7 2284 10
  · wct_piece 7 2287 11
  · wct_piece 7 2292 12
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine102_ready : RoutineReady ⟨102, by decide⟩ routine102 := by
  wct_ready_start 102 3 6
  wct_cases [2293,2298,2301,2306,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 7 2293 13
  · wct_piece 7 2298 14
  · wct_piece 7 2301 15
  · wct_piece 7 2306 16
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine103_ready : RoutineReady ⟨103, by decide⟩ routine103 := by
  wct_ready_start 103 3 7
  wct_cases [2307,2312,2315,2320,1448,1453,1455,1459,1301,862,867]
  · wct_piece 7 2307 17
  · wct_piece 7 2312 18
  · wct_piece 7 2315 19
  · wct_piece 7 2320 20
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine104_ready : RoutineReady ⟨104, by decide⟩ routine104 := by
  wct_ready_start 104 3 8
  wct_cases [2321,2326,2329,2334,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 7 2321 21
  · wct_piece 7 2326 22
  · wct_piece 7 2329 23
  · wct_piece 7 2334 24
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine105_ready : RoutineReady ⟨105, by decide⟩ routine105 := by
  wct_ready_start 105 3 9
  wct_cases [2335,2340,2343,2348,1489,1494,1496,1498,1502,945]
  · wct_piece 7 2335 25
  · wct_piece 7 2340 26
  · wct_piece 7 2343 27
  · wct_piece 7 2348 28
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine106_ready : RoutineReady ⟨106, by decide⟩ routine106 := by
  wct_ready_start 106 3 10
  wct_cases [2349,2354,2357,2362,2364,2368,1937,1081,799,804,807]
  · wct_piece 7 2349 29
  · wct_piece 7 2354 30
  · wct_piece 7 2357 31
  · wct_piece 7 2362 32
  · wct_piece 7 2364 33
  · wct_piece 7 2368 34
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine107_ready : RoutineReady ⟨107, by decide⟩ routine107 := by
  wct_ready_start 107 3 11
  wct_cases [2369,2374,2377,2382,2384,2388,1956,1097,1102,862,867]
  · wct_piece 7 2369 35
  · wct_piece 7 2374 36
  · wct_piece 7 2377 37
  · wct_piece 7 2382 38
  · wct_piece 7 2384 39
  · wct_piece 7 2388 40
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine108_ready : RoutineReady ⟨108, by decide⟩ routine108 := by
  wct_ready_start 108 3 12
  wct_cases [2389,2394,2397,2402,2404,2408,1975,1118,1123,1125,1129,945]
  · wct_piece 7 2389 41
  · wct_piece 7 2394 42
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
theorem routine109_ready : RoutineReady ⟨109, by decide⟩ routine109 := by
  wct_ready_start 109 3 13
  wct_cases [2409,2414,2417,2422,2425,1991,1996,2000,1301,862,867]
  · wct_piece 7 2409 47
  · wct_piece 7 2414 48
  · wct_piece 7 2417 49
  · wct_piece 7 2422 50
  · wct_piece 7 2425 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine110_ready : RoutineReady ⟨110, by decide⟩ routine110 := by
  wct_ready_start 110 3 14
  wct_cases [2426,2431,2434,2439,2442,2016,2021,1320,1325,1329,945]
  · wct_piece 7 2426 52
  · wct_piece 7 2431 53
  · wct_piece 7 2434 54
  · wct_piece 7 2439 55
  · wct_piece 7 2442 56
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine111_ready : RoutineReady ⟨111, by decide⟩ routine111 := by
  wct_ready_start 111 3 15
  wct_cases [2443,2448,2451,2456,2459,2037,2042,2044,2048,1502,945]
  · wct_piece 7 2443 57
  · wct_piece 7 2448 58
  · wct_piece 7 2451 59
  · wct_piece 7 2456 60
  · wct_piece 7 2459 61
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine112_ready : RoutineReady ⟨112, by decide⟩ routine112 := by
  wct_ready_start 112 3 16
  wct_cases [2460,2465,2468,2473,2475,2477,2481,1301,862,867]
  · wct_piece 7 2460 62
  · wct_piece 7 2465 63
  · wct_piece 8 2468 0
  · wct_piece 8 2473 1
  · wct_piece 8 2475 2
  · wct_piece 8 2477 3
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine113_ready : RoutineReady ⟨113, by decide⟩ routine113 := by
  wct_ready_start 113 3 17
  wct_cases [2482,2487,2490,2495,2497,2499,2503,1320,1325,1329,945]
  · wct_piece 8 2482 5
  · wct_piece 8 2487 6
  · wct_piece 8 2490 7
  · wct_piece 8 2495 8
  · wct_piece 8 2497 9
  · wct_piece 8 2499 10
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine114_ready : RoutineReady ⟨114, by decide⟩ routine114 := by
  wct_ready_start 114 3 18
  wct_cases [2504,2509,2512,2517,2519,2522,2527,2531,1502,945]
  · wct_piece 8 2504 12
  · wct_piece 8 2509 13
  · wct_piece 8 2512 14
  · wct_piece 8 2517 15
  · wct_piece 8 2519 16
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine115_ready : RoutineReady ⟨115, by decide⟩ routine115 := by
  wct_ready_start 115 3 19
  wct_cases [2532,2537,2539,2541,2545,1343,886,754,759,761,764]
  · wct_piece 8 2532 20
  · wct_piece 8 2537 21
  · wct_piece 8 2539 22
  · wct_piece 8 2541 23
  · wct_piece 8 2545 24
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine116_ready : RoutineReady ⟨116, by decide⟩ routine116 := by
  wct_ready_start 116 3 20
  wct_cases [2546,2551,2553,2555,2559,1357,897,902,799,804,807]
  · wct_piece 8 2546 25
  · wct_piece 8 2551 26
  · wct_piece 8 2553 27
  · wct_piece 8 2555 28
  · wct_piece 8 2559 29
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine117_ready : RoutineReady ⟨117, by decide⟩ routine117 := by
  wct_ready_start 117 3 21
  wct_cases [2560,2565,2567,2569,2573,1371,913,918,921,862,867]
  · wct_piece 8 2560 30
  · wct_piece 8 2565 31
  · wct_piece 8 2567 32
  · wct_piece 8 2569 33
  · wct_piece 8 2573 34
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine118_ready : RoutineReady ⟨118, by decide⟩ routine118 := by
  wct_ready_start 118 3 22
  wct_cases [2574,2579,2581,2583,2587,1385,932,937,939,941,945]
  · wct_piece 8 2574 35
  · wct_piece 8 2579 36
  · wct_piece 8 2581 37
  · wct_piece 8 2583 38
  · wct_piece 8 2587 39
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine119_ready : RoutineReady ⟨119, by decide⟩ routine119 := by
  wct_ready_start 119 3 23
  wct_cases [2588,2593,2595,2597,2601,1396,1401,1405,1081,799,804,807]
  · wct_piece 8 2588 40
  · wct_piece 8 2593 41
  · wct_piece 8 2595 42
  · wct_piece 8 2597 43
  · wct_piece 8 2601 44
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine120_ready : RoutineReady ⟨120, by decide⟩ routine120 := by
  wct_ready_start 120 3 24
  wct_cases [2602,2607,2609,2611,2615,1416,1421,1097,1102,862,867]
  · wct_piece 8 2602 45
  · wct_piece 8 2607 46
  · wct_piece 8 2609 47
  · wct_piece 8 2611 48
  · wct_piece 8 2615 49
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine121_ready : RoutineReady ⟨121, by decide⟩ routine121 := by
  wct_ready_start 121 3 25
  wct_cases [2616,2621,2623,2625,2629,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 8 2616 50
  · wct_piece 8 2621 51
  · wct_piece 8 2623 52
  · wct_piece 8 2625 53
  · wct_piece 8 2629 54
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine122_ready : RoutineReady ⟨122, by decide⟩ routine122 := by
  wct_ready_start 122 3 26
  wct_cases [2630,2635,2637,2639,2643,1448,1453,1455,1459,1301,862,867]
  · wct_piece 8 2630 55
  · wct_piece 8 2635 56
  · wct_piece 8 2637 57
  · wct_piece 8 2639 58
  · wct_piece 8 2643 59
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine123_ready : RoutineReady ⟨123, by decide⟩ routine123 := by
  wct_ready_start 123 3 27
  wct_cases [2644,2649,2651,2653,2657,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 8 2644 60
  · wct_piece 8 2649 61
  · wct_piece 8 2651 62
  · wct_piece 8 2653 63
  · wct_piece 9 2657 0
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine124_ready : RoutineReady ⟨124, by decide⟩ routine124 := by
  wct_ready_start 124 3 28
  wct_cases [2658,2663,2665,2667,2671,1489,1494,1496,1498,1502,945]
  · wct_piece 9 2658 1
  · wct_piece 9 2663 2
  · wct_piece 9 2665 3
  · wct_piece 9 2667 4
  · wct_piece 9 2671 5
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine125_ready : RoutineReady ⟨125, by decide⟩ routine125 := by
  wct_ready_start 125 3 29
  wct_cases [2672,2677,2679,2682,2687,2691,1937,1081,799,804,807]
  · wct_piece 9 2672 6
  · wct_piece 9 2677 7
  · wct_piece 9 2679 8
  · wct_piece 9 2682 9
  · wct_piece 9 2687 10
  · wct_piece 9 2691 11
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine126_ready : RoutineReady ⟨126, by decide⟩ routine126 := by
  wct_ready_start 126 3 30
  wct_cases [2692,2697,2699,2702,2707,2711,1956,1097,1102,862,867]
  · wct_piece 9 2692 12
  · wct_piece 9 2697 13
  · wct_piece 9 2699 14
  · wct_piece 9 2702 15
  · wct_piece 9 2707 16
  · wct_piece 9 2711 17
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine127_ready : RoutineReady ⟨127, by decide⟩ routine127 := by
  wct_ready_start 127 3 31
  wct_cases [2712,2717,2719,2722,2727,2731,1975,1118,1123,1125,1129,945]
  · wct_piece 9 2712 18
  · wct_piece 9 2717 19
  · wct_piece 9 2719 20
  · wct_piece 9 2722 21
  · wct_piece 9 2727 22
  · wct_piece 9 2731 23
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
end W9Machine.Chain
end
