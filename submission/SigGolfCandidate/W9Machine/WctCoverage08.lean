import SigGolfCandidate.W9Machine.WctRoutineCheck08
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

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
  wct_cases [235125,235131,235133,235137,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 17 235125 20
  · wct_piece 17 235131 21
  · wct_piece 17 235133 22
  · wct_piece 17 235137 23
  · wct_piece 7 2512 23
  · wct_piece 7 2518 24
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine257_ready : RoutineReady ⟨257, by decide⟩ routine257 := by
  wct_ready_start 257 8 1
  wct_cases [235138,235144,235146,235150,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 17 235138 24
  · wct_piece 17 235144 25
  · wct_piece 17 235146 26
  · wct_piece 17 235150 27
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine258_ready : RoutineReady ⟨258, by decide⟩ routine258 := by
  wct_ready_start 258 8 2
  wct_cases [235151,235157,235159,235163,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 17 235151 28
  · wct_piece 17 235157 29
  · wct_piece 17 235159 30
  · wct_piece 17 235163 31
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine259_ready : RoutineReady ⟨259, by decide⟩ routine259 := by
  wct_ready_start 259 8 3
  wct_cases [235164,235170,235172,235176,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 17 235164 32
  · wct_piece 17 235170 33
  · wct_piece 17 235172 34
  · wct_piece 17 235176 35
  · wct_piece 7 2566 37
  · wct_piece 7 2572 38
  · wct_piece 7 2574 39
  · wct_piece 7 2578 40
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine260_ready : RoutineReady ⟨260, by decide⟩ routine260 := by
  wct_ready_start 260 8 4
  wct_cases [235177,235183,235185,235189,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 17 235177 36
  · wct_piece 17 235183 37
  · wct_piece 17 235185 38
  · wct_piece 17 235189 39
  · wct_piece 7 2588 43
  · wct_piece 7 2594 44
  · wct_piece 7 2596 45
  · wct_piece 7 2600 46
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine261_ready : RoutineReady ⟨261, by decide⟩ routine261 := by
  wct_ready_start 261 8 5
  wct_cases [235190,235196,235198,235202,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 17 235190 40
  · wct_piece 17 235196 41
  · wct_piece 17 235198 42
  · wct_piece 17 235202 43
  · wct_piece 7 2610 49
  · wct_piece 7 2616 50
  · wct_piece 7 2619 51
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine262_ready : RoutineReady ⟨262, by decide⟩ routine262 := by
  wct_ready_start 262 8 6
  wct_cases [235203,235209,235211,235215,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 17 235203 44
  · wct_piece 17 235209 45
  · wct_piece 17 235211 46
  · wct_piece 17 235215 47
  · wct_piece 7 2629 54
  · wct_piece 7 2635 55
  · wct_piece 7 2638 56
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine263_ready : RoutineReady ⟨263, by decide⟩ routine263 := by
  wct_ready_start 263 8 7
  wct_cases [235216,235222,235224,235228,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 17 235216 48
  · wct_piece 17 235222 49
  · wct_piece 17 235224 50
  · wct_piece 17 235228 51
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine264_ready : RoutineReady ⟨264, by decide⟩ routine264 := by
  wct_ready_start 264 8 8
  wct_cases [235229,235235,235237,235241,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 17 235229 52
  · wct_piece 17 235235 53
  · wct_piece 17 235237 54
  · wct_piece 17 235241 55
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine265_ready : RoutineReady ⟨265, by decide⟩ routine265 := by
  wct_ready_start 265 8 9
  wct_cases [235242,235248,235250,235254,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 17 235242 56
  · wct_piece 17 235248 57
  · wct_piece 17 235250 58
  · wct_piece 17 235254 59
  · wct_piece 8 2691 7
  · wct_piece 8 2697 8
  · wct_piece 8 2699 9
  · wct_piece 8 2701 10
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine266_ready : RoutineReady ⟨266, by decide⟩ routine266 := by
  wct_ready_start 266 8 10
  wct_cases [235255,235261,235263,235267,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 17 235255 60
  · wct_piece 17 235261 61
  · wct_piece 17 235263 62
  · wct_piece 17 235267 63
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine267_ready : RoutineReady ⟨267, by decide⟩ routine267 := by
  wct_ready_start 267 8 11
  wct_cases [235268,235274,235277,235283,235287,2751,1411,901,755,761,763,766]
  · wct_piece 18 235268 0
  · wct_piece 18 235274 1
  · wct_piece 18 235277 2
  · wct_piece 18 235283 3
  · wct_piece 18 235287 4
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine268_ready : RoutineReady ⟨268, by decide⟩ routine268 := by
  wct_ready_start 268 8 12
  wct_cases [235288,235294,235297,235303,235307,2766,1426,913,919,805,811,814]
  · wct_piece 18 235288 5
  · wct_piece 18 235294 6
  · wct_piece 18 235297 7
  · wct_piece 18 235303 8
  · wct_piece 18 235307 9
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine269_ready : RoutineReady ⟨269, by decide⟩ routine269 := by
  wct_ready_start 269 8 13
  wct_cases [235308,235314,235317,235323,235327,2781,1441,931,937,940,875,881]
  · wct_piece 18 235308 10
  · wct_piece 18 235314 11
  · wct_piece 18 235317 12
  · wct_piece 18 235323 13
  · wct_piece 18 235327 14
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine270_ready : RoutineReady ⟨270, by decide⟩ routine270 := by
  wct_ready_start 270 8 14
  wct_cases [235328,235334,235337,235343,235347,2796,1456,952,958,960,962,966]
  · wct_piece 18 235328 15
  · wct_piece 18 235334 16
  · wct_piece 18 235337 17
  · wct_piece 18 235343 18
  · wct_piece 18 235347 19
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine271_ready : RoutineReady ⟨271, by decide⟩ routine271 := by
  wct_ready_start 271 8 15
  wct_cases [235348,235354,235357,235363,235367,1468,1474,1478,1120,805,811,814]
  · wct_piece 18 235348 20
  · wct_piece 18 235354 21
  · wct_piece 18 235357 22
  · wct_piece 18 235363 23
  · wct_piece 18 235367 24
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine272_ready : RoutineReady ⟨272, by decide⟩ routine272 := by
  wct_ready_start 272 8 16
  wct_cases [235368,235374,235377,235383,235387,2826,1490,1496,1138,1144,875,881]
  · wct_piece 18 235368 25
  · wct_piece 18 235374 26
  · wct_piece 18 235377 27
  · wct_piece 18 235383 28
  · wct_piece 18 235387 29
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine273_ready : RoutineReady ⟨273, by decide⟩ routine273 := by
  wct_ready_start 273 8 17
  wct_cases [235388,235394,235397,235403,235407,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 18 235388 30
  · wct_piece 18 235394 31
  · wct_piece 18 235397 32
  · wct_piece 18 235403 33
  · wct_piece 18 235407 34
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine274_ready : RoutineReady ⟨274, by decide⟩ routine274 := by
  wct_ready_start 274 8 18
  wct_cases [235408,235414,235417,235423,235427,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 18 235408 35
  · wct_piece 18 235414 36
  · wct_piece 18 235417 37
  · wct_piece 18 235423 38
  · wct_piece 18 235427 39
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine275_ready : RoutineReady ⟨275, by decide⟩ routine275 := by
  wct_ready_start 275 8 19
  wct_cases [235428,235434,235437,235443,235447,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 18 235428 40
  · wct_piece 18 235434 41
  · wct_piece 18 235437 42
  · wct_piece 18 235443 43
  · wct_piece 18 235447 44
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine276_ready : RoutineReady ⟨276, by decide⟩ routine276 := by
  wct_ready_start 276 8 20
  wct_cases [235448,235454,235457,235463,235467,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 18 235448 45
  · wct_piece 18 235454 46
  · wct_piece 18 235457 47
  · wct_piece 18 235463 48
  · wct_piece 18 235467 49
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine277_ready : RoutineReady ⟨277, by decide⟩ routine277 := by
  wct_ready_start 277 8 21
  wct_cases [235468,235474,235477,235483,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 18 235468 50
  · wct_piece 18 235474 51
  · wct_piece 18 235477 52
  · wct_piece 18 235483 53
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine278_ready : RoutineReady ⟨278, by decide⟩ routine278 := by
  wct_ready_start 278 8 22
  wct_cases [235484,235490,235493,235499,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 18 235484 54
  · wct_piece 18 235490 55
  · wct_piece 18 235493 56
  · wct_piece 18 235499 57
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine279_ready : RoutineReady ⟨279, by decide⟩ routine279 := by
  wct_ready_start 279 8 23
  wct_cases [235500,235506,235509,235515,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 18 235500 58
  · wct_piece 18 235506 59
  · wct_piece 18 235509 60
  · wct_piece 18 235515 61
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine280_ready : RoutineReady ⟨280, by decide⟩ routine280 := by
  wct_ready_start 280 8 24
  wct_cases [235516,235522,235525,235531,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 18 235516 62
  · wct_piece 18 235522 63
  · wct_piece 19 235525 0
  · wct_piece 19 235531 1
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine281_ready : RoutineReady ⟨281, by decide⟩ routine281 := by
  wct_ready_start 281 8 25
  wct_cases [235532,235538,235541,235547,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 19 235532 2
  · wct_piece 19 235538 3
  · wct_piece 19 235541 4
  · wct_piece 19 235547 5
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine282_ready : RoutineReady ⟨282, by decide⟩ routine282 := by
  wct_ready_start 282 8 26
  wct_cases [235548,235554,235557,235563,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 19 235548 6
  · wct_piece 19 235554 7
  · wct_piece 19 235557 8
  · wct_piece 19 235563 9
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine283_ready : RoutineReady ⟨283, by decide⟩ routine283 := by
  wct_ready_start 283 8 27
  wct_cases [235564,235570,235573,235579,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 19 235564 10
  · wct_piece 19 235570 11
  · wct_piece 19 235573 12
  · wct_piece 19 235579 13
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine284_ready : RoutineReady ⟨284, by decide⟩ routine284 := by
  wct_ready_start 284 8 28
  wct_cases [235580,235586,235589,235595,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 19 235580 14
  · wct_piece 19 235586 15
  · wct_piece 19 235589 16
  · wct_piece 19 235595 17
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine285_ready : RoutineReady ⟨285, by decide⟩ routine285 := by
  wct_ready_start 285 8 29
  wct_cases [235596,235602,235605,235611,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 19 235596 18
  · wct_piece 19 235602 19
  · wct_piece 19 235605 20
  · wct_piece 19 235611 21
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine286_ready : RoutineReady ⟨286, by decide⟩ routine286 := by
  wct_ready_start 286 8 30
  wct_cases [235612,235618,235621,235627,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 19 235612 22
  · wct_piece 19 235618 23
  · wct_piece 19 235621 24
  · wct_piece 19 235627 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine287_ready : RoutineReady ⟨287, by decide⟩ routine287 := by
  wct_ready_start 287 8 31
  wct_cases [235628,235634,235637,235643,235645,235649,4391,2078,1120,805,811,814]
  · wct_piece 19 235628 26
  · wct_piece 19 235634 27
  · wct_piece 19 235637 28
  · wct_piece 19 235643 29
  · wct_piece 19 235645 30
  · wct_piece 19 235649 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
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
