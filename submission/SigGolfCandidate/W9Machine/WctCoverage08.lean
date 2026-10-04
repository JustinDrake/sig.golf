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
  wct_cases [4867,4873,4875,4879,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 17 4867 20
  · wct_piece 17 4873 21
  · wct_piece 17 4875 22
  · wct_piece 17 4879 23
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
  wct_cases [4880,4886,4888,4892,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 17 4880 24
  · wct_piece 17 4886 25
  · wct_piece 17 4888 26
  · wct_piece 17 4892 27
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
  wct_cases [4893,4899,4901,4905,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 17 4893 28
  · wct_piece 17 4899 29
  · wct_piece 17 4901 30
  · wct_piece 17 4905 31
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
  wct_cases [4906,4912,4914,4918,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 17 4906 32
  · wct_piece 17 4912 33
  · wct_piece 17 4914 34
  · wct_piece 17 4918 35
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
  wct_cases [4919,4925,4927,4931,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 17 4919 36
  · wct_piece 17 4925 37
  · wct_piece 17 4927 38
  · wct_piece 17 4931 39
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
  wct_cases [4932,4938,4940,4944,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 17 4932 40
  · wct_piece 17 4938 41
  · wct_piece 17 4940 42
  · wct_piece 17 4944 43
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
  wct_cases [4945,4951,4953,4957,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 17 4945 44
  · wct_piece 17 4951 45
  · wct_piece 17 4953 46
  · wct_piece 17 4957 47
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
  wct_cases [4958,4964,4966,4970,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 17 4958 48
  · wct_piece 17 4964 49
  · wct_piece 17 4966 50
  · wct_piece 17 4970 51
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
  wct_cases [4971,4977,4979,4983,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 17 4971 52
  · wct_piece 17 4977 53
  · wct_piece 17 4979 54
  · wct_piece 17 4983 55
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
  wct_cases [4984,4990,4992,4996,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 17 4984 56
  · wct_piece 17 4990 57
  · wct_piece 17 4992 58
  · wct_piece 17 4996 59
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
  wct_cases [4997,5003,5005,5009,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 17 4997 60
  · wct_piece 17 5003 61
  · wct_piece 17 5005 62
  · wct_piece 17 5009 63
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
  wct_cases [5010,5016,5019,5025,5029,2751,1411,901,755,761,763,766]
  · wct_piece 18 5010 0
  · wct_piece 18 5016 1
  · wct_piece 18 5019 2
  · wct_piece 18 5025 3
  · wct_piece 18 5029 4
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine268_ready : RoutineReady ⟨268, by decide⟩ routine268 := by
  wct_ready_start 268 8 12
  wct_cases [5030,5036,5039,5045,5049,2766,1426,913,919,805,811,814]
  · wct_piece 18 5030 5
  · wct_piece 18 5036 6
  · wct_piece 18 5039 7
  · wct_piece 18 5045 8
  · wct_piece 18 5049 9
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine269_ready : RoutineReady ⟨269, by decide⟩ routine269 := by
  wct_ready_start 269 8 13
  wct_cases [5050,5056,5059,5065,5069,2781,1441,931,937,940,875,881]
  · wct_piece 18 5050 10
  · wct_piece 18 5056 11
  · wct_piece 18 5059 12
  · wct_piece 18 5065 13
  · wct_piece 18 5069 14
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine270_ready : RoutineReady ⟨270, by decide⟩ routine270 := by
  wct_ready_start 270 8 14
  wct_cases [5070,5076,5079,5085,5089,2796,1456,952,958,960,962,966]
  · wct_piece 18 5070 15
  · wct_piece 18 5076 16
  · wct_piece 18 5079 17
  · wct_piece 18 5085 18
  · wct_piece 18 5089 19
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine271_ready : RoutineReady ⟨271, by decide⟩ routine271 := by
  wct_ready_start 271 8 15
  wct_cases [5090,5096,5099,5105,5109,1468,1474,1478,1120,805,811,814]
  · wct_piece 18 5090 20
  · wct_piece 18 5096 21
  · wct_piece 18 5099 22
  · wct_piece 18 5105 23
  · wct_piece 18 5109 24
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine272_ready : RoutineReady ⟨272, by decide⟩ routine272 := by
  wct_ready_start 272 8 16
  wct_cases [5110,5116,5119,5125,5129,2826,1490,1496,1138,1144,875,881]
  · wct_piece 18 5110 25
  · wct_piece 18 5116 26
  · wct_piece 18 5119 27
  · wct_piece 18 5125 28
  · wct_piece 18 5129 29
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine273_ready : RoutineReady ⟨273, by decide⟩ routine273 := by
  wct_ready_start 273 8 17
  wct_cases [5130,5136,5139,5145,5149,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 18 5130 30
  · wct_piece 18 5136 31
  · wct_piece 18 5139 32
  · wct_piece 18 5145 33
  · wct_piece 18 5149 34
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
  wct_cases [5150,5156,5159,5165,5169,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 18 5150 35
  · wct_piece 18 5156 36
  · wct_piece 18 5159 37
  · wct_piece 18 5165 38
  · wct_piece 18 5169 39
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
  wct_cases [5170,5176,5179,5185,5189,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 18 5170 40
  · wct_piece 18 5176 41
  · wct_piece 18 5179 42
  · wct_piece 18 5185 43
  · wct_piece 18 5189 44
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine276_ready : RoutineReady ⟨276, by decide⟩ routine276 := by
  wct_ready_start 276 8 20
  wct_cases [5190,5196,5199,5205,5209,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 18 5190 45
  · wct_piece 18 5196 46
  · wct_piece 18 5199 47
  · wct_piece 18 5205 48
  · wct_piece 18 5209 49
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine277_ready : RoutineReady ⟨277, by decide⟩ routine277 := by
  wct_ready_start 277 8 21
  wct_cases [5210,5216,5219,5225,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 18 5210 50
  · wct_piece 18 5216 51
  · wct_piece 18 5219 52
  · wct_piece 18 5225 53
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
  wct_cases [5226,5232,5235,5241,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 18 5226 54
  · wct_piece 18 5232 55
  · wct_piece 18 5235 56
  · wct_piece 18 5241 57
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
  wct_cases [5242,5248,5251,5257,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 18 5242 58
  · wct_piece 18 5248 59
  · wct_piece 18 5251 60
  · wct_piece 18 5257 61
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
  wct_cases [5258,5264,5267,5273,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 18 5258 62
  · wct_piece 18 5264 63
  · wct_piece 19 5267 0
  · wct_piece 19 5273 1
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
  wct_cases [5274,5280,5283,5289,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 19 5274 2
  · wct_piece 19 5280 3
  · wct_piece 19 5283 4
  · wct_piece 19 5289 5
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
  wct_cases [5290,5296,5299,5305,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 19 5290 6
  · wct_piece 19 5296 7
  · wct_piece 19 5299 8
  · wct_piece 19 5305 9
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
  wct_cases [5306,5312,5315,5321,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 19 5306 10
  · wct_piece 19 5312 11
  · wct_piece 19 5315 12
  · wct_piece 19 5321 13
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
  wct_cases [5322,5328,5331,5337,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 19 5322 14
  · wct_piece 19 5328 15
  · wct_piece 19 5331 16
  · wct_piece 19 5337 17
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
  wct_cases [5338,5344,5347,5353,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 19 5338 18
  · wct_piece 19 5344 19
  · wct_piece 19 5347 20
  · wct_piece 19 5353 21
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
  wct_cases [5354,5360,5363,5369,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 19 5354 22
  · wct_piece 19 5360 23
  · wct_piece 19 5363 24
  · wct_piece 19 5369 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine287_ready : RoutineReady ⟨287, by decide⟩ routine287 := by
  wct_ready_start 287 8 31
  wct_cases [5370,5376,5379,5385,5387,5391,4391,2078,1120,805,811,814]
  · wct_piece 19 5370 26
  · wct_piece 19 5376 27
  · wct_piece 19 5379 28
  · wct_piece 19 5385 29
  · wct_piece 19 5387 30
  · wct_piece 19 5391 31
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
