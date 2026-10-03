import SigGolfCandidate.W9Machine.WctRoutineCheck18
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

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
  wct_cases [239950,239956,239958,4931,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 39 239950 5
  · wct_piece 39 239956 6
  · wct_piece 39 239958 7
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
theorem routine577_ready : RoutineReady ⟨577, by decide⟩ routine577 := by
  wct_ready_start 577 18 1
  wct_cases [239959,239965,239967,4944,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 39 239959 8
  · wct_piece 39 239965 9
  · wct_piece 39 239967 10
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
theorem routine578_ready : RoutineReady ⟨578, by decide⟩ routine578 := by
  wct_ready_start 578 18 2
  wct_cases [239968,239974,239976,4957,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 39 239968 11
  · wct_piece 39 239974 12
  · wct_piece 39 239976 13
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
theorem routine579_ready : RoutineReady ⟨579, by decide⟩ routine579 := by
  wct_ready_start 579 18 3
  wct_cases [239977,239983,239985,4970,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 39 239977 14
  · wct_piece 39 239983 15
  · wct_piece 39 239985 16
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
theorem routine580_ready : RoutineReady ⟨580, by decide⟩ routine580 := by
  wct_ready_start 580 18 4
  wct_cases [239986,239992,239994,4983,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 39 239986 17
  · wct_piece 39 239992 18
  · wct_piece 39 239994 19
  · wct_piece 17 4983 55
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine581_ready : RoutineReady ⟨581, by decide⟩ routine581 := by
  wct_ready_start 581 18 5
  wct_cases [239995,240001,240003,4996,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 39 239995 20
  · wct_piece 39 240001 21
  · wct_piece 39 240003 22
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
theorem routine582_ready : RoutineReady ⟨582, by decide⟩ routine582 := by
  wct_ready_start 582 18 6
  wct_cases [240004,240010,240012,5009,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 39 240004 23
  · wct_piece 39 240010 24
  · wct_piece 39 240012 25
  · wct_piece 17 5009 63
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine583_ready : RoutineReady ⟨583, by decide⟩ routine583 := by
  wct_ready_start 583 18 7
  wct_cases [240013,240019,240021,5019,5025,5029,2751,1411,901,755,761,763,766]
  · wct_piece 39 240013 26
  · wct_piece 39 240019 27
  · wct_piece 39 240021 28
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
theorem routine584_ready : RoutineReady ⟨584, by decide⟩ routine584 := by
  wct_ready_start 584 18 8
  wct_cases [240022,240028,240030,5039,5045,5049,2766,1426,913,919,805,811,814]
  · wct_piece 39 240022 29
  · wct_piece 39 240028 30
  · wct_piece 39 240030 31
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
theorem routine585_ready : RoutineReady ⟨585, by decide⟩ routine585 := by
  wct_ready_start 585 18 9
  wct_cases [240031,240037,240039,5059,5065,5069,2781,1441,931,937,940,875,881]
  · wct_piece 39 240031 32
  · wct_piece 39 240037 33
  · wct_piece 39 240039 34
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
theorem routine586_ready : RoutineReady ⟨586, by decide⟩ routine586 := by
  wct_ready_start 586 18 10
  wct_cases [240040,240046,240048,5079,5085,5089,2796,1456,952,958,960,962,966]
  · wct_piece 39 240040 35
  · wct_piece 39 240046 36
  · wct_piece 39 240048 37
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
theorem routine587_ready : RoutineReady ⟨587, by decide⟩ routine587 := by
  wct_ready_start 587 18 11
  wct_cases [240049,240055,240057,5099,5105,5109,1468,1474,1478,1120,805,811,814]
  · wct_piece 39 240049 38
  · wct_piece 39 240055 39
  · wct_piece 39 240057 40
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
theorem routine588_ready : RoutineReady ⟨588, by decide⟩ routine588 := by
  wct_ready_start 588 18 12
  wct_cases [240058,240064,240066,5119,5125,5129,2826,1490,1496,1138,1144,875,881]
  · wct_piece 39 240058 41
  · wct_piece 39 240064 42
  · wct_piece 39 240066 43
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
theorem routine589_ready : RoutineReady ⟨589, by decide⟩ routine589 := by
  wct_ready_start 589 18 13
  wct_cases [240067,240073,240075,5139,5145,5149,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 39 240067 44
  · wct_piece 39 240073 45
  · wct_piece 39 240075 46
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
theorem routine590_ready : RoutineReady ⟨590, by decide⟩ routine590 := by
  wct_ready_start 590 18 14
  wct_cases [240076,240082,240084,5159,5165,5169,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 39 240076 47
  · wct_piece 39 240082 48
  · wct_piece 39 240084 49
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
theorem routine591_ready : RoutineReady ⟨591, by decide⟩ routine591 := by
  wct_ready_start 591 18 15
  wct_cases [240085,240091,240093,5179,5185,5189,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 39 240085 50
  · wct_piece 39 240091 51
  · wct_piece 39 240093 52
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
theorem routine592_ready : RoutineReady ⟨592, by decide⟩ routine592 := by
  wct_ready_start 592 18 16
  wct_cases [240094,240100,240102,5199,5205,5209,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 39 240094 53
  · wct_piece 39 240100 54
  · wct_piece 39 240102 55
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
theorem routine593_ready : RoutineReady ⟨593, by decide⟩ routine593 := by
  wct_ready_start 593 18 17
  wct_cases [240103,240109,240111,5219,5225,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 39 240103 56
  · wct_piece 39 240109 57
  · wct_piece 39 240111 58
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
theorem routine594_ready : RoutineReady ⟨594, by decide⟩ routine594 := by
  wct_ready_start 594 18 18
  wct_cases [240112,240118,240120,5235,5241,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 39 240112 59
  · wct_piece 39 240118 60
  · wct_piece 39 240120 61
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
theorem routine595_ready : RoutineReady ⟨595, by decide⟩ routine595 := by
  wct_ready_start 595 18 19
  wct_cases [240121,240127,240129,5251,5257,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 39 240121 62
  · wct_piece 39 240127 63
  · wct_piece 40 240129 0
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
theorem routine596_ready : RoutineReady ⟨596, by decide⟩ routine596 := by
  wct_ready_start 596 18 20
  wct_cases [240130,240136,240138,5267,5273,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 40 240130 1
  · wct_piece 40 240136 2
  · wct_piece 40 240138 3
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
theorem routine597_ready : RoutineReady ⟨597, by decide⟩ routine597 := by
  wct_ready_start 597 18 21
  wct_cases [240139,240145,240147,5283,5289,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 40 240139 4
  · wct_piece 40 240145 5
  · wct_piece 40 240147 6
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
theorem routine598_ready : RoutineReady ⟨598, by decide⟩ routine598 := by
  wct_ready_start 598 18 22
  wct_cases [240148,240154,240156,5299,5305,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 40 240148 7
  · wct_piece 40 240154 8
  · wct_piece 40 240156 9
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
theorem routine599_ready : RoutineReady ⟨599, by decide⟩ routine599 := by
  wct_ready_start 599 18 23
  wct_cases [240157,240163,240165,5315,5321,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 40 240157 10
  · wct_piece 40 240163 11
  · wct_piece 40 240165 12
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
theorem routine600_ready : RoutineReady ⟨600, by decide⟩ routine600 := by
  wct_ready_start 600 18 24
  wct_cases [240166,240172,240174,5331,5337,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 40 240166 13
  · wct_piece 40 240172 14
  · wct_piece 40 240174 15
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
theorem routine601_ready : RoutineReady ⟨601, by decide⟩ routine601 := by
  wct_ready_start 601 18 25
  wct_cases [240175,240181,240183,5347,5353,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 40 240175 16
  · wct_piece 40 240181 17
  · wct_piece 40 240183 18
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
theorem routine602_ready : RoutineReady ⟨602, by decide⟩ routine602 := by
  wct_ready_start 602 18 26
  wct_cases [240184,240190,240192,5363,5369,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 40 240184 19
  · wct_piece 40 240190 20
  · wct_piece 40 240192 21
  · wct_piece 19 5363 24
  · wct_piece 19 5369 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine603_ready : RoutineReady ⟨603, by decide⟩ routine603 := by
  wct_ready_start 603 18 27
  wct_cases [240193,240199,240201,5379,5385,5387,5391,4391,2078,1120,805,811,814]
  · wct_piece 40 240193 22
  · wct_piece 40 240199 23
  · wct_piece 40 240201 24
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
theorem routine604_ready : RoutineReady ⟨604, by decide⟩ routine604 := by
  wct_ready_start 604 18 28
  wct_cases [240202,240208,240210,235017,235023,235025,235029,4412,2099,1138,1144,875,881]
  · wct_piece 40 240202 25
  · wct_piece 40 240208 26
  · wct_piece 40 240210 27
  · wct_piece 19 235017 34
  · wct_piece 19 235023 35
  · wct_piece 19 235025 36
  · wct_piece 19 235029 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine605_ready : RoutineReady ⟨605, by decide⟩ routine605 := by
  wct_ready_start 605 18 29
  wct_cases [240211,240217,240219,235039,235045,235047,235051,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 40 240211 28
  · wct_piece 40 240217 29
  · wct_piece 40 240219 30
  · wct_piece 19 235039 40
  · wct_piece 19 235045 41
  · wct_piece 19 235047 42
  · wct_piece 19 235051 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine606_ready : RoutineReady ⟨606, by decide⟩ routine606 := by
  wct_ready_start 606 18 30
  wct_cases [240220,240226,240228,235061,235067,235069,235073,4454,2138,2144,2148,1365,875,881]
  · wct_piece 40 240220 31
  · wct_piece 40 240226 32
  · wct_piece 40 240228 33
  · wct_piece 19 235061 46
  · wct_piece 19 235067 47
  · wct_piece 19 235069 48
  · wct_piece 19 235073 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine607_ready : RoutineReady ⟨607, by decide⟩ routine607 := by
  wct_ready_start 607 18 31
  wct_cases [240229,240235,240237,235083,235089,235091,235095,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 40 240229 34
  · wct_piece 40 240235 35
  · wct_piece 40 240237 36
  · wct_piece 19 235083 52
  · wct_piece 19 235089 53
  · wct_piece 19 235091 54
  · wct_piece 19 235095 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
end W9Machine.Chain
end
