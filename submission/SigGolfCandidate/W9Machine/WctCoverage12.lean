import SigGolfCandidate.W9Machine.WctRoutineCheck12
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch12_checked :
    (routineBatch12.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch12_checked :
    (routineBatch12.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine384_ready : RoutineReady ⟨384, by decide⟩ routine384 := by
  wct_ready_start 384 12 0
  wct_cases [236948,236954,236960,236964,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 25 236948 24
  · wct_piece 25 236954 25
  · wct_piece 25 236960 26
  · wct_piece 25 236964 27
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine385_ready : RoutineReady ⟨385, by decide⟩ routine385 := by
  wct_ready_start 385 12 1
  wct_cases [236965,236971,236977,236981,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 25 236965 28
  · wct_piece 25 236971 29
  · wct_piece 25 236977 30
  · wct_piece 25 236981 31
  · wct_piece 6 2332 40
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine386_ready : RoutineReady ⟨386, by decide⟩ routine386 := by
  wct_ready_start 386 12 2
  wct_cases [236982,236988,3746,3752,3756,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 25 236982 32
  · wct_piece 25 236988 33
  · wct_piece 12 3746 42
  · wct_piece 12 3752 43
  · wct_piece 12 3756 44
  · wct_piece 6 2345 44
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine387_ready : RoutineReady ⟨387, by decide⟩ routine387 := by
  wct_ready_start 387 12 3
  wct_cases [236989,236995,3763,3769,3773,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 25 236989 34
  · wct_piece 25 236995 35
  · wct_piece 12 3763 46
  · wct_piece 12 3769 47
  · wct_piece 12 3773 48
  · wct_piece 6 2358 48
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine388_ready : RoutineReady ⟨388, by decide⟩ routine388 := by
  wct_ready_start 388 12 4
  wct_cases [236996,237002,3780,3786,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 25 236996 36
  · wct_piece 25 237002 37
  · wct_piece 12 3780 50
  · wct_piece 12 3786 51
  · wct_piece 6 2368 51
  · wct_piece 6 2374 52
  · wct_piece 6 2378 53
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine389_ready : RoutineReady ⟨389, by decide⟩ routine389 := by
  wct_ready_start 389 12 5
  wct_cases [237003,237009,237015,2388,2394,2398,1426,913,919,805,811,814]
  · wct_piece 25 237003 38
  · wct_piece 25 237009 39
  · wct_piece 25 237015 40
  · wct_piece 6 2388 56
  · wct_piece 6 2394 57
  · wct_piece 6 2398 58
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine390_ready : RoutineReady ⟨390, by decide⟩ routine390 := by
  wct_ready_start 390 12 6
  wct_cases [237016,237022,237028,2408,2414,2418,1441,931,937,940,875,881]
  · wct_piece 25 237016 41
  · wct_piece 25 237022 42
  · wct_piece 25 237028 43
  · wct_piece 6 2408 61
  · wct_piece 6 2414 62
  · wct_piece 6 2418 63
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine391_ready : RoutineReady ⟨391, by decide⟩ routine391 := by
  wct_ready_start 391 12 7
  wct_cases [237029,237035,3819,3825,2428,2434,2438,1456,952,958,960,962,966]
  · wct_piece 25 237029 44
  · wct_piece 25 237035 45
  · wct_piece 12 3819 59
  · wct_piece 12 3825 60
  · wct_piece 7 2428 2
  · wct_piece 7 2434 3
  · wct_piece 7 2438 4
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine392_ready : RoutineReady ⟨392, by decide⟩ routine392 := by
  wct_ready_start 392 12 8
  wct_cases [237036,237042,237048,2448,2454,1468,1474,1478,1120,805,811,814]
  · wct_piece 25 237036 46
  · wct_piece 25 237042 47
  · wct_piece 25 237048 48
  · wct_piece 7 2448 7
  · wct_piece 7 2454 8
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine393_ready : RoutineReady ⟨393, by decide⟩ routine393 := by
  wct_ready_start 393 12 9
  wct_cases [237049,237055,3845,3851,2464,2470,1490,1496,1138,1144,875,881]
  · wct_piece 25 237049 49
  · wct_piece 25 237055 50
  · wct_piece 13 3845 1
  · wct_piece 13 3851 2
  · wct_piece 7 2464 11
  · wct_piece 7 2470 12
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine394_ready : RoutineReady ⟨394, by decide⟩ routine394 := by
  wct_ready_start 394 12 10
  wct_cases [237056,237062,3858,3864,2480,2486,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 25 237056 51
  · wct_piece 25 237062 52
  · wct_piece 13 3858 4
  · wct_piece 13 3864 5
  · wct_piece 7 2480 15
  · wct_piece 7 2486 16
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine395_ready : RoutineReady ⟨395, by decide⟩ routine395 := by
  wct_ready_start 395 12 11
  wct_cases [237063,237069,3871,3877,2496,2502,1526,1532,1534,1538,1365,875,881]
  · wct_piece 25 237063 53
  · wct_piece 25 237069 54
  · wct_piece 13 3871 7
  · wct_piece 13 3877 8
  · wct_piece 7 2496 19
  · wct_piece 7 2502 20
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine396_ready : RoutineReady ⟨396, by decide⟩ routine396 := by
  wct_ready_start 396 12 12
  wct_cases [237070,237076,237082,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 25 237070 55
  · wct_piece 25 237076 56
  · wct_piece 25 237082 57
  · wct_piece 7 2512 23
  · wct_piece 7 2518 24
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine397_ready : RoutineReady ⟨397, by decide⟩ routine397 := by
  wct_ready_start 397 12 13
  wct_cases [237083,237089,3897,3903,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 25 237083 58
  · wct_piece 25 237089 59
  · wct_piece 13 3897 13
  · wct_piece 13 3903 14
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine398_ready : RoutineReady ⟨398, by decide⟩ routine398 := by
  wct_ready_start 398 12 14
  wct_cases [237090,237096,3910,3916,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 25 237090 60
  · wct_piece 25 237096 61
  · wct_piece 13 3910 16
  · wct_piece 13 3916 17
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine399_ready : RoutineReady ⟨399, by decide⟩ routine399 := by
  wct_ready_start 399 12 15
  wct_cases [237097,237103,3923,3929,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 25 237097 62
  · wct_piece 25 237103 63
  · wct_piece 13 3923 19
  · wct_piece 13 3929 20
  · wct_piece 7 2566 37
  · wct_piece 7 2572 38
  · wct_piece 7 2574 39
  · wct_piece 7 2578 40
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine400_ready : RoutineReady ⟨400, by decide⟩ routine400 := by
  wct_ready_start 400 12 16
  wct_cases [237104,237110,3936,3942,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 26 237104 0
  · wct_piece 26 237110 1
  · wct_piece 13 3936 22
  · wct_piece 13 3942 23
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
theorem routine401_ready : RoutineReady ⟨401, by decide⟩ routine401 := by
  wct_ready_start 401 12 17
  wct_cases [237111,237117,237123,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 26 237111 2
  · wct_piece 26 237117 3
  · wct_piece 26 237123 4
  · wct_piece 7 2610 49
  · wct_piece 7 2616 50
  · wct_piece 7 2619 51
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine402_ready : RoutineReady ⟨402, by decide⟩ routine402 := by
  wct_ready_start 402 12 18
  wct_cases [237124,237130,237136,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 26 237124 5
  · wct_piece 26 237130 6
  · wct_piece 26 237136 7
  · wct_piece 7 2629 54
  · wct_piece 7 2635 55
  · wct_piece 7 2638 56
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine403_ready : RoutineReady ⟨403, by decide⟩ routine403 := by
  wct_ready_start 403 12 19
  wct_cases [237137,237143,3975,3981,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 26 237137 8
  · wct_piece 26 237143 9
  · wct_piece 13 3975 31
  · wct_piece 13 3981 32
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine404_ready : RoutineReady ⟨404, by decide⟩ routine404 := by
  wct_ready_start 404 12 20
  wct_cases [237144,237150,3988,3994,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 26 237144 10
  · wct_piece 26 237150 11
  · wct_piece 13 3988 34
  · wct_piece 13 3994 35
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine405_ready : RoutineReady ⟨405, by decide⟩ routine405 := by
  wct_ready_start 405 12 21
  wct_cases [237151,237157,4001,4007,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 26 237151 12
  · wct_piece 26 237157 13
  · wct_piece 13 4001 37
  · wct_piece 13 4007 38
  · wct_piece 8 2691 7
  · wct_piece 8 2697 8
  · wct_piece 8 2699 9
  · wct_piece 8 2701 10
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine406_ready : RoutineReady ⟨406, by decide⟩ routine406 := by
  wct_ready_start 406 12 22
  wct_cases [237158,237164,4014,4020,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 26 237158 14
  · wct_piece 26 237164 15
  · wct_piece 13 4014 40
  · wct_piece 13 4020 41
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine407_ready : RoutineReady ⟨407, by decide⟩ routine407 := by
  wct_ready_start 407 12 23
  wct_cases [237165,237171,4027,4033,4035,4039,2751,1411,901,755,761,763,766]
  · wct_piece 26 237165 16
  · wct_piece 26 237171 17
  · wct_piece 13 4027 43
  · wct_piece 13 4033 44
  · wct_piece 13 4035 45
  · wct_piece 13 4039 46
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine408_ready : RoutineReady ⟨408, by decide⟩ routine408 := by
  wct_ready_start 408 12 24
  wct_cases [237172,237178,4046,4052,4054,4058,2766,1426,913,919,805,811,814]
  · wct_piece 26 237172 18
  · wct_piece 26 237178 19
  · wct_piece 13 4046 48
  · wct_piece 13 4052 49
  · wct_piece 13 4054 50
  · wct_piece 13 4058 51
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine409_ready : RoutineReady ⟨409, by decide⟩ routine409 := by
  wct_ready_start 409 12 25
  wct_cases [237179,237185,4065,4071,4073,4077,2781,1441,931,937,940,875,881]
  · wct_piece 26 237179 20
  · wct_piece 26 237185 21
  · wct_piece 13 4065 53
  · wct_piece 13 4071 54
  · wct_piece 13 4073 55
  · wct_piece 13 4077 56
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine410_ready : RoutineReady ⟨410, by decide⟩ routine410 := by
  wct_ready_start 410 12 26
  wct_cases [237186,237192,4084,4090,4092,4096,2796,1456,952,958,960,962,966]
  · wct_piece 26 237186 22
  · wct_piece 26 237192 23
  · wct_piece 13 4084 58
  · wct_piece 13 4090 59
  · wct_piece 13 4092 60
  · wct_piece 13 4096 61
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine411_ready : RoutineReady ⟨411, by decide⟩ routine411 := by
  wct_ready_start 411 12 27
  wct_cases [237193,237199,237205,237207,237211,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 26 237193 24
  · wct_piece 26 237199 25
  · wct_piece 26 237205 26
  · wct_piece 26 237207 27
  · wct_piece 26 237211 28
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine412_ready : RoutineReady ⟨412, by decide⟩ routine412 := by
  wct_ready_start 412 12 28
  wct_cases [237212,237218,4122,4128,4130,4134,2826,1490,1496,1138,1144,875,881]
  · wct_piece 26 237212 29
  · wct_piece 26 237218 30
  · wct_piece 14 4122 4
  · wct_piece 14 4128 5
  · wct_piece 14 4130 6
  · wct_piece 14 4134 7
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine413_ready : RoutineReady ⟨413, by decide⟩ routine413 := by
  wct_ready_start 413 12 29
  wct_cases [237219,237225,4141,4147,4149,4153,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 26 237219 31
  · wct_piece 26 237225 32
  · wct_piece 14 4141 9
  · wct_piece 14 4147 10
  · wct_piece 14 4149 11
  · wct_piece 14 4153 12
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine414_ready : RoutineReady ⟨414, by decide⟩ routine414 := by
  wct_ready_start 414 12 30
  wct_cases [237226,237232,4160,4166,4168,4172,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 26 237226 33
  · wct_piece 26 237232 34
  · wct_piece 14 4160 14
  · wct_piece 14 4166 15
  · wct_piece 14 4168 16
  · wct_piece 14 4172 17
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine415_ready : RoutineReady ⟨415, by decide⟩ routine415 := by
  wct_ready_start 415 12 31
  wct_cases [237233,237239,237245,237247,237251,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 26 237233 35
  · wct_piece 26 237239 36
  · wct_piece 26 237245 37
  · wct_piece 26 237247 38
  · wct_piece 26 237251 39
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage12 (rank : Fin 728) (hlo : 384 ≤ rank.val) (hhi : rank.val < 416) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 384 ≤ n at hlo
  change n < 416 at hhi
  interval_cases n
  · exact ⟨routine384, routine384_ready⟩
  · exact ⟨routine385, routine385_ready⟩
  · exact ⟨routine386, routine386_ready⟩
  · exact ⟨routine387, routine387_ready⟩
  · exact ⟨routine388, routine388_ready⟩
  · exact ⟨routine389, routine389_ready⟩
  · exact ⟨routine390, routine390_ready⟩
  · exact ⟨routine391, routine391_ready⟩
  · exact ⟨routine392, routine392_ready⟩
  · exact ⟨routine393, routine393_ready⟩
  · exact ⟨routine394, routine394_ready⟩
  · exact ⟨routine395, routine395_ready⟩
  · exact ⟨routine396, routine396_ready⟩
  · exact ⟨routine397, routine397_ready⟩
  · exact ⟨routine398, routine398_ready⟩
  · exact ⟨routine399, routine399_ready⟩
  · exact ⟨routine400, routine400_ready⟩
  · exact ⟨routine401, routine401_ready⟩
  · exact ⟨routine402, routine402_ready⟩
  · exact ⟨routine403, routine403_ready⟩
  · exact ⟨routine404, routine404_ready⟩
  · exact ⟨routine405, routine405_ready⟩
  · exact ⟨routine406, routine406_ready⟩
  · exact ⟨routine407, routine407_ready⟩
  · exact ⟨routine408, routine408_ready⟩
  · exact ⟨routine409, routine409_ready⟩
  · exact ⟨routine410, routine410_ready⟩
  · exact ⟨routine411, routine411_ready⟩
  · exact ⟨routine412, routine412_ready⟩
  · exact ⟨routine413, routine413_ready⟩
  · exact ⟨routine414, routine414_ready⟩
  · exact ⟨routine415, routine415_ready⟩
end W9Machine.Chain
end
