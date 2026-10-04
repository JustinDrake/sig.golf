import SigGolfCandidate.W9Machine.WctRoutineCheck05
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch05_checked :
    (routineBatch05.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch05_checked :
    (routineBatch05.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine160_ready : RoutineReady ⟨160, by decide⟩ routine160 := by
  wct_ready_start 160 5 0
  wct_cases [3387,3393,3397,1911,1917,1919,1923,1426,913,919,805,811,814]
  · wct_piece 11 3387 16
  · wct_piece 11 3393 17
  · wct_piece 11 3397 18
  · wct_piece 4 1911 52
  · wct_piece 4 1917 53
  · wct_piece 4 1919 54
  · wct_piece 4 1923 55
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine161_ready : RoutineReady ⟨161, by decide⟩ routine161 := by
  wct_ready_start 161 5 1
  wct_cases [3398,3404,3408,1930,1936,1938,1942,1441,931,937,940,875,881]
  · wct_piece 11 3398 19
  · wct_piece 11 3404 20
  · wct_piece 11 3408 21
  · wct_piece 4 1930 57
  · wct_piece 4 1936 58
  · wct_piece 4 1938 59
  · wct_piece 4 1942 60
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine162_ready : RoutineReady ⟨162, by decide⟩ routine162 := by
  wct_ready_start 162 5 2
  wct_cases [3409,3415,3419,1949,1955,1957,1961,1456,952,958,960,962,966]
  · wct_piece 11 3409 22
  · wct_piece 11 3415 23
  · wct_piece 11 3419 24
  · wct_piece 4 1949 62
  · wct_piece 4 1955 63
  · wct_piece 5 1957 0
  · wct_piece 5 1961 1
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine163_ready : RoutineReady ⟨163, by decide⟩ routine163 := by
  wct_ready_start 163 5 3
  wct_cases [3420,3426,3430,3436,3439,1468,1474,1478,1120,805,811,814]
  · wct_piece 11 3420 25
  · wct_piece 11 3426 26
  · wct_piece 11 3430 27
  · wct_piece 11 3436 28
  · wct_piece 11 3439 29
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine164_ready : RoutineReady ⟨164, by decide⟩ routine164 := by
  wct_ready_start 164 5 4
  wct_cases [3440,3446,3450,1984,1990,1993,1490,1496,1138,1144,875,881]
  · wct_piece 11 3440 30
  · wct_piece 11 3446 31
  · wct_piece 11 3450 32
  · wct_piece 5 1984 7
  · wct_piece 5 1990 8
  · wct_piece 5 1993 9
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine165_ready : RoutineReady ⟨165, by decide⟩ routine165 := by
  wct_ready_start 165 5 5
  wct_cases [3451,3457,3461,2000,2006,2009,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 11 3451 33
  · wct_piece 11 3457 34
  · wct_piece 11 3461 35
  · wct_piece 5 2000 11
  · wct_piece 5 2006 12
  · wct_piece 5 2009 13
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine166_ready : RoutineReady ⟨166, by decide⟩ routine166 := by
  wct_ready_start 166 5 6
  wct_cases [3462,3468,3472,2016,2022,2025,1526,1532,1534,1538,1365,875,881]
  · wct_piece 11 3462 36
  · wct_piece 11 3468 37
  · wct_piece 11 3472 38
  · wct_piece 5 2016 15
  · wct_piece 5 2022 16
  · wct_piece 5 2025 17
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine167_ready : RoutineReady ⟨167, by decide⟩ routine167 := by
  wct_ready_start 167 5 7
  wct_cases [3473,3479,3483,3489,3492,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 11 3473 39
  · wct_piece 11 3479 40
  · wct_piece 11 3483 41
  · wct_piece 11 3489 42
  · wct_piece 11 3492 43
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine168_ready : RoutineReady ⟨168, by decide⟩ routine168 := by
  wct_ready_start 168 5 8
  wct_cases [3493,3499,3503,2048,2054,2057,1571,1577,1579,1581,1585,966]
  · wct_piece 11 3493 44
  · wct_piece 11 3499 45
  · wct_piece 11 3503 46
  · wct_piece 5 2048 23
  · wct_piece 5 2054 24
  · wct_piece 5 2057 25
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine169_ready : RoutineReady ⟨169, by decide⟩ routine169 := by
  wct_ready_start 169 5 9
  wct_cases [3504,3510,3514,2064,2070,2072,2074,2078,1120,805,811,814]
  · wct_piece 11 3504 47
  · wct_piece 11 3510 48
  · wct_piece 11 3514 49
  · wct_piece 5 2064 27
  · wct_piece 5 2070 28
  · wct_piece 5 2072 29
  · wct_piece 5 2074 30
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine170_ready : RoutineReady ⟨170, by decide⟩ routine170 := by
  wct_ready_start 170 5 10
  wct_cases [3515,3521,3525,2085,2091,2093,2095,2099,1138,1144,875,881]
  · wct_piece 11 3515 50
  · wct_piece 11 3521 51
  · wct_piece 11 3525 52
  · wct_piece 5 2085 33
  · wct_piece 5 2091 34
  · wct_piece 5 2093 35
  · wct_piece 5 2095 36
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine171_ready : RoutineReady ⟨171, by decide⟩ routine171 := by
  wct_ready_start 171 5 11
  wct_cases [3526,3532,3536,2106,2112,2114,2116,2120,1162,1168,1170,1174,966]
  · wct_piece 11 3526 53
  · wct_piece 11 3532 54
  · wct_piece 11 3536 55
  · wct_piece 5 2106 39
  · wct_piece 5 2112 40
  · wct_piece 5 2114 41
  · wct_piece 5 2116 42
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine172_ready : RoutineReady ⟨172, by decide⟩ routine172 := by
  wct_ready_start 172 5 12
  wct_cases [3537,3543,3547,2127,2133,2135,2138,2144,2148,1365,875,881]
  · wct_piece 11 3537 56
  · wct_piece 11 3543 57
  · wct_piece 11 3547 58
  · wct_piece 5 2127 45
  · wct_piece 5 2133 46
  · wct_piece 5 2135 47
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine173_ready : RoutineReady ⟨173, by decide⟩ routine173 := by
  wct_ready_start 173 5 13
  wct_cases [3548,3554,3558,2155,2161,2163,2166,2172,1386,1392,1396,966]
  · wct_piece 11 3548 59
  · wct_piece 11 3554 60
  · wct_piece 11 3558 61
  · wct_piece 5 2155 52
  · wct_piece 5 2161 53
  · wct_piece 5 2163 54
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine174_ready : RoutineReady ⟨174, by decide⟩ routine174 := by
  wct_ready_start 174 5 14
  wct_cases [3559,3565,3569,2179,2185,2187,2190,2196,2198,2202,1585,966]
  · wct_piece 11 3559 62
  · wct_piece 11 3565 63
  · wct_piece 12 3569 0
  · wct_piece 5 2179 58
  · wct_piece 5 2185 59
  · wct_piece 5 2187 60
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine175_ready : RoutineReady ⟨175, by decide⟩ routine175 := by
  wct_ready_start 175 5 15
  wct_cases [3570,3576,3582,3586,2215,1187,829,835,755,761,763,766]
  · wct_piece 12 3570 1
  · wct_piece 12 3576 2
  · wct_piece 12 3582 3
  · wct_piece 12 3586 4
  · wct_piece 6 2215 4
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine176_ready : RoutineReady ⟨176, by decide⟩ routine176 := by
  wct_ready_start 176 5 16
  wct_cases [3587,3593,3599,3603,2228,1200,845,851,854,805,811,814]
  · wct_piece 12 3587 5
  · wct_piece 12 3593 6
  · wct_piece 12 3599 7
  · wct_piece 12 3603 8
  · wct_piece 6 2228 8
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine177_ready : RoutineReady ⟨177, by decide⟩ routine177 := by
  wct_ready_start 177 5 17
  wct_cases [3604,3610,3616,3620,2241,1213,864,870,872,875,881]
  · wct_piece 12 3604 9
  · wct_piece 12 3610 10
  · wct_piece 12 3616 11
  · wct_piece 12 3620 12
  · wct_piece 6 2241 12
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine178_ready : RoutineReady ⟨178, by decide⟩ routine178 := by
  wct_ready_start 178 5 18
  wct_cases [3621,3627,3633,3637,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 12 3621 13
  · wct_piece 12 3627 14
  · wct_piece 12 3633 15
  · wct_piece 12 3637 16
  · wct_piece 6 2254 16
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine179_ready : RoutineReady ⟨179, by decide⟩ routine179 := by
  wct_ready_start 179 5 19
  wct_cases [3638,3644,3650,3654,2267,1243,1249,913,919,805,811,814]
  · wct_piece 12 3638 17
  · wct_piece 12 3644 18
  · wct_piece 12 3650 19
  · wct_piece 12 3654 20
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine180_ready : RoutineReady ⟨180, by decide⟩ routine180 := by
  wct_ready_start 180 5 20
  wct_cases [3655,3661,3667,3671,2280,1259,1265,931,937,940,875,881]
  · wct_piece 12 3655 21
  · wct_piece 12 3661 22
  · wct_piece 12 3667 23
  · wct_piece 12 3671 24
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine181_ready : RoutineReady ⟨181, by decide⟩ routine181 := by
  wct_ready_start 181 5 21
  wct_cases [3672,3678,3684,3688,2293,1275,1281,952,958,960,962,966]
  · wct_piece 12 3672 25
  · wct_piece 12 3678 26
  · wct_piece 12 3684 27
  · wct_piece 12 3688 28
  · wct_piece 6 2293 28
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine182_ready : RoutineReady ⟨182, by decide⟩ routine182 := by
  wct_ready_start 182 5 22
  wct_cases [3689,3695,3701,3705,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 12 3689 29
  · wct_piece 12 3695 30
  · wct_piece 12 3701 31
  · wct_piece 12 3705 32
  · wct_piece 6 2306 32
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine183_ready : RoutineReady ⟨183, by decide⟩ routine183 := by
  wct_ready_start 183 5 23
  wct_cases [3706,3712,3718,3722,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 12 3706 33
  · wct_piece 12 3712 34
  · wct_piece 12 3718 35
  · wct_piece 12 3722 36
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine184_ready : RoutineReady ⟨184, by decide⟩ routine184 := by
  wct_ready_start 184 5 24
  wct_cases [3723,3729,3735,3739,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 12 3723 37
  · wct_piece 12 3729 38
  · wct_piece 12 3735 39
  · wct_piece 12 3739 40
  · wct_piece 6 2332 40
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine185_ready : RoutineReady ⟨185, by decide⟩ routine185 := by
  wct_ready_start 185 5 25
  wct_cases [3740,3746,3752,3756,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 12 3740 41
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
theorem routine186_ready : RoutineReady ⟨186, by decide⟩ routine186 := by
  wct_ready_start 186 5 26
  wct_cases [3757,3763,3769,3773,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 12 3757 45
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
theorem routine187_ready : RoutineReady ⟨187, by decide⟩ routine187 := by
  wct_ready_start 187 5 27
  wct_cases [3774,3780,3786,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 12 3774 49
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
theorem routine188_ready : RoutineReady ⟨188, by decide⟩ routine188 := by
  wct_ready_start 188 5 28
  wct_cases [3787,3793,3799,2388,2394,2398,1426,913,919,805,811,814]
  · wct_piece 12 3787 52
  · wct_piece 12 3793 53
  · wct_piece 12 3799 54
  · wct_piece 6 2388 56
  · wct_piece 6 2394 57
  · wct_piece 6 2398 58
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine189_ready : RoutineReady ⟨189, by decide⟩ routine189 := by
  wct_ready_start 189 5 29
  wct_cases [3800,3806,3812,2408,2414,2418,1441,931,937,940,875,881]
  · wct_piece 12 3800 55
  · wct_piece 12 3806 56
  · wct_piece 12 3812 57
  · wct_piece 6 2408 61
  · wct_piece 6 2414 62
  · wct_piece 6 2418 63
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine190_ready : RoutineReady ⟨190, by decide⟩ routine190 := by
  wct_ready_start 190 5 30
  wct_cases [3813,3819,3825,2428,2434,2438,1456,952,958,960,962,966]
  · wct_piece 12 3813 58
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
theorem routine191_ready : RoutineReady ⟨191, by decide⟩ routine191 := by
  wct_ready_start 191 5 31
  wct_cases [3826,3832,3838,2448,2454,1468,1474,1478,1120,805,811,814]
  · wct_piece 12 3826 61
  · wct_piece 12 3832 62
  · wct_piece 12 3838 63
  · wct_piece 7 2448 7
  · wct_piece 7 2454 8
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
end W9Machine.Chain
end
