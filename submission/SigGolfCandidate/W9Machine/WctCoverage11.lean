import SigGolfCandidate.W9Machine.WctRoutineCheck11
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch11_checked :
    (routineBatch11.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch11_checked :
    (routineBatch11.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine352_ready : RoutineReady ⟨352, by decide⟩ routine352 := by
  wct_ready_start 352 11 0
  wct_cases [236684,236690,3298,1788,1794,1243,1249,913,919,805,811,814]
  · wct_piece 24 236684 16
  · wct_piece 24 236690 17
  · wct_piece 10 3298 55
  · wct_piece 4 1788 23
  · wct_piece 4 1794 24
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine353_ready : RoutineReady ⟨353, by decide⟩ routine353 := by
  wct_ready_start 353 11 1
  wct_cases [236691,236697,3309,1801,1807,1259,1265,931,937,940,875,881]
  · wct_piece 24 236691 18
  · wct_piece 24 236697 19
  · wct_piece 10 3309 58
  · wct_piece 4 1801 26
  · wct_piece 4 1807 27
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine354_ready : RoutineReady ⟨354, by decide⟩ routine354 := by
  wct_ready_start 354 11 2
  wct_cases [236698,236704,3320,1814,1820,1275,1281,952,958,960,962,966]
  · wct_piece 24 236698 20
  · wct_piece 24 236704 21
  · wct_piece 10 3320 61
  · wct_piece 4 1814 29
  · wct_piece 4 1820 30
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine355_ready : RoutineReady ⟨355, by decide⟩ routine355 := by
  wct_ready_start 355 11 3
  wct_cases [236705,236711,3331,1827,1833,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 24 236705 22
  · wct_piece 24 236711 23
  · wct_piece 11 3331 0
  · wct_piece 4 1827 32
  · wct_piece 4 1833 33
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine356_ready : RoutineReady ⟨356, by decide⟩ routine356 := by
  wct_ready_start 356 11 4
  wct_cases [236712,236718,3342,1840,1846,1313,1319,1322,1138,1144,875,881]
  · wct_piece 24 236712 24
  · wct_piece 24 236718 25
  · wct_piece 11 3342 3
  · wct_piece 4 1840 35
  · wct_piece 4 1846 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine357_ready : RoutineReady ⟨357, by decide⟩ routine357 := by
  wct_ready_start 357 11 5
  wct_cases [236719,236725,3353,1853,1859,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 24 236719 26
  · wct_piece 24 236725 27
  · wct_piece 11 3353 6
  · wct_piece 4 1853 38
  · wct_piece 4 1859 39
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine358_ready : RoutineReady ⟨358, by decide⟩ routine358 := by
  wct_ready_start 358 11 6
  wct_cases [236726,236732,3364,1866,1872,1351,1357,1359,1361,1365,875,881]
  · wct_piece 24 236726 28
  · wct_piece 24 236732 29
  · wct_piece 11 3364 9
  · wct_piece 4 1866 41
  · wct_piece 4 1872 42
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine359_ready : RoutineReady ⟨359, by decide⟩ routine359 := by
  wct_ready_start 359 11 7
  wct_cases [236733,236739,3375,1879,1885,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 24 236733 30
  · wct_piece 24 236739 31
  · wct_piece 11 3375 12
  · wct_piece 4 1879 44
  · wct_piece 4 1885 45
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine360_ready : RoutineReady ⟨360, by decide⟩ routine360 := by
  wct_ready_start 360 11 8
  wct_cases [236740,236746,3386,1892,1898,1900,1904,1411,901,755,761,763,766]
  · wct_piece 24 236740 32
  · wct_piece 24 236746 33
  · wct_piece 11 3386 15
  · wct_piece 4 1892 47
  · wct_piece 4 1898 48
  · wct_piece 4 1900 49
  · wct_piece 4 1904 50
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine361_ready : RoutineReady ⟨361, by decide⟩ routine361 := by
  wct_ready_start 361 11 9
  wct_cases [236747,236753,3397,1911,1917,1919,1923,1426,913,919,805,811,814]
  · wct_piece 24 236747 34
  · wct_piece 24 236753 35
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
theorem routine362_ready : RoutineReady ⟨362, by decide⟩ routine362 := by
  wct_ready_start 362 11 10
  wct_cases [236754,236760,3408,1930,1936,1938,1942,1441,931,937,940,875,881]
  · wct_piece 24 236754 36
  · wct_piece 24 236760 37
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
theorem routine363_ready : RoutineReady ⟨363, by decide⟩ routine363 := by
  wct_ready_start 363 11 11
  wct_cases [236761,236767,3419,1949,1955,1957,1961,1456,952,958,960,962,966]
  · wct_piece 24 236761 38
  · wct_piece 24 236767 39
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
theorem routine364_ready : RoutineReady ⟨364, by decide⟩ routine364 := by
  wct_ready_start 364 11 12
  wct_cases [236768,236774,3430,3436,3439,1468,1474,1478,1120,805,811,814]
  · wct_piece 24 236768 40
  · wct_piece 24 236774 41
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
theorem routine365_ready : RoutineReady ⟨365, by decide⟩ routine365 := by
  wct_ready_start 365 11 13
  wct_cases [236775,236781,3450,1984,1990,1993,1490,1496,1138,1144,875,881]
  · wct_piece 24 236775 42
  · wct_piece 24 236781 43
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
theorem routine366_ready : RoutineReady ⟨366, by decide⟩ routine366 := by
  wct_ready_start 366 11 14
  wct_cases [236782,236788,3461,2000,2006,2009,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 24 236782 44
  · wct_piece 24 236788 45
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
theorem routine367_ready : RoutineReady ⟨367, by decide⟩ routine367 := by
  wct_ready_start 367 11 15
  wct_cases [236789,236795,3472,2016,2022,2025,1526,1532,1534,1538,1365,875,881]
  · wct_piece 24 236789 46
  · wct_piece 24 236795 47
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
theorem routine368_ready : RoutineReady ⟨368, by decide⟩ routine368 := by
  wct_ready_start 368 11 16
  wct_cases [236796,236802,3483,3489,3492,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 24 236796 48
  · wct_piece 24 236802 49
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
theorem routine369_ready : RoutineReady ⟨369, by decide⟩ routine369 := by
  wct_ready_start 369 11 17
  wct_cases [236803,236809,3503,2048,2054,2057,1571,1577,1579,1581,1585,966]
  · wct_piece 24 236803 50
  · wct_piece 24 236809 51
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
theorem routine370_ready : RoutineReady ⟨370, by decide⟩ routine370 := by
  wct_ready_start 370 11 18
  wct_cases [236810,236816,3514,2064,2070,2072,2074,2078,1120,805,811,814]
  · wct_piece 24 236810 52
  · wct_piece 24 236816 53
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
theorem routine371_ready : RoutineReady ⟨371, by decide⟩ routine371 := by
  wct_ready_start 371 11 19
  wct_cases [236817,236823,3525,2085,2091,2093,2095,2099,1138,1144,875,881]
  · wct_piece 24 236817 54
  · wct_piece 24 236823 55
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
theorem routine372_ready : RoutineReady ⟨372, by decide⟩ routine372 := by
  wct_ready_start 372 11 20
  wct_cases [236824,236830,3536,2106,2112,2114,2116,2120,1162,1168,1170,1174,966]
  · wct_piece 24 236824 56
  · wct_piece 24 236830 57
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
theorem routine373_ready : RoutineReady ⟨373, by decide⟩ routine373 := by
  wct_ready_start 373 11 21
  wct_cases [236831,236837,3547,2127,2133,2135,2138,2144,2148,1365,875,881]
  · wct_piece 24 236831 58
  · wct_piece 24 236837 59
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
theorem routine374_ready : RoutineReady ⟨374, by decide⟩ routine374 := by
  wct_ready_start 374 11 22
  wct_cases [236838,236844,3558,2155,2161,2163,2166,2172,1386,1392,1396,966]
  · wct_piece 24 236838 60
  · wct_piece 24 236844 61
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
theorem routine375_ready : RoutineReady ⟨375, by decide⟩ routine375 := by
  wct_ready_start 375 11 23
  wct_cases [236845,236851,3569,2179,2185,2187,2190,2196,2198,2202,1585,966]
  · wct_piece 24 236845 62
  · wct_piece 24 236851 63
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
theorem routine376_ready : RoutineReady ⟨376, by decide⟩ routine376 := by
  wct_ready_start 376 11 24
  wct_cases [236852,236858,3576,3582,3586,2215,1187,829,835,755,761,763,766]
  · wct_piece 25 236852 0
  · wct_piece 25 236858 1
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
theorem routine377_ready : RoutineReady ⟨377, by decide⟩ routine377 := by
  wct_ready_start 377 11 25
  wct_cases [236859,236865,3593,3599,3603,2228,1200,845,851,854,805,811,814]
  · wct_piece 25 236859 2
  · wct_piece 25 236865 3
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
theorem routine378_ready : RoutineReady ⟨378, by decide⟩ routine378 := by
  wct_ready_start 378 11 26
  wct_cases [236866,236872,3610,3616,3620,2241,1213,864,870,872,875,881]
  · wct_piece 25 236866 4
  · wct_piece 25 236872 5
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
theorem routine379_ready : RoutineReady ⟨379, by decide⟩ routine379 := by
  wct_ready_start 379 11 27
  wct_cases [236873,236879,236885,236889,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 25 236873 6
  · wct_piece 25 236879 7
  · wct_piece 25 236885 8
  · wct_piece 25 236889 9
  · wct_piece 6 2254 16
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine380_ready : RoutineReady ⟨380, by decide⟩ routine380 := by
  wct_ready_start 380 11 28
  wct_cases [236890,236896,236902,236906,2267,1243,1249,913,919,805,811,814]
  · wct_piece 25 236890 10
  · wct_piece 25 236896 11
  · wct_piece 25 236902 12
  · wct_piece 25 236906 13
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine381_ready : RoutineReady ⟨381, by decide⟩ routine381 := by
  wct_ready_start 381 11 29
  wct_cases [236907,236913,236919,236923,2280,1259,1265,931,937,940,875,881]
  · wct_piece 25 236907 14
  · wct_piece 25 236913 15
  · wct_piece 25 236919 16
  · wct_piece 25 236923 17
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine382_ready : RoutineReady ⟨382, by decide⟩ routine382 := by
  wct_ready_start 382 11 30
  wct_cases [236924,236930,3678,3684,3688,2293,1275,1281,952,958,960,962,966]
  · wct_piece 25 236924 18
  · wct_piece 25 236930 19
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
theorem routine383_ready : RoutineReady ⟨383, by decide⟩ routine383 := by
  wct_ready_start 383 11 31
  wct_cases [236931,236937,236943,236947,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 25 236931 20
  · wct_piece 25 236937 21
  · wct_piece 25 236943 22
  · wct_piece 25 236947 23
  · wct_piece 6 2306 32
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
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
theorem coverage11 (rank : Fin 728) (hlo : 352 ≤ rank.val) (hhi : rank.val < 384) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 352 ≤ n at hlo
  change n < 384 at hhi
  interval_cases n
  · exact ⟨routine352, routine352_ready⟩
  · exact ⟨routine353, routine353_ready⟩
  · exact ⟨routine354, routine354_ready⟩
  · exact ⟨routine355, routine355_ready⟩
  · exact ⟨routine356, routine356_ready⟩
  · exact ⟨routine357, routine357_ready⟩
  · exact ⟨routine358, routine358_ready⟩
  · exact ⟨routine359, routine359_ready⟩
  · exact ⟨routine360, routine360_ready⟩
  · exact ⟨routine361, routine361_ready⟩
  · exact ⟨routine362, routine362_ready⟩
  · exact ⟨routine363, routine363_ready⟩
  · exact ⟨routine364, routine364_ready⟩
  · exact ⟨routine365, routine365_ready⟩
  · exact ⟨routine366, routine366_ready⟩
  · exact ⟨routine367, routine367_ready⟩
  · exact ⟨routine368, routine368_ready⟩
  · exact ⟨routine369, routine369_ready⟩
  · exact ⟨routine370, routine370_ready⟩
  · exact ⟨routine371, routine371_ready⟩
  · exact ⟨routine372, routine372_ready⟩
  · exact ⟨routine373, routine373_ready⟩
  · exact ⟨routine374, routine374_ready⟩
  · exact ⟨routine375, routine375_ready⟩
  · exact ⟨routine376, routine376_ready⟩
  · exact ⟨routine377, routine377_ready⟩
  · exact ⟨routine378, routine378_ready⟩
  · exact ⟨routine379, routine379_ready⟩
  · exact ⟨routine380, routine380_ready⟩
  · exact ⟨routine381, routine381_ready⟩
  · exact ⟨routine382, routine382_ready⟩
  · exact ⟨routine383, routine383_ready⟩
end W9Machine.Chain
end
