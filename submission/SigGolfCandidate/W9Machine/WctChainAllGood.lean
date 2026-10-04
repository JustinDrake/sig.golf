import SigGolfCandidate.W9Machine.WctRoutineCheck02
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence
import SigGolfCandidate.W9Machine.WctRoutineCheck01
import SigGolfCandidate.W9Machine.WctRoutineCheck00
import SigGolfCandidate.W9Machine.WctReadyCheck18
import SigGolfCandidate.W9Machine.WctReadyCheck07
import SigGolfCandidate.W9Machine.WctReadyCheck06
import SigGolfCandidate.W9Machine.WctReadyCheck05
import SigGolfCandidate.W9Machine.WctReadyCheck04
import SigGolfCandidate.W9Machine.WctReadyCheck03
import SigGolfCandidate.W9Machine.WctReadyCheck22
import SigGolfCandidate.W9Machine.WctCoverage08
import SigGolfCandidate.W9Machine.WctCoverage09
import SigGolfCandidate.W9Machine.WctCoverage10
import SigGolfCandidate.W9Machine.WctCoverage11
import SigGolfCandidate.W9Machine.WctCoverage12
import SigGolfCandidate.W9Machine.WctCoverage13
import SigGolfCandidate.W9Machine.WctCoverage14
import SigGolfCandidate.W9Machine.WctCoverage15
import SigGolfCandidate.W9Machine.WctCoverage16
import SigGolfCandidate.W9Machine.WctCoverage17
import SigGolfCandidate.W9Machine.WctCoverage19
import SigGolfCandidate.W9Machine.WctCoverage20
import SigGolfCandidate.W9Machine.WctCoverage21

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch02_checked :
    (routineBatch02.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch02_checked :
    (routineBatch02.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine64_ready : RoutineReady ⟨64, by decide⟩ routine64 := by
  wct_ready_start 64 2 0
  wct_cases [1834,1840,1846,1313,1319,1322,1138,1144,875,881]
  · wct_piece 4 1834 34
  · wct_piece 4 1840 35
  · wct_piece 4 1846 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine65_ready : RoutineReady ⟨65, by decide⟩ routine65 := by
  wct_ready_start 65 2 1
  wct_cases [1847,1853,1859,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 4 1847 37
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
theorem routine66_ready : RoutineReady ⟨66, by decide⟩ routine66 := by
  wct_ready_start 66 2 2
  wct_cases [1860,1866,1872,1351,1357,1359,1361,1365,875,881]
  · wct_piece 4 1860 40
  · wct_piece 4 1866 41
  · wct_piece 4 1872 42
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine67_ready : RoutineReady ⟨67, by decide⟩ routine67 := by
  wct_ready_start 67 2 3
  wct_cases [1873,1879,1885,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 4 1873 43
  · wct_piece 4 1879 44
  · wct_piece 4 1885 45
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine68_ready : RoutineReady ⟨68, by decide⟩ routine68 := by
  wct_ready_start 68 2 4
  wct_cases [1886,1892,1898,1900,1904,1411,901,755,761,763,766]
  · wct_piece 4 1886 46
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
theorem routine69_ready : RoutineReady ⟨69, by decide⟩ routine69 := by
  wct_ready_start 69 2 5
  wct_cases [1905,1911,1917,1919,1923,1426,913,919,805,811,814]
  · wct_piece 4 1905 51
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
theorem routine70_ready : RoutineReady ⟨70, by decide⟩ routine70 := by
  wct_ready_start 70 2 6
  wct_cases [1924,1930,1936,1938,1942,1441,931,937,940,875,881]
  · wct_piece 4 1924 56
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
theorem routine71_ready : RoutineReady ⟨71, by decide⟩ routine71 := by
  wct_ready_start 71 2 7
  wct_cases [1943,1949,1955,1957,1961,1456,952,958,960,962,966]
  · wct_piece 4 1943 61
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
theorem routine72_ready : RoutineReady ⟨72, by decide⟩ routine72 := by
  wct_ready_start 72 2 8
  wct_cases [1962,1968,1974,1977,1468,1474,1478,1120,805,811,814]
  · wct_piece 5 1962 2
  · wct_piece 5 1968 3
  · wct_piece 5 1974 4
  · wct_piece 5 1977 5
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine73_ready : RoutineReady ⟨73, by decide⟩ routine73 := by
  wct_ready_start 73 2 9
  wct_cases [1978,1984,1990,1993,1490,1496,1138,1144,875,881]
  · wct_piece 5 1978 6
  · wct_piece 5 1984 7
  · wct_piece 5 1990 8
  · wct_piece 5 1993 9
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine74_ready : RoutineReady ⟨74, by decide⟩ routine74 := by
  wct_ready_start 74 2 10
  wct_cases [1994,2000,2006,2009,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 5 1994 10
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
theorem routine75_ready : RoutineReady ⟨75, by decide⟩ routine75 := by
  wct_ready_start 75 2 11
  wct_cases [2010,2016,2022,2025,1526,1532,1534,1538,1365,875,881]
  · wct_piece 5 2010 14
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
theorem routine76_ready : RoutineReady ⟨76, by decide⟩ routine76 := by
  wct_ready_start 76 2 12
  wct_cases [2026,2032,2038,2041,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 5 2026 18
  · wct_piece 5 2032 19
  · wct_piece 5 2038 20
  · wct_piece 5 2041 21
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine77_ready : RoutineReady ⟨77, by decide⟩ routine77 := by
  wct_ready_start 77 2 13
  wct_cases [2042,2048,2054,2057,1571,1577,1579,1581,1585,966]
  · wct_piece 5 2042 22
  · wct_piece 5 2048 23
  · wct_piece 5 2054 24
  · wct_piece 5 2057 25
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine78_ready : RoutineReady ⟨78, by decide⟩ routine78 := by
  wct_ready_start 78 2 14
  wct_cases [2058,2064,2070,2072,2074,2078,1120,805,811,814]
  · wct_piece 5 2058 26
  · wct_piece 5 2064 27
  · wct_piece 5 2070 28
  · wct_piece 5 2072 29
  · wct_piece 5 2074 30
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine79_ready : RoutineReady ⟨79, by decide⟩ routine79 := by
  wct_ready_start 79 2 15
  wct_cases [2079,2085,2091,2093,2095,2099,1138,1144,875,881]
  · wct_piece 5 2079 32
  · wct_piece 5 2085 33
  · wct_piece 5 2091 34
  · wct_piece 5 2093 35
  · wct_piece 5 2095 36
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine80_ready : RoutineReady ⟨80, by decide⟩ routine80 := by
  wct_ready_start 80 2 16
  wct_cases [2100,2106,2112,2114,2116,2120,1162,1168,1170,1174,966]
  · wct_piece 5 2100 38
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
theorem routine81_ready : RoutineReady ⟨81, by decide⟩ routine81 := by
  wct_ready_start 81 2 17
  wct_cases [2121,2127,2133,2135,2138,2144,2148,1365,875,881]
  · wct_piece 5 2121 44
  · wct_piece 5 2127 45
  · wct_piece 5 2133 46
  · wct_piece 5 2135 47
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine82_ready : RoutineReady ⟨82, by decide⟩ routine82 := by
  wct_ready_start 82 2 18
  wct_cases [2149,2155,2161,2163,2166,2172,1386,1392,1396,966]
  · wct_piece 5 2149 51
  · wct_piece 5 2155 52
  · wct_piece 5 2161 53
  · wct_piece 5 2163 54
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine83_ready : RoutineReady ⟨83, by decide⟩ routine83 := by
  wct_ready_start 83 2 19
  wct_cases [2173,2179,2185,2187,2190,2196,2198,2202,1585,966]
  · wct_piece 5 2173 57
  · wct_piece 5 2179 58
  · wct_piece 5 2185 59
  · wct_piece 5 2187 60
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine84_ready : RoutineReady ⟨84, by decide⟩ routine84 := by
  wct_ready_start 84 2 20
  wct_cases [2203,2209,2211,2215,1187,829,835,755,761,763,766]
  · wct_piece 6 2203 1
  · wct_piece 6 2209 2
  · wct_piece 6 2211 3
  · wct_piece 6 2215 4
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine85_ready : RoutineReady ⟨85, by decide⟩ routine85 := by
  wct_ready_start 85 2 21
  wct_cases [2216,2222,2224,2228,1200,845,851,854,805,811,814]
  · wct_piece 6 2216 5
  · wct_piece 6 2222 6
  · wct_piece 6 2224 7
  · wct_piece 6 2228 8
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine86_ready : RoutineReady ⟨86, by decide⟩ routine86 := by
  wct_ready_start 86 2 22
  wct_cases [2229,2235,2237,2241,1213,864,870,872,875,881]
  · wct_piece 6 2229 9
  · wct_piece 6 2235 10
  · wct_piece 6 2237 11
  · wct_piece 6 2241 12
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine87_ready : RoutineReady ⟨87, by decide⟩ routine87 := by
  wct_ready_start 87 2 23
  wct_cases [2242,2248,2250,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 6 2242 13
  · wct_piece 6 2248 14
  · wct_piece 6 2250 15
  · wct_piece 6 2254 16
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine88_ready : RoutineReady ⟨88, by decide⟩ routine88 := by
  wct_ready_start 88 2 24
  wct_cases [2255,2261,2263,2267,1243,1249,913,919,805,811,814]
  · wct_piece 6 2255 17
  · wct_piece 6 2261 18
  · wct_piece 6 2263 19
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine89_ready : RoutineReady ⟨89, by decide⟩ routine89 := by
  wct_ready_start 89 2 25
  wct_cases [2268,2274,2276,2280,1259,1265,931,937,940,875,881]
  · wct_piece 6 2268 21
  · wct_piece 6 2274 22
  · wct_piece 6 2276 23
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine90_ready : RoutineReady ⟨90, by decide⟩ routine90 := by
  wct_ready_start 90 2 26
  wct_cases [2281,2287,2289,2293,1275,1281,952,958,960,962,966]
  · wct_piece 6 2281 25
  · wct_piece 6 2287 26
  · wct_piece 6 2289 27
  · wct_piece 6 2293 28
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine91_ready : RoutineReady ⟨91, by decide⟩ routine91 := by
  wct_ready_start 91 2 27
  wct_cases [2294,2300,2302,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 6 2294 29
  · wct_piece 6 2300 30
  · wct_piece 6 2302 31
  · wct_piece 6 2306 32
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine92_ready : RoutineReady ⟨92, by decide⟩ routine92 := by
  wct_ready_start 92 2 28
  wct_cases [2307,2313,2315,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 6 2307 33
  · wct_piece 6 2313 34
  · wct_piece 6 2315 35
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine93_ready : RoutineReady ⟨93, by decide⟩ routine93 := by
  wct_ready_start 93 2 29
  wct_cases [2320,2326,2328,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 6 2320 37
  · wct_piece 6 2326 38
  · wct_piece 6 2328 39
  · wct_piece 6 2332 40
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine94_ready : RoutineReady ⟨94, by decide⟩ routine94 := by
  wct_ready_start 94 2 30
  wct_cases [2333,2339,2341,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 6 2333 41
  · wct_piece 6 2339 42
  · wct_piece 6 2341 43
  · wct_piece 6 2345 44
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine95_ready : RoutineReady ⟨95, by decide⟩ routine95 := by
  wct_ready_start 95 2 31
  wct_cases [2346,2352,2354,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 6 2346 45
  · wct_piece 6 2352 46
  · wct_piece 6 2354 47
  · wct_piece 6 2358 48
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
end W9Machine.Chain
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch01_checked :
    (routineBatch01.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch01_checked :
    (routineBatch01.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine32_ready : RoutineReady ⟨32, by decide⟩ routine32 := by
  wct_ready_start 32 1 0
  wct_cases [1342,1348,1351,1357,1359,1361,1365,875,881]
  · wct_piece 2 1342 27
  · wct_piece 2 1348 28
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine33_ready : RoutineReady ⟨33, by decide⟩ routine33 := by
  wct_ready_start 33 1 1
  wct_cases [1366,1372,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 2 1366 34
  · wct_piece 2 1372 35
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine34_ready : RoutineReady ⟨34, by decide⟩ routine34 := by
  wct_ready_start 34 1 2
  wct_cases [1397,1403,1405,1407,1411,901,755,761,763,766]
  · wct_piece 2 1397 42
  · wct_piece 2 1403 43
  · wct_piece 2 1405 44
  · wct_piece 2 1407 45
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine35_ready : RoutineReady ⟨35, by decide⟩ routine35 := by
  wct_ready_start 35 1 3
  wct_cases [1412,1418,1420,1422,1426,913,919,805,811,814]
  · wct_piece 2 1412 47
  · wct_piece 2 1418 48
  · wct_piece 2 1420 49
  · wct_piece 2 1422 50
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine36_ready : RoutineReady ⟨36, by decide⟩ routine36 := by
  wct_ready_start 36 1 4
  wct_cases [1427,1433,1435,1437,1441,931,937,940,875,881]
  · wct_piece 2 1427 52
  · wct_piece 2 1433 53
  · wct_piece 2 1435 54
  · wct_piece 2 1437 55
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine37_ready : RoutineReady ⟨37, by decide⟩ routine37 := by
  wct_ready_start 37 1 5
  wct_cases [1442,1448,1450,1452,1456,952,958,960,962,966]
  · wct_piece 2 1442 57
  · wct_piece 2 1448 58
  · wct_piece 2 1450 59
  · wct_piece 2 1452 60
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine38_ready : RoutineReady ⟨38, by decide⟩ routine38 := by
  wct_ready_start 38 1 6
  wct_cases [1457,1463,1465,1468,1474,1478,1120,805,811,814]
  · wct_piece 2 1457 62
  · wct_piece 2 1463 63
  · wct_piece 3 1465 0
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine39_ready : RoutineReady ⟨39, by decide⟩ routine39 := by
  wct_ready_start 39 1 7
  wct_cases [1479,1485,1487,1490,1496,1138,1144,875,881]
  · wct_piece 3 1479 4
  · wct_piece 3 1485 5
  · wct_piece 3 1487 6
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine40_ready : RoutineReady ⟨40, by decide⟩ routine40 := by
  wct_ready_start 40 1 8
  wct_cases [1497,1503,1505,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 3 1497 9
  · wct_piece 3 1503 10
  · wct_piece 3 1505 11
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine41_ready : RoutineReady ⟨41, by decide⟩ routine41 := by
  wct_ready_start 41 1 9
  wct_cases [1515,1521,1523,1526,1532,1534,1538,1365,875,881]
  · wct_piece 3 1515 14
  · wct_piece 3 1521 15
  · wct_piece 3 1523 16
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine42_ready : RoutineReady ⟨42, by decide⟩ routine42 := by
  wct_ready_start 42 1 10
  wct_cases [1539,1545,1547,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 3 1539 21
  · wct_piece 3 1545 22
  · wct_piece 3 1547 23
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine43_ready : RoutineReady ⟨43, by decide⟩ routine43 := by
  wct_ready_start 43 1 11
  wct_cases [1560,1566,1568,1571,1577,1579,1581,1585,966]
  · wct_piece 3 1560 27
  · wct_piece 3 1566 28
  · wct_piece 3 1568 29
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine44_ready : RoutineReady ⟨44, by decide⟩ routine44 := by
  wct_ready_start 44 1 12
  wct_cases [1586,1592,1596,982,778,784,787,755,761,763,766]
  · wct_piece 3 1586 35
  · wct_piece 3 1592 36
  · wct_piece 3 1596 37
  · wct_piece 0 982 60
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine45_ready : RoutineReady ⟨45, by decide⟩ routine45 := by
  wct_ready_start 45 1 13
  wct_cases [1597,1603,1607,993,794,800,802,805,811,814]
  · wct_piece 3 1597 38
  · wct_piece 3 1603 39
  · wct_piece 3 1607 40
  · wct_piece 0 993 63
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine46_ready : RoutineReady ⟨46, by decide⟩ routine46 := by
  wct_ready_start 46 1 14
  wct_cases [1608,1614,1618,1000,1006,829,835,755,761,763,766]
  · wct_piece 3 1608 41
  · wct_piece 3 1614 42
  · wct_piece 3 1618 43
  · wct_piece 1 1000 1
  · wct_piece 1 1006 2
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine47_ready : RoutineReady ⟨47, by decide⟩ routine47 := by
  wct_ready_start 47 1 15
  wct_cases [1619,1625,1629,1013,1019,845,851,854,805,811,814]
  · wct_piece 3 1619 44
  · wct_piece 3 1625 45
  · wct_piece 3 1629 46
  · wct_piece 1 1013 4
  · wct_piece 1 1019 5
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine48_ready : RoutineReady ⟨48, by decide⟩ routine48 := by
  wct_ready_start 48 1 16
  wct_cases [1630,1636,1640,1026,1032,864,870,872,875,881]
  · wct_piece 3 1630 47
  · wct_piece 3 1636 48
  · wct_piece 3 1640 49
  · wct_piece 1 1026 7
  · wct_piece 1 1032 8
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine49_ready : RoutineReady ⟨49, by decide⟩ routine49 := by
  wct_ready_start 49 1 17
  wct_cases [1641,1647,1651,1039,1045,1047,1051,901,755,761,763,766]
  · wct_piece 3 1641 50
  · wct_piece 3 1647 51
  · wct_piece 3 1651 52
  · wct_piece 1 1039 10
  · wct_piece 1 1045 11
  · wct_piece 1 1047 12
  · wct_piece 1 1051 13
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine50_ready : RoutineReady ⟨50, by decide⟩ routine50 := by
  wct_ready_start 50 1 18
  wct_cases [1652,1658,1662,1058,1064,1067,913,919,805,811,814]
  · wct_piece 3 1652 53
  · wct_piece 3 1658 54
  · wct_piece 3 1662 55
  · wct_piece 1 1058 15
  · wct_piece 1 1064 16
  · wct_piece 1 1067 17
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine51_ready : RoutineReady ⟨51, by decide⟩ routine51 := by
  wct_ready_start 51 1 19
  wct_cases [1663,1669,1673,1074,1080,1083,931,937,940,875,881]
  · wct_piece 3 1663 56
  · wct_piece 3 1669 57
  · wct_piece 3 1673 58
  · wct_piece 1 1074 19
  · wct_piece 1 1080 20
  · wct_piece 1 1083 21
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine52_ready : RoutineReady ⟨52, by decide⟩ routine52 := by
  wct_ready_start 52 1 20
  wct_cases [1674,1680,1684,1090,1096,1099,952,958,960,962,966]
  · wct_piece 3 1674 59
  · wct_piece 3 1680 60
  · wct_piece 3 1684 61
  · wct_piece 1 1090 23
  · wct_piece 1 1096 24
  · wct_piece 1 1099 25
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine53_ready : RoutineReady ⟨53, by decide⟩ routine53 := by
  wct_ready_start 53 1 21
  wct_cases [1685,1691,1695,1106,1112,1114,1116,1120,805,811,814]
  · wct_piece 3 1685 62
  · wct_piece 3 1691 63
  · wct_piece 4 1695 0
  · wct_piece 1 1106 27
  · wct_piece 1 1112 28
  · wct_piece 1 1114 29
  · wct_piece 1 1116 30
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine54_ready : RoutineReady ⟨54, by decide⟩ routine54 := by
  wct_ready_start 54 1 22
  wct_cases [1696,1702,1706,1127,1133,1135,1138,1144,875,881]
  · wct_piece 4 1696 1
  · wct_piece 4 1702 2
  · wct_piece 4 1706 3
  · wct_piece 1 1127 33
  · wct_piece 1 1133 34
  · wct_piece 1 1135 35
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine55_ready : RoutineReady ⟨55, by decide⟩ routine55 := by
  wct_ready_start 55 1 23
  wct_cases [1707,1713,1717,1151,1157,1159,1162,1168,1170,1174,966]
  · wct_piece 4 1707 4
  · wct_piece 4 1713 5
  · wct_piece 4 1717 6
  · wct_piece 1 1151 39
  · wct_piece 1 1157 40
  · wct_piece 1 1159 41
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine56_ready : RoutineReady ⟨56, by decide⟩ routine56 := by
  wct_ready_start 56 1 24
  wct_cases [1718,1724,1730,1734,1187,829,835,755,761,763,766]
  · wct_piece 4 1718 7
  · wct_piece 4 1724 8
  · wct_piece 4 1730 9
  · wct_piece 4 1734 10
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine57_ready : RoutineReady ⟨57, by decide⟩ routine57 := by
  wct_ready_start 57 1 25
  wct_cases [1735,1741,1747,1751,1200,845,851,854,805,811,814]
  · wct_piece 4 1735 11
  · wct_piece 4 1741 12
  · wct_piece 4 1747 13
  · wct_piece 4 1751 14
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine58_ready : RoutineReady ⟨58, by decide⟩ routine58 := by
  wct_ready_start 58 1 26
  wct_cases [1752,1758,1764,1768,1213,864,870,872,875,881]
  · wct_piece 4 1752 15
  · wct_piece 4 1758 16
  · wct_piece 4 1764 17
  · wct_piece 4 1768 18
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine59_ready : RoutineReady ⟨59, by decide⟩ routine59 := by
  wct_ready_start 59 1 27
  wct_cases [1769,1775,1781,1223,1229,1233,901,755,761,763,766]
  · wct_piece 4 1769 19
  · wct_piece 4 1775 20
  · wct_piece 4 1781 21
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine60_ready : RoutineReady ⟨60, by decide⟩ routine60 := by
  wct_ready_start 60 1 28
  wct_cases [1782,1788,1794,1243,1249,913,919,805,811,814]
  · wct_piece 4 1782 22
  · wct_piece 4 1788 23
  · wct_piece 4 1794 24
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine61_ready : RoutineReady ⟨61, by decide⟩ routine61 := by
  wct_ready_start 61 1 29
  wct_cases [1795,1801,1807,1259,1265,931,937,940,875,881]
  · wct_piece 4 1795 25
  · wct_piece 4 1801 26
  · wct_piece 4 1807 27
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine62_ready : RoutineReady ⟨62, by decide⟩ routine62 := by
  wct_ready_start 62 1 30
  wct_cases [1808,1814,1820,1275,1281,952,958,960,962,966]
  · wct_piece 4 1808 28
  · wct_piece 4 1814 29
  · wct_piece 4 1820 30
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine63_ready : RoutineReady ⟨63, by decide⟩ routine63 := by
  wct_ready_start 63 1 31
  wct_cases [1821,1827,1833,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 4 1821 31
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
end W9Machine.Chain
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch00_checked :
    (routineBatch00.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch00_checked :
    (routineBatch00.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine0_ready : RoutineReady ⟨0, by decide⟩ routine0 := by
  wct_ready_start 0 0 0
  wct_cases [744,750,752,755,761,763,766]
  · wct_piece 0 744 0
  · wct_piece 0 750 1
  · wct_piece 0 752 2
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine1_ready : RoutineReady ⟨1, by decide⟩ routine1 := by
  wct_ready_start 1 0 1
  wct_cases [772,778,784,787,755,761,763,766]
  · wct_piece 0 772 7
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine2_ready : RoutineReady ⟨2, by decide⟩ routine2 := by
  wct_ready_start 2 0 2
  wct_cases [788,794,800,802,805,811,814]
  · wct_piece 0 788 11
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine3_ready : RoutineReady ⟨3, by decide⟩ routine3 := by
  wct_ready_start 3 0 3
  wct_cases [820,826,829,835,755,761,763,766]
  · wct_piece 0 820 18
  · wct_piece 0 826 19
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine4_ready : RoutineReady ⟨4, by decide⟩ routine4 := by
  wct_ready_start 4 0 4
  wct_cases [836,842,845,851,854,805,811,814]
  · wct_piece 0 836 22
  · wct_piece 0 842 23
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine5_ready : RoutineReady ⟨5, by decide⟩ routine5 := by
  wct_ready_start 5 0 5
  wct_cases [855,861,864,870,872,875,881]
  · wct_piece 0 855 27
  · wct_piece 0 861 28
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine6_ready : RoutineReady ⟨6, by decide⟩ routine6 := by
  wct_ready_start 6 0 6
  wct_cases [887,893,895,897,901,755,761,763,766]
  · wct_piece 0 887 34
  · wct_piece 0 893 35
  · wct_piece 0 895 36
  · wct_piece 0 897 37
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine7_ready : RoutineReady ⟨7, by decide⟩ routine7 := by
  wct_ready_start 7 0 7
  wct_cases [902,908,910,913,919,805,811,814]
  · wct_piece 0 902 39
  · wct_piece 0 908 40
  · wct_piece 0 910 41
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine8_ready : RoutineReady ⟨8, by decide⟩ routine8 := by
  wct_ready_start 8 0 8
  wct_cases [920,926,928,931,937,940,875,881]
  · wct_piece 0 920 44
  · wct_piece 0 926 45
  · wct_piece 0 928 46
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine9_ready : RoutineReady ⟨9, by decide⟩ routine9 := by
  wct_ready_start 9 0 9
  wct_cases [941,947,949,952,958,960,962,966]
  · wct_piece 0 941 50
  · wct_piece 0 947 51
  · wct_piece 0 949 52
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine10_ready : RoutineReady ⟨10, by decide⟩ routine10 := by
  wct_ready_start 10 0 10
  wct_cases [972,978,982,778,784,787,755,761,763,766]
  · wct_piece 0 972 58
  · wct_piece 0 978 59
  · wct_piece 0 982 60
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine11_ready : RoutineReady ⟨11, by decide⟩ routine11 := by
  wct_ready_start 11 0 11
  wct_cases [983,989,993,794,800,802,805,811,814]
  · wct_piece 0 983 61
  · wct_piece 0 989 62
  · wct_piece 0 993 63
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine12_ready : RoutineReady ⟨12, by decide⟩ routine12 := by
  wct_ready_start 12 0 12
  wct_cases [994,1000,1006,829,835,755,761,763,766]
  · wct_piece 1 994 0
  · wct_piece 1 1000 1
  · wct_piece 1 1006 2
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine13_ready : RoutineReady ⟨13, by decide⟩ routine13 := by
  wct_ready_start 13 0 13
  wct_cases [1007,1013,1019,845,851,854,805,811,814]
  · wct_piece 1 1007 3
  · wct_piece 1 1013 4
  · wct_piece 1 1019 5
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine14_ready : RoutineReady ⟨14, by decide⟩ routine14 := by
  wct_ready_start 14 0 14
  wct_cases [1020,1026,1032,864,870,872,875,881]
  · wct_piece 1 1020 6
  · wct_piece 1 1026 7
  · wct_piece 1 1032 8
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine15_ready : RoutineReady ⟨15, by decide⟩ routine15 := by
  wct_ready_start 15 0 15
  wct_cases [1033,1039,1045,1047,1051,901,755,761,763,766]
  · wct_piece 1 1033 9
  · wct_piece 1 1039 10
  · wct_piece 1 1045 11
  · wct_piece 1 1047 12
  · wct_piece 1 1051 13
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine16_ready : RoutineReady ⟨16, by decide⟩ routine16 := by
  wct_ready_start 16 0 16
  wct_cases [1052,1058,1064,1067,913,919,805,811,814]
  · wct_piece 1 1052 14
  · wct_piece 1 1058 15
  · wct_piece 1 1064 16
  · wct_piece 1 1067 17
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine17_ready : RoutineReady ⟨17, by decide⟩ routine17 := by
  wct_ready_start 17 0 17
  wct_cases [1068,1074,1080,1083,931,937,940,875,881]
  · wct_piece 1 1068 18
  · wct_piece 1 1074 19
  · wct_piece 1 1080 20
  · wct_piece 1 1083 21
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine18_ready : RoutineReady ⟨18, by decide⟩ routine18 := by
  wct_ready_start 18 0 18
  wct_cases [1084,1090,1096,1099,952,958,960,962,966]
  · wct_piece 1 1084 22
  · wct_piece 1 1090 23
  · wct_piece 1 1096 24
  · wct_piece 1 1099 25
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine19_ready : RoutineReady ⟨19, by decide⟩ routine19 := by
  wct_ready_start 19 0 19
  wct_cases [1100,1106,1112,1114,1116,1120,805,811,814]
  · wct_piece 1 1100 26
  · wct_piece 1 1106 27
  · wct_piece 1 1112 28
  · wct_piece 1 1114 29
  · wct_piece 1 1116 30
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine20_ready : RoutineReady ⟨20, by decide⟩ routine20 := by
  wct_ready_start 20 0 20
  wct_cases [1121,1127,1133,1135,1138,1144,875,881]
  · wct_piece 1 1121 32
  · wct_piece 1 1127 33
  · wct_piece 1 1133 34
  · wct_piece 1 1135 35
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine21_ready : RoutineReady ⟨21, by decide⟩ routine21 := by
  wct_ready_start 21 0 21
  wct_cases [1145,1151,1157,1159,1162,1168,1170,1174,966]
  · wct_piece 1 1145 38
  · wct_piece 1 1151 39
  · wct_piece 1 1157 40
  · wct_piece 1 1159 41
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine22_ready : RoutineReady ⟨22, by decide⟩ routine22 := by
  wct_ready_start 22 0 22
  wct_cases [1175,1181,1183,1187,829,835,755,761,763,766]
  · wct_piece 1 1175 46
  · wct_piece 1 1181 47
  · wct_piece 1 1183 48
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine23_ready : RoutineReady ⟨23, by decide⟩ routine23 := by
  wct_ready_start 23 0 23
  wct_cases [1188,1194,1196,1200,845,851,854,805,811,814]
  · wct_piece 1 1188 50
  · wct_piece 1 1194 51
  · wct_piece 1 1196 52
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine24_ready : RoutineReady ⟨24, by decide⟩ routine24 := by
  wct_ready_start 24 0 24
  wct_cases [1201,1207,1209,1213,864,870,872,875,881]
  · wct_piece 1 1201 54
  · wct_piece 1 1207 55
  · wct_piece 1 1209 56
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine25_ready : RoutineReady ⟨25, by decide⟩ routine25 := by
  wct_ready_start 25 0 25
  wct_cases [1214,1220,1223,1229,1233,901,755,761,763,766]
  · wct_piece 1 1214 58
  · wct_piece 1 1220 59
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine26_ready : RoutineReady ⟨26, by decide⟩ routine26 := by
  wct_ready_start 26 0 26
  wct_cases [1234,1240,1243,1249,913,919,805,811,814]
  · wct_piece 1 1234 63
  · wct_piece 2 1240 0
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine27_ready : RoutineReady ⟨27, by decide⟩ routine27 := by
  wct_ready_start 27 0 27
  wct_cases [1250,1256,1259,1265,931,937,940,875,881]
  · wct_piece 2 1250 3
  · wct_piece 2 1256 4
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine28_ready : RoutineReady ⟨28, by decide⟩ routine28 := by
  wct_ready_start 28 0 28
  wct_cases [1266,1272,1275,1281,952,958,960,962,966]
  · wct_piece 2 1266 7
  · wct_piece 2 1272 8
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine29_ready : RoutineReady ⟨29, by decide⟩ routine29 := by
  wct_ready_start 29 0 29
  wct_cases [1282,1288,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 2 1282 11
  · wct_piece 2 1288 12
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine30_ready : RoutineReady ⟨30, by decide⟩ routine30 := by
  wct_ready_start 30 0 30
  wct_cases [1304,1310,1313,1319,1322,1138,1144,875,881]
  · wct_piece 2 1304 17
  · wct_piece 2 1310 18
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine31_ready : RoutineReady ⟨31, by decide⟩ routine31 := by
  wct_ready_start 31 0 31
  wct_cases [1323,1329,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 2 1323 22
  · wct_piece 2 1329 23
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem good_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (rank : Fin 728) (r : ChainRoutine) (hr : RoutineReady rank r) : Good rank := by
  intro w index k j u N C A Q K hu hK
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD rank.val 0 := Option.some.inj he
    exact hu.pc.trans (congrArg pcOf he'.symm)
  have hk : ∀ answers s, Inv u index k j (terminalTrace r.pieces {}) answers s →
      GoodQFor Frozen.image (leafSetupRel.toState s) N C Q A
        (K (sourceEnds w k rank answers)) := by
    intro answers s hs
    exact hK _ _ (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints w index k j rank u s _ answers hu hs hr.endpoints))
  have hrun := runPlan_good hu r.pieces {} [] u (inv_initial w index k j rank u hu)
    hr.guard hr.linked hpc N C A Q (fun answers => K (sourceEnds w k rank answers)) hk
  have hcost := hr.cycles
  have hfuel := planFuel_le_cycles r.pieces
  have hbig := hrun.mono (A' := A + 89) (by omega : N + planFuel r.pieces ≤ N + 89)
    (by omega : C + planCycles r.pieces ≤ C + 89) (fun h => ⟨h, by omega⟩)
  apply hbig.congr
  rw [hr.queries]
  have he := congrArg (fun p => ccM p K) (source w index k j rank u hu)
  simpa only [ccM_bind, ccM_pure] using he
theorem allGood_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (ready : ∀ rank : Fin 728, ∃ r, RoutineReady rank r) : AllGood := by
  intro rank
  obtain ⟨r, hr⟩ := ready rank
  exact good_of_ready source endpoints rank r hr
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage18 (rank : Fin 728) (hlo : 576 ≤ rank.val) (hhi : rank.val < 608) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 576 ≤ n at hlo
  change n < 608 at hhi
  interval_cases n
  · exact ⟨routine576, routine576_ready⟩
  · exact ⟨routine577, routine577_ready⟩
  · exact ⟨routine578, routine578_ready⟩
  · exact ⟨routine579, routine579_ready⟩
  · exact ⟨routine580, routine580_ready⟩
  · exact ⟨routine581, routine581_ready⟩
  · exact ⟨routine582, routine582_ready⟩
  · exact ⟨routine583, routine583_ready⟩
  · exact ⟨routine584, routine584_ready⟩
  · exact ⟨routine585, routine585_ready⟩
  · exact ⟨routine586, routine586_ready⟩
  · exact ⟨routine587, routine587_ready⟩
  · exact ⟨routine588, routine588_ready⟩
  · exact ⟨routine589, routine589_ready⟩
  · exact ⟨routine590, routine590_ready⟩
  · exact ⟨routine591, routine591_ready⟩
  · exact ⟨routine592, routine592_ready⟩
  · exact ⟨routine593, routine593_ready⟩
  · exact ⟨routine594, routine594_ready⟩
  · exact ⟨routine595, routine595_ready⟩
  · exact ⟨routine596, routine596_ready⟩
  · exact ⟨routine597, routine597_ready⟩
  · exact ⟨routine598, routine598_ready⟩
  · exact ⟨routine599, routine599_ready⟩
  · exact ⟨routine600, routine600_ready⟩
  · exact ⟨routine601, routine601_ready⟩
  · exact ⟨routine602, routine602_ready⟩
  · exact ⟨routine603, routine603_ready⟩
  · exact ⟨routine604, routine604_ready⟩
  · exact ⟨routine605, routine605_ready⟩
  · exact ⟨routine606, routine606_ready⟩
  · exact ⟨routine607, routine607_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage07 (rank : Fin 728) (hlo : 224 ≤ rank.val) (hhi : rank.val < 256) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 224 ≤ n at hlo
  change n < 256 at hhi
  interval_cases n
  · exact ⟨routine224, routine224_ready⟩
  · exact ⟨routine225, routine225_ready⟩
  · exact ⟨routine226, routine226_ready⟩
  · exact ⟨routine227, routine227_ready⟩
  · exact ⟨routine228, routine228_ready⟩
  · exact ⟨routine229, routine229_ready⟩
  · exact ⟨routine230, routine230_ready⟩
  · exact ⟨routine231, routine231_ready⟩
  · exact ⟨routine232, routine232_ready⟩
  · exact ⟨routine233, routine233_ready⟩
  · exact ⟨routine234, routine234_ready⟩
  · exact ⟨routine235, routine235_ready⟩
  · exact ⟨routine236, routine236_ready⟩
  · exact ⟨routine237, routine237_ready⟩
  · exact ⟨routine238, routine238_ready⟩
  · exact ⟨routine239, routine239_ready⟩
  · exact ⟨routine240, routine240_ready⟩
  · exact ⟨routine241, routine241_ready⟩
  · exact ⟨routine242, routine242_ready⟩
  · exact ⟨routine243, routine243_ready⟩
  · exact ⟨routine244, routine244_ready⟩
  · exact ⟨routine245, routine245_ready⟩
  · exact ⟨routine246, routine246_ready⟩
  · exact ⟨routine247, routine247_ready⟩
  · exact ⟨routine248, routine248_ready⟩
  · exact ⟨routine249, routine249_ready⟩
  · exact ⟨routine250, routine250_ready⟩
  · exact ⟨routine251, routine251_ready⟩
  · exact ⟨routine252, routine252_ready⟩
  · exact ⟨routine253, routine253_ready⟩
  · exact ⟨routine254, routine254_ready⟩
  · exact ⟨routine255, routine255_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage06 (rank : Fin 728) (hlo : 192 ≤ rank.val) (hhi : rank.val < 224) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 192 ≤ n at hlo
  change n < 224 at hhi
  interval_cases n
  · exact ⟨routine192, routine192_ready⟩
  · exact ⟨routine193, routine193_ready⟩
  · exact ⟨routine194, routine194_ready⟩
  · exact ⟨routine195, routine195_ready⟩
  · exact ⟨routine196, routine196_ready⟩
  · exact ⟨routine197, routine197_ready⟩
  · exact ⟨routine198, routine198_ready⟩
  · exact ⟨routine199, routine199_ready⟩
  · exact ⟨routine200, routine200_ready⟩
  · exact ⟨routine201, routine201_ready⟩
  · exact ⟨routine202, routine202_ready⟩
  · exact ⟨routine203, routine203_ready⟩
  · exact ⟨routine204, routine204_ready⟩
  · exact ⟨routine205, routine205_ready⟩
  · exact ⟨routine206, routine206_ready⟩
  · exact ⟨routine207, routine207_ready⟩
  · exact ⟨routine208, routine208_ready⟩
  · exact ⟨routine209, routine209_ready⟩
  · exact ⟨routine210, routine210_ready⟩
  · exact ⟨routine211, routine211_ready⟩
  · exact ⟨routine212, routine212_ready⟩
  · exact ⟨routine213, routine213_ready⟩
  · exact ⟨routine214, routine214_ready⟩
  · exact ⟨routine215, routine215_ready⟩
  · exact ⟨routine216, routine216_ready⟩
  · exact ⟨routine217, routine217_ready⟩
  · exact ⟨routine218, routine218_ready⟩
  · exact ⟨routine219, routine219_ready⟩
  · exact ⟨routine220, routine220_ready⟩
  · exact ⟨routine221, routine221_ready⟩
  · exact ⟨routine222, routine222_ready⟩
  · exact ⟨routine223, routine223_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage05 (rank : Fin 728) (hlo : 160 ≤ rank.val) (hhi : rank.val < 192) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 160 ≤ n at hlo
  change n < 192 at hhi
  interval_cases n
  · exact ⟨routine160, routine160_ready⟩
  · exact ⟨routine161, routine161_ready⟩
  · exact ⟨routine162, routine162_ready⟩
  · exact ⟨routine163, routine163_ready⟩
  · exact ⟨routine164, routine164_ready⟩
  · exact ⟨routine165, routine165_ready⟩
  · exact ⟨routine166, routine166_ready⟩
  · exact ⟨routine167, routine167_ready⟩
  · exact ⟨routine168, routine168_ready⟩
  · exact ⟨routine169, routine169_ready⟩
  · exact ⟨routine170, routine170_ready⟩
  · exact ⟨routine171, routine171_ready⟩
  · exact ⟨routine172, routine172_ready⟩
  · exact ⟨routine173, routine173_ready⟩
  · exact ⟨routine174, routine174_ready⟩
  · exact ⟨routine175, routine175_ready⟩
  · exact ⟨routine176, routine176_ready⟩
  · exact ⟨routine177, routine177_ready⟩
  · exact ⟨routine178, routine178_ready⟩
  · exact ⟨routine179, routine179_ready⟩
  · exact ⟨routine180, routine180_ready⟩
  · exact ⟨routine181, routine181_ready⟩
  · exact ⟨routine182, routine182_ready⟩
  · exact ⟨routine183, routine183_ready⟩
  · exact ⟨routine184, routine184_ready⟩
  · exact ⟨routine185, routine185_ready⟩
  · exact ⟨routine186, routine186_ready⟩
  · exact ⟨routine187, routine187_ready⟩
  · exact ⟨routine188, routine188_ready⟩
  · exact ⟨routine189, routine189_ready⟩
  · exact ⟨routine190, routine190_ready⟩
  · exact ⟨routine191, routine191_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage04 (rank : Fin 728) (hlo : 128 ≤ rank.val) (hhi : rank.val < 160) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 128 ≤ n at hlo
  change n < 160 at hhi
  interval_cases n
  · exact ⟨routine128, routine128_ready⟩
  · exact ⟨routine129, routine129_ready⟩
  · exact ⟨routine130, routine130_ready⟩
  · exact ⟨routine131, routine131_ready⟩
  · exact ⟨routine132, routine132_ready⟩
  · exact ⟨routine133, routine133_ready⟩
  · exact ⟨routine134, routine134_ready⟩
  · exact ⟨routine135, routine135_ready⟩
  · exact ⟨routine136, routine136_ready⟩
  · exact ⟨routine137, routine137_ready⟩
  · exact ⟨routine138, routine138_ready⟩
  · exact ⟨routine139, routine139_ready⟩
  · exact ⟨routine140, routine140_ready⟩
  · exact ⟨routine141, routine141_ready⟩
  · exact ⟨routine142, routine142_ready⟩
  · exact ⟨routine143, routine143_ready⟩
  · exact ⟨routine144, routine144_ready⟩
  · exact ⟨routine145, routine145_ready⟩
  · exact ⟨routine146, routine146_ready⟩
  · exact ⟨routine147, routine147_ready⟩
  · exact ⟨routine148, routine148_ready⟩
  · exact ⟨routine149, routine149_ready⟩
  · exact ⟨routine150, routine150_ready⟩
  · exact ⟨routine151, routine151_ready⟩
  · exact ⟨routine152, routine152_ready⟩
  · exact ⟨routine153, routine153_ready⟩
  · exact ⟨routine154, routine154_ready⟩
  · exact ⟨routine155, routine155_ready⟩
  · exact ⟨routine156, routine156_ready⟩
  · exact ⟨routine157, routine157_ready⟩
  · exact ⟨routine158, routine158_ready⟩
  · exact ⟨routine159, routine159_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage03 (rank : Fin 728) (hlo : 96 ≤ rank.val) (hhi : rank.val < 128) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 96 ≤ n at hlo
  change n < 128 at hhi
  interval_cases n
  · exact ⟨routine96, routine96_ready⟩
  · exact ⟨routine97, routine97_ready⟩
  · exact ⟨routine98, routine98_ready⟩
  · exact ⟨routine99, routine99_ready⟩
  · exact ⟨routine100, routine100_ready⟩
  · exact ⟨routine101, routine101_ready⟩
  · exact ⟨routine102, routine102_ready⟩
  · exact ⟨routine103, routine103_ready⟩
  · exact ⟨routine104, routine104_ready⟩
  · exact ⟨routine105, routine105_ready⟩
  · exact ⟨routine106, routine106_ready⟩
  · exact ⟨routine107, routine107_ready⟩
  · exact ⟨routine108, routine108_ready⟩
  · exact ⟨routine109, routine109_ready⟩
  · exact ⟨routine110, routine110_ready⟩
  · exact ⟨routine111, routine111_ready⟩
  · exact ⟨routine112, routine112_ready⟩
  · exact ⟨routine113, routine113_ready⟩
  · exact ⟨routine114, routine114_ready⟩
  · exact ⟨routine115, routine115_ready⟩
  · exact ⟨routine116, routine116_ready⟩
  · exact ⟨routine117, routine117_ready⟩
  · exact ⟨routine118, routine118_ready⟩
  · exact ⟨routine119, routine119_ready⟩
  · exact ⟨routine120, routine120_ready⟩
  · exact ⟨routine121, routine121_ready⟩
  · exact ⟨routine122, routine122_ready⟩
  · exact ⟨routine123, routine123_ready⟩
  · exact ⟨routine124, routine124_ready⟩
  · exact ⟨routine125, routine125_ready⟩
  · exact ⟨routine126, routine126_ready⟩
  · exact ⟨routine127, routine127_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage02 (rank : Fin 728) (hlo : 64 ≤ rank.val) (hhi : rank.val < 96) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 64 ≤ n at hlo
  change n < 96 at hhi
  interval_cases n
  · exact ⟨routine64, routine64_ready⟩
  · exact ⟨routine65, routine65_ready⟩
  · exact ⟨routine66, routine66_ready⟩
  · exact ⟨routine67, routine67_ready⟩
  · exact ⟨routine68, routine68_ready⟩
  · exact ⟨routine69, routine69_ready⟩
  · exact ⟨routine70, routine70_ready⟩
  · exact ⟨routine71, routine71_ready⟩
  · exact ⟨routine72, routine72_ready⟩
  · exact ⟨routine73, routine73_ready⟩
  · exact ⟨routine74, routine74_ready⟩
  · exact ⟨routine75, routine75_ready⟩
  · exact ⟨routine76, routine76_ready⟩
  · exact ⟨routine77, routine77_ready⟩
  · exact ⟨routine78, routine78_ready⟩
  · exact ⟨routine79, routine79_ready⟩
  · exact ⟨routine80, routine80_ready⟩
  · exact ⟨routine81, routine81_ready⟩
  · exact ⟨routine82, routine82_ready⟩
  · exact ⟨routine83, routine83_ready⟩
  · exact ⟨routine84, routine84_ready⟩
  · exact ⟨routine85, routine85_ready⟩
  · exact ⟨routine86, routine86_ready⟩
  · exact ⟨routine87, routine87_ready⟩
  · exact ⟨routine88, routine88_ready⟩
  · exact ⟨routine89, routine89_ready⟩
  · exact ⟨routine90, routine90_ready⟩
  · exact ⟨routine91, routine91_ready⟩
  · exact ⟨routine92, routine92_ready⟩
  · exact ⟨routine93, routine93_ready⟩
  · exact ⟨routine94, routine94_ready⟩
  · exact ⟨routine95, routine95_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage01 (rank : Fin 728) (hlo : 32 ≤ rank.val) (hhi : rank.val < 64) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 32 ≤ n at hlo
  change n < 64 at hhi
  interval_cases n
  · exact ⟨routine32, routine32_ready⟩
  · exact ⟨routine33, routine33_ready⟩
  · exact ⟨routine34, routine34_ready⟩
  · exact ⟨routine35, routine35_ready⟩
  · exact ⟨routine36, routine36_ready⟩
  · exact ⟨routine37, routine37_ready⟩
  · exact ⟨routine38, routine38_ready⟩
  · exact ⟨routine39, routine39_ready⟩
  · exact ⟨routine40, routine40_ready⟩
  · exact ⟨routine41, routine41_ready⟩
  · exact ⟨routine42, routine42_ready⟩
  · exact ⟨routine43, routine43_ready⟩
  · exact ⟨routine44, routine44_ready⟩
  · exact ⟨routine45, routine45_ready⟩
  · exact ⟨routine46, routine46_ready⟩
  · exact ⟨routine47, routine47_ready⟩
  · exact ⟨routine48, routine48_ready⟩
  · exact ⟨routine49, routine49_ready⟩
  · exact ⟨routine50, routine50_ready⟩
  · exact ⟨routine51, routine51_ready⟩
  · exact ⟨routine52, routine52_ready⟩
  · exact ⟨routine53, routine53_ready⟩
  · exact ⟨routine54, routine54_ready⟩
  · exact ⟨routine55, routine55_ready⟩
  · exact ⟨routine56, routine56_ready⟩
  · exact ⟨routine57, routine57_ready⟩
  · exact ⟨routine58, routine58_ready⟩
  · exact ⟨routine59, routine59_ready⟩
  · exact ⟨routine60, routine60_ready⟩
  · exact ⟨routine61, routine61_ready⟩
  · exact ⟨routine62, routine62_ready⟩
  · exact ⟨routine63, routine63_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage00 (rank : Fin 728) (hlo : 0 ≤ rank.val) (hhi : rank.val < 32) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 0 ≤ n at hlo
  change n < 32 at hhi
  interval_cases n
  · exact ⟨routine0, routine0_ready⟩
  · exact ⟨routine1, routine1_ready⟩
  · exact ⟨routine2, routine2_ready⟩
  · exact ⟨routine3, routine3_ready⟩
  · exact ⟨routine4, routine4_ready⟩
  · exact ⟨routine5, routine5_ready⟩
  · exact ⟨routine6, routine6_ready⟩
  · exact ⟨routine7, routine7_ready⟩
  · exact ⟨routine8, routine8_ready⟩
  · exact ⟨routine9, routine9_ready⟩
  · exact ⟨routine10, routine10_ready⟩
  · exact ⟨routine11, routine11_ready⟩
  · exact ⟨routine12, routine12_ready⟩
  · exact ⟨routine13, routine13_ready⟩
  · exact ⟨routine14, routine14_ready⟩
  · exact ⟨routine15, routine15_ready⟩
  · exact ⟨routine16, routine16_ready⟩
  · exact ⟨routine17, routine17_ready⟩
  · exact ⟨routine18, routine18_ready⟩
  · exact ⟨routine19, routine19_ready⟩
  · exact ⟨routine20, routine20_ready⟩
  · exact ⟨routine21, routine21_ready⟩
  · exact ⟨routine22, routine22_ready⟩
  · exact ⟨routine23, routine23_ready⟩
  · exact ⟨routine24, routine24_ready⟩
  · exact ⟨routine25, routine25_ready⟩
  · exact ⟨routine26, routine26_ready⟩
  · exact ⟨routine27, routine27_ready⟩
  · exact ⟨routine28, routine28_ready⟩
  · exact ⟨routine29, routine29_ready⟩
  · exact ⟨routine30, routine30_ready⟩
  · exact ⟨routine31, routine31_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage22 (rank : Fin 728) (hlo : 704 ≤ rank.val) (hhi : rank.val < 728) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 704 ≤ n at hlo
  change n < 728 at hhi
  interval_cases n
  · exact ⟨routine704, routine704_ready⟩
  · exact ⟨routine705, routine705_ready⟩
  · exact ⟨routine706, routine706_ready⟩
  · exact ⟨routine707, routine707_ready⟩
  · exact ⟨routine708, routine708_ready⟩
  · exact ⟨routine709, routine709_ready⟩
  · exact ⟨routine710, routine710_ready⟩
  · exact ⟨routine711, routine711_ready⟩
  · exact ⟨routine712, routine712_ready⟩
  · exact ⟨routine713, routine713_ready⟩
  · exact ⟨routine714, routine714_ready⟩
  · exact ⟨routine715, routine715_ready⟩
  · exact ⟨routine716, routine716_ready⟩
  · exact ⟨routine717, routine717_ready⟩
  · exact ⟨routine718, routine718_ready⟩
  · exact ⟨routine719, routine719_ready⟩
  · exact ⟨routine720, routine720_ready⟩
  · exact ⟨routine721, routine721_ready⟩
  · exact ⟨routine722, routine722_ready⟩
  · exact ⟨routine723, routine723_ready⟩
  · exact ⟨routine724, routine724_ready⟩
  · exact ⟨routine725, routine725_ready⟩
  · exact ⟨routine726, routine726_ready⟩
  · exact ⟨routine727, routine727_ready⟩
end W9Machine.Chain
end

section
























namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem allRoutines_ready : ∀ rank : Fin 728, ∃ r, RoutineReady rank r := by
  intro rank
  by_cases h0 : rank.val < 32
  · exact coverage00 rank (by omega) h0
  by_cases h1 : rank.val < 64
  · exact coverage01 rank (by omega) h1
  by_cases h2 : rank.val < 96
  · exact coverage02 rank (by omega) h2
  by_cases h3 : rank.val < 128
  · exact coverage03 rank (by omega) h3
  by_cases h4 : rank.val < 160
  · exact coverage04 rank (by omega) h4
  by_cases h5 : rank.val < 192
  · exact coverage05 rank (by omega) h5
  by_cases h6 : rank.val < 224
  · exact coverage06 rank (by omega) h6
  by_cases h7 : rank.val < 256
  · exact coverage07 rank (by omega) h7
  by_cases h8 : rank.val < 288
  · exact coverage08 rank (by omega) h8
  by_cases h9 : rank.val < 320
  · exact coverage09 rank (by omega) h9
  by_cases h10 : rank.val < 352
  · exact coverage10 rank (by omega) h10
  by_cases h11 : rank.val < 384
  · exact coverage11 rank (by omega) h11
  by_cases h12 : rank.val < 416
  · exact coverage12 rank (by omega) h12
  by_cases h13 : rank.val < 448
  · exact coverage13 rank (by omega) h13
  by_cases h14 : rank.val < 480
  · exact coverage14 rank (by omega) h14
  by_cases h15 : rank.val < 512
  · exact coverage15 rank (by omega) h15
  by_cases h16 : rank.val < 544
  · exact coverage16 rank (by omega) h16
  by_cases h17 : rank.val < 576
  · exact coverage17 rank (by omega) h17
  by_cases h18 : rank.val < 608
  · exact coverage18 rank (by omega) h18
  by_cases h19 : rank.val < 640
  · exact coverage19 rank (by omega) h19
  by_cases h20 : rank.val < 672
  · exact coverage20 rank (by omega) h20
  by_cases h21 : rank.val < 704
  · exact coverage21 rank (by omega) h21
  exact coverage22 rank (by omega) rank.isLt
theorem allGood_of (S : SourceEquivalent) (E : EndpointsCorrect) : AllGood := by
  exact allGood_of_ready S E allRoutines_ready
end W9Machine.Chain
end
