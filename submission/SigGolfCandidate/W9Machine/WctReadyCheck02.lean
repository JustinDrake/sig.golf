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
def routine64 : ChainRoutine := ⟨64, [0, 0, 1, 1, 2, 1, 1], [piece1723, piece1728, piece1733, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine65 : ChainRoutine := ⟨65, [0, 0, 1, 1, 2, 2, 0], [piece1734, piece1739, piece1744, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine66 : ChainRoutine := ⟨66, [0, 0, 1, 1, 3, 0, 1], [piece1745, piece1750, piece1755, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine67 : ChainRoutine := ⟨67, [0, 0, 1, 1, 3, 1, 0], [piece1756, piece1761, piece1766, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine68 : ChainRoutine := ⟨68, [0, 0, 1, 2, 0, 0, 3], [piece1767, piece1772, piece1777, piece1779, piece1783, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine69 : ChainRoutine := ⟨69, [0, 0, 1, 2, 0, 1, 2], [piece1784, piece1789, piece1794, piece1796, piece1800, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine70 : ChainRoutine := ⟨70, [0, 0, 1, 2, 0, 2, 1], [piece1801, piece1806, piece1811, piece1813, piece1817, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine71 : ChainRoutine := ⟨71, [0, 0, 1, 2, 0, 3, 0], [piece1818, piece1823, piece1828, piece1830, piece1834, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine72 : ChainRoutine := ⟨72, [0, 0, 1, 2, 1, 0, 2], [piece1835, piece1840, piece1845, piece1848, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine73 : ChainRoutine := ⟨73, [0, 0, 1, 2, 1, 1, 1], [piece1849, piece1854, piece1859, piece1862, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine74 : ChainRoutine := ⟨74, [0, 0, 1, 2, 1, 2, 0], [piece1863, piece1868, piece1873, piece1876, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine75 : ChainRoutine := ⟨75, [0, 0, 1, 2, 2, 0, 1], [piece1877, piece1882, piece1887, piece1890, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine76 : ChainRoutine := ⟨76, [0, 0, 1, 2, 2, 1, 0], [piece1891, piece1896, piece1901, piece1904, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine77 : ChainRoutine := ⟨77, [0, 0, 1, 2, 3, 0, 0], [piece1905, piece1910, piece1915, piece1918, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine78 : ChainRoutine := ⟨78, [0, 0, 1, 3, 0, 0, 2], [piece1919, piece1924, piece1929, piece1931, piece1933, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine79 : ChainRoutine := ⟨79, [0, 0, 1, 3, 0, 1, 1], [piece1938, piece1943, piece1948, piece1950, piece1952, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine80 : ChainRoutine := ⟨80, [0, 0, 1, 3, 0, 2, 0], [piece1957, piece1962, piece1967, piece1969, piece1971, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine81 : ChainRoutine := ⟨81, [0, 0, 1, 3, 1, 0, 1], [piece1976, piece1981, piece1986, piece1988, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine82 : ChainRoutine := ⟨82, [0, 0, 1, 3, 1, 1, 0], [piece2001, piece2006, piece2011, piece2013, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine83 : ChainRoutine := ⟨83, [0, 0, 1, 3, 2, 0, 0], [piece2022, piece2027, piece2032, piece2034, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine84 : ChainRoutine := ⟨84, [0, 0, 2, 0, 0, 1, 3], [piece2049, piece2054, piece2056, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine85 : ChainRoutine := ⟨85, [0, 0, 2, 0, 0, 2, 2], [piece2061, piece2066, piece2068, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine86 : ChainRoutine := ⟨86, [0, 0, 2, 0, 0, 3, 1], [piece2073, piece2078, piece2080, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine87 : ChainRoutine := ⟨87, [0, 0, 2, 0, 1, 0, 3], [piece2085, piece2090, piece2092, piece2096, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine88 : ChainRoutine := ⟨88, [0, 0, 2, 0, 1, 1, 2], [piece2097, piece2102, piece2104, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine89 : ChainRoutine := ⟨89, [0, 0, 2, 0, 1, 2, 1], [piece2109, piece2114, piece2116, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine90 : ChainRoutine := ⟨90, [0, 0, 2, 0, 1, 3, 0], [piece2121, piece2126, piece2128, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine91 : ChainRoutine := ⟨91, [0, 0, 2, 0, 2, 0, 2], [piece2133, piece2138, piece2140, piece2144, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine92 : ChainRoutine := ⟨92, [0, 0, 2, 0, 2, 1, 1], [piece2145, piece2150, piece2152, piece2156, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine93 : ChainRoutine := ⟨93, [0, 0, 2, 0, 2, 2, 0], [piece2157, piece2162, piece2164, piece2168, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine94 : ChainRoutine := ⟨94, [0, 0, 2, 0, 3, 0, 1], [piece2169, piece2174, piece2176, piece2180, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine95 : ChainRoutine := ⟨95, [0, 0, 2, 0, 3, 1, 0], [piece2181, piece2186, piece2188, piece2192, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routineBatch02 : List ChainRoutine := [routine64, routine65, routine66, routine67, routine68, routine69, routine70, routine71, routine72, routine73, routine74, routine75, routine76, routine77, routine78, routine79, routine80, routine81, routine82, routine83, routine84, routine85, routine86, routine87, routine88, routine89, routine90, routine91, routine92, routine93, routine94, routine95]
theorem routineBatch02_checked : (routineBatch02.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

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
  wct_cases [1723,1728,1733,1254,1259,1262,1097,1102,862,867]
  · wct_piece 4 1723 34
  · wct_piece 4 1728 35
  · wct_piece 4 1733 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine65_ready : RoutineReady ⟨65, by decide⟩ routine65 := by
  wct_ready_start 65 2 1
  wct_cases [1734,1739,1744,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 4 1734 37
  · wct_piece 4 1739 38
  · wct_piece 4 1744 39
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine66_ready : RoutineReady ⟨66, by decide⟩ routine66 := by
  wct_ready_start 66 2 2
  wct_cases [1745,1750,1755,1288,1293,1295,1297,1301,862,867]
  · wct_piece 4 1745 40
  · wct_piece 4 1750 41
  · wct_piece 4 1755 42
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine67_ready : RoutineReady ⟨67, by decide⟩ routine67 := by
  wct_ready_start 67 2 3
  wct_cases [1756,1761,1766,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 4 1756 43
  · wct_piece 4 1761 44
  · wct_piece 4 1766 45
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine68_ready : RoutineReady ⟨68, by decide⟩ routine68 := by
  wct_ready_start 68 2 4
  wct_cases [1767,1772,1777,1779,1783,1343,886,754,759,761,764]
  · wct_piece 4 1767 46
  · wct_piece 4 1772 47
  · wct_piece 4 1777 48
  · wct_piece 4 1779 49
  · wct_piece 4 1783 50
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine69_ready : RoutineReady ⟨69, by decide⟩ routine69 := by
  wct_ready_start 69 2 5
  wct_cases [1784,1789,1794,1796,1800,1357,897,902,799,804,807]
  · wct_piece 4 1784 51
  · wct_piece 4 1789 52
  · wct_piece 4 1794 53
  · wct_piece 4 1796 54
  · wct_piece 4 1800 55
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine70_ready : RoutineReady ⟨70, by decide⟩ routine70 := by
  wct_ready_start 70 2 6
  wct_cases [1801,1806,1811,1813,1817,1371,913,918,921,862,867]
  · wct_piece 4 1801 56
  · wct_piece 4 1806 57
  · wct_piece 4 1811 58
  · wct_piece 4 1813 59
  · wct_piece 4 1817 60
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine71_ready : RoutineReady ⟨71, by decide⟩ routine71 := by
  wct_ready_start 71 2 7
  wct_cases [1818,1823,1828,1830,1834,1385,932,937,939,941,945]
  · wct_piece 4 1818 61
  · wct_piece 4 1823 62
  · wct_piece 4 1828 63
  · wct_piece 5 1830 0
  · wct_piece 5 1834 1
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine72_ready : RoutineReady ⟨72, by decide⟩ routine72 := by
  wct_ready_start 72 2 8
  wct_cases [1835,1840,1845,1848,1396,1401,1405,1081,799,804,807]
  · wct_piece 5 1835 2
  · wct_piece 5 1840 3
  · wct_piece 5 1845 4
  · wct_piece 5 1848 5
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine73_ready : RoutineReady ⟨73, by decide⟩ routine73 := by
  wct_ready_start 73 2 9
  wct_cases [1849,1854,1859,1862,1416,1421,1097,1102,862,867]
  · wct_piece 5 1849 6
  · wct_piece 5 1854 7
  · wct_piece 5 1859 8
  · wct_piece 5 1862 9
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine74_ready : RoutineReady ⟨74, by decide⟩ routine74 := by
  wct_ready_start 74 2 10
  wct_cases [1863,1868,1873,1876,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 5 1863 10
  · wct_piece 5 1868 11
  · wct_piece 5 1873 12
  · wct_piece 5 1876 13
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine75_ready : RoutineReady ⟨75, by decide⟩ routine75 := by
  wct_ready_start 75 2 11
  wct_cases [1877,1882,1887,1890,1448,1453,1455,1459,1301,862,867]
  · wct_piece 5 1877 14
  · wct_piece 5 1882 15
  · wct_piece 5 1887 16
  · wct_piece 5 1890 17
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine76_ready : RoutineReady ⟨76, by decide⟩ routine76 := by
  wct_ready_start 76 2 12
  wct_cases [1891,1896,1901,1904,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 5 1891 18
  · wct_piece 5 1896 19
  · wct_piece 5 1901 20
  · wct_piece 5 1904 21
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine77_ready : RoutineReady ⟨77, by decide⟩ routine77 := by
  wct_ready_start 77 2 13
  wct_cases [1905,1910,1915,1918,1489,1494,1496,1498,1502,945]
  · wct_piece 5 1905 22
  · wct_piece 5 1910 23
  · wct_piece 5 1915 24
  · wct_piece 5 1918 25
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine78_ready : RoutineReady ⟨78, by decide⟩ routine78 := by
  wct_ready_start 78 2 14
  wct_cases [1919,1924,1929,1931,1933,1937,1081,799,804,807]
  · wct_piece 5 1919 26
  · wct_piece 5 1924 27
  · wct_piece 5 1929 28
  · wct_piece 5 1931 29
  · wct_piece 5 1933 30
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine79_ready : RoutineReady ⟨79, by decide⟩ routine79 := by
  wct_ready_start 79 2 15
  wct_cases [1938,1943,1948,1950,1952,1956,1097,1102,862,867]
  · wct_piece 5 1938 32
  · wct_piece 5 1943 33
  · wct_piece 5 1948 34
  · wct_piece 5 1950 35
  · wct_piece 5 1952 36
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine80_ready : RoutineReady ⟨80, by decide⟩ routine80 := by
  wct_ready_start 80 2 16
  wct_cases [1957,1962,1967,1969,1971,1975,1118,1123,1125,1129,945]
  · wct_piece 5 1957 38
  · wct_piece 5 1962 39
  · wct_piece 5 1967 40
  · wct_piece 5 1969 41
  · wct_piece 5 1971 42
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine81_ready : RoutineReady ⟨81, by decide⟩ routine81 := by
  wct_ready_start 81 2 17
  wct_cases [1976,1981,1986,1988,1991,1996,2000,1301,862,867]
  · wct_piece 5 1976 44
  · wct_piece 5 1981 45
  · wct_piece 5 1986 46
  · wct_piece 5 1988 47
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine82_ready : RoutineReady ⟨82, by decide⟩ routine82 := by
  wct_ready_start 82 2 18
  wct_cases [2001,2006,2011,2013,2016,2021,1320,1325,1329,945]
  · wct_piece 5 2001 51
  · wct_piece 5 2006 52
  · wct_piece 5 2011 53
  · wct_piece 5 2013 54
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine83_ready : RoutineReady ⟨83, by decide⟩ routine83 := by
  wct_ready_start 83 2 19
  wct_cases [2022,2027,2032,2034,2037,2042,2044,2048,1502,945]
  · wct_piece 5 2022 57
  · wct_piece 5 2027 58
  · wct_piece 5 2032 59
  · wct_piece 5 2034 60
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine84_ready : RoutineReady ⟨84, by decide⟩ routine84 := by
  wct_ready_start 84 2 20
  wct_cases [2049,2054,2056,2060,1141,821,826,754,759,761,764]
  · wct_piece 6 2049 1
  · wct_piece 6 2054 2
  · wct_piece 6 2056 3
  · wct_piece 6 2060 4
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine85_ready : RoutineReady ⟨85, by decide⟩ routine85 := by
  wct_ready_start 85 2 21
  wct_cases [2061,2066,2068,2072,1153,835,840,843,799,804,807]
  · wct_piece 6 2061 5
  · wct_piece 6 2066 6
  · wct_piece 6 2068 7
  · wct_piece 6 2072 8
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine86_ready : RoutineReady ⟨86, by decide⟩ routine86 := by
  wct_ready_start 86 2 22
  wct_cases [2073,2078,2080,2084,1165,852,857,859,862,867]
  · wct_piece 6 2073 9
  · wct_piece 6 2078 10
  · wct_piece 6 2080 11
  · wct_piece 6 2084 12
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine87_ready : RoutineReady ⟨87, by decide⟩ routine87 := by
  wct_ready_start 87 2 23
  wct_cases [2085,2090,2092,2096,1174,1179,1183,886,754,759,761,764]
  · wct_piece 6 2085 13
  · wct_piece 6 2090 14
  · wct_piece 6 2092 15
  · wct_piece 6 2096 16
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine88_ready : RoutineReady ⟨88, by decide⟩ routine88 := by
  wct_ready_start 88 2 24
  wct_cases [2097,2102,2104,2108,1192,1197,897,902,799,804,807]
  · wct_piece 6 2097 17
  · wct_piece 6 2102 18
  · wct_piece 6 2104 19
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine89_ready : RoutineReady ⟨89, by decide⟩ routine89 := by
  wct_ready_start 89 2 25
  wct_cases [2109,2114,2116,2120,1206,1211,913,918,921,862,867]
  · wct_piece 6 2109 21
  · wct_piece 6 2114 22
  · wct_piece 6 2116 23
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine90_ready : RoutineReady ⟨90, by decide⟩ routine90 := by
  wct_ready_start 90 2 26
  wct_cases [2121,2126,2128,2132,1220,1225,932,937,939,941,945]
  · wct_piece 6 2121 25
  · wct_piece 6 2126 26
  · wct_piece 6 2128 27
  · wct_piece 6 2132 28
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine91_ready : RoutineReady ⟨91, by decide⟩ routine91 := by
  wct_ready_start 91 2 27
  wct_cases [2133,2138,2140,2144,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 6 2133 29
  · wct_piece 6 2138 30
  · wct_piece 6 2140 31
  · wct_piece 6 2144 32
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine92_ready : RoutineReady ⟨92, by decide⟩ routine92 := by
  wct_ready_start 92 2 28
  wct_cases [2145,2150,2152,2156,1254,1259,1262,1097,1102,862,867]
  · wct_piece 6 2145 33
  · wct_piece 6 2150 34
  · wct_piece 6 2152 35
  · wct_piece 6 2156 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine93_ready : RoutineReady ⟨93, by decide⟩ routine93 := by
  wct_ready_start 93 2 29
  wct_cases [2157,2162,2164,2168,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 6 2157 37
  · wct_piece 6 2162 38
  · wct_piece 6 2164 39
  · wct_piece 6 2168 40
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine94_ready : RoutineReady ⟨94, by decide⟩ routine94 := by
  wct_ready_start 94 2 30
  wct_cases [2169,2174,2176,2180,1288,1293,1295,1297,1301,862,867]
  · wct_piece 6 2169 41
  · wct_piece 6 2174 42
  · wct_piece 6 2176 43
  · wct_piece 6 2180 44
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine95_ready : RoutineReady ⟨95, by decide⟩ routine95 := by
  wct_ready_start 95 2 31
  wct_cases [2181,2186,2188,2192,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 6 2181 45
  · wct_piece 6 2186 46
  · wct_piece 6 2188 47
  · wct_piece 6 2192 48
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
end W9Machine.Chain
end
