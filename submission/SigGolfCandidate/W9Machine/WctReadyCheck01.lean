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
def routine32 : ChainRoutine := ⟨32, [0, 0, 0, 2, 3, 0, 1], [piece1280, piece1285, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine33 : ChainRoutine := ⟨33, [0, 0, 0, 2, 3, 1, 0], [piece1302, piece1307, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine34 : ChainRoutine := ⟨34, [0, 0, 0, 3, 0, 0, 3], [piece1330, piece1335, piece1337, piece1339, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine35 : ChainRoutine := ⟨35, [0, 0, 0, 3, 0, 1, 2], [piece1344, piece1349, piece1351, piece1353, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine36 : ChainRoutine := ⟨36, [0, 0, 0, 3, 0, 2, 1], [piece1358, piece1363, piece1365, piece1367, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine37 : ChainRoutine := ⟨37, [0, 0, 0, 3, 0, 3, 0], [piece1372, piece1377, piece1379, piece1381, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine38 : ChainRoutine := ⟨38, [0, 0, 0, 3, 1, 0, 2], [piece1386, piece1391, piece1393, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine39 : ChainRoutine := ⟨39, [0, 0, 0, 3, 1, 1, 1], [piece1406, piece1411, piece1413, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine40 : ChainRoutine := ⟨40, [0, 0, 0, 3, 1, 2, 0], [piece1422, piece1427, piece1429, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine41 : ChainRoutine := ⟨41, [0, 0, 0, 3, 2, 0, 1], [piece1438, piece1443, piece1445, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine42 : ChainRoutine := ⟨42, [0, 0, 0, 3, 2, 1, 0], [piece1460, piece1465, piece1467, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine43 : ChainRoutine := ⟨43, [0, 0, 0, 3, 3, 0, 0], [piece1479, piece1484, piece1486, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine44 : ChainRoutine := ⟨44, [0, 0, 1, 0, 0, 2, 3], [piece1503, piece1508, piece1512, piece960, piece775, piece780, piece783, piece754, piece759, piece761, piece764]⟩
def routine45 : ChainRoutine := ⟨45, [0, 0, 1, 0, 0, 3, 2], [piece1513, piece1518, piece1522, piece970, piece789, piece794, piece796, piece799, piece804, piece807]⟩
def routine46 : ChainRoutine := ⟨46, [0, 0, 1, 0, 1, 1, 3], [piece1523, piece1528, piece1532, piece976, piece981, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine47 : ChainRoutine := ⟨47, [0, 0, 1, 0, 1, 2, 2], [piece1533, piece1538, piece1542, piece987, piece992, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine48 : ChainRoutine := ⟨48, [0, 0, 1, 0, 1, 3, 1], [piece1543, piece1548, piece1552, piece998, piece1003, piece852, piece857, piece859, piece862, piece867]⟩
def routine49 : ChainRoutine := ⟨49, [0, 0, 1, 0, 2, 0, 3], [piece1553, piece1558, piece1562, piece1009, piece1014, piece1016, piece1020, piece886, piece754, piece759, piece761, piece764]⟩
def routine50 : ChainRoutine := ⟨50, [0, 0, 1, 0, 2, 1, 2], [piece1563, piece1568, piece1572, piece1026, piece1031, piece1034, piece897, piece902, piece799, piece804, piece807]⟩
def routine51 : ChainRoutine := ⟨51, [0, 0, 1, 0, 2, 2, 1], [piece1573, piece1578, piece1582, piece1040, piece1045, piece1048, piece913, piece918, piece921, piece862, piece867]⟩
def routine52 : ChainRoutine := ⟨52, [0, 0, 1, 0, 2, 3, 0], [piece1583, piece1588, piece1592, piece1054, piece1059, piece1062, piece932, piece937, piece939, piece941, piece945]⟩
def routine53 : ChainRoutine := ⟨53, [0, 0, 1, 0, 3, 0, 2], [piece1593, piece1598, piece1602, piece1068, piece1073, piece1075, piece1077, piece1081, piece799, piece804, piece807]⟩
def routine54 : ChainRoutine := ⟨54, [0, 0, 1, 0, 3, 1, 1], [piece1603, piece1608, piece1612, piece1087, piece1092, piece1094, piece1097, piece1102, piece862, piece867]⟩
def routine55 : ChainRoutine := ⟨55, [0, 0, 1, 0, 3, 2, 0], [piece1613, piece1618, piece1622, piece1108, piece1113, piece1115, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine56 : ChainRoutine := ⟨56, [0, 0, 1, 1, 0, 1, 3], [piece1623, piece1628, piece1633, piece1637, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine57 : ChainRoutine := ⟨57, [0, 0, 1, 1, 0, 2, 2], [piece1638, piece1643, piece1648, piece1652, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine58 : ChainRoutine := ⟨58, [0, 0, 1, 1, 0, 3, 1], [piece1653, piece1658, piece1663, piece1667, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine59 : ChainRoutine := ⟨59, [0, 0, 1, 1, 1, 0, 3], [piece1668, piece1673, piece1678, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine60 : ChainRoutine := ⟨60, [0, 0, 1, 1, 1, 1, 2], [piece1679, piece1684, piece1689, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine61 : ChainRoutine := ⟨61, [0, 0, 1, 1, 1, 2, 1], [piece1690, piece1695, piece1700, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine62 : ChainRoutine := ⟨62, [0, 0, 1, 1, 1, 3, 0], [piece1701, piece1706, piece1711, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine63 : ChainRoutine := ⟨63, [0, 0, 1, 1, 2, 0, 2], [piece1712, piece1717, piece1722, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routineBatch01 : List ChainRoutine := [routine32, routine33, routine34, routine35, routine36, routine37, routine38, routine39, routine40, routine41, routine42, routine43, routine44, routine45, routine46, routine47, routine48, routine49, routine50, routine51, routine52, routine53, routine54, routine55, routine56, routine57, routine58, routine59, routine60, routine61, routine62, routine63]
theorem routineBatch01_checked : (routineBatch01.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
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
  wct_cases [1280,1285,1288,1293,1295,1297,1301,862,867]
  · wct_piece 2 1280 27
  · wct_piece 2 1285 28
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine33_ready : RoutineReady ⟨33, by decide⟩ routine33 := by
  wct_ready_start 33 1 1
  wct_cases [1302,1307,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 2 1302 34
  · wct_piece 2 1307 35
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine34_ready : RoutineReady ⟨34, by decide⟩ routine34 := by
  wct_ready_start 34 1 2
  wct_cases [1330,1335,1337,1339,1343,886,754,759,761,764]
  · wct_piece 2 1330 42
  · wct_piece 2 1335 43
  · wct_piece 2 1337 44
  · wct_piece 2 1339 45
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine35_ready : RoutineReady ⟨35, by decide⟩ routine35 := by
  wct_ready_start 35 1 3
  wct_cases [1344,1349,1351,1353,1357,897,902,799,804,807]
  · wct_piece 2 1344 47
  · wct_piece 2 1349 48
  · wct_piece 2 1351 49
  · wct_piece 2 1353 50
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine36_ready : RoutineReady ⟨36, by decide⟩ routine36 := by
  wct_ready_start 36 1 4
  wct_cases [1358,1363,1365,1367,1371,913,918,921,862,867]
  · wct_piece 2 1358 52
  · wct_piece 2 1363 53
  · wct_piece 2 1365 54
  · wct_piece 2 1367 55
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine37_ready : RoutineReady ⟨37, by decide⟩ routine37 := by
  wct_ready_start 37 1 5
  wct_cases [1372,1377,1379,1381,1385,932,937,939,941,945]
  · wct_piece 2 1372 57
  · wct_piece 2 1377 58
  · wct_piece 2 1379 59
  · wct_piece 2 1381 60
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine38_ready : RoutineReady ⟨38, by decide⟩ routine38 := by
  wct_ready_start 38 1 6
  wct_cases [1386,1391,1393,1396,1401,1405,1081,799,804,807]
  · wct_piece 2 1386 62
  · wct_piece 2 1391 63
  · wct_piece 3 1393 0
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine39_ready : RoutineReady ⟨39, by decide⟩ routine39 := by
  wct_ready_start 39 1 7
  wct_cases [1406,1411,1413,1416,1421,1097,1102,862,867]
  · wct_piece 3 1406 4
  · wct_piece 3 1411 5
  · wct_piece 3 1413 6
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine40_ready : RoutineReady ⟨40, by decide⟩ routine40 := by
  wct_ready_start 40 1 8
  wct_cases [1422,1427,1429,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 3 1422 9
  · wct_piece 3 1427 10
  · wct_piece 3 1429 11
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine41_ready : RoutineReady ⟨41, by decide⟩ routine41 := by
  wct_ready_start 41 1 9
  wct_cases [1438,1443,1445,1448,1453,1455,1459,1301,862,867]
  · wct_piece 3 1438 14
  · wct_piece 3 1443 15
  · wct_piece 3 1445 16
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine42_ready : RoutineReady ⟨42, by decide⟩ routine42 := by
  wct_ready_start 42 1 10
  wct_cases [1460,1465,1467,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 3 1460 21
  · wct_piece 3 1465 22
  · wct_piece 3 1467 23
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine43_ready : RoutineReady ⟨43, by decide⟩ routine43 := by
  wct_ready_start 43 1 11
  wct_cases [1479,1484,1486,1489,1494,1496,1498,1502,945]
  · wct_piece 3 1479 27
  · wct_piece 3 1484 28
  · wct_piece 3 1486 29
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine44_ready : RoutineReady ⟨44, by decide⟩ routine44 := by
  wct_ready_start 44 1 12
  wct_cases [1503,1508,1512,960,775,780,783,754,759,761,764]
  · wct_piece 3 1503 35
  · wct_piece 3 1508 36
  · wct_piece 3 1512 37
  · wct_piece 0 960 60
  · wct_piece 0 775 8
  · wct_piece 0 780 9
  · wct_piece 0 783 10
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine45_ready : RoutineReady ⟨45, by decide⟩ routine45 := by
  wct_ready_start 45 1 13
  wct_cases [1513,1518,1522,970,789,794,796,799,804,807]
  · wct_piece 3 1513 38
  · wct_piece 3 1518 39
  · wct_piece 3 1522 40
  · wct_piece 0 970 63
  · wct_piece 0 789 12
  · wct_piece 0 794 13
  · wct_piece 0 796 14
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine46_ready : RoutineReady ⟨46, by decide⟩ routine46 := by
  wct_ready_start 46 1 14
  wct_cases [1523,1528,1532,976,981,821,826,754,759,761,764]
  · wct_piece 3 1523 41
  · wct_piece 3 1528 42
  · wct_piece 3 1532 43
  · wct_piece 1 976 1
  · wct_piece 1 981 2
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine47_ready : RoutineReady ⟨47, by decide⟩ routine47 := by
  wct_ready_start 47 1 15
  wct_cases [1533,1538,1542,987,992,835,840,843,799,804,807]
  · wct_piece 3 1533 44
  · wct_piece 3 1538 45
  · wct_piece 3 1542 46
  · wct_piece 1 987 4
  · wct_piece 1 992 5
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine48_ready : RoutineReady ⟨48, by decide⟩ routine48 := by
  wct_ready_start 48 1 16
  wct_cases [1543,1548,1552,998,1003,852,857,859,862,867]
  · wct_piece 3 1543 47
  · wct_piece 3 1548 48
  · wct_piece 3 1552 49
  · wct_piece 1 998 7
  · wct_piece 1 1003 8
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine49_ready : RoutineReady ⟨49, by decide⟩ routine49 := by
  wct_ready_start 49 1 17
  wct_cases [1553,1558,1562,1009,1014,1016,1020,886,754,759,761,764]
  · wct_piece 3 1553 50
  · wct_piece 3 1558 51
  · wct_piece 3 1562 52
  · wct_piece 1 1009 10
  · wct_piece 1 1014 11
  · wct_piece 1 1016 12
  · wct_piece 1 1020 13
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine50_ready : RoutineReady ⟨50, by decide⟩ routine50 := by
  wct_ready_start 50 1 18
  wct_cases [1563,1568,1572,1026,1031,1034,897,902,799,804,807]
  · wct_piece 3 1563 53
  · wct_piece 3 1568 54
  · wct_piece 3 1572 55
  · wct_piece 1 1026 15
  · wct_piece 1 1031 16
  · wct_piece 1 1034 17
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine51_ready : RoutineReady ⟨51, by decide⟩ routine51 := by
  wct_ready_start 51 1 19
  wct_cases [1573,1578,1582,1040,1045,1048,913,918,921,862,867]
  · wct_piece 3 1573 56
  · wct_piece 3 1578 57
  · wct_piece 3 1582 58
  · wct_piece 1 1040 19
  · wct_piece 1 1045 20
  · wct_piece 1 1048 21
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine52_ready : RoutineReady ⟨52, by decide⟩ routine52 := by
  wct_ready_start 52 1 20
  wct_cases [1583,1588,1592,1054,1059,1062,932,937,939,941,945]
  · wct_piece 3 1583 59
  · wct_piece 3 1588 60
  · wct_piece 3 1592 61
  · wct_piece 1 1054 23
  · wct_piece 1 1059 24
  · wct_piece 1 1062 25
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine53_ready : RoutineReady ⟨53, by decide⟩ routine53 := by
  wct_ready_start 53 1 21
  wct_cases [1593,1598,1602,1068,1073,1075,1077,1081,799,804,807]
  · wct_piece 3 1593 62
  · wct_piece 3 1598 63
  · wct_piece 4 1602 0
  · wct_piece 1 1068 27
  · wct_piece 1 1073 28
  · wct_piece 1 1075 29
  · wct_piece 1 1077 30
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine54_ready : RoutineReady ⟨54, by decide⟩ routine54 := by
  wct_ready_start 54 1 22
  wct_cases [1603,1608,1612,1087,1092,1094,1097,1102,862,867]
  · wct_piece 4 1603 1
  · wct_piece 4 1608 2
  · wct_piece 4 1612 3
  · wct_piece 1 1087 33
  · wct_piece 1 1092 34
  · wct_piece 1 1094 35
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine55_ready : RoutineReady ⟨55, by decide⟩ routine55 := by
  wct_ready_start 55 1 23
  wct_cases [1613,1618,1622,1108,1113,1115,1118,1123,1125,1129,945]
  · wct_piece 4 1613 4
  · wct_piece 4 1618 5
  · wct_piece 4 1622 6
  · wct_piece 1 1108 39
  · wct_piece 1 1113 40
  · wct_piece 1 1115 41
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine56_ready : RoutineReady ⟨56, by decide⟩ routine56 := by
  wct_ready_start 56 1 24
  wct_cases [1623,1628,1633,1637,1141,821,826,754,759,761,764]
  · wct_piece 4 1623 7
  · wct_piece 4 1628 8
  · wct_piece 4 1633 9
  · wct_piece 4 1637 10
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine57_ready : RoutineReady ⟨57, by decide⟩ routine57 := by
  wct_ready_start 57 1 25
  wct_cases [1638,1643,1648,1652,1153,835,840,843,799,804,807]
  · wct_piece 4 1638 11
  · wct_piece 4 1643 12
  · wct_piece 4 1648 13
  · wct_piece 4 1652 14
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine58_ready : RoutineReady ⟨58, by decide⟩ routine58 := by
  wct_ready_start 58 1 26
  wct_cases [1653,1658,1663,1667,1165,852,857,859,862,867]
  · wct_piece 4 1653 15
  · wct_piece 4 1658 16
  · wct_piece 4 1663 17
  · wct_piece 4 1667 18
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine59_ready : RoutineReady ⟨59, by decide⟩ routine59 := by
  wct_ready_start 59 1 27
  wct_cases [1668,1673,1678,1174,1179,1183,886,754,759,761,764]
  · wct_piece 4 1668 19
  · wct_piece 4 1673 20
  · wct_piece 4 1678 21
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine60_ready : RoutineReady ⟨60, by decide⟩ routine60 := by
  wct_ready_start 60 1 28
  wct_cases [1679,1684,1689,1192,1197,897,902,799,804,807]
  · wct_piece 4 1679 22
  · wct_piece 4 1684 23
  · wct_piece 4 1689 24
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine61_ready : RoutineReady ⟨61, by decide⟩ routine61 := by
  wct_ready_start 61 1 29
  wct_cases [1690,1695,1700,1206,1211,913,918,921,862,867]
  · wct_piece 4 1690 25
  · wct_piece 4 1695 26
  · wct_piece 4 1700 27
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine62_ready : RoutineReady ⟨62, by decide⟩ routine62 := by
  wct_ready_start 62 1 30
  wct_cases [1701,1706,1711,1220,1225,932,937,939,941,945]
  · wct_piece 4 1701 28
  · wct_piece 4 1706 29
  · wct_piece 4 1711 30
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine63_ready : RoutineReady ⟨63, by decide⟩ routine63 := by
  wct_ready_start 63 1 31
  wct_cases [1712,1717,1722,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 4 1712 31
  · wct_piece 4 1717 32
  · wct_piece 4 1722 33
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
end W9Machine.Chain
end
