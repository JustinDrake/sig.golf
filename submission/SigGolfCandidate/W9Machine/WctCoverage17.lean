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
def routine544 : ChainRoutine := ⟨544, [1, 3, 0, 1, 0, 1, 0], [piece239541, piece239546, piece239551, piece239553, piece239555, piece239559, piece239564, piece239568, piece239573, piece239577]⟩
def routine545 : ChainRoutine := ⟨545, [1, 3, 0, 1, 1, 0, 0], [piece239583, piece239588, piece239593, piece239595, piece239597, piece239601, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine546 : ChainRoutine := ⟨546, [1, 3, 0, 2, 0, 0, 0], [piece239602, piece239607, piece239612, piece239614, piece239616, piece239620, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine547 : ChainRoutine := ⟨547, [1, 3, 1, 0, 0, 0, 1], [piece239621, piece239626, piece239631, piece239633, piece239636, piece239641, piece239645, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine548 : ChainRoutine := ⟨548, [1, 3, 1, 0, 0, 1, 0], [piece239646, piece239651, piece239656, piece239658, piece239661, piece239666, piece239670, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine549 : ChainRoutine := ⟨549, [1, 3, 1, 0, 1, 0, 0], [piece239671, piece239676, piece239681, piece239683, piece239686, piece239691, piece239695, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine550 : ChainRoutine := ⟨550, [1, 3, 1, 1, 0, 0, 0], [piece239696, piece239701, piece239706, piece239708, piece239711, piece239716, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine551 : ChainRoutine := ⟨551, [1, 3, 2, 0, 0, 0, 0], [piece239717, piece239722, piece239727, piece239729, piece239732, piece239737, piece239739, piece239743, piece236239, piece2866, piece1502, piece945]⟩
def routine552 : ChainRoutine := ⟨552, [2, 0, 0, 0, 0, 1, 3], [piece239744, piece239749, piece239751, piece4313, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine553 : ChainRoutine := ⟨553, [2, 0, 0, 0, 0, 2, 2], [piece239752, piece239757, piece239759, piece4325, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine554 : ChainRoutine := ⟨554, [2, 0, 0, 0, 0, 3, 1], [piece239760, piece239765, piece239767, piece4337, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine555 : ChainRoutine := ⟨555, [2, 0, 0, 0, 1, 0, 3], [piece239768, piece239773, piece239775, piece4349, piece2096, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine556 : ChainRoutine := ⟨556, [2, 0, 0, 0, 1, 1, 2], [piece239776, piece239781, piece239783, piece4361, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine557 : ChainRoutine := ⟨557, [2, 0, 0, 0, 1, 2, 1], [piece239784, piece239789, piece239791, piece4373, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine558 : ChainRoutine := ⟨558, [2, 0, 0, 0, 1, 3, 0], [piece239792, piece239797, piece239799, piece4385, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine559 : ChainRoutine := ⟨559, [2, 0, 0, 0, 2, 0, 2], [piece239800, piece239805, piece239807, piece4397, piece2144, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine560 : ChainRoutine := ⟨560, [2, 0, 0, 0, 2, 1, 1], [piece239808, piece239813, piece239815, piece4409, piece2156, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine561 : ChainRoutine := ⟨561, [2, 0, 0, 0, 2, 2, 0], [piece239816, piece239821, piece239823, piece4421, piece2168, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine562 : ChainRoutine := ⟨562, [2, 0, 0, 0, 3, 0, 1], [piece239824, piece239829, piece239831, piece4433, piece2180, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine563 : ChainRoutine := ⟨563, [2, 0, 0, 0, 3, 1, 0], [piece239832, piece239837, piece239839, piece4445, piece2192, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine564 : ChainRoutine := ⟨564, [2, 0, 0, 1, 0, 0, 3], [piece239840, piece239845, piece239847, piece4457, piece2201, piece2206, piece2210, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine565 : ChainRoutine := ⟨565, [2, 0, 0, 1, 0, 1, 2], [piece239848, piece239853, piece239855, piece4469, piece4474, piece4478, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine566 : ChainRoutine := ⟨566, [2, 0, 0, 1, 0, 2, 1], [piece239856, piece239861, piece239863, piece4490, piece4495, piece4499, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine567 : ChainRoutine := ⟨567, [2, 0, 0, 1, 0, 3, 0], [piece239864, piece239869, piece239871, piece4511, piece2255, piece2260, piece2264, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine568 : ChainRoutine := ⟨568, [2, 0, 0, 1, 1, 0, 2], [piece239872, piece239877, piece239879, piece4523, piece4528, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine569 : ChainRoutine := ⟨569, [2, 0, 0, 1, 1, 1, 1], [piece239880, piece239885, piece239887, piece4540, piece2287, piece2292, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine570 : ChainRoutine := ⟨570, [2, 0, 0, 1, 1, 2, 0], [piece239888, piece239893, piece239895, piece4552, piece2301, piece2306, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine571 : ChainRoutine := ⟨571, [2, 0, 0, 1, 2, 0, 1], [piece239896, piece239901, piece239903, piece4564, piece2315, piece2320, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routine572 : ChainRoutine := ⟨572, [2, 0, 0, 1, 2, 1, 0], [piece239904, piece239909, piece239911, piece4576, piece4581, piece1470, piece1475, piece1478, piece1320, piece1325, piece1329, piece945]⟩
def routine573 : ChainRoutine := ⟨573, [2, 0, 0, 1, 3, 0, 0], [piece239912, piece239917, piece239919, piece4593, piece2343, piece2348, piece1489, piece1494, piece1496, piece1498, piece1502, piece945]⟩
def routine574 : ChainRoutine := ⟨574, [2, 0, 0, 2, 0, 0, 2], [piece239920, piece239925, piece239927, piece4605, piece2357, piece2362, piece2364, piece2368, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine575 : ChainRoutine := ⟨575, [2, 0, 0, 2, 0, 1, 1], [piece239928, piece239933, piece239935, piece4617, piece2377, piece2382, piece2384, piece2388, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routineBatch17 : List ChainRoutine := [routine544, routine545, routine546, routine547, routine548, routine549, routine550, routine551, routine552, routine553, routine554, routine555, routine556, routine557, routine558, routine559, routine560, routine561, routine562, routine563, routine564, routine565, routine566, routine567, routine568, routine569, routine570, routine571, routine572, routine573, routine574, routine575]
theorem routineBatch17_checked : (routineBatch17.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch17_checked :
    (routineBatch17.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch17_checked :
    (routineBatch17.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine544_ready : RoutineReady ⟨544, by decide⟩ routine544 := by
  wct_ready_start 544 17 0
  wct_cases [239541,239546,239551,239553,239555,239559,239564,239568,239573,239577]
  · wct_piece 38 239541 28
  · wct_piece 38 239546 29
  · wct_piece 38 239551 30
  · wct_piece 38 239553 31
  · wct_piece 38 239555 32
  · wct_piece 38 239559 33
  · wct_piece 38 239564 34
  · wct_piece 38 239568 35
  · wct_piece 38 239573 36
  · wct_piece 38 239577 37
theorem routine545_ready : RoutineReady ⟨545, by decide⟩ routine545 := by
  wct_ready_start 545 17 1
  wct_cases [239583,239588,239593,239595,239597,239601,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 38 239583 38
  · wct_piece 38 239588 39
  · wct_piece 38 239593 40
  · wct_piece 38 239595 41
  · wct_piece 38 239597 42
  · wct_piece 38 239601 43
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine546_ready : RoutineReady ⟨546, by decide⟩ routine546 := by
  wct_ready_start 546 17 2
  wct_cases [239602,239607,239612,239614,239616,239620,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 38 239602 44
  · wct_piece 38 239607 45
  · wct_piece 38 239612 46
  · wct_piece 38 239614 47
  · wct_piece 38 239616 48
  · wct_piece 38 239620 49
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine547_ready : RoutineReady ⟨547, by decide⟩ routine547 := by
  wct_ready_start 547 17 3
  wct_cases [239621,239626,239631,239633,239636,239641,239645,235565,2481,1301,862,867]
  · wct_piece 38 239621 50
  · wct_piece 38 239626 51
  · wct_piece 38 239631 52
  · wct_piece 38 239633 53
  · wct_piece 38 239636 54
  · wct_piece 38 239641 55
  · wct_piece 38 239645 56
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine548_ready : RoutineReady ⟨548, by decide⟩ routine548 := by
  wct_ready_start 548 17 4
  wct_cases [239646,239651,239656,239658,239661,239666,239670,2503,1320,1325,1329,945]
  · wct_piece 38 239646 57
  · wct_piece 38 239651 58
  · wct_piece 38 239656 59
  · wct_piece 38 239658 60
  · wct_piece 38 239661 61
  · wct_piece 38 239666 62
  · wct_piece 38 239670 63
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine549_ready : RoutineReady ⟨549, by decide⟩ routine549 := by
  wct_ready_start 549 17 5
  wct_cases [239671,239676,239681,239683,239686,239691,239695,2522,2527,2531,1502,945]
  · wct_piece 39 239671 0
  · wct_piece 39 239676 1
  · wct_piece 39 239681 2
  · wct_piece 39 239683 3
  · wct_piece 39 239686 4
  · wct_piece 39 239691 5
  · wct_piece 39 239695 6
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine550_ready : RoutineReady ⟨550, by decide⟩ routine550 := by
  wct_ready_start 550 17 6
  wct_cases [239696,239701,239706,239708,239711,239716,235628,235633,235637,2866,1502,945]
  · wct_piece 39 239696 7
  · wct_piece 39 239701 8
  · wct_piece 39 239706 9
  · wct_piece 39 239708 10
  · wct_piece 39 239711 11
  · wct_piece 39 239716 12
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine551_ready : RoutineReady ⟨551, by decide⟩ routine551 := by
  wct_ready_start 551 17 7
  wct_cases [239717,239722,239727,239729,239732,239737,239739,239743,236239,2866,1502,945]
  · wct_piece 39 239717 13
  · wct_piece 39 239722 14
  · wct_piece 39 239727 15
  · wct_piece 39 239729 16
  · wct_piece 39 239732 17
  · wct_piece 39 239737 18
  · wct_piece 39 239739 19
  · wct_piece 39 239743 20
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine552_ready : RoutineReady ⟨552, by decide⟩ routine552 := by
  wct_ready_start 552 17 8
  wct_cases [239744,239749,239751,4313,2060,1141,821,826,754,759,761,764]
  · wct_piece 39 239744 21
  · wct_piece 39 239749 22
  · wct_piece 39 239751 23
  · wct_piece 16 4313 31
  · wct_piece 6 2060 4
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine553_ready : RoutineReady ⟨553, by decide⟩ routine553 := by
  wct_ready_start 553 17 9
  wct_cases [239752,239757,239759,4325,2072,1153,835,840,843,799,804,807]
  · wct_piece 39 239752 24
  · wct_piece 39 239757 25
  · wct_piece 39 239759 26
  · wct_piece 16 4325 35
  · wct_piece 6 2072 8
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine554_ready : RoutineReady ⟨554, by decide⟩ routine554 := by
  wct_ready_start 554 17 10
  wct_cases [239760,239765,239767,4337,2084,1165,852,857,859,862,867]
  · wct_piece 39 239760 27
  · wct_piece 39 239765 28
  · wct_piece 39 239767 29
  · wct_piece 16 4337 39
  · wct_piece 6 2084 12
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine555_ready : RoutineReady ⟨555, by decide⟩ routine555 := by
  wct_ready_start 555 17 11
  wct_cases [239768,239773,239775,4349,2096,1174,1179,1183,886,754,759,761,764]
  · wct_piece 39 239768 30
  · wct_piece 39 239773 31
  · wct_piece 39 239775 32
  · wct_piece 16 4349 43
  · wct_piece 6 2096 16
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine556_ready : RoutineReady ⟨556, by decide⟩ routine556 := by
  wct_ready_start 556 17 12
  wct_cases [239776,239781,239783,4361,2108,1192,1197,897,902,799,804,807]
  · wct_piece 39 239776 33
  · wct_piece 39 239781 34
  · wct_piece 39 239783 35
  · wct_piece 16 4361 47
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine557_ready : RoutineReady ⟨557, by decide⟩ routine557 := by
  wct_ready_start 557 17 13
  wct_cases [239784,239789,239791,4373,2120,1206,1211,913,918,921,862,867]
  · wct_piece 39 239784 36
  · wct_piece 39 239789 37
  · wct_piece 39 239791 38
  · wct_piece 16 4373 51
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine558_ready : RoutineReady ⟨558, by decide⟩ routine558 := by
  wct_ready_start 558 17 14
  wct_cases [239792,239797,239799,4385,2132,1220,1225,932,937,939,941,945]
  · wct_piece 39 239792 39
  · wct_piece 39 239797 40
  · wct_piece 39 239799 41
  · wct_piece 16 4385 55
  · wct_piece 6 2132 28
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine559_ready : RoutineReady ⟨559, by decide⟩ routine559 := by
  wct_ready_start 559 17 15
  wct_cases [239800,239805,239807,4397,2144,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 39 239800 42
  · wct_piece 39 239805 43
  · wct_piece 39 239807 44
  · wct_piece 16 4397 59
  · wct_piece 6 2144 32
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine560_ready : RoutineReady ⟨560, by decide⟩ routine560 := by
  wct_ready_start 560 17 16
  wct_cases [239808,239813,239815,4409,2156,1254,1259,1262,1097,1102,862,867]
  · wct_piece 39 239808 45
  · wct_piece 39 239813 46
  · wct_piece 39 239815 47
  · wct_piece 16 4409 63
  · wct_piece 6 2156 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine561_ready : RoutineReady ⟨561, by decide⟩ routine561 := by
  wct_ready_start 561 17 17
  wct_cases [239816,239821,239823,4421,2168,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 39 239816 48
  · wct_piece 39 239821 49
  · wct_piece 39 239823 50
  · wct_piece 17 4421 3
  · wct_piece 6 2168 40
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine562_ready : RoutineReady ⟨562, by decide⟩ routine562 := by
  wct_ready_start 562 17 18
  wct_cases [239824,239829,239831,4433,2180,1288,1293,1295,1297,1301,862,867]
  · wct_piece 39 239824 51
  · wct_piece 39 239829 52
  · wct_piece 39 239831 53
  · wct_piece 17 4433 7
  · wct_piece 6 2180 44
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine563_ready : RoutineReady ⟨563, by decide⟩ routine563 := by
  wct_ready_start 563 17 19
  wct_cases [239832,239837,239839,4445,2192,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 39 239832 54
  · wct_piece 39 239837 55
  · wct_piece 39 239839 56
  · wct_piece 17 4445 11
  · wct_piece 6 2192 48
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine564_ready : RoutineReady ⟨564, by decide⟩ routine564 := by
  wct_ready_start 564 17 20
  wct_cases [239840,239845,239847,4457,2201,2206,2210,1343,886,754,759,761,764]
  · wct_piece 39 239840 57
  · wct_piece 39 239845 58
  · wct_piece 39 239847 59
  · wct_piece 17 4457 15
  · wct_piece 6 2201 51
  · wct_piece 6 2206 52
  · wct_piece 6 2210 53
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine565_ready : RoutineReady ⟨565, by decide⟩ routine565 := by
  wct_ready_start 565 17 21
  wct_cases [239848,239853,239855,4469,4474,4478,1357,897,902,799,804,807]
  · wct_piece 39 239848 60
  · wct_piece 39 239853 61
  · wct_piece 39 239855 62
  · wct_piece 17 4469 19
  · wct_piece 17 4474 20
  · wct_piece 17 4478 21
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine566_ready : RoutineReady ⟨566, by decide⟩ routine566 := by
  wct_ready_start 566 17 22
  wct_cases [239856,239861,239863,4490,4495,4499,1371,913,918,921,862,867]
  · wct_piece 39 239856 63
  · wct_piece 40 239861 0
  · wct_piece 40 239863 1
  · wct_piece 17 4490 25
  · wct_piece 17 4495 26
  · wct_piece 17 4499 27
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine567_ready : RoutineReady ⟨567, by decide⟩ routine567 := by
  wct_ready_start 567 17 23
  wct_cases [239864,239869,239871,4511,2255,2260,2264,1385,932,937,939,941,945]
  · wct_piece 40 239864 2
  · wct_piece 40 239869 3
  · wct_piece 40 239871 4
  · wct_piece 17 4511 31
  · wct_piece 7 2255 2
  · wct_piece 7 2260 3
  · wct_piece 7 2264 4
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine568_ready : RoutineReady ⟨568, by decide⟩ routine568 := by
  wct_ready_start 568 17 24
  wct_cases [239872,239877,239879,4523,4528,1396,1401,1405,1081,799,804,807]
  · wct_piece 40 239872 5
  · wct_piece 40 239877 6
  · wct_piece 40 239879 7
  · wct_piece 17 4523 35
  · wct_piece 17 4528 36
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine569_ready : RoutineReady ⟨569, by decide⟩ routine569 := by
  wct_ready_start 569 17 25
  wct_cases [239880,239885,239887,4540,2287,2292,1416,1421,1097,1102,862,867]
  · wct_piece 40 239880 8
  · wct_piece 40 239885 9
  · wct_piece 40 239887 10
  · wct_piece 17 4540 40
  · wct_piece 7 2287 11
  · wct_piece 7 2292 12
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine570_ready : RoutineReady ⟨570, by decide⟩ routine570 := by
  wct_ready_start 570 17 26
  wct_cases [239888,239893,239895,4552,2301,2306,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 40 239888 11
  · wct_piece 40 239893 12
  · wct_piece 40 239895 13
  · wct_piece 17 4552 44
  · wct_piece 7 2301 15
  · wct_piece 7 2306 16
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine571_ready : RoutineReady ⟨571, by decide⟩ routine571 := by
  wct_ready_start 571 17 27
  wct_cases [239896,239901,239903,4564,2315,2320,1448,1453,1455,1459,1301,862,867]
  · wct_piece 40 239896 14
  · wct_piece 40 239901 15
  · wct_piece 40 239903 16
  · wct_piece 17 4564 48
  · wct_piece 7 2315 19
  · wct_piece 7 2320 20
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine572_ready : RoutineReady ⟨572, by decide⟩ routine572 := by
  wct_ready_start 572 17 28
  wct_cases [239904,239909,239911,4576,4581,1470,1475,1478,1320,1325,1329,945]
  · wct_piece 40 239904 17
  · wct_piece 40 239909 18
  · wct_piece 40 239911 19
  · wct_piece 17 4576 52
  · wct_piece 17 4581 53
  · wct_piece 3 1470 24
  · wct_piece 3 1475 25
  · wct_piece 3 1478 26
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine573_ready : RoutineReady ⟨573, by decide⟩ routine573 := by
  wct_ready_start 573 17 29
  wct_cases [239912,239917,239919,4593,2343,2348,1489,1494,1496,1498,1502,945]
  · wct_piece 40 239912 20
  · wct_piece 40 239917 21
  · wct_piece 40 239919 22
  · wct_piece 17 4593 57
  · wct_piece 7 2343 27
  · wct_piece 7 2348 28
  · wct_piece 3 1489 30
  · wct_piece 3 1494 31
  · wct_piece 3 1496 32
  · wct_piece 3 1498 33
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine574_ready : RoutineReady ⟨574, by decide⟩ routine574 := by
  wct_ready_start 574 17 30
  wct_cases [239920,239925,239927,4605,2357,2362,2364,2368,1937,1081,799,804,807]
  · wct_piece 40 239920 23
  · wct_piece 40 239925 24
  · wct_piece 40 239927 25
  · wct_piece 17 4605 61
  · wct_piece 7 2357 31
  · wct_piece 7 2362 32
  · wct_piece 7 2364 33
  · wct_piece 7 2368 34
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine575_ready : RoutineReady ⟨575, by decide⟩ routine575 := by
  wct_ready_start 575 17 31
  wct_cases [239928,239933,239935,4617,2377,2382,2384,2388,1956,1097,1102,862,867]
  · wct_piece 40 239928 26
  · wct_piece 40 239933 27
  · wct_piece 40 239935 28
  · wct_piece 18 4617 1
  · wct_piece 7 2377 37
  · wct_piece 7 2382 38
  · wct_piece 7 2384 39
  · wct_piece 7 2388 40
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage17 (rank : Fin 728) (hlo : 544 ≤ rank.val) (hhi : rank.val < 576) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 544 ≤ n at hlo
  change n < 576 at hhi
  interval_cases n
  · exact ⟨routine544, routine544_ready⟩
  · exact ⟨routine545, routine545_ready⟩
  · exact ⟨routine546, routine546_ready⟩
  · exact ⟨routine547, routine547_ready⟩
  · exact ⟨routine548, routine548_ready⟩
  · exact ⟨routine549, routine549_ready⟩
  · exact ⟨routine550, routine550_ready⟩
  · exact ⟨routine551, routine551_ready⟩
  · exact ⟨routine552, routine552_ready⟩
  · exact ⟨routine553, routine553_ready⟩
  · exact ⟨routine554, routine554_ready⟩
  · exact ⟨routine555, routine555_ready⟩
  · exact ⟨routine556, routine556_ready⟩
  · exact ⟨routine557, routine557_ready⟩
  · exact ⟨routine558, routine558_ready⟩
  · exact ⟨routine559, routine559_ready⟩
  · exact ⟨routine560, routine560_ready⟩
  · exact ⟨routine561, routine561_ready⟩
  · exact ⟨routine562, routine562_ready⟩
  · exact ⟨routine563, routine563_ready⟩
  · exact ⟨routine564, routine564_ready⟩
  · exact ⟨routine565, routine565_ready⟩
  · exact ⟨routine566, routine566_ready⟩
  · exact ⟨routine567, routine567_ready⟩
  · exact ⟨routine568, routine568_ready⟩
  · exact ⟨routine569, routine569_ready⟩
  · exact ⟨routine570, routine570_ready⟩
  · exact ⟨routine571, routine571_ready⟩
  · exact ⟨routine572, routine572_ready⟩
  · exact ⟨routine573, routine573_ready⟩
  · exact ⟨routine574, routine574_ready⟩
  · exact ⟨routine575, routine575_ready⟩
end W9Machine.Chain
end
