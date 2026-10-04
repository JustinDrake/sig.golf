import SigGolfCandidate.W9Machine.WctRoutineCheck10
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch10_checked :
    (routineBatch10.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch10_checked :
    (routineBatch10.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine320_ready : RoutineReady ⟨320, by decide⟩ routine320 := by
  wct_ready_start 320 10 0
  wct_cases [235592,235598,235600,235602,235606,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 22 235592 16
  · wct_piece 22 235598 17
  · wct_piece 22 235600 18
  · wct_piece 22 235602 19
  · wct_piece 22 235606 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine321_ready : RoutineReady ⟨321, by decide⟩ routine321 := by
  wct_ready_start 321 10 1
  wct_cases [235607,235613,235615,235618,235624,235628,4391,2078,1120,805,811,814]
  · wct_piece 22 235607 21
  · wct_piece 22 235613 22
  · wct_piece 22 235615 23
  · wct_piece 22 235618 24
  · wct_piece 22 235624 25
  · wct_piece 22 235628 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine322_ready : RoutineReady ⟨322, by decide⟩ routine322 := by
  wct_ready_start 322 10 2
  wct_cases [235629,235635,235637,235640,235646,235650,4412,2099,1138,1144,875,881]
  · wct_piece 22 235629 27
  · wct_piece 22 235635 28
  · wct_piece 22 235637 29
  · wct_piece 22 235640 30
  · wct_piece 22 235646 31
  · wct_piece 22 235650 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine323_ready : RoutineReady ⟨323, by decide⟩ routine323 := by
  wct_ready_start 323 10 3
  wct_cases [235651,235657,235659,235662,235668,235672,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 22 235651 33
  · wct_piece 22 235657 34
  · wct_piece 22 235659 35
  · wct_piece 22 235662 36
  · wct_piece 22 235668 37
  · wct_piece 22 235672 38
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine324_ready : RoutineReady ⟨324, by decide⟩ routine324 := by
  wct_ready_start 324 10 4
  wct_cases [235673,235679,235681,235684,235690,235694,4454,2138,2144,2148,1365,875,881]
  · wct_piece 22 235673 39
  · wct_piece 22 235679 40
  · wct_piece 22 235681 41
  · wct_piece 22 235684 42
  · wct_piece 22 235690 43
  · wct_piece 22 235694 44
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine325_ready : RoutineReady ⟨325, by decide⟩ routine325 := by
  wct_ready_start 325 10 5
  wct_cases [235695,235701,235703,235706,235712,235716,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 22 235695 45
  · wct_piece 22 235701 46
  · wct_piece 22 235703 47
  · wct_piece 22 235706 48
  · wct_piece 22 235712 49
  · wct_piece 22 235716 50
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine326_ready : RoutineReady ⟨326, by decide⟩ routine326 := by
  wct_ready_start 326 10 6
  wct_cases [235717,235723,235725,235728,235734,235738,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 22 235717 51
  · wct_piece 22 235723 52
  · wct_piece 22 235725 53
  · wct_piece 22 235728 54
  · wct_piece 22 235734 55
  · wct_piece 22 235738 56
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine327_ready : RoutineReady ⟨327, by decide⟩ routine327 := by
  wct_ready_start 327 10 7
  wct_cases [235739,235745,235747,235750,235756,4514,4520,4524,2681,1365,875,881]
  · wct_piece 22 235739 57
  · wct_piece 22 235745 58
  · wct_piece 22 235747 59
  · wct_piece 22 235750 60
  · wct_piece 22 235756 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine328_ready : RoutineReady ⟨328, by decide⟩ routine328 := by
  wct_ready_start 328 10 8
  wct_cases [235757,235763,235765,235768,235774,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 22 235757 62
  · wct_piece 22 235763 63
  · wct_piece 23 235765 0
  · wct_piece 23 235768 1
  · wct_piece 23 235774 2
  · wct_piece 15 4542 51
  · wct_piece 15 4548 52
  · wct_piece 15 4552 53
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine329_ready : RoutineReady ⟨329, by decide⟩ routine329 := by
  wct_ready_start 329 10 9
  wct_cases [235775,235781,235783,235786,235792,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 23 235775 3
  · wct_piece 23 235781 4
  · wct_piece 23 235783 5
  · wct_piece 23 235786 6
  · wct_piece 23 235792 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine330_ready : RoutineReady ⟨330, by decide⟩ routine330 := by
  wct_ready_start 330 10 10
  wct_cases [235793,235799,235801,235804,235810,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 23 235793 8
  · wct_piece 23 235799 9
  · wct_piece 23 235801 10
  · wct_piece 23 235804 11
  · wct_piece 23 235810 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine331_ready : RoutineReady ⟨331, by decide⟩ routine331 := by
  wct_ready_start 331 10 11
  wct_cases [235811,235817,235819,235822,235828,235830,235834,235227,2681,1365,875,881]
  · wct_piece 23 235811 13
  · wct_piece 23 235817 14
  · wct_piece 23 235819 15
  · wct_piece 23 235822 16
  · wct_piece 23 235828 17
  · wct_piece 23 235830 18
  · wct_piece 23 235834 19
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine332_ready : RoutineReady ⟨332, by decide⟩ routine332 := by
  wct_ready_start 332 10 12
  wct_cases [235835,235841,235843,235846,235852,235854,235858,235251,2705,1386,1392,1396,966]
  · wct_piece 23 235835 20
  · wct_piece 23 235841 21
  · wct_piece 23 235843 22
  · wct_piece 23 235846 23
  · wct_piece 23 235852 24
  · wct_piece 23 235854 25
  · wct_piece 23 235858 26
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine333_ready : RoutineReady ⟨333, by decide⟩ routine333 := by
  wct_ready_start 333 10 13
  wct_cases [235859,235865,235867,235870,235876,235878,235882,235275,2726,2732,2736,1585,966]
  · wct_piece 23 235859 27
  · wct_piece 23 235865 28
  · wct_piece 23 235867 29
  · wct_piece 23 235870 30
  · wct_piece 23 235876 31
  · wct_piece 23 235878 32
  · wct_piece 23 235882 33
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine334_ready : RoutineReady ⟨334, by decide⟩ routine334 := by
  wct_ready_start 334 10 14
  wct_cases [235883,235889,235891,235894,235900,235903,235296,235302,235306,3101,1585,966]
  · wct_piece 23 235883 34
  · wct_piece 23 235889 35
  · wct_piece 23 235891 36
  · wct_piece 23 235894 37
  · wct_piece 23 235900 38
  · wct_piece 23 235903 39
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine335_ready : RoutineReady ⟨335, by decide⟩ routine335 := by
  wct_ready_start 335 10 15
  wct_cases [235904,235910,235912,235915,235921,235923,235925,235929,3101,1585,966]
  · wct_piece 23 235904 40
  · wct_piece 23 235910 41
  · wct_piece 23 235912 42
  · wct_piece 23 235915 43
  · wct_piece 23 235921 44
  · wct_piece 23 235923 45
  · wct_piece 23 235925 46
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine336_ready : RoutineReady ⟨336, by decide⟩ routine336 := by
  wct_ready_start 336 10 16
  wct_cases [235930,235936,3112,1596,982,778,784,787,755,761,763,766]
  · wct_piece 23 235930 48
  · wct_piece 23 235936 49
  · wct_piece 10 3112 5
  · wct_piece 3 1596 37
  · wct_piece 0 982 60
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine337_ready : RoutineReady ⟨337, by decide⟩ routine337 := by
  wct_ready_start 337 10 17
  wct_cases [235937,235943,3123,1607,993,794,800,802,805,811,814]
  · wct_piece 23 235937 50
  · wct_piece 23 235943 51
  · wct_piece 10 3123 8
  · wct_piece 3 1607 40
  · wct_piece 0 993 63
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine338_ready : RoutineReady ⟨338, by decide⟩ routine338 := by
  wct_ready_start 338 10 18
  wct_cases [235944,235950,3134,1618,1000,1006,829,835,755,761,763,766]
  · wct_piece 23 235944 52
  · wct_piece 23 235950 53
  · wct_piece 10 3134 11
  · wct_piece 3 1618 43
  · wct_piece 1 1000 1
  · wct_piece 1 1006 2
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine339_ready : RoutineReady ⟨339, by decide⟩ routine339 := by
  wct_ready_start 339 10 19
  wct_cases [235951,235957,3145,1629,1013,1019,845,851,854,805,811,814]
  · wct_piece 23 235951 54
  · wct_piece 23 235957 55
  · wct_piece 10 3145 14
  · wct_piece 3 1629 46
  · wct_piece 1 1013 4
  · wct_piece 1 1019 5
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine340_ready : RoutineReady ⟨340, by decide⟩ routine340 := by
  wct_ready_start 340 10 20
  wct_cases [235958,235964,3156,1640,1026,1032,864,870,872,875,881]
  · wct_piece 23 235958 56
  · wct_piece 23 235964 57
  · wct_piece 10 3156 17
  · wct_piece 3 1640 49
  · wct_piece 1 1026 7
  · wct_piece 1 1032 8
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine341_ready : RoutineReady ⟨341, by decide⟩ routine341 := by
  wct_ready_start 341 10 21
  wct_cases [235965,235971,3167,1651,1039,1045,1047,1051,901,755,761,763,766]
  · wct_piece 23 235965 58
  · wct_piece 23 235971 59
  · wct_piece 10 3167 20
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
theorem routine342_ready : RoutineReady ⟨342, by decide⟩ routine342 := by
  wct_ready_start 342 10 22
  wct_cases [235972,235978,3178,1662,1058,1064,1067,913,919,805,811,814]
  · wct_piece 23 235972 60
  · wct_piece 23 235978 61
  · wct_piece 10 3178 23
  · wct_piece 3 1662 55
  · wct_piece 1 1058 15
  · wct_piece 1 1064 16
  · wct_piece 1 1067 17
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine343_ready : RoutineReady ⟨343, by decide⟩ routine343 := by
  wct_ready_start 343 10 23
  wct_cases [235979,235985,3189,1673,1074,1080,1083,931,937,940,875,881]
  · wct_piece 23 235979 62
  · wct_piece 23 235985 63
  · wct_piece 10 3189 26
  · wct_piece 3 1673 58
  · wct_piece 1 1074 19
  · wct_piece 1 1080 20
  · wct_piece 1 1083 21
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine344_ready : RoutineReady ⟨344, by decide⟩ routine344 := by
  wct_ready_start 344 10 24
  wct_cases [235986,235992,3200,1684,1090,1096,1099,952,958,960,962,966]
  · wct_piece 24 235986 0
  · wct_piece 24 235992 1
  · wct_piece 10 3200 29
  · wct_piece 3 1684 61
  · wct_piece 1 1090 23
  · wct_piece 1 1096 24
  · wct_piece 1 1099 25
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine345_ready : RoutineReady ⟨345, by decide⟩ routine345 := by
  wct_ready_start 345 10 25
  wct_cases [235993,235999,3211,1695,1106,1112,1114,1116,1120,805,811,814]
  · wct_piece 24 235993 2
  · wct_piece 24 235999 3
  · wct_piece 10 3211 32
  · wct_piece 4 1695 0
  · wct_piece 1 1106 27
  · wct_piece 1 1112 28
  · wct_piece 1 1114 29
  · wct_piece 1 1116 30
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine346_ready : RoutineReady ⟨346, by decide⟩ routine346 := by
  wct_ready_start 346 10 26
  wct_cases [236000,236006,3222,1706,1127,1133,1135,1138,1144,875,881]
  · wct_piece 24 236000 4
  · wct_piece 24 236006 5
  · wct_piece 10 3222 35
  · wct_piece 4 1706 3
  · wct_piece 1 1127 33
  · wct_piece 1 1133 34
  · wct_piece 1 1135 35
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine347_ready : RoutineReady ⟨347, by decide⟩ routine347 := by
  wct_ready_start 347 10 27
  wct_cases [236007,236013,3233,1717,1151,1157,1159,1162,1168,1170,1174,966]
  · wct_piece 24 236007 6
  · wct_piece 24 236013 7
  · wct_piece 10 3233 38
  · wct_piece 4 1717 6
  · wct_piece 1 1151 39
  · wct_piece 1 1157 40
  · wct_piece 1 1159 41
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine348_ready : RoutineReady ⟨348, by decide⟩ routine348 := by
  wct_ready_start 348 10 28
  wct_cases [236014,236020,3244,1724,1730,1734,1187,829,835,755,761,763,766]
  · wct_piece 24 236014 8
  · wct_piece 24 236020 9
  · wct_piece 10 3244 41
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
theorem routine349_ready : RoutineReady ⟨349, by decide⟩ routine349 := by
  wct_ready_start 349 10 29
  wct_cases [236021,236027,3255,3261,3265,1200,845,851,854,805,811,814]
  · wct_piece 24 236021 10
  · wct_piece 24 236027 11
  · wct_piece 10 3255 44
  · wct_piece 10 3261 45
  · wct_piece 10 3265 46
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine350_ready : RoutineReady ⟨350, by decide⟩ routine350 := by
  wct_ready_start 350 10 30
  wct_cases [236028,236034,3276,1758,1764,1768,1213,864,870,872,875,881]
  · wct_piece 24 236028 12
  · wct_piece 24 236034 13
  · wct_piece 10 3276 49
  · wct_piece 4 1758 16
  · wct_piece 4 1764 17
  · wct_piece 4 1768 18
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine351_ready : RoutineReady ⟨351, by decide⟩ routine351 := by
  wct_ready_start 351 10 31
  wct_cases [236035,236041,3287,1775,1781,1223,1229,1233,901,755,761,763,766]
  · wct_piece 24 236035 14
  · wct_piece 24 236041 15
  · wct_piece 10 3287 52
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
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage10 (rank : Fin 728) (hlo : 320 ≤ rank.val) (hhi : rank.val < 352) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 320 ≤ n at hlo
  change n < 352 at hhi
  interval_cases n
  · exact ⟨routine320, routine320_ready⟩
  · exact ⟨routine321, routine321_ready⟩
  · exact ⟨routine322, routine322_ready⟩
  · exact ⟨routine323, routine323_ready⟩
  · exact ⟨routine324, routine324_ready⟩
  · exact ⟨routine325, routine325_ready⟩
  · exact ⟨routine326, routine326_ready⟩
  · exact ⟨routine327, routine327_ready⟩
  · exact ⟨routine328, routine328_ready⟩
  · exact ⟨routine329, routine329_ready⟩
  · exact ⟨routine330, routine330_ready⟩
  · exact ⟨routine331, routine331_ready⟩
  · exact ⟨routine332, routine332_ready⟩
  · exact ⟨routine333, routine333_ready⟩
  · exact ⟨routine334, routine334_ready⟩
  · exact ⟨routine335, routine335_ready⟩
  · exact ⟨routine336, routine336_ready⟩
  · exact ⟨routine337, routine337_ready⟩
  · exact ⟨routine338, routine338_ready⟩
  · exact ⟨routine339, routine339_ready⟩
  · exact ⟨routine340, routine340_ready⟩
  · exact ⟨routine341, routine341_ready⟩
  · exact ⟨routine342, routine342_ready⟩
  · exact ⟨routine343, routine343_ready⟩
  · exact ⟨routine344, routine344_ready⟩
  · exact ⟨routine345, routine345_ready⟩
  · exact ⟨routine346, routine346_ready⟩
  · exact ⟨routine347, routine347_ready⟩
  · exact ⟨routine348, routine348_ready⟩
  · exact ⟨routine349, routine349_ready⟩
  · exact ⟨routine350, routine350_ready⟩
  · exact ⟨routine351, routine351_ready⟩
end W9Machine.Chain
end
