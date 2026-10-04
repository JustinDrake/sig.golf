import SigGolfCandidate.W9Machine.WctRoutineCheck09
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch09_checked :
    (routineBatch09.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch09_checked :
    (routineBatch09.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine288_ready : RoutineReady ⟨288, by decide⟩ routine288 := by
  wct_ready_start 288 9 0
  wct_cases [235650,235656,235659,235665,235667,235671,4412,2099,1138,1144,875,881]
  · wct_piece 19 235650 32
  · wct_piece 19 235656 33
  · wct_piece 19 235659 34
  · wct_piece 19 235665 35
  · wct_piece 19 235667 36
  · wct_piece 19 235671 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine289_ready : RoutineReady ⟨289, by decide⟩ routine289 := by
  wct_ready_start 289 9 1
  wct_cases [235672,235678,235681,235687,235689,235693,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 19 235672 38
  · wct_piece 19 235678 39
  · wct_piece 19 235681 40
  · wct_piece 19 235687 41
  · wct_piece 19 235689 42
  · wct_piece 19 235693 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine290_ready : RoutineReady ⟨290, by decide⟩ routine290 := by
  wct_ready_start 290 9 2
  wct_cases [235694,235700,235703,235709,235711,235715,4454,2138,2144,2148,1365,875,881]
  · wct_piece 19 235694 44
  · wct_piece 19 235700 45
  · wct_piece 19 235703 46
  · wct_piece 19 235709 47
  · wct_piece 19 235711 48
  · wct_piece 19 235715 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine291_ready : RoutineReady ⟨291, by decide⟩ routine291 := by
  wct_ready_start 291 9 3
  wct_cases [235716,235722,235725,235731,235733,235737,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 19 235716 50
  · wct_piece 19 235722 51
  · wct_piece 19 235725 52
  · wct_piece 19 235731 53
  · wct_piece 19 235733 54
  · wct_piece 19 235737 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine292_ready : RoutineReady ⟨292, by decide⟩ routine292 := by
  wct_ready_start 292 9 4
  wct_cases [235738,235744,235747,235753,235755,235759,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 19 235738 56
  · wct_piece 19 235744 57
  · wct_piece 19 235747 58
  · wct_piece 19 235753 59
  · wct_piece 19 235755 60
  · wct_piece 19 235759 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine293_ready : RoutineReady ⟨293, by decide⟩ routine293 := by
  wct_ready_start 293 9 5
  wct_cases [235760,235766,235769,235775,235778,4514,4520,4524,2681,1365,875,881]
  · wct_piece 19 235760 62
  · wct_piece 19 235766 63
  · wct_piece 20 235769 0
  · wct_piece 20 235775 1
  · wct_piece 20 235778 2
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine294_ready : RoutineReady ⟨294, by decide⟩ routine294 := by
  wct_ready_start 294 9 6
  wct_cases [235779,235785,235788,235794,235797,235803,235807,2705,1386,1392,1396,966]
  · wct_piece 20 235779 3
  · wct_piece 20 235785 4
  · wct_piece 20 235788 5
  · wct_piece 20 235794 6
  · wct_piece 20 235797 7
  · wct_piece 20 235803 8
  · wct_piece 20 235807 9
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine295_ready : RoutineReady ⟨295, by decide⟩ routine295 := by
  wct_ready_start 295 9 7
  wct_cases [235808,235814,235817,235823,235826,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 20 235808 10
  · wct_piece 20 235814 11
  · wct_piece 20 235817 12
  · wct_piece 20 235823 13
  · wct_piece 20 235826 14
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine296_ready : RoutineReady ⟨296, by decide⟩ routine296 := by
  wct_ready_start 296 9 8
  wct_cases [235827,235833,235836,235842,235845,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 20 235827 15
  · wct_piece 20 235833 16
  · wct_piece 20 235836 17
  · wct_piece 20 235842 18
  · wct_piece 20 235845 19
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine297_ready : RoutineReady ⟨297, by decide⟩ routine297 := by
  wct_ready_start 297 9 9
  wct_cases [235846,235852,235855,235861,235863,235865,235869,2681,1365,875,881]
  · wct_piece 20 235846 20
  · wct_piece 20 235852 21
  · wct_piece 20 235855 22
  · wct_piece 20 235861 23
  · wct_piece 20 235863 24
  · wct_piece 20 235865 25
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine298_ready : RoutineReady ⟨298, by decide⟩ routine298 := by
  wct_ready_start 298 9 10
  wct_cases [235870,235876,235879,235885,235887,235889,235893,2705,1386,1392,1396,966]
  · wct_piece 20 235870 27
  · wct_piece 20 235876 28
  · wct_piece 20 235879 29
  · wct_piece 20 235885 30
  · wct_piece 20 235887 31
  · wct_piece 20 235889 32
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine299_ready : RoutineReady ⟨299, by decide⟩ routine299 := by
  wct_ready_start 299 9 11
  wct_cases [235894,235900,235903,235909,235911,235913,235917,2726,2732,2736,1585,966]
  · wct_piece 20 235894 34
  · wct_piece 20 235900 35
  · wct_piece 20 235903 36
  · wct_piece 20 235909 37
  · wct_piece 20 235911 38
  · wct_piece 20 235913 39
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine300_ready : RoutineReady ⟨300, by decide⟩ routine300 := by
  wct_ready_start 300 9 12
  wct_cases [235918,235924,235927,235933,235935,235938,235944,235948,3101,1585,966]
  · wct_piece 20 235918 41
  · wct_piece 20 235924 42
  · wct_piece 20 235927 43
  · wct_piece 20 235933 44
  · wct_piece 20 235935 45
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine301_ready : RoutineReady ⟨301, by decide⟩ routine301 := by
  wct_ready_start 301 9 13
  wct_cases [235949,235955,235957,235959,235963,2751,1411,901,755,761,763,766]
  · wct_piece 20 235949 49
  · wct_piece 20 235955 50
  · wct_piece 20 235957 51
  · wct_piece 20 235959 52
  · wct_piece 20 235963 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine302_ready : RoutineReady ⟨302, by decide⟩ routine302 := by
  wct_ready_start 302 9 14
  wct_cases [235964,235970,235972,235974,235978,2766,1426,913,919,805,811,814]
  · wct_piece 20 235964 54
  · wct_piece 20 235970 55
  · wct_piece 20 235972 56
  · wct_piece 20 235974 57
  · wct_piece 20 235978 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine303_ready : RoutineReady ⟨303, by decide⟩ routine303 := by
  wct_ready_start 303 9 15
  wct_cases [235979,235985,235987,235989,235993,2781,1441,931,937,940,875,881]
  · wct_piece 20 235979 59
  · wct_piece 20 235985 60
  · wct_piece 20 235987 61
  · wct_piece 20 235989 62
  · wct_piece 20 235993 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine304_ready : RoutineReady ⟨304, by decide⟩ routine304 := by
  wct_ready_start 304 9 16
  wct_cases [235994,236000,236002,236004,236008,2796,1456,952,958,960,962,966]
  · wct_piece 21 235994 0
  · wct_piece 21 236000 1
  · wct_piece 21 236002 2
  · wct_piece 21 236004 3
  · wct_piece 21 236008 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine305_ready : RoutineReady ⟨305, by decide⟩ routine305 := by
  wct_ready_start 305 9 17
  wct_cases [236009,236015,236017,236019,236023,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 21 236009 5
  · wct_piece 21 236015 6
  · wct_piece 21 236017 7
  · wct_piece 21 236019 8
  · wct_piece 21 236023 9
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine306_ready : RoutineReady ⟨306, by decide⟩ routine306 := by
  wct_ready_start 306 9 18
  wct_cases [236024,236030,236032,236034,236038,2826,1490,1496,1138,1144,875,881]
  · wct_piece 21 236024 10
  · wct_piece 21 236030 11
  · wct_piece 21 236032 12
  · wct_piece 21 236034 13
  · wct_piece 21 236038 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine307_ready : RoutineReady ⟨307, by decide⟩ routine307 := by
  wct_ready_start 307 9 19
  wct_cases [236039,236045,236047,236049,236053,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 21 236039 15
  · wct_piece 21 236045 16
  · wct_piece 21 236047 17
  · wct_piece 21 236049 18
  · wct_piece 21 236053 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine308_ready : RoutineReady ⟨308, by decide⟩ routine308 := by
  wct_ready_start 308 9 20
  wct_cases [236054,236060,236062,236064,236068,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 21 236054 20
  · wct_piece 21 236060 21
  · wct_piece 21 236062 22
  · wct_piece 21 236064 23
  · wct_piece 21 236068 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine309_ready : RoutineReady ⟨309, by decide⟩ routine309 := by
  wct_ready_start 309 9 21
  wct_cases [236069,236075,236077,236079,236083,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 21 236069 25
  · wct_piece 21 236075 26
  · wct_piece 21 236077 27
  · wct_piece 21 236079 28
  · wct_piece 21 236083 29
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine310_ready : RoutineReady ⟨310, by decide⟩ routine310 := by
  wct_ready_start 310 9 22
  wct_cases [236084,236090,236092,236094,236098,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 21 236084 30
  · wct_piece 21 236090 31
  · wct_piece 21 236092 32
  · wct_piece 21 236094 33
  · wct_piece 21 236098 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine311_ready : RoutineReady ⟨311, by decide⟩ routine311 := by
  wct_ready_start 311 9 23
  wct_cases [236099,236105,236107,236109,236113,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 21 236099 35
  · wct_piece 21 236105 36
  · wct_piece 21 236107 37
  · wct_piece 21 236109 38
  · wct_piece 21 236113 39
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine312_ready : RoutineReady ⟨312, by decide⟩ routine312 := by
  wct_ready_start 312 9 24
  wct_cases [236114,236120,236122,236124,236128,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 21 236114 40
  · wct_piece 21 236120 41
  · wct_piece 21 236122 42
  · wct_piece 21 236124 43
  · wct_piece 21 236128 44
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine313_ready : RoutineReady ⟨313, by decide⟩ routine313 := by
  wct_ready_start 313 9 25
  wct_cases [236129,236135,236137,236139,236143,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 21 236129 45
  · wct_piece 21 236135 46
  · wct_piece 21 236137 47
  · wct_piece 21 236139 48
  · wct_piece 21 236143 49
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine314_ready : RoutineReady ⟨314, by decide⟩ routine314 := by
  wct_ready_start 314 9 26
  wct_cases [236144,236150,236152,236154,236158,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 21 236144 50
  · wct_piece 21 236150 51
  · wct_piece 21 236152 52
  · wct_piece 21 236154 53
  · wct_piece 21 236158 54
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine315_ready : RoutineReady ⟨315, by decide⟩ routine315 := by
  wct_ready_start 315 9 27
  wct_cases [236159,236165,236167,236169,236173,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 21 236159 55
  · wct_piece 21 236165 56
  · wct_piece 21 236167 57
  · wct_piece 21 236169 58
  · wct_piece 21 236173 59
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine316_ready : RoutineReady ⟨316, by decide⟩ routine316 := by
  wct_ready_start 316 9 28
  wct_cases [236174,236180,236182,236184,236188,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 21 236174 60
  · wct_piece 21 236180 61
  · wct_piece 21 236182 62
  · wct_piece 21 236184 63
  · wct_piece 22 236188 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine317_ready : RoutineReady ⟨317, by decide⟩ routine317 := by
  wct_ready_start 317 9 29
  wct_cases [236189,236195,236197,236199,236203,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 22 236189 1
  · wct_piece 22 236195 2
  · wct_piece 22 236197 3
  · wct_piece 22 236199 4
  · wct_piece 22 236203 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine318_ready : RoutineReady ⟨318, by decide⟩ routine318 := by
  wct_ready_start 318 9 30
  wct_cases [236204,236210,236212,236214,236218,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 22 236204 6
  · wct_piece 22 236210 7
  · wct_piece 22 236212 8
  · wct_piece 22 236214 9
  · wct_piece 22 236218 10
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine319_ready : RoutineReady ⟨319, by decide⟩ routine319 := by
  wct_ready_start 319 9 31
  wct_cases [236219,236225,236227,236229,236233,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 22 236219 11
  · wct_piece 22 236225 12
  · wct_piece 22 236227 13
  · wct_piece 22 236229 14
  · wct_piece 22 236233 15
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage09 (rank : Fin 728) (hlo : 288 ≤ rank.val) (hhi : rank.val < 320) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 288 ≤ n at hlo
  change n < 320 at hhi
  interval_cases n
  · exact ⟨routine288, routine288_ready⟩
  · exact ⟨routine289, routine289_ready⟩
  · exact ⟨routine290, routine290_ready⟩
  · exact ⟨routine291, routine291_ready⟩
  · exact ⟨routine292, routine292_ready⟩
  · exact ⟨routine293, routine293_ready⟩
  · exact ⟨routine294, routine294_ready⟩
  · exact ⟨routine295, routine295_ready⟩
  · exact ⟨routine296, routine296_ready⟩
  · exact ⟨routine297, routine297_ready⟩
  · exact ⟨routine298, routine298_ready⟩
  · exact ⟨routine299, routine299_ready⟩
  · exact ⟨routine300, routine300_ready⟩
  · exact ⟨routine301, routine301_ready⟩
  · exact ⟨routine302, routine302_ready⟩
  · exact ⟨routine303, routine303_ready⟩
  · exact ⟨routine304, routine304_ready⟩
  · exact ⟨routine305, routine305_ready⟩
  · exact ⟨routine306, routine306_ready⟩
  · exact ⟨routine307, routine307_ready⟩
  · exact ⟨routine308, routine308_ready⟩
  · exact ⟨routine309, routine309_ready⟩
  · exact ⟨routine310, routine310_ready⟩
  · exact ⟨routine311, routine311_ready⟩
  · exact ⟨routine312, routine312_ready⟩
  · exact ⟨routine313, routine313_ready⟩
  · exact ⟨routine314, routine314_ready⟩
  · exact ⟨routine315, routine315_ready⟩
  · exact ⟨routine316, routine316_ready⟩
  · exact ⟨routine317, routine317_ready⟩
  · exact ⟨routine318, routine318_ready⟩
  · exact ⟨routine319, routine319_ready⟩
end W9Machine.Chain
end
