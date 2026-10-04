import SigGolfCandidate.W9Machine.WctRoutineCheck15
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch15_checked :
    (routineBatch15.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch15_checked :
    (routineBatch15.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine480_ready : RoutineReady ⟨480, by decide⟩ routine480 := by
  wct_ready_start 480 15 0
  wct_cases [238631,238637,238643,238649,238655,238659,238665,238667,238671,966]
  · wct_piece 31 238631 28
  · wct_piece 31 238637 29
  · wct_piece 31 238643 30
  · wct_piece 31 238649 31
  · wct_piece 31 238655 32
  · wct_piece 31 238659 33
  · wct_piece 31 238665 34
  · wct_piece 31 238667 35
  · wct_piece 31 238671 36
  · wct_piece 0 966 57
theorem routine481_ready : RoutineReady ⟨481, by decide⟩ routine481 := by
  wct_ready_start 481 15 1
  wct_cases [238672,238678,238684,238690,238696,238702,238706,875,881]
  · wct_piece 31 238672 37
  · wct_piece 31 238678 38
  · wct_piece 31 238684 39
  · wct_piece 31 238690 40
  · wct_piece 31 238696 41
  · wct_piece 31 238702 42
  · wct_piece 31 238706 43
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine482_ready : RoutineReady ⟨482, by decide⟩ routine482 := by
  wct_ready_start 482 15 2
  wct_cases [238707,238713,238719,238725,238731,238737,238743,238747,966]
  · wct_piece 31 238707 44
  · wct_piece 31 238713 45
  · wct_piece 31 238719 46
  · wct_piece 31 238725 47
  · wct_piece 31 238731 48
  · wct_piece 31 238737 49
  · wct_piece 31 238743 50
  · wct_piece 31 238747 51
  · wct_piece 0 966 57
theorem routine483_ready : RoutineReady ⟨483, by decide⟩ routine483 := by
  wct_ready_start 483 15 3
  wct_cases [238748,238754,238760,235557,235563,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 31 238748 52
  · wct_piece 31 238754 53
  · wct_piece 31 238760 54
  · wct_piece 19 235557 8
  · wct_piece 19 235563 9
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine484_ready : RoutineReady ⟨484, by decide⟩ routine484 := by
  wct_ready_start 484 15 4
  wct_cases [238761,238767,238773,235573,235579,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 31 238761 55
  · wct_piece 31 238767 56
  · wct_piece 31 238773 57
  · wct_piece 19 235573 12
  · wct_piece 19 235579 13
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine485_ready : RoutineReady ⟨485, by decide⟩ routine485 := by
  wct_ready_start 485 15 5
  wct_cases [238774,238780,238786,238792,238798,238800,238804,238810,238814,966]
  · wct_piece 31 238774 58
  · wct_piece 31 238780 59
  · wct_piece 31 238786 60
  · wct_piece 31 238792 61
  · wct_piece 31 238798 62
  · wct_piece 31 238800 63
  · wct_piece 32 238804 0
  · wct_piece 32 238810 1
  · wct_piece 32 238814 2
  · wct_piece 0 966 57
theorem routine486_ready : RoutineReady ⟨486, by decide⟩ routine486 := by
  wct_ready_start 486 15 6
  wct_cases [238815,238821,238827,238833,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 32 238815 3
  · wct_piece 32 238821 4
  · wct_piece 32 238827 5
  · wct_piece 32 238833 6
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine487_ready : RoutineReady ⟨487, by decide⟩ routine487 := by
  wct_ready_start 487 15 7
  wct_cases [238834,238840,238846,235621,235627,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 32 238834 7
  · wct_piece 32 238840 8
  · wct_piece 32 238846 9
  · wct_piece 19 235621 24
  · wct_piece 19 235627 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine488_ready : RoutineReady ⟨488, by decide⟩ routine488 := by
  wct_ready_start 488 15 8
  wct_cases [238847,238853,238859,235637,235643,235645,235649,4391,2078,1120,805,811,814]
  · wct_piece 32 238847 10
  · wct_piece 32 238853 11
  · wct_piece 32 238859 12
  · wct_piece 19 235637 28
  · wct_piece 19 235643 29
  · wct_piece 19 235645 30
  · wct_piece 19 235649 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine489_ready : RoutineReady ⟨489, by decide⟩ routine489 := by
  wct_ready_start 489 15 9
  wct_cases [238860,238866,238872,235659,235665,235667,235671,4412,2099,1138,1144,875,881]
  · wct_piece 32 238860 13
  · wct_piece 32 238866 14
  · wct_piece 32 238872 15
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
theorem routine490_ready : RoutineReady ⟨490, by decide⟩ routine490 := by
  wct_ready_start 490 15 10
  wct_cases [238873,238879,238885,235681,235687,235689,235693,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 32 238873 16
  · wct_piece 32 238879 17
  · wct_piece 32 238885 18
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
theorem routine491_ready : RoutineReady ⟨491, by decide⟩ routine491 := by
  wct_ready_start 491 15 11
  wct_cases [238886,238892,238898,238904,238906,238910,238916,238920,875,881]
  · wct_piece 32 238886 19
  · wct_piece 32 238892 20
  · wct_piece 32 238898 21
  · wct_piece 32 238904 22
  · wct_piece 32 238906 23
  · wct_piece 32 238910 24
  · wct_piece 32 238916 25
  · wct_piece 32 238920 26
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine492_ready : RoutineReady ⟨492, by decide⟩ routine492 := by
  wct_ready_start 492 15 12
  wct_cases [238921,238927,238933,238939,238941,238945,238951,238957,238961,966]
  · wct_piece 32 238921 27
  · wct_piece 32 238927 28
  · wct_piece 32 238933 29
  · wct_piece 32 238939 30
  · wct_piece 32 238941 31
  · wct_piece 32 238945 32
  · wct_piece 32 238951 33
  · wct_piece 32 238957 34
  · wct_piece 32 238961 35
  · wct_piece 0 966 57
theorem routine493_ready : RoutineReady ⟨493, by decide⟩ routine493 := by
  wct_ready_start 493 15 13
  wct_cases [238962,238968,238974,235747,235753,235755,235759,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 32 238962 36
  · wct_piece 32 238968 37
  · wct_piece 32 238974 38
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
theorem routine494_ready : RoutineReady ⟨494, by decide⟩ routine494 := by
  wct_ready_start 494 15 14
  wct_cases [238975,238981,238987,238993,238996,4514,4520,4524,2681,1365,875,881]
  · wct_piece 32 238975 39
  · wct_piece 32 238981 40
  · wct_piece 32 238987 41
  · wct_piece 32 238993 42
  · wct_piece 32 238996 43
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine495_ready : RoutineReady ⟨495, by decide⟩ routine495 := by
  wct_ready_start 495 15 15
  wct_cases [238997,239003,239009,239015,239018,239024,239028,239034,239038]
  · wct_piece 32 238997 44
  · wct_piece 32 239003 45
  · wct_piece 32 239009 46
  · wct_piece 32 239015 47
  · wct_piece 32 239018 48
  · wct_piece 32 239024 49
  · wct_piece 32 239028 50
  · wct_piece 32 239034 51
  · wct_piece 32 239038 52
theorem routine496_ready : RoutineReady ⟨496, by decide⟩ routine496 := by
  wct_ready_start 496 15 16
  wct_cases [239044,239050,239056,239062,239065,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 32 239044 53
  · wct_piece 32 239050 54
  · wct_piece 32 239056 55
  · wct_piece 32 239062 56
  · wct_piece 32 239065 57
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine497_ready : RoutineReady ⟨497, by decide⟩ routine497 := by
  wct_ready_start 497 15 17
  wct_cases [239066,239072,239078,235836,235842,235845,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 32 239066 58
  · wct_piece 32 239072 59
  · wct_piece 32 239078 60
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
theorem routine498_ready : RoutineReady ⟨498, by decide⟩ routine498 := by
  wct_ready_start 498 15 18
  wct_cases [239079,239085,239091,235855,235861,235863,235865,235869,2681,1365,875,881]
  · wct_piece 32 239079 61
  · wct_piece 32 239085 62
  · wct_piece 32 239091 63
  · wct_piece 20 235855 22
  · wct_piece 20 235861 23
  · wct_piece 20 235863 24
  · wct_piece 20 235865 25
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine499_ready : RoutineReady ⟨499, by decide⟩ routine499 := by
  wct_ready_start 499 15 19
  wct_cases [239092,239098,239104,235879,235885,235887,235889,235893,2705,1386,1392,1396,966]
  · wct_piece 33 239092 0
  · wct_piece 33 239098 1
  · wct_piece 33 239104 2
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
theorem routine500_ready : RoutineReady ⟨500, by decide⟩ routine500 := by
  wct_ready_start 500 15 20
  wct_cases [239105,239111,239117,235903,235909,235911,235913,235917,2726,2732,2736,1585,966]
  · wct_piece 33 239105 3
  · wct_piece 33 239111 4
  · wct_piece 33 239117 5
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
theorem routine501_ready : RoutineReady ⟨501, by decide⟩ routine501 := by
  wct_ready_start 501 15 21
  wct_cases [239118,239124,239130,235927,235933,235935,235938,235944,235948,3101,1585,966]
  · wct_piece 33 239118 6
  · wct_piece 33 239124 7
  · wct_piece 33 239130 8
  · wct_piece 20 235927 43
  · wct_piece 20 235933 44
  · wct_piece 20 235935 45
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine502_ready : RoutineReady ⟨502, by decide⟩ routine502 := by
  wct_ready_start 502 15 22
  wct_cases [239131,239137,239143,239145,239149,235963,2751,1411,901,755,761,763,766]
  · wct_piece 33 239131 9
  · wct_piece 33 239137 10
  · wct_piece 33 239143 11
  · wct_piece 33 239145 12
  · wct_piece 33 239149 13
  · wct_piece 20 235963 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine503_ready : RoutineReady ⟨503, by decide⟩ routine503 := by
  wct_ready_start 503 15 23
  wct_cases [239150,239156,239162,239164,239168,235978,2766,1426,913,919,805,811,814]
  · wct_piece 33 239150 14
  · wct_piece 33 239156 15
  · wct_piece 33 239162 16
  · wct_piece 33 239164 17
  · wct_piece 33 239168 18
  · wct_piece 20 235978 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine504_ready : RoutineReady ⟨504, by decide⟩ routine504 := by
  wct_ready_start 504 15 24
  wct_cases [239169,239175,239181,239183,239187,235993,2781,1441,931,937,940,875,881]
  · wct_piece 33 239169 19
  · wct_piece 33 239175 20
  · wct_piece 33 239181 21
  · wct_piece 33 239183 22
  · wct_piece 33 239187 23
  · wct_piece 20 235993 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine505_ready : RoutineReady ⟨505, by decide⟩ routine505 := by
  wct_ready_start 505 15 25
  wct_cases [239188,239194,239200,239202,239206,236008,2796,1456,952,958,960,962,966]
  · wct_piece 33 239188 24
  · wct_piece 33 239194 25
  · wct_piece 33 239200 26
  · wct_piece 33 239202 27
  · wct_piece 33 239206 28
  · wct_piece 21 236008 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine506_ready : RoutineReady ⟨506, by decide⟩ routine506 := by
  wct_ready_start 506 15 26
  wct_cases [239207,239213,239219,239221,239225,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 33 239207 29
  · wct_piece 33 239213 30
  · wct_piece 33 239219 31
  · wct_piece 33 239221 32
  · wct_piece 33 239225 33
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine507_ready : RoutineReady ⟨507, by decide⟩ routine507 := by
  wct_ready_start 507 15 27
  wct_cases [239226,239232,239238,239240,239244,236038,2826,1490,1496,1138,1144,875,881]
  · wct_piece 33 239226 34
  · wct_piece 33 239232 35
  · wct_piece 33 239238 36
  · wct_piece 33 239240 37
  · wct_piece 33 239244 38
  · wct_piece 21 236038 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine508_ready : RoutineReady ⟨508, by decide⟩ routine508 := by
  wct_ready_start 508 15 28
  wct_cases [239245,239251,239257,239259,239263,236053,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 33 239245 39
  · wct_piece 33 239251 40
  · wct_piece 33 239257 41
  · wct_piece 33 239259 42
  · wct_piece 33 239263 43
  · wct_piece 21 236053 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine509_ready : RoutineReady ⟨509, by decide⟩ routine509 := by
  wct_ready_start 509 15 29
  wct_cases [239264,239270,239276,239278,239282,236068,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 33 239264 44
  · wct_piece 33 239270 45
  · wct_piece 33 239276 46
  · wct_piece 33 239278 47
  · wct_piece 33 239282 48
  · wct_piece 21 236068 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine510_ready : RoutineReady ⟨510, by decide⟩ routine510 := by
  wct_ready_start 510 15 30
  wct_cases [239283,239289,239295,239297,239301,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 33 239283 49
  · wct_piece 33 239289 50
  · wct_piece 33 239295 51
  · wct_piece 33 239297 52
  · wct_piece 33 239301 53
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine511_ready : RoutineReady ⟨511, by decide⟩ routine511 := by
  wct_ready_start 511 15 31
  wct_cases [239302,239308,239314,239316,239320,236098,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 33 239302 54
  · wct_piece 33 239308 55
  · wct_piece 33 239314 56
  · wct_piece 33 239316 57
  · wct_piece 33 239320 58
  · wct_piece 21 236098 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage15 (rank : Fin 728) (hlo : 480 ≤ rank.val) (hhi : rank.val < 512) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 480 ≤ n at hlo
  change n < 512 at hhi
  interval_cases n
  · exact ⟨routine480, routine480_ready⟩
  · exact ⟨routine481, routine481_ready⟩
  · exact ⟨routine482, routine482_ready⟩
  · exact ⟨routine483, routine483_ready⟩
  · exact ⟨routine484, routine484_ready⟩
  · exact ⟨routine485, routine485_ready⟩
  · exact ⟨routine486, routine486_ready⟩
  · exact ⟨routine487, routine487_ready⟩
  · exact ⟨routine488, routine488_ready⟩
  · exact ⟨routine489, routine489_ready⟩
  · exact ⟨routine490, routine490_ready⟩
  · exact ⟨routine491, routine491_ready⟩
  · exact ⟨routine492, routine492_ready⟩
  · exact ⟨routine493, routine493_ready⟩
  · exact ⟨routine494, routine494_ready⟩
  · exact ⟨routine495, routine495_ready⟩
  · exact ⟨routine496, routine496_ready⟩
  · exact ⟨routine497, routine497_ready⟩
  · exact ⟨routine498, routine498_ready⟩
  · exact ⟨routine499, routine499_ready⟩
  · exact ⟨routine500, routine500_ready⟩
  · exact ⟨routine501, routine501_ready⟩
  · exact ⟨routine502, routine502_ready⟩
  · exact ⟨routine503, routine503_ready⟩
  · exact ⟨routine504, routine504_ready⟩
  · exact ⟨routine505, routine505_ready⟩
  · exact ⟨routine506, routine506_ready⟩
  · exact ⟨routine507, routine507_ready⟩
  · exact ⟨routine508, routine508_ready⟩
  · exact ⟨routine509, routine509_ready⟩
  · exact ⟨routine510, routine510_ready⟩
  · exact ⟨routine511, routine511_ready⟩
end W9Machine.Chain
end
