import SigGolfCandidate.W9Machine.WctRoutineCheck20
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch20_checked :
    (routineBatch20.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch20_checked :
    (routineBatch20.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine640_ready : RoutineReady ⟨640, by decide⟩ routine640 := by
  wct_ready_start 640 20 0
  wct_cases [240842,240848,240850,240856,240862,240866,240872,240876,875,881]
  · wct_piece 43 240842 4
  · wct_piece 43 240848 5
  · wct_piece 43 240850 6
  · wct_piece 43 240856 7
  · wct_piece 43 240862 8
  · wct_piece 43 240866 9
  · wct_piece 43 240872 10
  · wct_piece 43 240876 11
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine641_ready : RoutineReady ⟨641, by decide⟩ routine641 := by
  wct_ready_start 641 20 1
  wct_cases [240877,240883,240885,240891,240897,240901,240907,240913,240917,966]
  · wct_piece 43 240877 12
  · wct_piece 43 240883 13
  · wct_piece 43 240885 14
  · wct_piece 43 240891 15
  · wct_piece 43 240897 16
  · wct_piece 43 240901 17
  · wct_piece 43 240907 18
  · wct_piece 43 240913 19
  · wct_piece 43 240917 20
  · wct_piece 0 966 57
theorem routine642_ready : RoutineReady ⟨642, by decide⟩ routine642 := by
  wct_ready_start 642 20 2
  wct_cases [240918,240924,240926,240932,235728,235734,235738,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 43 240918 21
  · wct_piece 43 240924 22
  · wct_piece 43 240926 23
  · wct_piece 43 240932 24
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
theorem routine643_ready : RoutineReady ⟨643, by decide⟩ routine643 := by
  wct_ready_start 643 20 3
  wct_cases [240933,240939,240941,240947,235750,235756,4514,4520,4524,2681,1365,875,881]
  · wct_piece 43 240933 25
  · wct_piece 43 240939 26
  · wct_piece 43 240941 27
  · wct_piece 43 240947 28
  · wct_piece 22 235750 60
  · wct_piece 22 235756 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine644_ready : RoutineReady ⟨644, by decide⟩ routine644 := by
  wct_ready_start 644 20 4
  wct_cases [240948,240954,240956,240962,240968,240974,240978,240984,240988,966]
  · wct_piece 43 240948 29
  · wct_piece 43 240954 30
  · wct_piece 43 240956 31
  · wct_piece 43 240962 32
  · wct_piece 43 240968 33
  · wct_piece 43 240974 34
  · wct_piece 43 240978 35
  · wct_piece 43 240984 36
  · wct_piece 43 240988 37
  · wct_piece 0 966 57
theorem routine645_ready : RoutineReady ⟨645, by decide⟩ routine645 := by
  wct_ready_start 645 20 5
  wct_cases [240989,240995,240997,241003,235786,235792,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 43 240989 38
  · wct_piece 43 240995 39
  · wct_piece 43 240997 40
  · wct_piece 43 241003 41
  · wct_piece 23 235786 6
  · wct_piece 23 235792 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine646_ready : RoutineReady ⟨646, by decide⟩ routine646 := by
  wct_ready_start 646 20 6
  wct_cases [241004,241010,241012,241018,235804,235810,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 43 241004 42
  · wct_piece 43 241010 43
  · wct_piece 43 241012 44
  · wct_piece 43 241018 45
  · wct_piece 23 235804 11
  · wct_piece 23 235810 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine647_ready : RoutineReady ⟨647, by decide⟩ routine647 := by
  wct_ready_start 647 20 7
  wct_cases [241019,241025,241027,241033,235822,235828,235830,235834,235227,2681,1365,875,881]
  · wct_piece 43 241019 46
  · wct_piece 43 241025 47
  · wct_piece 43 241027 48
  · wct_piece 43 241033 49
  · wct_piece 23 235822 16
  · wct_piece 23 235828 17
  · wct_piece 23 235830 18
  · wct_piece 23 235834 19
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine648_ready : RoutineReady ⟨648, by decide⟩ routine648 := by
  wct_ready_start 648 20 8
  wct_cases [241034,241040,241042,241048,235846,235852,235854,235858,235251,2705,1386,1392,1396,966]
  · wct_piece 43 241034 50
  · wct_piece 43 241040 51
  · wct_piece 43 241042 52
  · wct_piece 43 241048 53
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
theorem routine649_ready : RoutineReady ⟨649, by decide⟩ routine649 := by
  wct_ready_start 649 20 9
  wct_cases [241049,241055,241057,241063,235870,235876,235878,235882,235275,2726,2732,2736,1585,966]
  · wct_piece 43 241049 54
  · wct_piece 43 241055 55
  · wct_piece 43 241057 56
  · wct_piece 43 241063 57
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
theorem routine650_ready : RoutineReady ⟨650, by decide⟩ routine650 := by
  wct_ready_start 650 20 10
  wct_cases [241064,241070,241072,241078,235894,235900,235903,235296,235302,235306,3101,1585,966]
  · wct_piece 43 241064 58
  · wct_piece 43 241070 59
  · wct_piece 43 241072 60
  · wct_piece 43 241078 61
  · wct_piece 23 235894 37
  · wct_piece 23 235900 38
  · wct_piece 23 235903 39
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine651_ready : RoutineReady ⟨651, by decide⟩ routine651 := by
  wct_ready_start 651 20 11
  wct_cases [241079,241085,241087,241093,235915,235921,235923,235925,235929,3101,1585,966]
  · wct_piece 43 241079 62
  · wct_piece 43 241085 63
  · wct_piece 44 241087 0
  · wct_piece 44 241093 1
  · wct_piece 23 235915 43
  · wct_piece 23 235921 44
  · wct_piece 23 235923 45
  · wct_piece 23 235925 46
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine652_ready : RoutineReady ⟨652, by decide⟩ routine652 := by
  wct_ready_start 652 20 12
  wct_cases [241094,241100,241102,241108,241110,241114,239386,4391,2078,1120,805,811,814]
  · wct_piece 44 241094 2
  · wct_piece 44 241100 3
  · wct_piece 44 241102 4
  · wct_piece 44 241108 5
  · wct_piece 44 241110 6
  · wct_piece 44 241114 7
  · wct_piece 36 239386 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine653_ready : RoutineReady ⟨653, by decide⟩ routine653 := by
  wct_ready_start 653 20 13
  wct_cases [241115,241121,241123,241129,241131,241135,239407,4412,2099,1138,1144,875,881]
  · wct_piece 44 241115 8
  · wct_piece 44 241121 9
  · wct_piece 44 241123 10
  · wct_piece 44 241129 11
  · wct_piece 44 241131 12
  · wct_piece 44 241135 13
  · wct_piece 36 239407 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine654_ready : RoutineReady ⟨654, by decide⟩ routine654 := by
  wct_ready_start 654 20 14
  wct_cases [241136,241142,241144,241150,241152,241156,239428,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 44 241136 14
  · wct_piece 44 241142 15
  · wct_piece 44 241144 16
  · wct_piece 44 241150 17
  · wct_piece 44 241152 18
  · wct_piece 44 241156 19
  · wct_piece 36 239428 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine655_ready : RoutineReady ⟨655, by decide⟩ routine655 := by
  wct_ready_start 655 20 15
  wct_cases [241157,241163,241165,241171,241173,241177,239449,4454,2138,2144,2148,1365,875,881]
  · wct_piece 44 241157 20
  · wct_piece 44 241163 21
  · wct_piece 44 241165 22
  · wct_piece 44 241171 23
  · wct_piece 44 241173 24
  · wct_piece 44 241177 25
  · wct_piece 36 239449 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine656_ready : RoutineReady ⟨656, by decide⟩ routine656 := by
  wct_ready_start 656 20 16
  wct_cases [241178,241184,241186,241192,241194,241198,239470,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 44 241178 26
  · wct_piece 44 241184 27
  · wct_piece 44 241186 28
  · wct_piece 44 241192 29
  · wct_piece 44 241194 30
  · wct_piece 44 241198 31
  · wct_piece 36 239470 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine657_ready : RoutineReady ⟨657, by decide⟩ routine657 := by
  wct_ready_start 657 20 17
  wct_cases [241199,241205,241207,241213,241215,241219,239491,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 44 241199 32
  · wct_piece 44 241205 33
  · wct_piece 44 241207 34
  · wct_piece 44 241213 35
  · wct_piece 44 241215 36
  · wct_piece 44 241219 37
  · wct_piece 36 239491 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine658_ready : RoutineReady ⟨658, by decide⟩ routine658 := by
  wct_ready_start 658 20 18
  wct_cases [241220,241226,241228,241234,241236,241240,239512,4514,4520,4524,2681,1365,875,881]
  · wct_piece 44 241220 38
  · wct_piece 44 241226 39
  · wct_piece 44 241228 40
  · wct_piece 44 241234 41
  · wct_piece 44 241236 42
  · wct_piece 44 241240 43
  · wct_piece 37 239512 3
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine659_ready : RoutineReady ⟨659, by decide⟩ routine659 := by
  wct_ready_start 659 20 19
  wct_cases [241241,241247,241249,241255,241257,241261,241267,241271,241277,241281,966]
  · wct_piece 44 241241 44
  · wct_piece 44 241247 45
  · wct_piece 44 241249 46
  · wct_piece 44 241255 47
  · wct_piece 44 241257 48
  · wct_piece 44 241261 49
  · wct_piece 44 241267 50
  · wct_piece 44 241271 51
  · wct_piece 44 241277 52
  · wct_piece 44 241281 53
  · wct_piece 0 966 57
theorem routine660_ready : RoutineReady ⟨660, by decide⟩ routine660 := by
  wct_ready_start 660 20 20
  wct_cases [241282,241288,241290,241296,241298,241302,239574,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 44 241282 54
  · wct_piece 44 241288 55
  · wct_piece 44 241290 56
  · wct_piece 44 241296 57
  · wct_piece 44 241298 58
  · wct_piece 44 241302 59
  · wct_piece 37 239574 19
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine661_ready : RoutineReady ⟨661, by decide⟩ routine661 := by
  wct_ready_start 661 20 21
  wct_cases [241303,241309,241311,241317,241319,241323,239595,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 44 241303 60
  · wct_piece 44 241309 61
  · wct_piece 44 241311 62
  · wct_piece 44 241317 63
  · wct_piece 45 241319 0
  · wct_piece 45 241323 1
  · wct_piece 37 239595 25
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine662_ready : RoutineReady ⟨662, by decide⟩ routine662 := by
  wct_ready_start 662 20 22
  wct_cases [241324,241330,241332,241338,241341,239613,239619,239623,235227,2681,1365,875,881]
  · wct_piece 45 241324 2
  · wct_piece 45 241330 3
  · wct_piece 45 241332 4
  · wct_piece 45 241338 5
  · wct_piece 45 241341 6
  · wct_piece 37 239613 30
  · wct_piece 37 239619 31
  · wct_piece 37 239623 32
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine663_ready : RoutineReady ⟨663, by decide⟩ routine663 := by
  wct_ready_start 663 20 23
  wct_cases [241342,241348,241350,241356,241359,241365,241369,235251,2705,1386,1392,1396,966]
  · wct_piece 45 241342 7
  · wct_piece 45 241348 8
  · wct_piece 45 241350 9
  · wct_piece 45 241356 10
  · wct_piece 45 241359 11
  · wct_piece 45 241365 12
  · wct_piece 45 241369 13
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine664_ready : RoutineReady ⟨664, by decide⟩ routine664 := by
  wct_ready_start 664 20 24
  wct_cases [241370,241376,241378,241384,241387,241393,241397,235275,2726,2732,2736,1585,966]
  · wct_piece 45 241370 14
  · wct_piece 45 241376 15
  · wct_piece 45 241378 16
  · wct_piece 45 241384 17
  · wct_piece 45 241387 18
  · wct_piece 45 241393 19
  · wct_piece 45 241397 20
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine665_ready : RoutineReady ⟨665, by decide⟩ routine665 := by
  wct_ready_start 665 20 25
  wct_cases [241398,241404,241406,241412,241415,239697,239703,235296,235302,235306,3101,1585,966]
  · wct_piece 45 241398 21
  · wct_piece 45 241404 22
  · wct_piece 45 241406 23
  · wct_piece 45 241412 24
  · wct_piece 45 241415 25
  · wct_piece 37 239697 51
  · wct_piece 37 239703 52
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine666_ready : RoutineReady ⟨666, by decide⟩ routine666 := by
  wct_ready_start 666 20 26
  wct_cases [241416,241422,241424,241430,241433,239721,239727,239729,239733,235929,3101,1585,966]
  · wct_piece 45 241416 26
  · wct_piece 45 241422 27
  · wct_piece 45 241424 28
  · wct_piece 45 241430 29
  · wct_piece 45 241433 30
  · wct_piece 37 239721 57
  · wct_piece 37 239727 58
  · wct_piece 37 239729 59
  · wct_piece 37 239733 60
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine667_ready : RoutineReady ⟨667, by decide⟩ routine667 := by
  wct_ready_start 667 20 27
  wct_cases [241434,241440,241442,241448,241450,241452,241456,235227,2681,1365,875,881]
  · wct_piece 45 241434 31
  · wct_piece 45 241440 32
  · wct_piece 45 241442 33
  · wct_piece 45 241448 34
  · wct_piece 45 241450 35
  · wct_piece 45 241452 36
  · wct_piece 45 241456 37
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine668_ready : RoutineReady ⟨668, by decide⟩ routine668 := by
  wct_ready_start 668 20 28
  wct_cases [241457,241463,241465,241471,241473,241475,241479,235251,2705,1386,1392,1396,966]
  · wct_piece 45 241457 38
  · wct_piece 45 241463 39
  · wct_piece 45 241465 40
  · wct_piece 45 241471 41
  · wct_piece 45 241473 42
  · wct_piece 45 241475 43
  · wct_piece 45 241479 44
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine669_ready : RoutineReady ⟨669, by decide⟩ routine669 := by
  wct_ready_start 669 20 29
  wct_cases [241480,241486,241488,241494,241496,241498,241502,235275,2726,2732,2736,1585,966]
  · wct_piece 45 241480 45
  · wct_piece 45 241486 46
  · wct_piece 45 241488 47
  · wct_piece 45 241494 48
  · wct_piece 45 241496 49
  · wct_piece 45 241498 50
  · wct_piece 45 241502 51
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine670_ready : RoutineReady ⟨670, by decide⟩ routine670 := by
  wct_ready_start 670 20 30
  wct_cases [241503,241509,241511,241517,241519,241521,241525,235296,235302,235306,3101,1585,966]
  · wct_piece 45 241503 52
  · wct_piece 45 241509 53
  · wct_piece 45 241511 54
  · wct_piece 45 241517 55
  · wct_piece 45 241519 56
  · wct_piece 45 241521 57
  · wct_piece 45 241525 58
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine671_ready : RoutineReady ⟨671, by decide⟩ routine671 := by
  wct_ready_start 671 20 31
  wct_cases [241526,241532,241534,241540,241542,241545,241551,241555,235929,3101,1585,966]
  · wct_piece 45 241526 59
  · wct_piece 45 241532 60
  · wct_piece 45 241534 61
  · wct_piece 45 241540 62
  · wct_piece 45 241542 63
  · wct_piece 46 241545 0
  · wct_piece 46 241551 1
  · wct_piece 46 241555 2
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage20 (rank : Fin 728) (hlo : 640 ≤ rank.val) (hhi : rank.val < 672) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 640 ≤ n at hlo
  change n < 672 at hhi
  interval_cases n
  · exact ⟨routine640, routine640_ready⟩
  · exact ⟨routine641, routine641_ready⟩
  · exact ⟨routine642, routine642_ready⟩
  · exact ⟨routine643, routine643_ready⟩
  · exact ⟨routine644, routine644_ready⟩
  · exact ⟨routine645, routine645_ready⟩
  · exact ⟨routine646, routine646_ready⟩
  · exact ⟨routine647, routine647_ready⟩
  · exact ⟨routine648, routine648_ready⟩
  · exact ⟨routine649, routine649_ready⟩
  · exact ⟨routine650, routine650_ready⟩
  · exact ⟨routine651, routine651_ready⟩
  · exact ⟨routine652, routine652_ready⟩
  · exact ⟨routine653, routine653_ready⟩
  · exact ⟨routine654, routine654_ready⟩
  · exact ⟨routine655, routine655_ready⟩
  · exact ⟨routine656, routine656_ready⟩
  · exact ⟨routine657, routine657_ready⟩
  · exact ⟨routine658, routine658_ready⟩
  · exact ⟨routine659, routine659_ready⟩
  · exact ⟨routine660, routine660_ready⟩
  · exact ⟨routine661, routine661_ready⟩
  · exact ⟨routine662, routine662_ready⟩
  · exact ⟨routine663, routine663_ready⟩
  · exact ⟨routine664, routine664_ready⟩
  · exact ⟨routine665, routine665_ready⟩
  · exact ⟨routine666, routine666_ready⟩
  · exact ⟨routine667, routine667_ready⟩
  · exact ⟨routine668, routine668_ready⟩
  · exact ⟨routine669, routine669_ready⟩
  · exact ⟨routine670, routine670_ready⟩
  · exact ⟨routine671, routine671_ready⟩
end W9Machine.Chain
end
