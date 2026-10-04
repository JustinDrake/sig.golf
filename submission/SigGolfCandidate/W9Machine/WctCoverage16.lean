import SigGolfCandidate.W9Machine.WctRoutineCheck16
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch16_checked :
    (routineBatch16.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch16_checked :
    (routineBatch16.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine512_ready : RoutineReady ⟨512, by decide⟩ routine512 := by
  wct_ready_start 512 16 0
  wct_cases [238679,238685,238691,238693,238697,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 33 238679 59
  · wct_piece 33 238685 60
  · wct_piece 33 238691 61
  · wct_piece 33 238693 62
  · wct_piece 33 238697 63
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine513_ready : RoutineReady ⟨513, by decide⟩ routine513 := by
  wct_ready_start 513 16 1
  wct_cases [238698,238704,238710,238712,238716,238722,238726,238732,875,881]
  · wct_piece 34 238698 0
  · wct_piece 34 238704 1
  · wct_piece 34 238710 2
  · wct_piece 34 238712 3
  · wct_piece 34 238716 4
  · wct_piece 34 238722 5
  · wct_piece 34 238726 6
  · wct_piece 34 238732 7
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine514_ready : RoutineReady ⟨514, by decide⟩ routine514 := by
  wct_ready_start 514 16 2
  wct_cases [238733,238739,238745,238747,238751,238757,238761,238767,238769,238773,966]
  · wct_piece 34 238733 8
  · wct_piece 34 238739 9
  · wct_piece 34 238745 10
  · wct_piece 34 238747 11
  · wct_piece 34 238751 12
  · wct_piece 34 238757 13
  · wct_piece 34 238761 14
  · wct_piece 34 238767 15
  · wct_piece 34 238769 16
  · wct_piece 34 238773 17
  · wct_piece 0 966 57
theorem routine515_ready : RoutineReady ⟨515, by decide⟩ routine515 := by
  wct_ready_start 515 16 3
  wct_cases [238774,238780,238786,238788,238792,238798,238804,238808,875,881]
  · wct_piece 34 238774 18
  · wct_piece 34 238780 19
  · wct_piece 34 238786 20
  · wct_piece 34 238788 21
  · wct_piece 34 238792 22
  · wct_piece 34 238798 23
  · wct_piece 34 238804 24
  · wct_piece 34 238808 25
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine516_ready : RoutineReady ⟨516, by decide⟩ routine516 := by
  wct_ready_start 516 16 4
  wct_cases [238809,238815,238821,238823,238827,238833,238839,238845,238849,966]
  · wct_piece 34 238809 26
  · wct_piece 34 238815 27
  · wct_piece 34 238821 28
  · wct_piece 34 238823 29
  · wct_piece 34 238827 30
  · wct_piece 34 238833 31
  · wct_piece 34 238839 32
  · wct_piece 34 238845 33
  · wct_piece 34 238849 34
  · wct_piece 0 966 57
theorem routine517_ready : RoutineReady ⟨517, by decide⟩ routine517 := by
  wct_ready_start 517 16 5
  wct_cases [238850,238856,238862,238864,238868,235546,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 34 238850 35
  · wct_piece 34 238856 36
  · wct_piece 34 238862 37
  · wct_piece 34 238864 38
  · wct_piece 34 238868 39
  · wct_piece 22 235546 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine518_ready : RoutineReady ⟨518, by decide⟩ routine518 := by
  wct_ready_start 518 16 6
  wct_cases [238869,238875,238881,238883,238887,235561,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 34 238869 40
  · wct_piece 34 238875 41
  · wct_piece 34 238881 42
  · wct_piece 34 238883 43
  · wct_piece 34 238887 44
  · wct_piece 22 235561 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine519_ready : RoutineReady ⟨519, by decide⟩ routine519 := by
  wct_ready_start 519 16 7
  wct_cases [238888,238894,238900,238902,238906,238912,238914,238918,238924,238928,966]
  · wct_piece 34 238888 45
  · wct_piece 34 238894 46
  · wct_piece 34 238900 47
  · wct_piece 34 238902 48
  · wct_piece 34 238906 49
  · wct_piece 34 238912 50
  · wct_piece 34 238914 51
  · wct_piece 34 238918 52
  · wct_piece 34 238924 53
  · wct_piece 34 238928 54
  · wct_piece 0 966 57
theorem routine520_ready : RoutineReady ⟨520, by decide⟩ routine520 := by
  wct_ready_start 520 16 8
  wct_cases [238929,238935,238941,238943,238947,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 34 238929 55
  · wct_piece 34 238935 56
  · wct_piece 34 238941 57
  · wct_piece 34 238943 58
  · wct_piece 34 238947 59
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine521_ready : RoutineReady ⟨521, by decide⟩ routine521 := by
  wct_ready_start 521 16 9
  wct_cases [238948,238954,238960,238962,238966,235606,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 34 238948 60
  · wct_piece 34 238954 61
  · wct_piece 34 238960 62
  · wct_piece 34 238962 63
  · wct_piece 35 238966 0
  · wct_piece 22 235606 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine522_ready : RoutineReady ⟨522, by decide⟩ routine522 := by
  wct_ready_start 522 16 10
  wct_cases [238967,238973,238979,238982,235618,235624,235628,4391,2078,1120,805,811,814]
  · wct_piece 35 238967 1
  · wct_piece 35 238973 2
  · wct_piece 35 238979 3
  · wct_piece 35 238982 4
  · wct_piece 22 235618 24
  · wct_piece 22 235624 25
  · wct_piece 22 235628 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine523_ready : RoutineReady ⟨523, by decide⟩ routine523 := by
  wct_ready_start 523 16 11
  wct_cases [238983,238989,238995,238998,239004,239008,4412,2099,1138,1144,875,881]
  · wct_piece 35 238983 5
  · wct_piece 35 238989 6
  · wct_piece 35 238995 7
  · wct_piece 35 238998 8
  · wct_piece 35 239004 9
  · wct_piece 35 239008 10
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine524_ready : RoutineReady ⟨524, by decide⟩ routine524 := by
  wct_ready_start 524 16 12
  wct_cases [239009,239015,239021,239024,239030,239034,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 35 239009 11
  · wct_piece 35 239015 12
  · wct_piece 35 239021 13
  · wct_piece 35 239024 14
  · wct_piece 35 239030 15
  · wct_piece 35 239034 16
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine525_ready : RoutineReady ⟨525, by decide⟩ routine525 := by
  wct_ready_start 525 16 13
  wct_cases [239035,239041,239047,239050,239056,239060,239066,239070,239076]
  · wct_piece 35 239035 17
  · wct_piece 35 239041 18
  · wct_piece 35 239047 19
  · wct_piece 35 239050 20
  · wct_piece 35 239056 21
  · wct_piece 35 239060 22
  · wct_piece 35 239066 23
  · wct_piece 35 239070 24
  · wct_piece 35 239076 25
theorem routine526_ready : RoutineReady ⟨526, by decide⟩ routine526 := by
  wct_ready_start 526 16 14
  wct_cases [239082,239088,239094,239097,239103,239107,239113,239119,239123]
  · wct_piece 35 239082 26
  · wct_piece 35 239088 27
  · wct_piece 35 239094 28
  · wct_piece 35 239097 29
  · wct_piece 35 239103 30
  · wct_piece 35 239107 31
  · wct_piece 35 239113 32
  · wct_piece 35 239119 33
  · wct_piece 35 239123 34
theorem routine527_ready : RoutineReady ⟨527, by decide⟩ routine527 := by
  wct_ready_start 527 16 15
  wct_cases [239129,239135,239141,239144,239150,239154,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 35 239129 35
  · wct_piece 35 239135 36
  · wct_piece 35 239141 37
  · wct_piece 35 239144 38
  · wct_piece 35 239150 39
  · wct_piece 35 239154 40
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine528_ready : RoutineReady ⟨528, by decide⟩ routine528 := by
  wct_ready_start 528 16 16
  wct_cases [239155,239161,239167,239170,239176,4514,4520,4524,2681,1365,875,881]
  · wct_piece 35 239155 41
  · wct_piece 35 239161 42
  · wct_piece 35 239167 43
  · wct_piece 35 239170 44
  · wct_piece 35 239176 45
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine529_ready : RoutineReady ⟨529, by decide⟩ routine529 := by
  wct_ready_start 529 16 17
  wct_cases [239177,239183,239189,239192,239198,239204,239208,239214,239218]
  · wct_piece 35 239177 46
  · wct_piece 35 239183 47
  · wct_piece 35 239189 48
  · wct_piece 35 239192 49
  · wct_piece 35 239198 50
  · wct_piece 35 239204 51
  · wct_piece 35 239208 52
  · wct_piece 35 239214 53
  · wct_piece 35 239218 54
theorem routine530_ready : RoutineReady ⟨530, by decide⟩ routine530 := by
  wct_ready_start 530 16 18
  wct_cases [239224,239230,239236,239239,239245,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 35 239224 55
  · wct_piece 35 239230 56
  · wct_piece 35 239236 57
  · wct_piece 35 239239 58
  · wct_piece 35 239245 59
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine531_ready : RoutineReady ⟨531, by decide⟩ routine531 := by
  wct_ready_start 531 16 19
  wct_cases [239246,239252,239258,239261,235804,235810,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 35 239246 60
  · wct_piece 35 239252 61
  · wct_piece 35 239258 62
  · wct_piece 35 239261 63
  · wct_piece 23 235804 11
  · wct_piece 23 235810 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine532_ready : RoutineReady ⟨532, by decide⟩ routine532 := by
  wct_ready_start 532 16 20
  wct_cases [239262,239268,239274,239277,235822,235828,235830,235834,235227,2681,1365,875,881]
  · wct_piece 36 239262 0
  · wct_piece 36 239268 1
  · wct_piece 36 239274 2
  · wct_piece 36 239277 3
  · wct_piece 23 235822 16
  · wct_piece 23 235828 17
  · wct_piece 23 235830 18
  · wct_piece 23 235834 19
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine533_ready : RoutineReady ⟨533, by decide⟩ routine533 := by
  wct_ready_start 533 16 21
  wct_cases [239278,239284,239290,239293,239299,239301,239305,235251,2705,1386,1392,1396,966]
  · wct_piece 36 239278 4
  · wct_piece 36 239284 5
  · wct_piece 36 239290 6
  · wct_piece 36 239293 7
  · wct_piece 36 239299 8
  · wct_piece 36 239301 9
  · wct_piece 36 239305 10
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine534_ready : RoutineReady ⟨534, by decide⟩ routine534 := by
  wct_ready_start 534 16 22
  wct_cases [239306,239312,239318,239321,239327,239329,239333,235275,2726,2732,2736,1585,966]
  · wct_piece 36 239306 11
  · wct_piece 36 239312 12
  · wct_piece 36 239318 13
  · wct_piece 36 239321 14
  · wct_piece 36 239327 15
  · wct_piece 36 239329 16
  · wct_piece 36 239333 17
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine535_ready : RoutineReady ⟨535, by decide⟩ routine535 := by
  wct_ready_start 535 16 23
  wct_cases [239334,239340,239346,239349,235894,235900,235903,235296,235302,235306,3101,1585,966]
  · wct_piece 36 239334 18
  · wct_piece 36 239340 19
  · wct_piece 36 239346 20
  · wct_piece 36 239349 21
  · wct_piece 23 235894 37
  · wct_piece 23 235900 38
  · wct_piece 23 235903 39
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine536_ready : RoutineReady ⟨536, by decide⟩ routine536 := by
  wct_ready_start 536 16 24
  wct_cases [239350,239356,239362,239365,235915,235921,235923,235925,235929,3101,1585,966]
  · wct_piece 36 239350 22
  · wct_piece 36 239356 23
  · wct_piece 36 239362 24
  · wct_piece 36 239365 25
  · wct_piece 23 235915 43
  · wct_piece 23 235921 44
  · wct_piece 23 235923 45
  · wct_piece 23 235925 46
  · wct_piece 23 235929 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine537_ready : RoutineReady ⟨537, by decide⟩ routine537 := by
  wct_ready_start 537 16 25
  wct_cases [239366,239372,239378,239380,239382,239386,4391,2078,1120,805,811,814]
  · wct_piece 36 239366 26
  · wct_piece 36 239372 27
  · wct_piece 36 239378 28
  · wct_piece 36 239380 29
  · wct_piece 36 239382 30
  · wct_piece 36 239386 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine538_ready : RoutineReady ⟨538, by decide⟩ routine538 := by
  wct_ready_start 538 16 26
  wct_cases [239387,239393,239399,239401,239403,239407,4412,2099,1138,1144,875,881]
  · wct_piece 36 239387 32
  · wct_piece 36 239393 33
  · wct_piece 36 239399 34
  · wct_piece 36 239401 35
  · wct_piece 36 239403 36
  · wct_piece 36 239407 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine539_ready : RoutineReady ⟨539, by decide⟩ routine539 := by
  wct_ready_start 539 16 27
  wct_cases [239408,239414,239420,239422,239424,239428,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 36 239408 38
  · wct_piece 36 239414 39
  · wct_piece 36 239420 40
  · wct_piece 36 239422 41
  · wct_piece 36 239424 42
  · wct_piece 36 239428 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine540_ready : RoutineReady ⟨540, by decide⟩ routine540 := by
  wct_ready_start 540 16 28
  wct_cases [239429,239435,239441,239443,239445,239449,4454,2138,2144,2148,1365,875,881]
  · wct_piece 36 239429 44
  · wct_piece 36 239435 45
  · wct_piece 36 239441 46
  · wct_piece 36 239443 47
  · wct_piece 36 239445 48
  · wct_piece 36 239449 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine541_ready : RoutineReady ⟨541, by decide⟩ routine541 := by
  wct_ready_start 541 16 29
  wct_cases [239450,239456,239462,239464,239466,239470,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 36 239450 50
  · wct_piece 36 239456 51
  · wct_piece 36 239462 52
  · wct_piece 36 239464 53
  · wct_piece 36 239466 54
  · wct_piece 36 239470 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine542_ready : RoutineReady ⟨542, by decide⟩ routine542 := by
  wct_ready_start 542 16 30
  wct_cases [239471,239477,239483,239485,239487,239491,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 36 239471 56
  · wct_piece 36 239477 57
  · wct_piece 36 239483 58
  · wct_piece 36 239485 59
  · wct_piece 36 239487 60
  · wct_piece 36 239491 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine543_ready : RoutineReady ⟨543, by decide⟩ routine543 := by
  wct_ready_start 543 16 31
  wct_cases [239492,239498,239504,239506,239508,239512,4514,4520,4524,2681,1365,875,881]
  · wct_piece 36 239492 62
  · wct_piece 36 239498 63
  · wct_piece 37 239504 0
  · wct_piece 37 239506 1
  · wct_piece 37 239508 2
  · wct_piece 37 239512 3
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage16 (rank : Fin 728) (hlo : 512 ≤ rank.val) (hhi : rank.val < 544) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 512 ≤ n at hlo
  change n < 544 at hhi
  interval_cases n
  · exact ⟨routine512, routine512_ready⟩
  · exact ⟨routine513, routine513_ready⟩
  · exact ⟨routine514, routine514_ready⟩
  · exact ⟨routine515, routine515_ready⟩
  · exact ⟨routine516, routine516_ready⟩
  · exact ⟨routine517, routine517_ready⟩
  · exact ⟨routine518, routine518_ready⟩
  · exact ⟨routine519, routine519_ready⟩
  · exact ⟨routine520, routine520_ready⟩
  · exact ⟨routine521, routine521_ready⟩
  · exact ⟨routine522, routine522_ready⟩
  · exact ⟨routine523, routine523_ready⟩
  · exact ⟨routine524, routine524_ready⟩
  · exact ⟨routine525, routine525_ready⟩
  · exact ⟨routine526, routine526_ready⟩
  · exact ⟨routine527, routine527_ready⟩
  · exact ⟨routine528, routine528_ready⟩
  · exact ⟨routine529, routine529_ready⟩
  · exact ⟨routine530, routine530_ready⟩
  · exact ⟨routine531, routine531_ready⟩
  · exact ⟨routine532, routine532_ready⟩
  · exact ⟨routine533, routine533_ready⟩
  · exact ⟨routine534, routine534_ready⟩
  · exact ⟨routine535, routine535_ready⟩
  · exact ⟨routine536, routine536_ready⟩
  · exact ⟨routine537, routine537_ready⟩
  · exact ⟨routine538, routine538_ready⟩
  · exact ⟨routine539, routine539_ready⟩
  · exact ⟨routine540, routine540_ready⟩
  · exact ⟨routine541, routine541_ready⟩
  · exact ⟨routine542, routine542_ready⟩
  · exact ⟨routine543, routine543_ready⟩
end W9Machine.Chain
end
