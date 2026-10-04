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
  wct_cases [239321,239327,239333,239335,239339,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 33 239321 59
  · wct_piece 33 239327 60
  · wct_piece 33 239333 61
  · wct_piece 33 239335 62
  · wct_piece 33 239339 63
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
  wct_cases [239340,239346,239352,239354,239358,239364,239368,239374,875,881]
  · wct_piece 34 239340 0
  · wct_piece 34 239346 1
  · wct_piece 34 239352 2
  · wct_piece 34 239354 3
  · wct_piece 34 239358 4
  · wct_piece 34 239364 5
  · wct_piece 34 239368 6
  · wct_piece 34 239374 7
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine514_ready : RoutineReady ⟨514, by decide⟩ routine514 := by
  wct_ready_start 514 16 2
  wct_cases [239375,239381,239387,239389,239393,239399,239403,239409,239411,239415,966]
  · wct_piece 34 239375 8
  · wct_piece 34 239381 9
  · wct_piece 34 239387 10
  · wct_piece 34 239389 11
  · wct_piece 34 239393 12
  · wct_piece 34 239399 13
  · wct_piece 34 239403 14
  · wct_piece 34 239409 15
  · wct_piece 34 239411 16
  · wct_piece 34 239415 17
  · wct_piece 0 966 57
theorem routine515_ready : RoutineReady ⟨515, by decide⟩ routine515 := by
  wct_ready_start 515 16 3
  wct_cases [239416,239422,239428,239430,239434,239440,239446,239450,875,881]
  · wct_piece 34 239416 18
  · wct_piece 34 239422 19
  · wct_piece 34 239428 20
  · wct_piece 34 239430 21
  · wct_piece 34 239434 22
  · wct_piece 34 239440 23
  · wct_piece 34 239446 24
  · wct_piece 34 239450 25
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine516_ready : RoutineReady ⟨516, by decide⟩ routine516 := by
  wct_ready_start 516 16 4
  wct_cases [239451,239457,239463,239465,239469,239475,239481,239487,239491,966]
  · wct_piece 34 239451 26
  · wct_piece 34 239457 27
  · wct_piece 34 239463 28
  · wct_piece 34 239465 29
  · wct_piece 34 239469 30
  · wct_piece 34 239475 31
  · wct_piece 34 239481 32
  · wct_piece 34 239487 33
  · wct_piece 34 239491 34
  · wct_piece 0 966 57
theorem routine517_ready : RoutineReady ⟨517, by decide⟩ routine517 := by
  wct_ready_start 517 16 5
  wct_cases [239492,239498,239504,239506,239510,236188,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 34 239492 35
  · wct_piece 34 239498 36
  · wct_piece 34 239504 37
  · wct_piece 34 239506 38
  · wct_piece 34 239510 39
  · wct_piece 22 236188 0
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
  wct_cases [239511,239517,239523,239525,239529,236203,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 34 239511 40
  · wct_piece 34 239517 41
  · wct_piece 34 239523 42
  · wct_piece 34 239525 43
  · wct_piece 34 239529 44
  · wct_piece 22 236203 5
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
  wct_cases [239530,239536,239542,239544,239548,239554,239556,239560,239566,239570,966]
  · wct_piece 34 239530 45
  · wct_piece 34 239536 46
  · wct_piece 34 239542 47
  · wct_piece 34 239544 48
  · wct_piece 34 239548 49
  · wct_piece 34 239554 50
  · wct_piece 34 239556 51
  · wct_piece 34 239560 52
  · wct_piece 34 239566 53
  · wct_piece 34 239570 54
  · wct_piece 0 966 57
theorem routine520_ready : RoutineReady ⟨520, by decide⟩ routine520 := by
  wct_ready_start 520 16 8
  wct_cases [239571,239577,239583,239585,239589,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 34 239571 55
  · wct_piece 34 239577 56
  · wct_piece 34 239583 57
  · wct_piece 34 239585 58
  · wct_piece 34 239589 59
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
  wct_cases [239590,239596,239602,239604,239608,236248,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 34 239590 60
  · wct_piece 34 239596 61
  · wct_piece 34 239602 62
  · wct_piece 34 239604 63
  · wct_piece 35 239608 0
  · wct_piece 22 236248 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine522_ready : RoutineReady ⟨522, by decide⟩ routine522 := by
  wct_ready_start 522 16 10
  wct_cases [239609,239615,239621,239624,236260,236266,236270,4391,2078,1120,805,811,814]
  · wct_piece 35 239609 1
  · wct_piece 35 239615 2
  · wct_piece 35 239621 3
  · wct_piece 35 239624 4
  · wct_piece 22 236260 24
  · wct_piece 22 236266 25
  · wct_piece 22 236270 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine523_ready : RoutineReady ⟨523, by decide⟩ routine523 := by
  wct_ready_start 523 16 11
  wct_cases [239625,239631,239637,239640,239646,239650,4412,2099,1138,1144,875,881]
  · wct_piece 35 239625 5
  · wct_piece 35 239631 6
  · wct_piece 35 239637 7
  · wct_piece 35 239640 8
  · wct_piece 35 239646 9
  · wct_piece 35 239650 10
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine524_ready : RoutineReady ⟨524, by decide⟩ routine524 := by
  wct_ready_start 524 16 12
  wct_cases [239651,239657,239663,239666,239672,239676,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 35 239651 11
  · wct_piece 35 239657 12
  · wct_piece 35 239663 13
  · wct_piece 35 239666 14
  · wct_piece 35 239672 15
  · wct_piece 35 239676 16
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine525_ready : RoutineReady ⟨525, by decide⟩ routine525 := by
  wct_ready_start 525 16 13
  wct_cases [239677,239683,239689,239692,239698,239702,239708,239712,239718]
  · wct_piece 35 239677 17
  · wct_piece 35 239683 18
  · wct_piece 35 239689 19
  · wct_piece 35 239692 20
  · wct_piece 35 239698 21
  · wct_piece 35 239702 22
  · wct_piece 35 239708 23
  · wct_piece 35 239712 24
  · wct_piece 35 239718 25
theorem routine526_ready : RoutineReady ⟨526, by decide⟩ routine526 := by
  wct_ready_start 526 16 14
  wct_cases [239724,239730,239736,239739,239745,239749,239755,239761,239765]
  · wct_piece 35 239724 26
  · wct_piece 35 239730 27
  · wct_piece 35 239736 28
  · wct_piece 35 239739 29
  · wct_piece 35 239745 30
  · wct_piece 35 239749 31
  · wct_piece 35 239755 32
  · wct_piece 35 239761 33
  · wct_piece 35 239765 34
theorem routine527_ready : RoutineReady ⟨527, by decide⟩ routine527 := by
  wct_ready_start 527 16 15
  wct_cases [239771,239777,239783,239786,239792,239796,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 35 239771 35
  · wct_piece 35 239777 36
  · wct_piece 35 239783 37
  · wct_piece 35 239786 38
  · wct_piece 35 239792 39
  · wct_piece 35 239796 40
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine528_ready : RoutineReady ⟨528, by decide⟩ routine528 := by
  wct_ready_start 528 16 16
  wct_cases [239797,239803,239809,239812,239818,4514,4520,4524,2681,1365,875,881]
  · wct_piece 35 239797 41
  · wct_piece 35 239803 42
  · wct_piece 35 239809 43
  · wct_piece 35 239812 44
  · wct_piece 35 239818 45
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine529_ready : RoutineReady ⟨529, by decide⟩ routine529 := by
  wct_ready_start 529 16 17
  wct_cases [239819,239825,239831,239834,239840,239846,239850,239856,239860]
  · wct_piece 35 239819 46
  · wct_piece 35 239825 47
  · wct_piece 35 239831 48
  · wct_piece 35 239834 49
  · wct_piece 35 239840 50
  · wct_piece 35 239846 51
  · wct_piece 35 239850 52
  · wct_piece 35 239856 53
  · wct_piece 35 239860 54
theorem routine530_ready : RoutineReady ⟨530, by decide⟩ routine530 := by
  wct_ready_start 530 16 18
  wct_cases [239866,239872,239878,239881,239887,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 35 239866 55
  · wct_piece 35 239872 56
  · wct_piece 35 239878 57
  · wct_piece 35 239881 58
  · wct_piece 35 239887 59
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine531_ready : RoutineReady ⟨531, by decide⟩ routine531 := by
  wct_ready_start 531 16 19
  wct_cases [239888,239894,239900,239903,236446,236452,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 35 239888 60
  · wct_piece 35 239894 61
  · wct_piece 35 239900 62
  · wct_piece 35 239903 63
  · wct_piece 23 236446 11
  · wct_piece 23 236452 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine532_ready : RoutineReady ⟨532, by decide⟩ routine532 := by
  wct_ready_start 532 16 20
  wct_cases [239904,239910,239916,239919,236464,236470,236472,236476,235869,2681,1365,875,881]
  · wct_piece 36 239904 0
  · wct_piece 36 239910 1
  · wct_piece 36 239916 2
  · wct_piece 36 239919 3
  · wct_piece 23 236464 16
  · wct_piece 23 236470 17
  · wct_piece 23 236472 18
  · wct_piece 23 236476 19
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine533_ready : RoutineReady ⟨533, by decide⟩ routine533 := by
  wct_ready_start 533 16 21
  wct_cases [239920,239926,239932,239935,239941,239943,239947,235893,2705,1386,1392,1396,966]
  · wct_piece 36 239920 4
  · wct_piece 36 239926 5
  · wct_piece 36 239932 6
  · wct_piece 36 239935 7
  · wct_piece 36 239941 8
  · wct_piece 36 239943 9
  · wct_piece 36 239947 10
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine534_ready : RoutineReady ⟨534, by decide⟩ routine534 := by
  wct_ready_start 534 16 22
  wct_cases [239948,239954,239960,239963,239969,239971,239975,235917,2726,2732,2736,1585,966]
  · wct_piece 36 239948 11
  · wct_piece 36 239954 12
  · wct_piece 36 239960 13
  · wct_piece 36 239963 14
  · wct_piece 36 239969 15
  · wct_piece 36 239971 16
  · wct_piece 36 239975 17
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine535_ready : RoutineReady ⟨535, by decide⟩ routine535 := by
  wct_ready_start 535 16 23
  wct_cases [239976,239982,239988,239991,236536,236542,236545,235938,235944,235948,3101,1585,966]
  · wct_piece 36 239976 18
  · wct_piece 36 239982 19
  · wct_piece 36 239988 20
  · wct_piece 36 239991 21
  · wct_piece 23 236536 37
  · wct_piece 23 236542 38
  · wct_piece 23 236545 39
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine536_ready : RoutineReady ⟨536, by decide⟩ routine536 := by
  wct_ready_start 536 16 24
  wct_cases [239992,239998,240004,240007,236557,236563,236565,236567,236571,3101,1585,966]
  · wct_piece 36 239992 22
  · wct_piece 36 239998 23
  · wct_piece 36 240004 24
  · wct_piece 36 240007 25
  · wct_piece 23 236557 43
  · wct_piece 23 236563 44
  · wct_piece 23 236565 45
  · wct_piece 23 236567 46
  · wct_piece 23 236571 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine537_ready : RoutineReady ⟨537, by decide⟩ routine537 := by
  wct_ready_start 537 16 25
  wct_cases [240008,240014,240020,240022,240024,240028,4391,2078,1120,805,811,814]
  · wct_piece 36 240008 26
  · wct_piece 36 240014 27
  · wct_piece 36 240020 28
  · wct_piece 36 240022 29
  · wct_piece 36 240024 30
  · wct_piece 36 240028 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine538_ready : RoutineReady ⟨538, by decide⟩ routine538 := by
  wct_ready_start 538 16 26
  wct_cases [240029,240035,240041,240043,240045,240049,4412,2099,1138,1144,875,881]
  · wct_piece 36 240029 32
  · wct_piece 36 240035 33
  · wct_piece 36 240041 34
  · wct_piece 36 240043 35
  · wct_piece 36 240045 36
  · wct_piece 36 240049 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine539_ready : RoutineReady ⟨539, by decide⟩ routine539 := by
  wct_ready_start 539 16 27
  wct_cases [240050,240056,240062,240064,240066,240070,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 36 240050 38
  · wct_piece 36 240056 39
  · wct_piece 36 240062 40
  · wct_piece 36 240064 41
  · wct_piece 36 240066 42
  · wct_piece 36 240070 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine540_ready : RoutineReady ⟨540, by decide⟩ routine540 := by
  wct_ready_start 540 16 28
  wct_cases [240071,240077,240083,240085,240087,240091,4454,2138,2144,2148,1365,875,881]
  · wct_piece 36 240071 44
  · wct_piece 36 240077 45
  · wct_piece 36 240083 46
  · wct_piece 36 240085 47
  · wct_piece 36 240087 48
  · wct_piece 36 240091 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine541_ready : RoutineReady ⟨541, by decide⟩ routine541 := by
  wct_ready_start 541 16 29
  wct_cases [240092,240098,240104,240106,240108,240112,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 36 240092 50
  · wct_piece 36 240098 51
  · wct_piece 36 240104 52
  · wct_piece 36 240106 53
  · wct_piece 36 240108 54
  · wct_piece 36 240112 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine542_ready : RoutineReady ⟨542, by decide⟩ routine542 := by
  wct_ready_start 542 16 30
  wct_cases [240113,240119,240125,240127,240129,240133,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 36 240113 56
  · wct_piece 36 240119 57
  · wct_piece 36 240125 58
  · wct_piece 36 240127 59
  · wct_piece 36 240129 60
  · wct_piece 36 240133 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine543_ready : RoutineReady ⟨543, by decide⟩ routine543 := by
  wct_ready_start 543 16 31
  wct_cases [240134,240140,240146,240148,240150,240154,4514,4520,4524,2681,1365,875,881]
  · wct_piece 36 240134 62
  · wct_piece 36 240140 63
  · wct_piece 37 240146 0
  · wct_piece 37 240148 1
  · wct_piece 37 240150 2
  · wct_piece 37 240154 3
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
