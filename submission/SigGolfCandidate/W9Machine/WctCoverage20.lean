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
  wct_cases [241484,241490,241492,241498,241504,241508,241514,241518,875,881]
  · wct_piece 43 241484 4
  · wct_piece 43 241490 5
  · wct_piece 43 241492 6
  · wct_piece 43 241498 7
  · wct_piece 43 241504 8
  · wct_piece 43 241508 9
  · wct_piece 43 241514 10
  · wct_piece 43 241518 11
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine641_ready : RoutineReady ⟨641, by decide⟩ routine641 := by
  wct_ready_start 641 20 1
  wct_cases [241519,241525,241527,241533,241539,241543,241549,241555,241559,966]
  · wct_piece 43 241519 12
  · wct_piece 43 241525 13
  · wct_piece 43 241527 14
  · wct_piece 43 241533 15
  · wct_piece 43 241539 16
  · wct_piece 43 241543 17
  · wct_piece 43 241549 18
  · wct_piece 43 241555 19
  · wct_piece 43 241559 20
  · wct_piece 0 966 57
theorem routine642_ready : RoutineReady ⟨642, by decide⟩ routine642 := by
  wct_ready_start 642 20 2
  wct_cases [241560,241566,241568,241574,236370,236376,236380,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 43 241560 21
  · wct_piece 43 241566 22
  · wct_piece 43 241568 23
  · wct_piece 43 241574 24
  · wct_piece 22 236370 54
  · wct_piece 22 236376 55
  · wct_piece 22 236380 56
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine643_ready : RoutineReady ⟨643, by decide⟩ routine643 := by
  wct_ready_start 643 20 3
  wct_cases [241575,241581,241583,241589,236392,236398,4514,4520,4524,2681,1365,875,881]
  · wct_piece 43 241575 25
  · wct_piece 43 241581 26
  · wct_piece 43 241583 27
  · wct_piece 43 241589 28
  · wct_piece 22 236392 60
  · wct_piece 22 236398 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine644_ready : RoutineReady ⟨644, by decide⟩ routine644 := by
  wct_ready_start 644 20 4
  wct_cases [241590,241596,241598,241604,241610,241616,241620,241626,241630,966]
  · wct_piece 43 241590 29
  · wct_piece 43 241596 30
  · wct_piece 43 241598 31
  · wct_piece 43 241604 32
  · wct_piece 43 241610 33
  · wct_piece 43 241616 34
  · wct_piece 43 241620 35
  · wct_piece 43 241626 36
  · wct_piece 43 241630 37
  · wct_piece 0 966 57
theorem routine645_ready : RoutineReady ⟨645, by decide⟩ routine645 := by
  wct_ready_start 645 20 5
  wct_cases [241631,241637,241639,241645,236428,236434,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 43 241631 38
  · wct_piece 43 241637 39
  · wct_piece 43 241639 40
  · wct_piece 43 241645 41
  · wct_piece 23 236428 6
  · wct_piece 23 236434 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine646_ready : RoutineReady ⟨646, by decide⟩ routine646 := by
  wct_ready_start 646 20 6
  wct_cases [241646,241652,241654,241660,236446,236452,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 43 241646 42
  · wct_piece 43 241652 43
  · wct_piece 43 241654 44
  · wct_piece 43 241660 45
  · wct_piece 23 236446 11
  · wct_piece 23 236452 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine647_ready : RoutineReady ⟨647, by decide⟩ routine647 := by
  wct_ready_start 647 20 7
  wct_cases [241661,241667,241669,241675,236464,236470,236472,236476,235869,2681,1365,875,881]
  · wct_piece 43 241661 46
  · wct_piece 43 241667 47
  · wct_piece 43 241669 48
  · wct_piece 43 241675 49
  · wct_piece 23 236464 16
  · wct_piece 23 236470 17
  · wct_piece 23 236472 18
  · wct_piece 23 236476 19
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine648_ready : RoutineReady ⟨648, by decide⟩ routine648 := by
  wct_ready_start 648 20 8
  wct_cases [241676,241682,241684,241690,236488,236494,236496,236500,235893,2705,1386,1392,1396,966]
  · wct_piece 43 241676 50
  · wct_piece 43 241682 51
  · wct_piece 43 241684 52
  · wct_piece 43 241690 53
  · wct_piece 23 236488 23
  · wct_piece 23 236494 24
  · wct_piece 23 236496 25
  · wct_piece 23 236500 26
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine649_ready : RoutineReady ⟨649, by decide⟩ routine649 := by
  wct_ready_start 649 20 9
  wct_cases [241691,241697,241699,241705,236512,236518,236520,236524,235917,2726,2732,2736,1585,966]
  · wct_piece 43 241691 54
  · wct_piece 43 241697 55
  · wct_piece 43 241699 56
  · wct_piece 43 241705 57
  · wct_piece 23 236512 30
  · wct_piece 23 236518 31
  · wct_piece 23 236520 32
  · wct_piece 23 236524 33
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine650_ready : RoutineReady ⟨650, by decide⟩ routine650 := by
  wct_ready_start 650 20 10
  wct_cases [241706,241712,241714,241720,236536,236542,236545,235938,235944,235948,3101,1585,966]
  · wct_piece 43 241706 58
  · wct_piece 43 241712 59
  · wct_piece 43 241714 60
  · wct_piece 43 241720 61
  · wct_piece 23 236536 37
  · wct_piece 23 236542 38
  · wct_piece 23 236545 39
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine651_ready : RoutineReady ⟨651, by decide⟩ routine651 := by
  wct_ready_start 651 20 11
  wct_cases [241721,241727,241729,241735,236557,236563,236565,236567,236571,3101,1585,966]
  · wct_piece 43 241721 62
  · wct_piece 43 241727 63
  · wct_piece 44 241729 0
  · wct_piece 44 241735 1
  · wct_piece 23 236557 43
  · wct_piece 23 236563 44
  · wct_piece 23 236565 45
  · wct_piece 23 236567 46
  · wct_piece 23 236571 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine652_ready : RoutineReady ⟨652, by decide⟩ routine652 := by
  wct_ready_start 652 20 12
  wct_cases [241736,241742,241744,241750,241752,241756,240028,4391,2078,1120,805,811,814]
  · wct_piece 44 241736 2
  · wct_piece 44 241742 3
  · wct_piece 44 241744 4
  · wct_piece 44 241750 5
  · wct_piece 44 241752 6
  · wct_piece 44 241756 7
  · wct_piece 36 240028 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine653_ready : RoutineReady ⟨653, by decide⟩ routine653 := by
  wct_ready_start 653 20 13
  wct_cases [241757,241763,241765,241771,241773,241777,240049,4412,2099,1138,1144,875,881]
  · wct_piece 44 241757 8
  · wct_piece 44 241763 9
  · wct_piece 44 241765 10
  · wct_piece 44 241771 11
  · wct_piece 44 241773 12
  · wct_piece 44 241777 13
  · wct_piece 36 240049 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine654_ready : RoutineReady ⟨654, by decide⟩ routine654 := by
  wct_ready_start 654 20 14
  wct_cases [241778,241784,241786,241792,241794,241798,240070,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 44 241778 14
  · wct_piece 44 241784 15
  · wct_piece 44 241786 16
  · wct_piece 44 241792 17
  · wct_piece 44 241794 18
  · wct_piece 44 241798 19
  · wct_piece 36 240070 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine655_ready : RoutineReady ⟨655, by decide⟩ routine655 := by
  wct_ready_start 655 20 15
  wct_cases [241799,241805,241807,241813,241815,241819,240091,4454,2138,2144,2148,1365,875,881]
  · wct_piece 44 241799 20
  · wct_piece 44 241805 21
  · wct_piece 44 241807 22
  · wct_piece 44 241813 23
  · wct_piece 44 241815 24
  · wct_piece 44 241819 25
  · wct_piece 36 240091 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine656_ready : RoutineReady ⟨656, by decide⟩ routine656 := by
  wct_ready_start 656 20 16
  wct_cases [241820,241826,241828,241834,241836,241840,240112,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 44 241820 26
  · wct_piece 44 241826 27
  · wct_piece 44 241828 28
  · wct_piece 44 241834 29
  · wct_piece 44 241836 30
  · wct_piece 44 241840 31
  · wct_piece 36 240112 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine657_ready : RoutineReady ⟨657, by decide⟩ routine657 := by
  wct_ready_start 657 20 17
  wct_cases [241841,241847,241849,241855,241857,241861,240133,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 44 241841 32
  · wct_piece 44 241847 33
  · wct_piece 44 241849 34
  · wct_piece 44 241855 35
  · wct_piece 44 241857 36
  · wct_piece 44 241861 37
  · wct_piece 36 240133 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine658_ready : RoutineReady ⟨658, by decide⟩ routine658 := by
  wct_ready_start 658 20 18
  wct_cases [241862,241868,241870,241876,241878,241882,240154,4514,4520,4524,2681,1365,875,881]
  · wct_piece 44 241862 38
  · wct_piece 44 241868 39
  · wct_piece 44 241870 40
  · wct_piece 44 241876 41
  · wct_piece 44 241878 42
  · wct_piece 44 241882 43
  · wct_piece 37 240154 3
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine659_ready : RoutineReady ⟨659, by decide⟩ routine659 := by
  wct_ready_start 659 20 19
  wct_cases [241883,241889,241891,241897,241899,241903,241909,241913,241919,241923,966]
  · wct_piece 44 241883 44
  · wct_piece 44 241889 45
  · wct_piece 44 241891 46
  · wct_piece 44 241897 47
  · wct_piece 44 241899 48
  · wct_piece 44 241903 49
  · wct_piece 44 241909 50
  · wct_piece 44 241913 51
  · wct_piece 44 241919 52
  · wct_piece 44 241923 53
  · wct_piece 0 966 57
theorem routine660_ready : RoutineReady ⟨660, by decide⟩ routine660 := by
  wct_ready_start 660 20 20
  wct_cases [241924,241930,241932,241938,241940,241944,240216,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 44 241924 54
  · wct_piece 44 241930 55
  · wct_piece 44 241932 56
  · wct_piece 44 241938 57
  · wct_piece 44 241940 58
  · wct_piece 44 241944 59
  · wct_piece 37 240216 19
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine661_ready : RoutineReady ⟨661, by decide⟩ routine661 := by
  wct_ready_start 661 20 21
  wct_cases [241945,241951,241953,241959,241961,241965,240237,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 44 241945 60
  · wct_piece 44 241951 61
  · wct_piece 44 241953 62
  · wct_piece 44 241959 63
  · wct_piece 45 241961 0
  · wct_piece 45 241965 1
  · wct_piece 37 240237 25
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine662_ready : RoutineReady ⟨662, by decide⟩ routine662 := by
  wct_ready_start 662 20 22
  wct_cases [241966,241972,241974,241980,241983,240255,240261,240265,235869,2681,1365,875,881]
  · wct_piece 45 241966 2
  · wct_piece 45 241972 3
  · wct_piece 45 241974 4
  · wct_piece 45 241980 5
  · wct_piece 45 241983 6
  · wct_piece 37 240255 30
  · wct_piece 37 240261 31
  · wct_piece 37 240265 32
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine663_ready : RoutineReady ⟨663, by decide⟩ routine663 := by
  wct_ready_start 663 20 23
  wct_cases [241984,241990,241992,241998,242001,242007,242011,235893,2705,1386,1392,1396,966]
  · wct_piece 45 241984 7
  · wct_piece 45 241990 8
  · wct_piece 45 241992 9
  · wct_piece 45 241998 10
  · wct_piece 45 242001 11
  · wct_piece 45 242007 12
  · wct_piece 45 242011 13
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine664_ready : RoutineReady ⟨664, by decide⟩ routine664 := by
  wct_ready_start 664 20 24
  wct_cases [242012,242018,242020,242026,242029,242035,242039,235917,2726,2732,2736,1585,966]
  · wct_piece 45 242012 14
  · wct_piece 45 242018 15
  · wct_piece 45 242020 16
  · wct_piece 45 242026 17
  · wct_piece 45 242029 18
  · wct_piece 45 242035 19
  · wct_piece 45 242039 20
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine665_ready : RoutineReady ⟨665, by decide⟩ routine665 := by
  wct_ready_start 665 20 25
  wct_cases [242040,242046,242048,242054,242057,240339,240345,235938,235944,235948,3101,1585,966]
  · wct_piece 45 242040 21
  · wct_piece 45 242046 22
  · wct_piece 45 242048 23
  · wct_piece 45 242054 24
  · wct_piece 45 242057 25
  · wct_piece 37 240339 51
  · wct_piece 37 240345 52
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine666_ready : RoutineReady ⟨666, by decide⟩ routine666 := by
  wct_ready_start 666 20 26
  wct_cases [242058,242064,242066,242072,242075,240363,240369,240371,240375,236571,3101,1585,966]
  · wct_piece 45 242058 26
  · wct_piece 45 242064 27
  · wct_piece 45 242066 28
  · wct_piece 45 242072 29
  · wct_piece 45 242075 30
  · wct_piece 37 240363 57
  · wct_piece 37 240369 58
  · wct_piece 37 240371 59
  · wct_piece 37 240375 60
  · wct_piece 23 236571 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine667_ready : RoutineReady ⟨667, by decide⟩ routine667 := by
  wct_ready_start 667 20 27
  wct_cases [242076,242082,242084,242090,242092,242094,242098,235869,2681,1365,875,881]
  · wct_piece 45 242076 31
  · wct_piece 45 242082 32
  · wct_piece 45 242084 33
  · wct_piece 45 242090 34
  · wct_piece 45 242092 35
  · wct_piece 45 242094 36
  · wct_piece 45 242098 37
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine668_ready : RoutineReady ⟨668, by decide⟩ routine668 := by
  wct_ready_start 668 20 28
  wct_cases [242099,242105,242107,242113,242115,242117,242121,235893,2705,1386,1392,1396,966]
  · wct_piece 45 242099 38
  · wct_piece 45 242105 39
  · wct_piece 45 242107 40
  · wct_piece 45 242113 41
  · wct_piece 45 242115 42
  · wct_piece 45 242117 43
  · wct_piece 45 242121 44
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine669_ready : RoutineReady ⟨669, by decide⟩ routine669 := by
  wct_ready_start 669 20 29
  wct_cases [242122,242128,242130,242136,242138,242140,242144,235917,2726,2732,2736,1585,966]
  · wct_piece 45 242122 45
  · wct_piece 45 242128 46
  · wct_piece 45 242130 47
  · wct_piece 45 242136 48
  · wct_piece 45 242138 49
  · wct_piece 45 242140 50
  · wct_piece 45 242144 51
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine670_ready : RoutineReady ⟨670, by decide⟩ routine670 := by
  wct_ready_start 670 20 30
  wct_cases [242145,242151,242153,242159,242161,242163,242167,235938,235944,235948,3101,1585,966]
  · wct_piece 45 242145 52
  · wct_piece 45 242151 53
  · wct_piece 45 242153 54
  · wct_piece 45 242159 55
  · wct_piece 45 242161 56
  · wct_piece 45 242163 57
  · wct_piece 45 242167 58
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine671_ready : RoutineReady ⟨671, by decide⟩ routine671 := by
  wct_ready_start 671 20 31
  wct_cases [242168,242174,242176,242182,242184,242187,242193,242197,236571,3101,1585,966]
  · wct_piece 45 242168 59
  · wct_piece 45 242174 60
  · wct_piece 45 242176 61
  · wct_piece 45 242182 62
  · wct_piece 45 242184 63
  · wct_piece 46 242187 0
  · wct_piece 46 242193 1
  · wct_piece 46 242197 2
  · wct_piece 23 236571 47
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
