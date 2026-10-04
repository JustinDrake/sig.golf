import SigGolfCandidate.W9Machine.WctRoutineCheck18
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch18_checked :
    (routineBatch18.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch18_checked :
    (routineBatch18.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine576_ready : RoutineReady ⟨576, by decide⟩ routine576 := by
  wct_ready_start 576 18 0
  wct_cases [240592,240598,240600,235189,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 39 240592 5
  · wct_piece 39 240598 6
  · wct_piece 39 240600 7
  · wct_piece 17 235189 39
  · wct_piece 7 2588 43
  · wct_piece 7 2594 44
  · wct_piece 7 2596 45
  · wct_piece 7 2600 46
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine577_ready : RoutineReady ⟨577, by decide⟩ routine577 := by
  wct_ready_start 577 18 1
  wct_cases [240601,240607,240609,235202,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 39 240601 8
  · wct_piece 39 240607 9
  · wct_piece 39 240609 10
  · wct_piece 17 235202 43
  · wct_piece 7 2610 49
  · wct_piece 7 2616 50
  · wct_piece 7 2619 51
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine578_ready : RoutineReady ⟨578, by decide⟩ routine578 := by
  wct_ready_start 578 18 2
  wct_cases [240610,240616,240618,235215,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 39 240610 11
  · wct_piece 39 240616 12
  · wct_piece 39 240618 13
  · wct_piece 17 235215 47
  · wct_piece 7 2629 54
  · wct_piece 7 2635 55
  · wct_piece 7 2638 56
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine579_ready : RoutineReady ⟨579, by decide⟩ routine579 := by
  wct_ready_start 579 18 3
  wct_cases [240619,240625,240627,235228,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 39 240619 14
  · wct_piece 39 240625 15
  · wct_piece 39 240627 16
  · wct_piece 17 235228 51
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine580_ready : RoutineReady ⟨580, by decide⟩ routine580 := by
  wct_ready_start 580 18 4
  wct_cases [240628,240634,240636,235241,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 39 240628 17
  · wct_piece 39 240634 18
  · wct_piece 39 240636 19
  · wct_piece 17 235241 55
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine581_ready : RoutineReady ⟨581, by decide⟩ routine581 := by
  wct_ready_start 581 18 5
  wct_cases [240637,240643,240645,235254,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 39 240637 20
  · wct_piece 39 240643 21
  · wct_piece 39 240645 22
  · wct_piece 17 235254 59
  · wct_piece 8 2691 7
  · wct_piece 8 2697 8
  · wct_piece 8 2699 9
  · wct_piece 8 2701 10
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine582_ready : RoutineReady ⟨582, by decide⟩ routine582 := by
  wct_ready_start 582 18 6
  wct_cases [240646,240652,240654,235267,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 39 240646 23
  · wct_piece 39 240652 24
  · wct_piece 39 240654 25
  · wct_piece 17 235267 63
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine583_ready : RoutineReady ⟨583, by decide⟩ routine583 := by
  wct_ready_start 583 18 7
  wct_cases [240655,240661,240663,235277,235283,235287,2751,1411,901,755,761,763,766]
  · wct_piece 39 240655 26
  · wct_piece 39 240661 27
  · wct_piece 39 240663 28
  · wct_piece 18 235277 2
  · wct_piece 18 235283 3
  · wct_piece 18 235287 4
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine584_ready : RoutineReady ⟨584, by decide⟩ routine584 := by
  wct_ready_start 584 18 8
  wct_cases [240664,240670,240672,235297,235303,235307,2766,1426,913,919,805,811,814]
  · wct_piece 39 240664 29
  · wct_piece 39 240670 30
  · wct_piece 39 240672 31
  · wct_piece 18 235297 7
  · wct_piece 18 235303 8
  · wct_piece 18 235307 9
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine585_ready : RoutineReady ⟨585, by decide⟩ routine585 := by
  wct_ready_start 585 18 9
  wct_cases [240673,240679,240681,235317,235323,235327,2781,1441,931,937,940,875,881]
  · wct_piece 39 240673 32
  · wct_piece 39 240679 33
  · wct_piece 39 240681 34
  · wct_piece 18 235317 12
  · wct_piece 18 235323 13
  · wct_piece 18 235327 14
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine586_ready : RoutineReady ⟨586, by decide⟩ routine586 := by
  wct_ready_start 586 18 10
  wct_cases [240682,240688,240690,235337,235343,235347,2796,1456,952,958,960,962,966]
  · wct_piece 39 240682 35
  · wct_piece 39 240688 36
  · wct_piece 39 240690 37
  · wct_piece 18 235337 17
  · wct_piece 18 235343 18
  · wct_piece 18 235347 19
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine587_ready : RoutineReady ⟨587, by decide⟩ routine587 := by
  wct_ready_start 587 18 11
  wct_cases [240691,240697,240699,235357,235363,235367,1468,1474,1478,1120,805,811,814]
  · wct_piece 39 240691 38
  · wct_piece 39 240697 39
  · wct_piece 39 240699 40
  · wct_piece 18 235357 22
  · wct_piece 18 235363 23
  · wct_piece 18 235367 24
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine588_ready : RoutineReady ⟨588, by decide⟩ routine588 := by
  wct_ready_start 588 18 12
  wct_cases [240700,240706,240708,235377,235383,235387,2826,1490,1496,1138,1144,875,881]
  · wct_piece 39 240700 41
  · wct_piece 39 240706 42
  · wct_piece 39 240708 43
  · wct_piece 18 235377 27
  · wct_piece 18 235383 28
  · wct_piece 18 235387 29
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine589_ready : RoutineReady ⟨589, by decide⟩ routine589 := by
  wct_ready_start 589 18 13
  wct_cases [240709,240715,240717,235397,235403,235407,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 39 240709 44
  · wct_piece 39 240715 45
  · wct_piece 39 240717 46
  · wct_piece 18 235397 32
  · wct_piece 18 235403 33
  · wct_piece 18 235407 34
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine590_ready : RoutineReady ⟨590, by decide⟩ routine590 := by
  wct_ready_start 590 18 14
  wct_cases [240718,240724,240726,235417,235423,235427,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 39 240718 47
  · wct_piece 39 240724 48
  · wct_piece 39 240726 49
  · wct_piece 18 235417 37
  · wct_piece 18 235423 38
  · wct_piece 18 235427 39
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine591_ready : RoutineReady ⟨591, by decide⟩ routine591 := by
  wct_ready_start 591 18 15
  wct_cases [240727,240733,240735,235437,235443,235447,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 39 240727 50
  · wct_piece 39 240733 51
  · wct_piece 39 240735 52
  · wct_piece 18 235437 42
  · wct_piece 18 235443 43
  · wct_piece 18 235447 44
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine592_ready : RoutineReady ⟨592, by decide⟩ routine592 := by
  wct_ready_start 592 18 16
  wct_cases [240736,240742,240744,235457,235463,235467,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 39 240736 53
  · wct_piece 39 240742 54
  · wct_piece 39 240744 55
  · wct_piece 18 235457 47
  · wct_piece 18 235463 48
  · wct_piece 18 235467 49
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine593_ready : RoutineReady ⟨593, by decide⟩ routine593 := by
  wct_ready_start 593 18 17
  wct_cases [240745,240751,240753,235477,235483,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 39 240745 56
  · wct_piece 39 240751 57
  · wct_piece 39 240753 58
  · wct_piece 18 235477 52
  · wct_piece 18 235483 53
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine594_ready : RoutineReady ⟨594, by decide⟩ routine594 := by
  wct_ready_start 594 18 18
  wct_cases [240754,240760,240762,235493,235499,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 39 240754 59
  · wct_piece 39 240760 60
  · wct_piece 39 240762 61
  · wct_piece 18 235493 56
  · wct_piece 18 235499 57
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine595_ready : RoutineReady ⟨595, by decide⟩ routine595 := by
  wct_ready_start 595 18 19
  wct_cases [240763,240769,240771,235509,235515,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 39 240763 62
  · wct_piece 39 240769 63
  · wct_piece 40 240771 0
  · wct_piece 18 235509 60
  · wct_piece 18 235515 61
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine596_ready : RoutineReady ⟨596, by decide⟩ routine596 := by
  wct_ready_start 596 18 20
  wct_cases [240772,240778,240780,235525,235531,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 40 240772 1
  · wct_piece 40 240778 2
  · wct_piece 40 240780 3
  · wct_piece 19 235525 0
  · wct_piece 19 235531 1
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine597_ready : RoutineReady ⟨597, by decide⟩ routine597 := by
  wct_ready_start 597 18 21
  wct_cases [240781,240787,240789,235541,235547,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 40 240781 4
  · wct_piece 40 240787 5
  · wct_piece 40 240789 6
  · wct_piece 19 235541 4
  · wct_piece 19 235547 5
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine598_ready : RoutineReady ⟨598, by decide⟩ routine598 := by
  wct_ready_start 598 18 22
  wct_cases [240790,240796,240798,235557,235563,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 40 240790 7
  · wct_piece 40 240796 8
  · wct_piece 40 240798 9
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
theorem routine599_ready : RoutineReady ⟨599, by decide⟩ routine599 := by
  wct_ready_start 599 18 23
  wct_cases [240799,240805,240807,235573,235579,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 40 240799 10
  · wct_piece 40 240805 11
  · wct_piece 40 240807 12
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
theorem routine600_ready : RoutineReady ⟨600, by decide⟩ routine600 := by
  wct_ready_start 600 18 24
  wct_cases [240808,240814,240816,235589,235595,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 40 240808 13
  · wct_piece 40 240814 14
  · wct_piece 40 240816 15
  · wct_piece 19 235589 16
  · wct_piece 19 235595 17
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine601_ready : RoutineReady ⟨601, by decide⟩ routine601 := by
  wct_ready_start 601 18 25
  wct_cases [240817,240823,240825,235605,235611,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 40 240817 16
  · wct_piece 40 240823 17
  · wct_piece 40 240825 18
  · wct_piece 19 235605 20
  · wct_piece 19 235611 21
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine602_ready : RoutineReady ⟨602, by decide⟩ routine602 := by
  wct_ready_start 602 18 26
  wct_cases [240826,240832,240834,235621,235627,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 40 240826 19
  · wct_piece 40 240832 20
  · wct_piece 40 240834 21
  · wct_piece 19 235621 24
  · wct_piece 19 235627 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine603_ready : RoutineReady ⟨603, by decide⟩ routine603 := by
  wct_ready_start 603 18 27
  wct_cases [240835,240841,240843,235637,235643,235645,235649,4391,2078,1120,805,811,814]
  · wct_piece 40 240835 22
  · wct_piece 40 240841 23
  · wct_piece 40 240843 24
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
theorem routine604_ready : RoutineReady ⟨604, by decide⟩ routine604 := by
  wct_ready_start 604 18 28
  wct_cases [240844,240850,240852,235659,235665,235667,235671,4412,2099,1138,1144,875,881]
  · wct_piece 40 240844 25
  · wct_piece 40 240850 26
  · wct_piece 40 240852 27
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
theorem routine605_ready : RoutineReady ⟨605, by decide⟩ routine605 := by
  wct_ready_start 605 18 29
  wct_cases [240853,240859,240861,235681,235687,235689,235693,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 40 240853 28
  · wct_piece 40 240859 29
  · wct_piece 40 240861 30
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
theorem routine606_ready : RoutineReady ⟨606, by decide⟩ routine606 := by
  wct_ready_start 606 18 30
  wct_cases [240862,240868,240870,235703,235709,235711,235715,4454,2138,2144,2148,1365,875,881]
  · wct_piece 40 240862 31
  · wct_piece 40 240868 32
  · wct_piece 40 240870 33
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
theorem routine607_ready : RoutineReady ⟨607, by decide⟩ routine607 := by
  wct_ready_start 607 18 31
  wct_cases [240871,240877,240879,235725,235731,235733,235737,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 40 240871 34
  · wct_piece 40 240877 35
  · wct_piece 40 240879 36
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
end W9Machine.Chain
end
