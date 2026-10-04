import SigGolfCandidate.W9Machine.WctRoutineCheck21
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch21_checked :
    (routineBatch21.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch21_checked :
    (routineBatch21.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine672_ready : RoutineReady ⟨672, by decide⟩ routine672 := by
  wct_ready_start 672 21 0
  wct_cases [241556,241562,241564,241566,235321,2751,1411,901,755,761,763,766]
  · wct_piece 46 241556 3
  · wct_piece 46 241562 4
  · wct_piece 46 241564 5
  · wct_piece 46 241566 6
  · wct_piece 20 235321 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine673_ready : RoutineReady ⟨673, by decide⟩ routine673 := by
  wct_ready_start 673 21 1
  wct_cases [241567,241573,241575,241577,235336,2766,1426,913,919,805,811,814]
  · wct_piece 46 241567 7
  · wct_piece 46 241573 8
  · wct_piece 46 241575 9
  · wct_piece 46 241577 10
  · wct_piece 20 235336 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine674_ready : RoutineReady ⟨674, by decide⟩ routine674 := by
  wct_ready_start 674 21 2
  wct_cases [241578,241584,241586,241588,235351,2781,1441,931,937,940,875,881]
  · wct_piece 46 241578 11
  · wct_piece 46 241584 12
  · wct_piece 46 241586 13
  · wct_piece 46 241588 14
  · wct_piece 20 235351 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine675_ready : RoutineReady ⟨675, by decide⟩ routine675 := by
  wct_ready_start 675 21 3
  wct_cases [241589,241595,241597,241599,235366,2796,1456,952,958,960,962,966]
  · wct_piece 46 241589 15
  · wct_piece 46 241595 16
  · wct_piece 46 241597 17
  · wct_piece 46 241599 18
  · wct_piece 21 235366 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine676_ready : RoutineReady ⟨676, by decide⟩ routine676 := by
  wct_ready_start 676 21 4
  wct_cases [241600,241606,241608,241610,235381,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 46 241600 19
  · wct_piece 46 241606 20
  · wct_piece 46 241608 21
  · wct_piece 46 241610 22
  · wct_piece 21 235381 9
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine677_ready : RoutineReady ⟨677, by decide⟩ routine677 := by
  wct_ready_start 677 21 5
  wct_cases [241611,241617,241619,241621,235396,2826,1490,1496,1138,1144,875,881]
  · wct_piece 46 241611 23
  · wct_piece 46 241617 24
  · wct_piece 46 241619 25
  · wct_piece 46 241621 26
  · wct_piece 21 235396 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine678_ready : RoutineReady ⟨678, by decide⟩ routine678 := by
  wct_ready_start 678 21 6
  wct_cases [241622,241628,241630,241632,235411,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 46 241622 27
  · wct_piece 46 241628 28
  · wct_piece 46 241630 29
  · wct_piece 46 241632 30
  · wct_piece 21 235411 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine679_ready : RoutineReady ⟨679, by decide⟩ routine679 := by
  wct_ready_start 679 21 7
  wct_cases [241633,241639,241641,241643,235426,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 46 241633 31
  · wct_piece 46 241639 32
  · wct_piece 46 241641 33
  · wct_piece 46 241643 34
  · wct_piece 21 235426 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine680_ready : RoutineReady ⟨680, by decide⟩ routine680 := by
  wct_ready_start 680 21 8
  wct_cases [241644,241650,241652,241654,235441,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 46 241644 35
  · wct_piece 46 241650 36
  · wct_piece 46 241652 37
  · wct_piece 46 241654 38
  · wct_piece 21 235441 29
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine681_ready : RoutineReady ⟨681, by decide⟩ routine681 := by
  wct_ready_start 681 21 9
  wct_cases [241655,241661,241663,241665,235456,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 46 241655 39
  · wct_piece 46 241661 40
  · wct_piece 46 241663 41
  · wct_piece 46 241665 42
  · wct_piece 21 235456 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine682_ready : RoutineReady ⟨682, by decide⟩ routine682 := by
  wct_ready_start 682 21 10
  wct_cases [241666,241672,241674,241676,235471,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 46 241666 43
  · wct_piece 46 241672 44
  · wct_piece 46 241674 45
  · wct_piece 46 241676 46
  · wct_piece 21 235471 39
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine683_ready : RoutineReady ⟨683, by decide⟩ routine683 := by
  wct_ready_start 683 21 11
  wct_cases [241677,241683,241685,241687,235486,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 46 241677 47
  · wct_piece 46 241683 48
  · wct_piece 46 241685 49
  · wct_piece 46 241687 50
  · wct_piece 21 235486 44
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine684_ready : RoutineReady ⟨684, by decide⟩ routine684 := by
  wct_ready_start 684 21 12
  wct_cases [241688,241694,241696,241698,235501,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 46 241688 51
  · wct_piece 46 241694 52
  · wct_piece 46 241696 53
  · wct_piece 46 241698 54
  · wct_piece 21 235501 49
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine685_ready : RoutineReady ⟨685, by decide⟩ routine685 := by
  wct_ready_start 685 21 13
  wct_cases [241699,241705,241707,241709,235516,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 46 241699 55
  · wct_piece 46 241705 56
  · wct_piece 46 241707 57
  · wct_piece 46 241709 58
  · wct_piece 21 235516 54
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine686_ready : RoutineReady ⟨686, by decide⟩ routine686 := by
  wct_ready_start 686 21 14
  wct_cases [241710,241716,241718,241720,235531,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 46 241710 59
  · wct_piece 46 241716 60
  · wct_piece 46 241718 61
  · wct_piece 46 241720 62
  · wct_piece 21 235531 59
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine687_ready : RoutineReady ⟨687, by decide⟩ routine687 := by
  wct_ready_start 687 21 15
  wct_cases [241721,241727,241729,241731,235546,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 46 241721 63
  · wct_piece 47 241727 0
  · wct_piece 47 241729 1
  · wct_piece 47 241731 2
  · wct_piece 22 235546 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine688_ready : RoutineReady ⟨688, by decide⟩ routine688 := by
  wct_ready_start 688 21 16
  wct_cases [241732,241738,241740,241742,235561,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 47 241732 3
  · wct_piece 47 241738 4
  · wct_piece 47 241740 5
  · wct_piece 47 241742 6
  · wct_piece 22 235561 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine689_ready : RoutineReady ⟨689, by decide⟩ routine689 := by
  wct_ready_start 689 21 17
  wct_cases [241743,241749,241751,241753,235576,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 47 241743 7
  · wct_piece 47 241749 8
  · wct_piece 47 241751 9
  · wct_piece 47 241753 10
  · wct_piece 22 235576 10
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine690_ready : RoutineReady ⟨690, by decide⟩ routine690 := by
  wct_ready_start 690 21 18
  wct_cases [241754,241760,241762,241764,235591,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 47 241754 11
  · wct_piece 47 241760 12
  · wct_piece 47 241762 13
  · wct_piece 47 241764 14
  · wct_piece 22 235591 15
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine691_ready : RoutineReady ⟨691, by decide⟩ routine691 := by
  wct_ready_start 691 21 19
  wct_cases [241765,241771,241773,241775,235606,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 47 241765 15
  · wct_piece 47 241771 16
  · wct_piece 47 241773 17
  · wct_piece 47 241775 18
  · wct_piece 22 235606 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine692_ready : RoutineReady ⟨692, by decide⟩ routine692 := by
  wct_ready_start 692 21 20
  wct_cases [241776,241782,241784,241786,235618,235624,235628,4391,2078,1120,805,811,814]
  · wct_piece 47 241776 19
  · wct_piece 47 241782 20
  · wct_piece 47 241784 21
  · wct_piece 47 241786 22
  · wct_piece 22 235618 24
  · wct_piece 22 235624 25
  · wct_piece 22 235628 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine693_ready : RoutineReady ⟨693, by decide⟩ routine693 := by
  wct_ready_start 693 21 21
  wct_cases [241787,241793,241795,241797,235640,235646,235650,4412,2099,1138,1144,875,881]
  · wct_piece 47 241787 23
  · wct_piece 47 241793 24
  · wct_piece 47 241795 25
  · wct_piece 47 241797 26
  · wct_piece 22 235640 30
  · wct_piece 22 235646 31
  · wct_piece 22 235650 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine694_ready : RoutineReady ⟨694, by decide⟩ routine694 := by
  wct_ready_start 694 21 22
  wct_cases [241798,241804,241806,241808,235662,235668,235672,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 47 241798 27
  · wct_piece 47 241804 28
  · wct_piece 47 241806 29
  · wct_piece 47 241808 30
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
theorem routine695_ready : RoutineReady ⟨695, by decide⟩ routine695 := by
  wct_ready_start 695 21 23
  wct_cases [241809,241815,241817,241819,235684,235690,235694,4454,2138,2144,2148,1365,875,881]
  · wct_piece 47 241809 31
  · wct_piece 47 241815 32
  · wct_piece 47 241817 33
  · wct_piece 47 241819 34
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
theorem routine696_ready : RoutineReady ⟨696, by decide⟩ routine696 := by
  wct_ready_start 696 21 24
  wct_cases [241820,241826,241828,241830,235706,235712,235716,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 47 241820 35
  · wct_piece 47 241826 36
  · wct_piece 47 241828 37
  · wct_piece 47 241830 38
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
theorem routine697_ready : RoutineReady ⟨697, by decide⟩ routine697 := by
  wct_ready_start 697 21 25
  wct_cases [241831,241837,241839,241841,235728,235734,235738,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 47 241831 39
  · wct_piece 47 241837 40
  · wct_piece 47 241839 41
  · wct_piece 47 241841 42
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
theorem routine698_ready : RoutineReady ⟨698, by decide⟩ routine698 := by
  wct_ready_start 698 21 26
  wct_cases [241842,241848,241850,241852,235750,235756,4514,4520,4524,2681,1365,875,881]
  · wct_piece 47 241842 43
  · wct_piece 47 241848 44
  · wct_piece 47 241850 45
  · wct_piece 47 241852 46
  · wct_piece 22 235750 60
  · wct_piece 22 235756 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine699_ready : RoutineReady ⟨699, by decide⟩ routine699 := by
  wct_ready_start 699 21 27
  wct_cases [241853,241859,241861,241863,235768,235774,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 47 241853 47
  · wct_piece 47 241859 48
  · wct_piece 47 241861 49
  · wct_piece 47 241863 50
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
theorem routine700_ready : RoutineReady ⟨700, by decide⟩ routine700 := by
  wct_ready_start 700 21 28
  wct_cases [241864,241870,241872,241874,235786,235792,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 47 241864 51
  · wct_piece 47 241870 52
  · wct_piece 47 241872 53
  · wct_piece 47 241874 54
  · wct_piece 23 235786 6
  · wct_piece 23 235792 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine701_ready : RoutineReady ⟨701, by decide⟩ routine701 := by
  wct_ready_start 701 21 29
  wct_cases [241875,241881,241883,241885,235804,235810,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 47 241875 55
  · wct_piece 47 241881 56
  · wct_piece 47 241883 57
  · wct_piece 47 241885 58
  · wct_piece 23 235804 11
  · wct_piece 23 235810 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine702_ready : RoutineReady ⟨702, by decide⟩ routine702 := by
  wct_ready_start 702 21 30
  wct_cases [241886,241892,241894,241896,235822,235828,235830,235834,235227,2681,1365,875,881]
  · wct_piece 47 241886 59
  · wct_piece 47 241892 60
  · wct_piece 47 241894 61
  · wct_piece 47 241896 62
  · wct_piece 23 235822 16
  · wct_piece 23 235828 17
  · wct_piece 23 235830 18
  · wct_piece 23 235834 19
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine703_ready : RoutineReady ⟨703, by decide⟩ routine703 := by
  wct_ready_start 703 21 31
  wct_cases [241897,241903,241905,241907,235846,235852,235854,235858,235251,2705,1386,1392,1396,966]
  · wct_piece 47 241897 63
  · wct_piece 48 241903 0
  · wct_piece 48 241905 1
  · wct_piece 48 241907 2
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
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage21 (rank : Fin 728) (hlo : 672 ≤ rank.val) (hhi : rank.val < 704) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 672 ≤ n at hlo
  change n < 704 at hhi
  interval_cases n
  · exact ⟨routine672, routine672_ready⟩
  · exact ⟨routine673, routine673_ready⟩
  · exact ⟨routine674, routine674_ready⟩
  · exact ⟨routine675, routine675_ready⟩
  · exact ⟨routine676, routine676_ready⟩
  · exact ⟨routine677, routine677_ready⟩
  · exact ⟨routine678, routine678_ready⟩
  · exact ⟨routine679, routine679_ready⟩
  · exact ⟨routine680, routine680_ready⟩
  · exact ⟨routine681, routine681_ready⟩
  · exact ⟨routine682, routine682_ready⟩
  · exact ⟨routine683, routine683_ready⟩
  · exact ⟨routine684, routine684_ready⟩
  · exact ⟨routine685, routine685_ready⟩
  · exact ⟨routine686, routine686_ready⟩
  · exact ⟨routine687, routine687_ready⟩
  · exact ⟨routine688, routine688_ready⟩
  · exact ⟨routine689, routine689_ready⟩
  · exact ⟨routine690, routine690_ready⟩
  · exact ⟨routine691, routine691_ready⟩
  · exact ⟨routine692, routine692_ready⟩
  · exact ⟨routine693, routine693_ready⟩
  · exact ⟨routine694, routine694_ready⟩
  · exact ⟨routine695, routine695_ready⟩
  · exact ⟨routine696, routine696_ready⟩
  · exact ⟨routine697, routine697_ready⟩
  · exact ⟨routine698, routine698_ready⟩
  · exact ⟨routine699, routine699_ready⟩
  · exact ⟨routine700, routine700_ready⟩
  · exact ⟨routine701, routine701_ready⟩
  · exact ⟨routine702, routine702_ready⟩
  · exact ⟨routine703, routine703_ready⟩
end W9Machine.Chain
end
