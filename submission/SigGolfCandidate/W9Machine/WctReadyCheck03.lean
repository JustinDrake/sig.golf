import SigGolfCandidate.W9Machine.WctRoutineCheck03
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch03_checked :
    (routineBatch03.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch03_checked :
    (routineBatch03.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine96_ready : RoutineReady ⟨96, by decide⟩ routine96 := by
  wct_ready_start 96 3 0
  wct_cases [2359,2365,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 6 2359 49
  · wct_piece 6 2365 50
  · wct_piece 6 2368 51
  · wct_piece 6 2374 52
  · wct_piece 6 2378 53
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine97_ready : RoutineReady ⟨97, by decide⟩ routine97 := by
  wct_ready_start 97 3 1
  wct_cases [2379,2385,2388,2394,2398,1426,913,919,805,811,814]
  · wct_piece 6 2379 54
  · wct_piece 6 2385 55
  · wct_piece 6 2388 56
  · wct_piece 6 2394 57
  · wct_piece 6 2398 58
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine98_ready : RoutineReady ⟨98, by decide⟩ routine98 := by
  wct_ready_start 98 3 2
  wct_cases [2399,2405,2408,2414,2418,1441,931,937,940,875,881]
  · wct_piece 6 2399 59
  · wct_piece 6 2405 60
  · wct_piece 6 2408 61
  · wct_piece 6 2414 62
  · wct_piece 6 2418 63
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine99_ready : RoutineReady ⟨99, by decide⟩ routine99 := by
  wct_ready_start 99 3 3
  wct_cases [2419,2425,2428,2434,2438,1456,952,958,960,962,966]
  · wct_piece 7 2419 0
  · wct_piece 7 2425 1
  · wct_piece 7 2428 2
  · wct_piece 7 2434 3
  · wct_piece 7 2438 4
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine100_ready : RoutineReady ⟨100, by decide⟩ routine100 := by
  wct_ready_start 100 3 4
  wct_cases [2439,2445,2448,2454,1468,1474,1478,1120,805,811,814]
  · wct_piece 7 2439 5
  · wct_piece 7 2445 6
  · wct_piece 7 2448 7
  · wct_piece 7 2454 8
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine101_ready : RoutineReady ⟨101, by decide⟩ routine101 := by
  wct_ready_start 101 3 5
  wct_cases [2455,2461,2464,2470,1490,1496,1138,1144,875,881]
  · wct_piece 7 2455 9
  · wct_piece 7 2461 10
  · wct_piece 7 2464 11
  · wct_piece 7 2470 12
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine102_ready : RoutineReady ⟨102, by decide⟩ routine102 := by
  wct_ready_start 102 3 6
  wct_cases [2471,2477,2480,2486,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 7 2471 13
  · wct_piece 7 2477 14
  · wct_piece 7 2480 15
  · wct_piece 7 2486 16
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine103_ready : RoutineReady ⟨103, by decide⟩ routine103 := by
  wct_ready_start 103 3 7
  wct_cases [2487,2493,2496,2502,1526,1532,1534,1538,1365,875,881]
  · wct_piece 7 2487 17
  · wct_piece 7 2493 18
  · wct_piece 7 2496 19
  · wct_piece 7 2502 20
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine104_ready : RoutineReady ⟨104, by decide⟩ routine104 := by
  wct_ready_start 104 3 8
  wct_cases [2503,2509,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 7 2503 21
  · wct_piece 7 2509 22
  · wct_piece 7 2512 23
  · wct_piece 7 2518 24
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine105_ready : RoutineReady ⟨105, by decide⟩ routine105 := by
  wct_ready_start 105 3 9
  wct_cases [2519,2525,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 7 2519 25
  · wct_piece 7 2525 26
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine106_ready : RoutineReady ⟨106, by decide⟩ routine106 := by
  wct_ready_start 106 3 10
  wct_cases [2535,2541,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 7 2535 29
  · wct_piece 7 2541 30
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine107_ready : RoutineReady ⟨107, by decide⟩ routine107 := by
  wct_ready_start 107 3 11
  wct_cases [2557,2563,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 7 2557 35
  · wct_piece 7 2563 36
  · wct_piece 7 2566 37
  · wct_piece 7 2572 38
  · wct_piece 7 2574 39
  · wct_piece 7 2578 40
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine108_ready : RoutineReady ⟨108, by decide⟩ routine108 := by
  wct_ready_start 108 3 12
  wct_cases [2579,2585,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 7 2579 41
  · wct_piece 7 2585 42
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
theorem routine109_ready : RoutineReady ⟨109, by decide⟩ routine109 := by
  wct_ready_start 109 3 13
  wct_cases [2601,2607,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 7 2601 47
  · wct_piece 7 2607 48
  · wct_piece 7 2610 49
  · wct_piece 7 2616 50
  · wct_piece 7 2619 51
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine110_ready : RoutineReady ⟨110, by decide⟩ routine110 := by
  wct_ready_start 110 3 14
  wct_cases [2620,2626,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 7 2620 52
  · wct_piece 7 2626 53
  · wct_piece 7 2629 54
  · wct_piece 7 2635 55
  · wct_piece 7 2638 56
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine111_ready : RoutineReady ⟨111, by decide⟩ routine111 := by
  wct_ready_start 111 3 15
  wct_cases [2639,2645,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 7 2639 57
  · wct_piece 7 2645 58
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine112_ready : RoutineReady ⟨112, by decide⟩ routine112 := by
  wct_ready_start 112 3 16
  wct_cases [2658,2664,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 7 2658 62
  · wct_piece 7 2664 63
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine113_ready : RoutineReady ⟨113, by decide⟩ routine113 := by
  wct_ready_start 113 3 17
  wct_cases [2682,2688,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 8 2682 5
  · wct_piece 8 2688 6
  · wct_piece 8 2691 7
  · wct_piece 8 2697 8
  · wct_piece 8 2699 9
  · wct_piece 8 2701 10
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine114_ready : RoutineReady ⟨114, by decide⟩ routine114 := by
  wct_ready_start 114 3 18
  wct_cases [2706,2712,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 8 2706 12
  · wct_piece 8 2712 13
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine115_ready : RoutineReady ⟨115, by decide⟩ routine115 := by
  wct_ready_start 115 3 19
  wct_cases [2737,2743,2745,2747,2751,1411,901,755,761,763,766]
  · wct_piece 8 2737 20
  · wct_piece 8 2743 21
  · wct_piece 8 2745 22
  · wct_piece 8 2747 23
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine116_ready : RoutineReady ⟨116, by decide⟩ routine116 := by
  wct_ready_start 116 3 20
  wct_cases [2752,2758,2760,2762,2766,1426,913,919,805,811,814]
  · wct_piece 8 2752 25
  · wct_piece 8 2758 26
  · wct_piece 8 2760 27
  · wct_piece 8 2762 28
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine117_ready : RoutineReady ⟨117, by decide⟩ routine117 := by
  wct_ready_start 117 3 21
  wct_cases [2767,2773,2775,2777,2781,1441,931,937,940,875,881]
  · wct_piece 8 2767 30
  · wct_piece 8 2773 31
  · wct_piece 8 2775 32
  · wct_piece 8 2777 33
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine118_ready : RoutineReady ⟨118, by decide⟩ routine118 := by
  wct_ready_start 118 3 22
  wct_cases [2782,2788,2790,2792,2796,1456,952,958,960,962,966]
  · wct_piece 8 2782 35
  · wct_piece 8 2788 36
  · wct_piece 8 2790 37
  · wct_piece 8 2792 38
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine119_ready : RoutineReady ⟨119, by decide⟩ routine119 := by
  wct_ready_start 119 3 23
  wct_cases [2797,2803,2805,2807,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 8 2797 40
  · wct_piece 8 2803 41
  · wct_piece 8 2805 42
  · wct_piece 8 2807 43
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine120_ready : RoutineReady ⟨120, by decide⟩ routine120 := by
  wct_ready_start 120 3 24
  wct_cases [2812,2818,2820,2822,2826,1490,1496,1138,1144,875,881]
  · wct_piece 8 2812 45
  · wct_piece 8 2818 46
  · wct_piece 8 2820 47
  · wct_piece 8 2822 48
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine121_ready : RoutineReady ⟨121, by decide⟩ routine121 := by
  wct_ready_start 121 3 25
  wct_cases [2827,2833,2835,2837,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 8 2827 50
  · wct_piece 8 2833 51
  · wct_piece 8 2835 52
  · wct_piece 8 2837 53
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine122_ready : RoutineReady ⟨122, by decide⟩ routine122 := by
  wct_ready_start 122 3 26
  wct_cases [2842,2848,2850,2852,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 8 2842 55
  · wct_piece 8 2848 56
  · wct_piece 8 2850 57
  · wct_piece 8 2852 58
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine123_ready : RoutineReady ⟨123, by decide⟩ routine123 := by
  wct_ready_start 123 3 27
  wct_cases [2857,2863,2865,2867,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 8 2857 60
  · wct_piece 8 2863 61
  · wct_piece 8 2865 62
  · wct_piece 8 2867 63
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine124_ready : RoutineReady ⟨124, by decide⟩ routine124 := by
  wct_ready_start 124 3 28
  wct_cases [2872,2878,2880,2882,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 9 2872 1
  · wct_piece 9 2878 2
  · wct_piece 9 2880 3
  · wct_piece 9 2882 4
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine125_ready : RoutineReady ⟨125, by decide⟩ routine125 := by
  wct_ready_start 125 3 29
  wct_cases [2887,2893,2895,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 9 2887 6
  · wct_piece 9 2893 7
  · wct_piece 9 2895 8
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine126_ready : RoutineReady ⟨126, by decide⟩ routine126 := by
  wct_ready_start 126 3 30
  wct_cases [2909,2915,2917,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 9 2909 12
  · wct_piece 9 2915 13
  · wct_piece 9 2917 14
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine127_ready : RoutineReady ⟨127, by decide⟩ routine127 := by
  wct_ready_start 127 3 31
  wct_cases [2931,2937,2939,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 9 2931 18
  · wct_piece 9 2937 19
  · wct_piece 9 2939 20
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
end W9Machine.Chain
end
