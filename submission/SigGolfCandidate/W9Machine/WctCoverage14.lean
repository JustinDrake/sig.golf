import SigGolfCandidate.W9Machine.WctRoutineCheck14
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch14_checked :
    (routineBatch14.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch14_checked :
    (routineBatch14.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine448_ready : RoutineReady ⟨448, by decide⟩ routine448 := by
  wct_ready_start 448 14 0
  wct_cases [236989,236995,237001,237005,4762,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 28 236989 8
  · wct_piece 28 236995 9
  · wct_piece 28 237001 10
  · wct_piece 28 237005 11
  · wct_piece 16 4762 51
  · wct_piece 6 2358 48
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine449_ready : RoutineReady ⟨449, by decide⟩ routine449 := by
  wct_ready_start 449 14 1
  wct_cases [237006,237012,237018,237022,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 28 237006 12
  · wct_piece 28 237012 13
  · wct_piece 28 237018 14
  · wct_piece 28 237022 15
  · wct_piece 6 2368 51
  · wct_piece 6 2374 52
  · wct_piece 6 2378 53
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine450_ready : RoutineReady ⟨450, by decide⟩ routine450 := by
  wct_ready_start 450 14 2
  wct_cases [237023,237029,237035,237039,237045,237049,237055,237061,237064]
  · wct_piece 28 237023 16
  · wct_piece 28 237029 17
  · wct_piece 28 237035 18
  · wct_piece 28 237039 19
  · wct_piece 28 237045 20
  · wct_piece 28 237049 21
  · wct_piece 28 237055 22
  · wct_piece 28 237061 23
  · wct_piece 28 237064 24
theorem routine451_ready : RoutineReady ⟨451, by decide⟩ routine451 := by
  wct_ready_start 451 14 3
  wct_cases [237070,237076,237082,237086,237092,237096,237102,237105,237111]
  · wct_piece 28 237070 25
  · wct_piece 28 237076 26
  · wct_piece 28 237082 27
  · wct_piece 28 237086 28
  · wct_piece 28 237092 29
  · wct_piece 28 237096 30
  · wct_piece 28 237102 31
  · wct_piece 28 237105 32
  · wct_piece 28 237111 33
theorem routine452_ready : RoutineReady ⟨452, by decide⟩ routine452 := by
  wct_ready_start 452 14 4
  wct_cases [237117,237123,237129,237133,237139,237143,952,958,960,962,966]
  · wct_piece 28 237117 34
  · wct_piece 28 237123 35
  · wct_piece 28 237129 36
  · wct_piece 28 237133 37
  · wct_piece 28 237139 38
  · wct_piece 28 237143 39
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine453_ready : RoutineReady ⟨453, by decide⟩ routine453 := by
  wct_ready_start 453 14 5
  wct_cases [237144,237150,237156,237160,237166,237172,237176,237182,237185]
  · wct_piece 28 237144 40
  · wct_piece 28 237150 41
  · wct_piece 28 237156 42
  · wct_piece 28 237160 43
  · wct_piece 28 237166 44
  · wct_piece 28 237172 45
  · wct_piece 28 237176 46
  · wct_piece 28 237182 47
  · wct_piece 28 237185 48
theorem routine454_ready : RoutineReady ⟨454, by decide⟩ routine454 := by
  wct_ready_start 454 14 6
  wct_cases [237191,237197,237203,237207,237213,237219,237225,875,881]
  · wct_piece 28 237191 49
  · wct_piece 28 237197 50
  · wct_piece 28 237203 51
  · wct_piece 28 237207 52
  · wct_piece 28 237213 53
  · wct_piece 28 237219 54
  · wct_piece 28 237225 55
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine455_ready : RoutineReady ⟨455, by decide⟩ routine455 := by
  wct_ready_start 455 14 7
  wct_cases [237226,237232,237238,237242,237248,237254,237260,237262,237266,966]
  · wct_piece 28 237226 56
  · wct_piece 28 237232 57
  · wct_piece 28 237238 58
  · wct_piece 28 237242 59
  · wct_piece 28 237248 60
  · wct_piece 28 237254 61
  · wct_piece 28 237260 62
  · wct_piece 28 237262 63
  · wct_piece 29 237266 0
  · wct_piece 0 966 57
theorem routine456_ready : RoutineReady ⟨456, by decide⟩ routine456 := by
  wct_ready_start 456 14 8
  wct_cases [237267,237273,237279,237283,237289,237295,237297,237301,875,881]
  · wct_piece 29 237267 1
  · wct_piece 29 237273 2
  · wct_piece 29 237279 3
  · wct_piece 29 237283 4
  · wct_piece 29 237289 5
  · wct_piece 29 237295 6
  · wct_piece 29 237297 7
  · wct_piece 29 237301 8
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine457_ready : RoutineReady ⟨457, by decide⟩ routine457 := by
  wct_ready_start 457 14 9
  wct_cases [237302,237308,237314,237318,237324,237330,237333,237339,237343]
  · wct_piece 29 237302 9
  · wct_piece 29 237308 10
  · wct_piece 29 237314 11
  · wct_piece 29 237318 12
  · wct_piece 29 237324 13
  · wct_piece 29 237330 14
  · wct_piece 29 237333 15
  · wct_piece 29 237339 16
  · wct_piece 29 237343 17
theorem routine458_ready : RoutineReady ⟨458, by decide⟩ routine458 := by
  wct_ready_start 458 14 10
  wct_cases [237349,237355,237361,237365,4892,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 29 237349 18
  · wct_piece 29 237355 19
  · wct_piece 29 237361 20
  · wct_piece 29 237365 21
  · wct_piece 17 4892 27
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine459_ready : RoutineReady ⟨459, by decide⟩ routine459 := by
  wct_ready_start 459 14 11
  wct_cases [237366,237372,237378,237382,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 29 237366 22
  · wct_piece 29 237372 23
  · wct_piece 29 237378 24
  · wct_piece 29 237382 25
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine460_ready : RoutineReady ⟨460, by decide⟩ routine460 := by
  wct_ready_start 460 14 12
  wct_cases [237383,237389,237395,237399,237405,237407,237411,237417,875,881]
  · wct_piece 29 237383 26
  · wct_piece 29 237389 27
  · wct_piece 29 237395 28
  · wct_piece 29 237399 29
  · wct_piece 29 237405 30
  · wct_piece 29 237407 31
  · wct_piece 29 237411 32
  · wct_piece 29 237417 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine461_ready : RoutineReady ⟨461, by decide⟩ routine461 := by
  wct_ready_start 461 14 13
  wct_cases [237418,237424,237430,237434,237440,237442,237446,237452,237454,237458,966]
  · wct_piece 29 237418 34
  · wct_piece 29 237424 35
  · wct_piece 29 237430 36
  · wct_piece 29 237434 37
  · wct_piece 29 237440 38
  · wct_piece 29 237442 39
  · wct_piece 29 237446 40
  · wct_piece 29 237452 41
  · wct_piece 29 237454 42
  · wct_piece 29 237458 43
  · wct_piece 0 966 57
theorem routine462_ready : RoutineReady ⟨462, by decide⟩ routine462 := by
  wct_ready_start 462 14 14
  wct_cases [237459,237465,237471,237475,237481,237484,237490,237494,237500]
  · wct_piece 29 237459 44
  · wct_piece 29 237465 45
  · wct_piece 29 237471 46
  · wct_piece 29 237475 47
  · wct_piece 29 237481 48
  · wct_piece 29 237484 49
  · wct_piece 29 237490 50
  · wct_piece 29 237494 51
  · wct_piece 29 237500 52
theorem routine463_ready : RoutineReady ⟨463, by decide⟩ routine463 := by
  wct_ready_start 463 14 15
  wct_cases [237506,237512,237518,237522,237528,237531,237537,237543,237547]
  · wct_piece 29 237506 53
  · wct_piece 29 237512 54
  · wct_piece 29 237518 55
  · wct_piece 29 237522 56
  · wct_piece 29 237528 57
  · wct_piece 29 237531 58
  · wct_piece 29 237537 59
  · wct_piece 29 237543 60
  · wct_piece 29 237547 61
theorem routine464_ready : RoutineReady ⟨464, by decide⟩ routine464 := by
  wct_ready_start 464 14 16
  wct_cases [237553,237559,237565,237569,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 29 237553 62
  · wct_piece 29 237559 63
  · wct_piece 30 237565 0
  · wct_piece 30 237569 1
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine465_ready : RoutineReady ⟨465, by decide⟩ routine465 := by
  wct_ready_start 465 14 17
  wct_cases [237570,237576,237582,237586,4983,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 30 237570 2
  · wct_piece 30 237576 3
  · wct_piece 30 237582 4
  · wct_piece 30 237586 5
  · wct_piece 17 4983 55
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine466_ready : RoutineReady ⟨466, by decide⟩ routine466 := by
  wct_ready_start 466 14 18
  wct_cases [237587,237593,237599,237603,237609,237611,237613,237617,237623,237627,966]
  · wct_piece 30 237587 6
  · wct_piece 30 237593 7
  · wct_piece 30 237599 8
  · wct_piece 30 237603 9
  · wct_piece 30 237609 10
  · wct_piece 30 237611 11
  · wct_piece 30 237613 12
  · wct_piece 30 237617 13
  · wct_piece 30 237623 14
  · wct_piece 30 237627 15
  · wct_piece 0 966 57
theorem routine467_ready : RoutineReady ⟨467, by decide⟩ routine467 := by
  wct_ready_start 467 14 19
  wct_cases [237628,237634,237640,237644,5009,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 30 237628 16
  · wct_piece 30 237634 17
  · wct_piece 30 237640 18
  · wct_piece 30 237644 19
  · wct_piece 17 5009 63
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine468_ready : RoutineReady ⟨468, by decide⟩ routine468 := by
  wct_ready_start 468 14 20
  wct_cases [237645,237651,237657,5019,5025,5029,2751,1411,901,755,761,763,766]
  · wct_piece 30 237645 20
  · wct_piece 30 237651 21
  · wct_piece 30 237657 22
  · wct_piece 18 5019 2
  · wct_piece 18 5025 3
  · wct_piece 18 5029 4
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine469_ready : RoutineReady ⟨469, by decide⟩ routine469 := by
  wct_ready_start 469 14 21
  wct_cases [237658,237664,237670,237676,237680,2766,1426,913,919,805,811,814]
  · wct_piece 30 237658 23
  · wct_piece 30 237664 24
  · wct_piece 30 237670 25
  · wct_piece 30 237676 26
  · wct_piece 30 237680 27
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine470_ready : RoutineReady ⟨470, by decide⟩ routine470 := by
  wct_ready_start 470 14 22
  wct_cases [237681,237687,237693,237699,237703,2781,1441,931,937,940,875,881]
  · wct_piece 30 237681 28
  · wct_piece 30 237687 29
  · wct_piece 30 237693 30
  · wct_piece 30 237699 31
  · wct_piece 30 237703 32
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine471_ready : RoutineReady ⟨471, by decide⟩ routine471 := by
  wct_ready_start 471 14 23
  wct_cases [237704,237710,237716,5079,5085,5089,2796,1456,952,958,960,962,966]
  · wct_piece 30 237704 33
  · wct_piece 30 237710 34
  · wct_piece 30 237716 35
  · wct_piece 18 5079 17
  · wct_piece 18 5085 18
  · wct_piece 18 5089 19
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine472_ready : RoutineReady ⟨472, by decide⟩ routine472 := by
  wct_ready_start 472 14 24
  wct_cases [237717,237723,237729,237735,237739,237745,237749,237755,237758]
  · wct_piece 30 237717 36
  · wct_piece 30 237723 37
  · wct_piece 30 237729 38
  · wct_piece 30 237735 39
  · wct_piece 30 237739 40
  · wct_piece 30 237745 41
  · wct_piece 30 237749 42
  · wct_piece 30 237755 43
  · wct_piece 30 237758 44
theorem routine473_ready : RoutineReady ⟨473, by decide⟩ routine473 := by
  wct_ready_start 473 14 25
  wct_cases [237764,237770,237776,237782,237786,237792,237798,875,881]
  · wct_piece 30 237764 45
  · wct_piece 30 237770 46
  · wct_piece 30 237776 47
  · wct_piece 30 237782 48
  · wct_piece 30 237786 49
  · wct_piece 30 237792 50
  · wct_piece 30 237798 51
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine474_ready : RoutineReady ⟨474, by decide⟩ routine474 := by
  wct_ready_start 474 14 26
  wct_cases [237799,237805,237811,237817,237821,237827,237833,237835,237839,966]
  · wct_piece 30 237799 52
  · wct_piece 30 237805 53
  · wct_piece 30 237811 54
  · wct_piece 30 237817 55
  · wct_piece 30 237821 56
  · wct_piece 30 237827 57
  · wct_piece 30 237833 58
  · wct_piece 30 237835 59
  · wct_piece 30 237839 60
  · wct_piece 0 966 57
theorem routine475_ready : RoutineReady ⟨475, by decide⟩ routine475 := by
  wct_ready_start 475 14 27
  wct_cases [237840,237846,237852,237858,237862,237868,237870,237874,875,881]
  · wct_piece 30 237840 61
  · wct_piece 30 237846 62
  · wct_piece 30 237852 63
  · wct_piece 31 237858 0
  · wct_piece 31 237862 1
  · wct_piece 31 237868 2
  · wct_piece 31 237870 3
  · wct_piece 31 237874 4
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine476_ready : RoutineReady ⟨476, by decide⟩ routine476 := by
  wct_ready_start 476 14 28
  wct_cases [237875,237881,237887,237893,237897,237903,237906,237912,237916]
  · wct_piece 31 237875 5
  · wct_piece 31 237881 6
  · wct_piece 31 237887 7
  · wct_piece 31 237893 8
  · wct_piece 31 237897 9
  · wct_piece 31 237903 10
  · wct_piece 31 237906 11
  · wct_piece 31 237912 12
  · wct_piece 31 237916 13
theorem routine477_ready : RoutineReady ⟨477, by decide⟩ routine477 := by
  wct_ready_start 477 14 29
  wct_cases [237922,237928,237934,5199,5205,5209,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 31 237922 14
  · wct_piece 31 237928 15
  · wct_piece 31 237934 16
  · wct_piece 18 5199 47
  · wct_piece 18 5205 48
  · wct_piece 18 5209 49
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine478_ready : RoutineReady ⟨478, by decide⟩ routine478 := by
  wct_ready_start 478 14 30
  wct_cases [237935,237941,237947,237953,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 31 237935 17
  · wct_piece 31 237941 18
  · wct_piece 31 237947 19
  · wct_piece 31 237953 20
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine479_ready : RoutineReady ⟨479, by decide⟩ routine479 := by
  wct_ready_start 479 14 31
  wct_cases [237954,237960,237966,237972,237978,237982,237988,875,881]
  · wct_piece 31 237954 21
  · wct_piece 31 237960 22
  · wct_piece 31 237966 23
  · wct_piece 31 237972 24
  · wct_piece 31 237978 25
  · wct_piece 31 237982 26
  · wct_piece 31 237988 27
  · wct_piece 0 875 32
  · wct_piece 0 881 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage14 (rank : Fin 728) (hlo : 448 ≤ rank.val) (hhi : rank.val < 480) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 448 ≤ n at hlo
  change n < 480 at hhi
  interval_cases n
  · exact ⟨routine448, routine448_ready⟩
  · exact ⟨routine449, routine449_ready⟩
  · exact ⟨routine450, routine450_ready⟩
  · exact ⟨routine451, routine451_ready⟩
  · exact ⟨routine452, routine452_ready⟩
  · exact ⟨routine453, routine453_ready⟩
  · exact ⟨routine454, routine454_ready⟩
  · exact ⟨routine455, routine455_ready⟩
  · exact ⟨routine456, routine456_ready⟩
  · exact ⟨routine457, routine457_ready⟩
  · exact ⟨routine458, routine458_ready⟩
  · exact ⟨routine459, routine459_ready⟩
  · exact ⟨routine460, routine460_ready⟩
  · exact ⟨routine461, routine461_ready⟩
  · exact ⟨routine462, routine462_ready⟩
  · exact ⟨routine463, routine463_ready⟩
  · exact ⟨routine464, routine464_ready⟩
  · exact ⟨routine465, routine465_ready⟩
  · exact ⟨routine466, routine466_ready⟩
  · exact ⟨routine467, routine467_ready⟩
  · exact ⟨routine468, routine468_ready⟩
  · exact ⟨routine469, routine469_ready⟩
  · exact ⟨routine470, routine470_ready⟩
  · exact ⟨routine471, routine471_ready⟩
  · exact ⟨routine472, routine472_ready⟩
  · exact ⟨routine473, routine473_ready⟩
  · exact ⟨routine474, routine474_ready⟩
  · exact ⟨routine475, routine475_ready⟩
  · exact ⟨routine476, routine476_ready⟩
  · exact ⟨routine477, routine477_ready⟩
  · exact ⟨routine478, routine478_ready⟩
  · exact ⟨routine479, routine479_ready⟩
end W9Machine.Chain
end
