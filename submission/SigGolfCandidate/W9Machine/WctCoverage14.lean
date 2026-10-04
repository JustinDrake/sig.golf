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
  wct_cases [237631,237637,237643,237647,235020,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 28 237631 8
  · wct_piece 28 237637 9
  · wct_piece 28 237643 10
  · wct_piece 28 237647 11
  · wct_piece 16 235020 51
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
  wct_cases [237648,237654,237660,237664,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 28 237648 12
  · wct_piece 28 237654 13
  · wct_piece 28 237660 14
  · wct_piece 28 237664 15
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
  wct_cases [237665,237671,237677,237681,237687,237691,237697,237703,237706]
  · wct_piece 28 237665 16
  · wct_piece 28 237671 17
  · wct_piece 28 237677 18
  · wct_piece 28 237681 19
  · wct_piece 28 237687 20
  · wct_piece 28 237691 21
  · wct_piece 28 237697 22
  · wct_piece 28 237703 23
  · wct_piece 28 237706 24
theorem routine451_ready : RoutineReady ⟨451, by decide⟩ routine451 := by
  wct_ready_start 451 14 3
  wct_cases [237712,237718,237724,237728,237734,237738,237744,237747,237753]
  · wct_piece 28 237712 25
  · wct_piece 28 237718 26
  · wct_piece 28 237724 27
  · wct_piece 28 237728 28
  · wct_piece 28 237734 29
  · wct_piece 28 237738 30
  · wct_piece 28 237744 31
  · wct_piece 28 237747 32
  · wct_piece 28 237753 33
theorem routine452_ready : RoutineReady ⟨452, by decide⟩ routine452 := by
  wct_ready_start 452 14 4
  wct_cases [237759,237765,237771,237775,237781,237785,952,958,960,962,966]
  · wct_piece 28 237759 34
  · wct_piece 28 237765 35
  · wct_piece 28 237771 36
  · wct_piece 28 237775 37
  · wct_piece 28 237781 38
  · wct_piece 28 237785 39
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine453_ready : RoutineReady ⟨453, by decide⟩ routine453 := by
  wct_ready_start 453 14 5
  wct_cases [237786,237792,237798,237802,237808,237814,237818,237824,237827]
  · wct_piece 28 237786 40
  · wct_piece 28 237792 41
  · wct_piece 28 237798 42
  · wct_piece 28 237802 43
  · wct_piece 28 237808 44
  · wct_piece 28 237814 45
  · wct_piece 28 237818 46
  · wct_piece 28 237824 47
  · wct_piece 28 237827 48
theorem routine454_ready : RoutineReady ⟨454, by decide⟩ routine454 := by
  wct_ready_start 454 14 6
  wct_cases [237833,237839,237845,237849,237855,237861,237867,875,881]
  · wct_piece 28 237833 49
  · wct_piece 28 237839 50
  · wct_piece 28 237845 51
  · wct_piece 28 237849 52
  · wct_piece 28 237855 53
  · wct_piece 28 237861 54
  · wct_piece 28 237867 55
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine455_ready : RoutineReady ⟨455, by decide⟩ routine455 := by
  wct_ready_start 455 14 7
  wct_cases [237868,237874,237880,237884,237890,237896,237902,237904,237908,966]
  · wct_piece 28 237868 56
  · wct_piece 28 237874 57
  · wct_piece 28 237880 58
  · wct_piece 28 237884 59
  · wct_piece 28 237890 60
  · wct_piece 28 237896 61
  · wct_piece 28 237902 62
  · wct_piece 28 237904 63
  · wct_piece 29 237908 0
  · wct_piece 0 966 57
theorem routine456_ready : RoutineReady ⟨456, by decide⟩ routine456 := by
  wct_ready_start 456 14 8
  wct_cases [237909,237915,237921,237925,237931,237937,237939,237943,875,881]
  · wct_piece 29 237909 1
  · wct_piece 29 237915 2
  · wct_piece 29 237921 3
  · wct_piece 29 237925 4
  · wct_piece 29 237931 5
  · wct_piece 29 237937 6
  · wct_piece 29 237939 7
  · wct_piece 29 237943 8
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine457_ready : RoutineReady ⟨457, by decide⟩ routine457 := by
  wct_ready_start 457 14 9
  wct_cases [237944,237950,237956,237960,237966,237972,237975,237981,237985]
  · wct_piece 29 237944 9
  · wct_piece 29 237950 10
  · wct_piece 29 237956 11
  · wct_piece 29 237960 12
  · wct_piece 29 237966 13
  · wct_piece 29 237972 14
  · wct_piece 29 237975 15
  · wct_piece 29 237981 16
  · wct_piece 29 237985 17
theorem routine458_ready : RoutineReady ⟨458, by decide⟩ routine458 := by
  wct_ready_start 458 14 10
  wct_cases [237991,237997,238003,238007,235150,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 29 237991 18
  · wct_piece 29 237997 19
  · wct_piece 29 238003 20
  · wct_piece 29 238007 21
  · wct_piece 17 235150 27
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
  wct_cases [238008,238014,238020,238024,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 29 238008 22
  · wct_piece 29 238014 23
  · wct_piece 29 238020 24
  · wct_piece 29 238024 25
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
  wct_cases [238025,238031,238037,238041,238047,238049,238053,238059,875,881]
  · wct_piece 29 238025 26
  · wct_piece 29 238031 27
  · wct_piece 29 238037 28
  · wct_piece 29 238041 29
  · wct_piece 29 238047 30
  · wct_piece 29 238049 31
  · wct_piece 29 238053 32
  · wct_piece 29 238059 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine461_ready : RoutineReady ⟨461, by decide⟩ routine461 := by
  wct_ready_start 461 14 13
  wct_cases [238060,238066,238072,238076,238082,238084,238088,238094,238096,238100,966]
  · wct_piece 29 238060 34
  · wct_piece 29 238066 35
  · wct_piece 29 238072 36
  · wct_piece 29 238076 37
  · wct_piece 29 238082 38
  · wct_piece 29 238084 39
  · wct_piece 29 238088 40
  · wct_piece 29 238094 41
  · wct_piece 29 238096 42
  · wct_piece 29 238100 43
  · wct_piece 0 966 57
theorem routine462_ready : RoutineReady ⟨462, by decide⟩ routine462 := by
  wct_ready_start 462 14 14
  wct_cases [238101,238107,238113,238117,238123,238126,238132,238136,238142]
  · wct_piece 29 238101 44
  · wct_piece 29 238107 45
  · wct_piece 29 238113 46
  · wct_piece 29 238117 47
  · wct_piece 29 238123 48
  · wct_piece 29 238126 49
  · wct_piece 29 238132 50
  · wct_piece 29 238136 51
  · wct_piece 29 238142 52
theorem routine463_ready : RoutineReady ⟨463, by decide⟩ routine463 := by
  wct_ready_start 463 14 15
  wct_cases [238148,238154,238160,238164,238170,238173,238179,238185,238189]
  · wct_piece 29 238148 53
  · wct_piece 29 238154 54
  · wct_piece 29 238160 55
  · wct_piece 29 238164 56
  · wct_piece 29 238170 57
  · wct_piece 29 238173 58
  · wct_piece 29 238179 59
  · wct_piece 29 238185 60
  · wct_piece 29 238189 61
theorem routine464_ready : RoutineReady ⟨464, by decide⟩ routine464 := by
  wct_ready_start 464 14 16
  wct_cases [238195,238201,238207,238211,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 29 238195 62
  · wct_piece 29 238201 63
  · wct_piece 30 238207 0
  · wct_piece 30 238211 1
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
  wct_cases [238212,238218,238224,238228,235241,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 30 238212 2
  · wct_piece 30 238218 3
  · wct_piece 30 238224 4
  · wct_piece 30 238228 5
  · wct_piece 17 235241 55
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
  wct_cases [238229,238235,238241,238245,238251,238253,238255,238259,238265,238269,966]
  · wct_piece 30 238229 6
  · wct_piece 30 238235 7
  · wct_piece 30 238241 8
  · wct_piece 30 238245 9
  · wct_piece 30 238251 10
  · wct_piece 30 238253 11
  · wct_piece 30 238255 12
  · wct_piece 30 238259 13
  · wct_piece 30 238265 14
  · wct_piece 30 238269 15
  · wct_piece 0 966 57
theorem routine467_ready : RoutineReady ⟨467, by decide⟩ routine467 := by
  wct_ready_start 467 14 19
  wct_cases [238270,238276,238282,238286,235267,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 30 238270 16
  · wct_piece 30 238276 17
  · wct_piece 30 238282 18
  · wct_piece 30 238286 19
  · wct_piece 17 235267 63
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
  wct_cases [238287,238293,238299,235277,235283,235287,2751,1411,901,755,761,763,766]
  · wct_piece 30 238287 20
  · wct_piece 30 238293 21
  · wct_piece 30 238299 22
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
theorem routine469_ready : RoutineReady ⟨469, by decide⟩ routine469 := by
  wct_ready_start 469 14 21
  wct_cases [238300,238306,238312,238318,238322,2766,1426,913,919,805,811,814]
  · wct_piece 30 238300 23
  · wct_piece 30 238306 24
  · wct_piece 30 238312 25
  · wct_piece 30 238318 26
  · wct_piece 30 238322 27
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine470_ready : RoutineReady ⟨470, by decide⟩ routine470 := by
  wct_ready_start 470 14 22
  wct_cases [238323,238329,238335,238341,238345,2781,1441,931,937,940,875,881]
  · wct_piece 30 238323 28
  · wct_piece 30 238329 29
  · wct_piece 30 238335 30
  · wct_piece 30 238341 31
  · wct_piece 30 238345 32
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine471_ready : RoutineReady ⟨471, by decide⟩ routine471 := by
  wct_ready_start 471 14 23
  wct_cases [238346,238352,238358,235337,235343,235347,2796,1456,952,958,960,962,966]
  · wct_piece 30 238346 33
  · wct_piece 30 238352 34
  · wct_piece 30 238358 35
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
theorem routine472_ready : RoutineReady ⟨472, by decide⟩ routine472 := by
  wct_ready_start 472 14 24
  wct_cases [238359,238365,238371,238377,238381,238387,238391,238397,238400]
  · wct_piece 30 238359 36
  · wct_piece 30 238365 37
  · wct_piece 30 238371 38
  · wct_piece 30 238377 39
  · wct_piece 30 238381 40
  · wct_piece 30 238387 41
  · wct_piece 30 238391 42
  · wct_piece 30 238397 43
  · wct_piece 30 238400 44
theorem routine473_ready : RoutineReady ⟨473, by decide⟩ routine473 := by
  wct_ready_start 473 14 25
  wct_cases [238406,238412,238418,238424,238428,238434,238440,875,881]
  · wct_piece 30 238406 45
  · wct_piece 30 238412 46
  · wct_piece 30 238418 47
  · wct_piece 30 238424 48
  · wct_piece 30 238428 49
  · wct_piece 30 238434 50
  · wct_piece 30 238440 51
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine474_ready : RoutineReady ⟨474, by decide⟩ routine474 := by
  wct_ready_start 474 14 26
  wct_cases [238441,238447,238453,238459,238463,238469,238475,238477,238481,966]
  · wct_piece 30 238441 52
  · wct_piece 30 238447 53
  · wct_piece 30 238453 54
  · wct_piece 30 238459 55
  · wct_piece 30 238463 56
  · wct_piece 30 238469 57
  · wct_piece 30 238475 58
  · wct_piece 30 238477 59
  · wct_piece 30 238481 60
  · wct_piece 0 966 57
theorem routine475_ready : RoutineReady ⟨475, by decide⟩ routine475 := by
  wct_ready_start 475 14 27
  wct_cases [238482,238488,238494,238500,238504,238510,238512,238516,875,881]
  · wct_piece 30 238482 61
  · wct_piece 30 238488 62
  · wct_piece 30 238494 63
  · wct_piece 31 238500 0
  · wct_piece 31 238504 1
  · wct_piece 31 238510 2
  · wct_piece 31 238512 3
  · wct_piece 31 238516 4
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine476_ready : RoutineReady ⟨476, by decide⟩ routine476 := by
  wct_ready_start 476 14 28
  wct_cases [238517,238523,238529,238535,238539,238545,238548,238554,238558]
  · wct_piece 31 238517 5
  · wct_piece 31 238523 6
  · wct_piece 31 238529 7
  · wct_piece 31 238535 8
  · wct_piece 31 238539 9
  · wct_piece 31 238545 10
  · wct_piece 31 238548 11
  · wct_piece 31 238554 12
  · wct_piece 31 238558 13
theorem routine477_ready : RoutineReady ⟨477, by decide⟩ routine477 := by
  wct_ready_start 477 14 29
  wct_cases [238564,238570,238576,235457,235463,235467,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 31 238564 14
  · wct_piece 31 238570 15
  · wct_piece 31 238576 16
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
theorem routine478_ready : RoutineReady ⟨478, by decide⟩ routine478 := by
  wct_ready_start 478 14 30
  wct_cases [238577,238583,238589,238595,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 31 238577 17
  · wct_piece 31 238583 18
  · wct_piece 31 238589 19
  · wct_piece 31 238595 20
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
  wct_cases [238596,238602,238608,238614,238620,238624,238630,875,881]
  · wct_piece 31 238596 21
  · wct_piece 31 238602 22
  · wct_piece 31 238608 23
  · wct_piece 31 238614 24
  · wct_piece 31 238620 25
  · wct_piece 31 238624 26
  · wct_piece 31 238630 27
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
