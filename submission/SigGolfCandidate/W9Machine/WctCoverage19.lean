import SigGolfCandidate.W9Machine.WctRoutineCheck19
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch19_checked :
    (routineBatch19.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch19_checked :
    (routineBatch19.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine608_ready : RoutineReady ⟨608, by decide⟩ routine608 := by
  wct_ready_start 608 19 0
  wct_cases [240238,240244,240246,235105,235111,235113,235117,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 40 240238 37
  · wct_piece 40 240244 38
  · wct_piece 40 240246 39
  · wct_piece 19 235105 58
  · wct_piece 19 235111 59
  · wct_piece 19 235113 60
  · wct_piece 19 235117 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine609_ready : RoutineReady ⟨609, by decide⟩ routine609 := by
  wct_ready_start 609 19 1
  wct_cases [240247,240253,240255,235127,235133,235136,4514,4520,4524,2681,1365,875,881]
  · wct_piece 40 240247 40
  · wct_piece 40 240253 41
  · wct_piece 40 240255 42
  · wct_piece 20 235127 0
  · wct_piece 20 235133 1
  · wct_piece 20 235136 2
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine610_ready : RoutineReady ⟨610, by decide⟩ routine610 := by
  wct_ready_start 610 19 2
  wct_cases [240256,240262,240264,235146,235152,235155,235161,235165,2705,1386,1392,1396,966]
  · wct_piece 40 240256 43
  · wct_piece 40 240262 44
  · wct_piece 40 240264 45
  · wct_piece 20 235146 5
  · wct_piece 20 235152 6
  · wct_piece 20 235155 7
  · wct_piece 20 235161 8
  · wct_piece 20 235165 9
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine611_ready : RoutineReady ⟨611, by decide⟩ routine611 := by
  wct_ready_start 611 19 3
  wct_cases [240265,240271,240273,235175,235181,235184,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 40 240265 46
  · wct_piece 40 240271 47
  · wct_piece 40 240273 48
  · wct_piece 20 235175 12
  · wct_piece 20 235181 13
  · wct_piece 20 235184 14
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine612_ready : RoutineReady ⟨612, by decide⟩ routine612 := by
  wct_ready_start 612 19 4
  wct_cases [240274,240280,240282,235194,235200,235203,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 40 240274 49
  · wct_piece 40 240280 50
  · wct_piece 40 240282 51
  · wct_piece 20 235194 17
  · wct_piece 20 235200 18
  · wct_piece 20 235203 19
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine613_ready : RoutineReady ⟨613, by decide⟩ routine613 := by
  wct_ready_start 613 19 5
  wct_cases [240283,240289,240291,235213,235219,235221,235223,235227,2681,1365,875,881]
  · wct_piece 40 240283 52
  · wct_piece 40 240289 53
  · wct_piece 40 240291 54
  · wct_piece 20 235213 22
  · wct_piece 20 235219 23
  · wct_piece 20 235221 24
  · wct_piece 20 235223 25
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine614_ready : RoutineReady ⟨614, by decide⟩ routine614 := by
  wct_ready_start 614 19 6
  wct_cases [240292,240298,240300,235237,235243,235245,235247,235251,2705,1386,1392,1396,966]
  · wct_piece 40 240292 55
  · wct_piece 40 240298 56
  · wct_piece 40 240300 57
  · wct_piece 20 235237 29
  · wct_piece 20 235243 30
  · wct_piece 20 235245 31
  · wct_piece 20 235247 32
  · wct_piece 20 235251 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine615_ready : RoutineReady ⟨615, by decide⟩ routine615 := by
  wct_ready_start 615 19 7
  wct_cases [240301,240307,240309,235261,235267,235269,235271,235275,2726,2732,2736,1585,966]
  · wct_piece 40 240301 58
  · wct_piece 40 240307 59
  · wct_piece 40 240309 60
  · wct_piece 20 235261 36
  · wct_piece 20 235267 37
  · wct_piece 20 235269 38
  · wct_piece 20 235271 39
  · wct_piece 20 235275 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine616_ready : RoutineReady ⟨616, by decide⟩ routine616 := by
  wct_ready_start 616 19 8
  wct_cases [240310,240316,240318,235285,235291,235293,235296,235302,235306,3101,1585,966]
  · wct_piece 40 240310 61
  · wct_piece 40 240316 62
  · wct_piece 40 240318 63
  · wct_piece 20 235285 43
  · wct_piece 20 235291 44
  · wct_piece 20 235293 45
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine617_ready : RoutineReady ⟨617, by decide⟩ routine617 := by
  wct_ready_start 617 19 9
  wct_cases [240319,240325,240327,240333,240337,235321,2751,1411,901,755,761,763,766]
  · wct_piece 41 240319 0
  · wct_piece 41 240325 1
  · wct_piece 41 240327 2
  · wct_piece 41 240333 3
  · wct_piece 41 240337 4
  · wct_piece 20 235321 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine618_ready : RoutineReady ⟨618, by decide⟩ routine618 := by
  wct_ready_start 618 19 10
  wct_cases [240338,240344,240346,240352,240356,235336,2766,1426,913,919,805,811,814]
  · wct_piece 41 240338 5
  · wct_piece 41 240344 6
  · wct_piece 41 240346 7
  · wct_piece 41 240352 8
  · wct_piece 41 240356 9
  · wct_piece 20 235336 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine619_ready : RoutineReady ⟨619, by decide⟩ routine619 := by
  wct_ready_start 619 19 11
  wct_cases [240357,240363,240365,240371,240375,235351,2781,1441,931,937,940,875,881]
  · wct_piece 41 240357 10
  · wct_piece 41 240363 11
  · wct_piece 41 240365 12
  · wct_piece 41 240371 13
  · wct_piece 41 240375 14
  · wct_piece 20 235351 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine620_ready : RoutineReady ⟨620, by decide⟩ routine620 := by
  wct_ready_start 620 19 12
  wct_cases [240376,240382,240384,240390,240394,235366,2796,1456,952,958,960,962,966]
  · wct_piece 41 240376 15
  · wct_piece 41 240382 16
  · wct_piece 41 240384 17
  · wct_piece 41 240390 18
  · wct_piece 41 240394 19
  · wct_piece 21 235366 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine621_ready : RoutineReady ⟨621, by decide⟩ routine621 := by
  wct_ready_start 621 19 13
  wct_cases [240395,240401,240403,240409,240413,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 41 240395 20
  · wct_piece 41 240401 21
  · wct_piece 41 240403 22
  · wct_piece 41 240409 23
  · wct_piece 41 240413 24
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine622_ready : RoutineReady ⟨622, by decide⟩ routine622 := by
  wct_ready_start 622 19 14
  wct_cases [240414,240420,240422,240428,240432,235396,2826,1490,1496,1138,1144,875,881]
  · wct_piece 41 240414 25
  · wct_piece 41 240420 26
  · wct_piece 41 240422 27
  · wct_piece 41 240428 28
  · wct_piece 41 240432 29
  · wct_piece 21 235396 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine623_ready : RoutineReady ⟨623, by decide⟩ routine623 := by
  wct_ready_start 623 19 15
  wct_cases [240433,240439,240441,240447,240451,235411,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 41 240433 30
  · wct_piece 41 240439 31
  · wct_piece 41 240441 32
  · wct_piece 41 240447 33
  · wct_piece 41 240451 34
  · wct_piece 21 235411 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine624_ready : RoutineReady ⟨624, by decide⟩ routine624 := by
  wct_ready_start 624 19 16
  wct_cases [240452,240458,240460,240466,240470,235426,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 41 240452 35
  · wct_piece 41 240458 36
  · wct_piece 41 240460 37
  · wct_piece 41 240466 38
  · wct_piece 41 240470 39
  · wct_piece 21 235426 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine625_ready : RoutineReady ⟨625, by decide⟩ routine625 := by
  wct_ready_start 625 19 17
  wct_cases [240471,240477,240479,240485,240489,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 41 240471 40
  · wct_piece 41 240477 41
  · wct_piece 41 240479 42
  · wct_piece 41 240485 43
  · wct_piece 41 240489 44
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine626_ready : RoutineReady ⟨626, by decide⟩ routine626 := by
  wct_ready_start 626 19 18
  wct_cases [240490,240496,240498,240504,240508,235456,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 41 240490 45
  · wct_piece 41 240496 46
  · wct_piece 41 240498 47
  · wct_piece 41 240504 48
  · wct_piece 41 240508 49
  · wct_piece 21 235456 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine627_ready : RoutineReady ⟨627, by decide⟩ routine627 := by
  wct_ready_start 627 19 19
  wct_cases [240509,240515,240517,240523,240527,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 41 240509 50
  · wct_piece 41 240515 51
  · wct_piece 41 240517 52
  · wct_piece 41 240523 53
  · wct_piece 41 240527 54
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine628_ready : RoutineReady ⟨628, by decide⟩ routine628 := by
  wct_ready_start 628 19 20
  wct_cases [240528,240534,240536,240542,240546,240552,240556,240562,875,881]
  · wct_piece 41 240528 55
  · wct_piece 41 240534 56
  · wct_piece 41 240536 57
  · wct_piece 41 240542 58
  · wct_piece 41 240546 59
  · wct_piece 41 240552 60
  · wct_piece 41 240556 61
  · wct_piece 41 240562 62
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine629_ready : RoutineReady ⟨629, by decide⟩ routine629 := by
  wct_ready_start 629 19 21
  wct_cases [240563,240569,240571,240577,240581,240587,240591,240597,240599,240603,966]
  · wct_piece 41 240563 63
  · wct_piece 42 240569 0
  · wct_piece 42 240571 1
  · wct_piece 42 240577 2
  · wct_piece 42 240581 3
  · wct_piece 42 240587 4
  · wct_piece 42 240591 5
  · wct_piece 42 240597 6
  · wct_piece 42 240599 7
  · wct_piece 42 240603 8
  · wct_piece 0 966 57
theorem routine630_ready : RoutineReady ⟨630, by decide⟩ routine630 := by
  wct_ready_start 630 19 22
  wct_cases [240604,240610,240612,240618,240622,240628,240634,240638,875,881]
  · wct_piece 42 240604 9
  · wct_piece 42 240610 10
  · wct_piece 42 240612 11
  · wct_piece 42 240618 12
  · wct_piece 42 240622 13
  · wct_piece 42 240628 14
  · wct_piece 42 240634 15
  · wct_piece 42 240638 16
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine631_ready : RoutineReady ⟨631, by decide⟩ routine631 := by
  wct_ready_start 631 19 23
  wct_cases [240639,240645,240647,240653,240657,240663,240669,240675,240679,966]
  · wct_piece 42 240639 17
  · wct_piece 42 240645 18
  · wct_piece 42 240647 19
  · wct_piece 42 240653 20
  · wct_piece 42 240657 21
  · wct_piece 42 240663 22
  · wct_piece 42 240669 23
  · wct_piece 42 240675 24
  · wct_piece 42 240679 25
  · wct_piece 0 966 57
theorem routine632_ready : RoutineReady ⟨632, by decide⟩ routine632 := by
  wct_ready_start 632 19 24
  wct_cases [240680,240686,240688,240694,240698,235546,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 42 240680 26
  · wct_piece 42 240686 27
  · wct_piece 42 240688 28
  · wct_piece 42 240694 29
  · wct_piece 42 240698 30
  · wct_piece 22 235546 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine633_ready : RoutineReady ⟨633, by decide⟩ routine633 := by
  wct_ready_start 633 19 25
  wct_cases [240699,240705,240707,240713,240717,235561,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 42 240699 31
  · wct_piece 42 240705 32
  · wct_piece 42 240707 33
  · wct_piece 42 240713 34
  · wct_piece 42 240717 35
  · wct_piece 22 235561 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine634_ready : RoutineReady ⟨634, by decide⟩ routine634 := by
  wct_ready_start 634 19 26
  wct_cases [240718,240724,240726,240732,240736,240742,240744,240748,240754,240758,966]
  · wct_piece 42 240718 36
  · wct_piece 42 240724 37
  · wct_piece 42 240726 38
  · wct_piece 42 240732 39
  · wct_piece 42 240736 40
  · wct_piece 42 240742 41
  · wct_piece 42 240744 42
  · wct_piece 42 240748 43
  · wct_piece 42 240754 44
  · wct_piece 42 240758 45
  · wct_piece 0 966 57
theorem routine635_ready : RoutineReady ⟨635, by decide⟩ routine635 := by
  wct_ready_start 635 19 27
  wct_cases [240759,240765,240767,240773,240777,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 42 240759 46
  · wct_piece 42 240765 47
  · wct_piece 42 240767 48
  · wct_piece 42 240773 49
  · wct_piece 42 240777 50
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine636_ready : RoutineReady ⟨636, by decide⟩ routine636 := by
  wct_ready_start 636 19 28
  wct_cases [240778,240784,240786,240792,240796,235606,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 42 240778 51
  · wct_piece 42 240784 52
  · wct_piece 42 240786 53
  · wct_piece 42 240792 54
  · wct_piece 42 240796 55
  · wct_piece 22 235606 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine637_ready : RoutineReady ⟨637, by decide⟩ routine637 := by
  wct_ready_start 637 19 29
  wct_cases [240797,240803,240805,240811,235618,235624,235628,4391,2078,1120,805,811,814]
  · wct_piece 42 240797 56
  · wct_piece 42 240803 57
  · wct_piece 42 240805 58
  · wct_piece 42 240811 59
  · wct_piece 22 235618 24
  · wct_piece 22 235624 25
  · wct_piece 22 235628 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine638_ready : RoutineReady ⟨638, by decide⟩ routine638 := by
  wct_ready_start 638 19 30
  wct_cases [240812,240818,240820,240826,235640,235646,235650,4412,2099,1138,1144,875,881]
  · wct_piece 42 240812 60
  · wct_piece 42 240818 61
  · wct_piece 42 240820 62
  · wct_piece 42 240826 63
  · wct_piece 22 235640 30
  · wct_piece 22 235646 31
  · wct_piece 22 235650 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine639_ready : RoutineReady ⟨639, by decide⟩ routine639 := by
  wct_ready_start 639 19 31
  wct_cases [240827,240833,240835,240841,235662,235668,235672,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 43 240827 0
  · wct_piece 43 240833 1
  · wct_piece 43 240835 2
  · wct_piece 43 240841 3
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
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage19 (rank : Fin 728) (hlo : 608 ≤ rank.val) (hhi : rank.val < 640) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 608 ≤ n at hlo
  change n < 640 at hhi
  interval_cases n
  · exact ⟨routine608, routine608_ready⟩
  · exact ⟨routine609, routine609_ready⟩
  · exact ⟨routine610, routine610_ready⟩
  · exact ⟨routine611, routine611_ready⟩
  · exact ⟨routine612, routine612_ready⟩
  · exact ⟨routine613, routine613_ready⟩
  · exact ⟨routine614, routine614_ready⟩
  · exact ⟨routine615, routine615_ready⟩
  · exact ⟨routine616, routine616_ready⟩
  · exact ⟨routine617, routine617_ready⟩
  · exact ⟨routine618, routine618_ready⟩
  · exact ⟨routine619, routine619_ready⟩
  · exact ⟨routine620, routine620_ready⟩
  · exact ⟨routine621, routine621_ready⟩
  · exact ⟨routine622, routine622_ready⟩
  · exact ⟨routine623, routine623_ready⟩
  · exact ⟨routine624, routine624_ready⟩
  · exact ⟨routine625, routine625_ready⟩
  · exact ⟨routine626, routine626_ready⟩
  · exact ⟨routine627, routine627_ready⟩
  · exact ⟨routine628, routine628_ready⟩
  · exact ⟨routine629, routine629_ready⟩
  · exact ⟨routine630, routine630_ready⟩
  · exact ⟨routine631, routine631_ready⟩
  · exact ⟨routine632, routine632_ready⟩
  · exact ⟨routine633, routine633_ready⟩
  · exact ⟨routine634, routine634_ready⟩
  · exact ⟨routine635, routine635_ready⟩
  · exact ⟨routine636, routine636_ready⟩
  · exact ⟨routine637, routine637_ready⟩
  · exact ⟨routine638, routine638_ready⟩
  · exact ⟨routine639, routine639_ready⟩
end W9Machine.Chain
end
