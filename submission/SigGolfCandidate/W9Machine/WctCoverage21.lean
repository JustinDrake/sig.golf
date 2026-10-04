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
  wct_cases [242198,242204,242206,242208,235963,2751,1411,901,755,761,763,766]
  · wct_piece 46 242198 3
  · wct_piece 46 242204 4
  · wct_piece 46 242206 5
  · wct_piece 46 242208 6
  · wct_piece 20 235963 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine673_ready : RoutineReady ⟨673, by decide⟩ routine673 := by
  wct_ready_start 673 21 1
  wct_cases [242209,242215,242217,242219,235978,2766,1426,913,919,805,811,814]
  · wct_piece 46 242209 7
  · wct_piece 46 242215 8
  · wct_piece 46 242217 9
  · wct_piece 46 242219 10
  · wct_piece 20 235978 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine674_ready : RoutineReady ⟨674, by decide⟩ routine674 := by
  wct_ready_start 674 21 2
  wct_cases [242220,242226,242228,242230,235993,2781,1441,931,937,940,875,881]
  · wct_piece 46 242220 11
  · wct_piece 46 242226 12
  · wct_piece 46 242228 13
  · wct_piece 46 242230 14
  · wct_piece 20 235993 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine675_ready : RoutineReady ⟨675, by decide⟩ routine675 := by
  wct_ready_start 675 21 3
  wct_cases [242231,242237,242239,242241,236008,2796,1456,952,958,960,962,966]
  · wct_piece 46 242231 15
  · wct_piece 46 242237 16
  · wct_piece 46 242239 17
  · wct_piece 46 242241 18
  · wct_piece 21 236008 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine676_ready : RoutineReady ⟨676, by decide⟩ routine676 := by
  wct_ready_start 676 21 4
  wct_cases [242242,242248,242250,242252,236023,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 46 242242 19
  · wct_piece 46 242248 20
  · wct_piece 46 242250 21
  · wct_piece 46 242252 22
  · wct_piece 21 236023 9
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
  wct_cases [242253,242259,242261,242263,236038,2826,1490,1496,1138,1144,875,881]
  · wct_piece 46 242253 23
  · wct_piece 46 242259 24
  · wct_piece 46 242261 25
  · wct_piece 46 242263 26
  · wct_piece 21 236038 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine678_ready : RoutineReady ⟨678, by decide⟩ routine678 := by
  wct_ready_start 678 21 6
  wct_cases [242264,242270,242272,242274,236053,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 46 242264 27
  · wct_piece 46 242270 28
  · wct_piece 46 242272 29
  · wct_piece 46 242274 30
  · wct_piece 21 236053 19
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
  wct_cases [242275,242281,242283,242285,236068,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 46 242275 31
  · wct_piece 46 242281 32
  · wct_piece 46 242283 33
  · wct_piece 46 242285 34
  · wct_piece 21 236068 24
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
  wct_cases [242286,242292,242294,242296,236083,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 46 242286 35
  · wct_piece 46 242292 36
  · wct_piece 46 242294 37
  · wct_piece 46 242296 38
  · wct_piece 21 236083 29
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
  wct_cases [242297,242303,242305,242307,236098,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 46 242297 39
  · wct_piece 46 242303 40
  · wct_piece 46 242305 41
  · wct_piece 46 242307 42
  · wct_piece 21 236098 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine682_ready : RoutineReady ⟨682, by decide⟩ routine682 := by
  wct_ready_start 682 21 10
  wct_cases [242308,242314,242316,242318,236113,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 46 242308 43
  · wct_piece 46 242314 44
  · wct_piece 46 242316 45
  · wct_piece 46 242318 46
  · wct_piece 21 236113 39
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
  wct_cases [242319,242325,242327,242329,236128,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 46 242319 47
  · wct_piece 46 242325 48
  · wct_piece 46 242327 49
  · wct_piece 46 242329 50
  · wct_piece 21 236128 44
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
  wct_cases [242330,242336,242338,242340,236143,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 46 242330 51
  · wct_piece 46 242336 52
  · wct_piece 46 242338 53
  · wct_piece 46 242340 54
  · wct_piece 21 236143 49
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
  wct_cases [242341,242347,242349,242351,236158,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 46 242341 55
  · wct_piece 46 242347 56
  · wct_piece 46 242349 57
  · wct_piece 46 242351 58
  · wct_piece 21 236158 54
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
  wct_cases [242352,242358,242360,242362,236173,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 46 242352 59
  · wct_piece 46 242358 60
  · wct_piece 46 242360 61
  · wct_piece 46 242362 62
  · wct_piece 21 236173 59
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
  wct_cases [242363,242369,242371,242373,236188,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 46 242363 63
  · wct_piece 47 242369 0
  · wct_piece 47 242371 1
  · wct_piece 47 242373 2
  · wct_piece 22 236188 0
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
  wct_cases [242374,242380,242382,242384,236203,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 47 242374 3
  · wct_piece 47 242380 4
  · wct_piece 47 242382 5
  · wct_piece 47 242384 6
  · wct_piece 22 236203 5
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
  wct_cases [242385,242391,242393,242395,236218,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 47 242385 7
  · wct_piece 47 242391 8
  · wct_piece 47 242393 9
  · wct_piece 47 242395 10
  · wct_piece 22 236218 10
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
  wct_cases [242396,242402,242404,242406,236233,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 47 242396 11
  · wct_piece 47 242402 12
  · wct_piece 47 242404 13
  · wct_piece 47 242406 14
  · wct_piece 22 236233 15
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
  wct_cases [242407,242413,242415,242417,236248,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 47 242407 15
  · wct_piece 47 242413 16
  · wct_piece 47 242415 17
  · wct_piece 47 242417 18
  · wct_piece 22 236248 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine692_ready : RoutineReady ⟨692, by decide⟩ routine692 := by
  wct_ready_start 692 21 20
  wct_cases [242418,242424,242426,242428,236260,236266,236270,4391,2078,1120,805,811,814]
  · wct_piece 47 242418 19
  · wct_piece 47 242424 20
  · wct_piece 47 242426 21
  · wct_piece 47 242428 22
  · wct_piece 22 236260 24
  · wct_piece 22 236266 25
  · wct_piece 22 236270 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine693_ready : RoutineReady ⟨693, by decide⟩ routine693 := by
  wct_ready_start 693 21 21
  wct_cases [242429,242435,242437,242439,236282,236288,236292,4412,2099,1138,1144,875,881]
  · wct_piece 47 242429 23
  · wct_piece 47 242435 24
  · wct_piece 47 242437 25
  · wct_piece 47 242439 26
  · wct_piece 22 236282 30
  · wct_piece 22 236288 31
  · wct_piece 22 236292 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine694_ready : RoutineReady ⟨694, by decide⟩ routine694 := by
  wct_ready_start 694 21 22
  wct_cases [242440,242446,242448,242450,236304,236310,236314,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 47 242440 27
  · wct_piece 47 242446 28
  · wct_piece 47 242448 29
  · wct_piece 47 242450 30
  · wct_piece 22 236304 36
  · wct_piece 22 236310 37
  · wct_piece 22 236314 38
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine695_ready : RoutineReady ⟨695, by decide⟩ routine695 := by
  wct_ready_start 695 21 23
  wct_cases [242451,242457,242459,242461,236326,236332,236336,4454,2138,2144,2148,1365,875,881]
  · wct_piece 47 242451 31
  · wct_piece 47 242457 32
  · wct_piece 47 242459 33
  · wct_piece 47 242461 34
  · wct_piece 22 236326 42
  · wct_piece 22 236332 43
  · wct_piece 22 236336 44
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine696_ready : RoutineReady ⟨696, by decide⟩ routine696 := by
  wct_ready_start 696 21 24
  wct_cases [242462,242468,242470,242472,236348,236354,236358,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 47 242462 35
  · wct_piece 47 242468 36
  · wct_piece 47 242470 37
  · wct_piece 47 242472 38
  · wct_piece 22 236348 48
  · wct_piece 22 236354 49
  · wct_piece 22 236358 50
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine697_ready : RoutineReady ⟨697, by decide⟩ routine697 := by
  wct_ready_start 697 21 25
  wct_cases [242473,242479,242481,242483,236370,236376,236380,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 47 242473 39
  · wct_piece 47 242479 40
  · wct_piece 47 242481 41
  · wct_piece 47 242483 42
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
theorem routine698_ready : RoutineReady ⟨698, by decide⟩ routine698 := by
  wct_ready_start 698 21 26
  wct_cases [242484,242490,242492,242494,236392,236398,4514,4520,4524,2681,1365,875,881]
  · wct_piece 47 242484 43
  · wct_piece 47 242490 44
  · wct_piece 47 242492 45
  · wct_piece 47 242494 46
  · wct_piece 22 236392 60
  · wct_piece 22 236398 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine699_ready : RoutineReady ⟨699, by decide⟩ routine699 := by
  wct_ready_start 699 21 27
  wct_cases [242495,242501,242503,242505,236410,236416,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 47 242495 47
  · wct_piece 47 242501 48
  · wct_piece 47 242503 49
  · wct_piece 47 242505 50
  · wct_piece 23 236410 1
  · wct_piece 23 236416 2
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
  wct_cases [242506,242512,242514,242516,236428,236434,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 47 242506 51
  · wct_piece 47 242512 52
  · wct_piece 47 242514 53
  · wct_piece 47 242516 54
  · wct_piece 23 236428 6
  · wct_piece 23 236434 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine701_ready : RoutineReady ⟨701, by decide⟩ routine701 := by
  wct_ready_start 701 21 29
  wct_cases [242517,242523,242525,242527,236446,236452,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 47 242517 55
  · wct_piece 47 242523 56
  · wct_piece 47 242525 57
  · wct_piece 47 242527 58
  · wct_piece 23 236446 11
  · wct_piece 23 236452 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine702_ready : RoutineReady ⟨702, by decide⟩ routine702 := by
  wct_ready_start 702 21 30
  wct_cases [242528,242534,242536,242538,236464,236470,236472,236476,235869,2681,1365,875,881]
  · wct_piece 47 242528 59
  · wct_piece 47 242534 60
  · wct_piece 47 242536 61
  · wct_piece 47 242538 62
  · wct_piece 23 236464 16
  · wct_piece 23 236470 17
  · wct_piece 23 236472 18
  · wct_piece 23 236476 19
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine703_ready : RoutineReady ⟨703, by decide⟩ routine703 := by
  wct_ready_start 703 21 31
  wct_cases [242539,242545,242547,242549,236488,236494,236496,236500,235893,2705,1386,1392,1396,966]
  · wct_piece 47 242539 63
  · wct_piece 48 242545 0
  · wct_piece 48 242547 1
  · wct_piece 48 242549 2
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
