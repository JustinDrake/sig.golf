import SigGolfCandidate.W9Machine.WctRoutineCheck10
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch10_checked :
    (routineBatch10.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch10_checked :
    (routineBatch10.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine320_ready : RoutineReady ⟨320, by decide⟩ routine320 := by
  wct_ready_start 320 10 0
  wct_cases [236234,236240,236242,236244,236248,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 22 236234 16
  · wct_piece 22 236240 17
  · wct_piece 22 236242 18
  · wct_piece 22 236244 19
  · wct_piece 22 236248 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine321_ready : RoutineReady ⟨321, by decide⟩ routine321 := by
  wct_ready_start 321 10 1
  wct_cases [236249,236255,236257,236260,236266,236270,4391,2078,1120,805,811,814]
  · wct_piece 22 236249 21
  · wct_piece 22 236255 22
  · wct_piece 22 236257 23
  · wct_piece 22 236260 24
  · wct_piece 22 236266 25
  · wct_piece 22 236270 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine322_ready : RoutineReady ⟨322, by decide⟩ routine322 := by
  wct_ready_start 322 10 2
  wct_cases [236271,236277,236279,236282,236288,236292,4412,2099,1138,1144,875,881]
  · wct_piece 22 236271 27
  · wct_piece 22 236277 28
  · wct_piece 22 236279 29
  · wct_piece 22 236282 30
  · wct_piece 22 236288 31
  · wct_piece 22 236292 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine323_ready : RoutineReady ⟨323, by decide⟩ routine323 := by
  wct_ready_start 323 10 3
  wct_cases [236293,236299,236301,236304,236310,236314,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 22 236293 33
  · wct_piece 22 236299 34
  · wct_piece 22 236301 35
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
theorem routine324_ready : RoutineReady ⟨324, by decide⟩ routine324 := by
  wct_ready_start 324 10 4
  wct_cases [236315,236321,236323,236326,236332,236336,4454,2138,2144,2148,1365,875,881]
  · wct_piece 22 236315 39
  · wct_piece 22 236321 40
  · wct_piece 22 236323 41
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
theorem routine325_ready : RoutineReady ⟨325, by decide⟩ routine325 := by
  wct_ready_start 325 10 5
  wct_cases [236337,236343,236345,236348,236354,236358,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 22 236337 45
  · wct_piece 22 236343 46
  · wct_piece 22 236345 47
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
theorem routine326_ready : RoutineReady ⟨326, by decide⟩ routine326 := by
  wct_ready_start 326 10 6
  wct_cases [236359,236365,236367,236370,236376,236380,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 22 236359 51
  · wct_piece 22 236365 52
  · wct_piece 22 236367 53
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
theorem routine327_ready : RoutineReady ⟨327, by decide⟩ routine327 := by
  wct_ready_start 327 10 7
  wct_cases [236381,236387,236389,236392,236398,4514,4520,4524,2681,1365,875,881]
  · wct_piece 22 236381 57
  · wct_piece 22 236387 58
  · wct_piece 22 236389 59
  · wct_piece 22 236392 60
  · wct_piece 22 236398 61
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine328_ready : RoutineReady ⟨328, by decide⟩ routine328 := by
  wct_ready_start 328 10 8
  wct_cases [236399,236405,236407,236410,236416,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 22 236399 62
  · wct_piece 22 236405 63
  · wct_piece 23 236407 0
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
theorem routine329_ready : RoutineReady ⟨329, by decide⟩ routine329 := by
  wct_ready_start 329 10 9
  wct_cases [236417,236423,236425,236428,236434,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 23 236417 3
  · wct_piece 23 236423 4
  · wct_piece 23 236425 5
  · wct_piece 23 236428 6
  · wct_piece 23 236434 7
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine330_ready : RoutineReady ⟨330, by decide⟩ routine330 := by
  wct_ready_start 330 10 10
  wct_cases [236435,236441,236443,236446,236452,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 23 236435 8
  · wct_piece 23 236441 9
  · wct_piece 23 236443 10
  · wct_piece 23 236446 11
  · wct_piece 23 236452 12
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine331_ready : RoutineReady ⟨331, by decide⟩ routine331 := by
  wct_ready_start 331 10 11
  wct_cases [236453,236459,236461,236464,236470,236472,236476,235869,2681,1365,875,881]
  · wct_piece 23 236453 13
  · wct_piece 23 236459 14
  · wct_piece 23 236461 15
  · wct_piece 23 236464 16
  · wct_piece 23 236470 17
  · wct_piece 23 236472 18
  · wct_piece 23 236476 19
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine332_ready : RoutineReady ⟨332, by decide⟩ routine332 := by
  wct_ready_start 332 10 12
  wct_cases [236477,236483,236485,236488,236494,236496,236500,235893,2705,1386,1392,1396,966]
  · wct_piece 23 236477 20
  · wct_piece 23 236483 21
  · wct_piece 23 236485 22
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
theorem routine333_ready : RoutineReady ⟨333, by decide⟩ routine333 := by
  wct_ready_start 333 10 13
  wct_cases [236501,236507,236509,236512,236518,236520,236524,235917,2726,2732,2736,1585,966]
  · wct_piece 23 236501 27
  · wct_piece 23 236507 28
  · wct_piece 23 236509 29
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
theorem routine334_ready : RoutineReady ⟨334, by decide⟩ routine334 := by
  wct_ready_start 334 10 14
  wct_cases [236525,236531,236533,236536,236542,236545,235938,235944,235948,3101,1585,966]
  · wct_piece 23 236525 34
  · wct_piece 23 236531 35
  · wct_piece 23 236533 36
  · wct_piece 23 236536 37
  · wct_piece 23 236542 38
  · wct_piece 23 236545 39
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine335_ready : RoutineReady ⟨335, by decide⟩ routine335 := by
  wct_ready_start 335 10 15
  wct_cases [236546,236552,236554,236557,236563,236565,236567,236571,3101,1585,966]
  · wct_piece 23 236546 40
  · wct_piece 23 236552 41
  · wct_piece 23 236554 42
  · wct_piece 23 236557 43
  · wct_piece 23 236563 44
  · wct_piece 23 236565 45
  · wct_piece 23 236567 46
  · wct_piece 23 236571 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine336_ready : RoutineReady ⟨336, by decide⟩ routine336 := by
  wct_ready_start 336 10 16
  wct_cases [236572,236578,3112,1596,982,778,784,787,755,761,763,766]
  · wct_piece 23 236572 48
  · wct_piece 23 236578 49
  · wct_piece 10 3112 5
  · wct_piece 3 1596 37
  · wct_piece 0 982 60
  · wct_piece 0 778 8
  · wct_piece 0 784 9
  · wct_piece 0 787 10
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine337_ready : RoutineReady ⟨337, by decide⟩ routine337 := by
  wct_ready_start 337 10 17
  wct_cases [236579,236585,3123,1607,993,794,800,802,805,811,814]
  · wct_piece 23 236579 50
  · wct_piece 23 236585 51
  · wct_piece 10 3123 8
  · wct_piece 3 1607 40
  · wct_piece 0 993 63
  · wct_piece 0 794 12
  · wct_piece 0 800 13
  · wct_piece 0 802 14
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine338_ready : RoutineReady ⟨338, by decide⟩ routine338 := by
  wct_ready_start 338 10 18
  wct_cases [236586,236592,3134,1618,1000,1006,829,835,755,761,763,766]
  · wct_piece 23 236586 52
  · wct_piece 23 236592 53
  · wct_piece 10 3134 11
  · wct_piece 3 1618 43
  · wct_piece 1 1000 1
  · wct_piece 1 1006 2
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine339_ready : RoutineReady ⟨339, by decide⟩ routine339 := by
  wct_ready_start 339 10 19
  wct_cases [236593,236599,3145,1629,1013,1019,845,851,854,805,811,814]
  · wct_piece 23 236593 54
  · wct_piece 23 236599 55
  · wct_piece 10 3145 14
  · wct_piece 3 1629 46
  · wct_piece 1 1013 4
  · wct_piece 1 1019 5
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine340_ready : RoutineReady ⟨340, by decide⟩ routine340 := by
  wct_ready_start 340 10 20
  wct_cases [236600,236606,3156,1640,1026,1032,864,870,872,875,881]
  · wct_piece 23 236600 56
  · wct_piece 23 236606 57
  · wct_piece 10 3156 17
  · wct_piece 3 1640 49
  · wct_piece 1 1026 7
  · wct_piece 1 1032 8
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine341_ready : RoutineReady ⟨341, by decide⟩ routine341 := by
  wct_ready_start 341 10 21
  wct_cases [236607,236613,3167,1651,1039,1045,1047,1051,901,755,761,763,766]
  · wct_piece 23 236607 58
  · wct_piece 23 236613 59
  · wct_piece 10 3167 20
  · wct_piece 3 1651 52
  · wct_piece 1 1039 10
  · wct_piece 1 1045 11
  · wct_piece 1 1047 12
  · wct_piece 1 1051 13
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine342_ready : RoutineReady ⟨342, by decide⟩ routine342 := by
  wct_ready_start 342 10 22
  wct_cases [236614,236620,3178,1662,1058,1064,1067,913,919,805,811,814]
  · wct_piece 23 236614 60
  · wct_piece 23 236620 61
  · wct_piece 10 3178 23
  · wct_piece 3 1662 55
  · wct_piece 1 1058 15
  · wct_piece 1 1064 16
  · wct_piece 1 1067 17
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine343_ready : RoutineReady ⟨343, by decide⟩ routine343 := by
  wct_ready_start 343 10 23
  wct_cases [236621,236627,3189,1673,1074,1080,1083,931,937,940,875,881]
  · wct_piece 23 236621 62
  · wct_piece 23 236627 63
  · wct_piece 10 3189 26
  · wct_piece 3 1673 58
  · wct_piece 1 1074 19
  · wct_piece 1 1080 20
  · wct_piece 1 1083 21
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine344_ready : RoutineReady ⟨344, by decide⟩ routine344 := by
  wct_ready_start 344 10 24
  wct_cases [236628,236634,3200,1684,1090,1096,1099,952,958,960,962,966]
  · wct_piece 24 236628 0
  · wct_piece 24 236634 1
  · wct_piece 10 3200 29
  · wct_piece 3 1684 61
  · wct_piece 1 1090 23
  · wct_piece 1 1096 24
  · wct_piece 1 1099 25
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine345_ready : RoutineReady ⟨345, by decide⟩ routine345 := by
  wct_ready_start 345 10 25
  wct_cases [236635,236641,3211,1695,1106,1112,1114,1116,1120,805,811,814]
  · wct_piece 24 236635 2
  · wct_piece 24 236641 3
  · wct_piece 10 3211 32
  · wct_piece 4 1695 0
  · wct_piece 1 1106 27
  · wct_piece 1 1112 28
  · wct_piece 1 1114 29
  · wct_piece 1 1116 30
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine346_ready : RoutineReady ⟨346, by decide⟩ routine346 := by
  wct_ready_start 346 10 26
  wct_cases [236642,236648,3222,1706,1127,1133,1135,1138,1144,875,881]
  · wct_piece 24 236642 4
  · wct_piece 24 236648 5
  · wct_piece 10 3222 35
  · wct_piece 4 1706 3
  · wct_piece 1 1127 33
  · wct_piece 1 1133 34
  · wct_piece 1 1135 35
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine347_ready : RoutineReady ⟨347, by decide⟩ routine347 := by
  wct_ready_start 347 10 27
  wct_cases [236649,236655,3233,1717,1151,1157,1159,1162,1168,1170,1174,966]
  · wct_piece 24 236649 6
  · wct_piece 24 236655 7
  · wct_piece 10 3233 38
  · wct_piece 4 1717 6
  · wct_piece 1 1151 39
  · wct_piece 1 1157 40
  · wct_piece 1 1159 41
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine348_ready : RoutineReady ⟨348, by decide⟩ routine348 := by
  wct_ready_start 348 10 28
  wct_cases [236656,236662,3244,1724,1730,1734,1187,829,835,755,761,763,766]
  · wct_piece 24 236656 8
  · wct_piece 24 236662 9
  · wct_piece 10 3244 41
  · wct_piece 4 1724 8
  · wct_piece 4 1730 9
  · wct_piece 4 1734 10
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine349_ready : RoutineReady ⟨349, by decide⟩ routine349 := by
  wct_ready_start 349 10 29
  wct_cases [236663,236669,3255,3261,3265,1200,845,851,854,805,811,814]
  · wct_piece 24 236663 10
  · wct_piece 24 236669 11
  · wct_piece 10 3255 44
  · wct_piece 10 3261 45
  · wct_piece 10 3265 46
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine350_ready : RoutineReady ⟨350, by decide⟩ routine350 := by
  wct_ready_start 350 10 30
  wct_cases [236670,236676,3276,1758,1764,1768,1213,864,870,872,875,881]
  · wct_piece 24 236670 12
  · wct_piece 24 236676 13
  · wct_piece 10 3276 49
  · wct_piece 4 1758 16
  · wct_piece 4 1764 17
  · wct_piece 4 1768 18
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine351_ready : RoutineReady ⟨351, by decide⟩ routine351 := by
  wct_ready_start 351 10 31
  wct_cases [236677,236683,3287,1775,1781,1223,1229,1233,901,755,761,763,766]
  · wct_piece 24 236677 14
  · wct_piece 24 236683 15
  · wct_piece 10 3287 52
  · wct_piece 4 1775 20
  · wct_piece 4 1781 21
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage10 (rank : Fin 728) (hlo : 320 ≤ rank.val) (hhi : rank.val < 352) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 320 ≤ n at hlo
  change n < 352 at hhi
  interval_cases n
  · exact ⟨routine320, routine320_ready⟩
  · exact ⟨routine321, routine321_ready⟩
  · exact ⟨routine322, routine322_ready⟩
  · exact ⟨routine323, routine323_ready⟩
  · exact ⟨routine324, routine324_ready⟩
  · exact ⟨routine325, routine325_ready⟩
  · exact ⟨routine326, routine326_ready⟩
  · exact ⟨routine327, routine327_ready⟩
  · exact ⟨routine328, routine328_ready⟩
  · exact ⟨routine329, routine329_ready⟩
  · exact ⟨routine330, routine330_ready⟩
  · exact ⟨routine331, routine331_ready⟩
  · exact ⟨routine332, routine332_ready⟩
  · exact ⟨routine333, routine333_ready⟩
  · exact ⟨routine334, routine334_ready⟩
  · exact ⟨routine335, routine335_ready⟩
  · exact ⟨routine336, routine336_ready⟩
  · exact ⟨routine337, routine337_ready⟩
  · exact ⟨routine338, routine338_ready⟩
  · exact ⟨routine339, routine339_ready⟩
  · exact ⟨routine340, routine340_ready⟩
  · exact ⟨routine341, routine341_ready⟩
  · exact ⟨routine342, routine342_ready⟩
  · exact ⟨routine343, routine343_ready⟩
  · exact ⟨routine344, routine344_ready⟩
  · exact ⟨routine345, routine345_ready⟩
  · exact ⟨routine346, routine346_ready⟩
  · exact ⟨routine347, routine347_ready⟩
  · exact ⟨routine348, routine348_ready⟩
  · exact ⟨routine349, routine349_ready⟩
  · exact ⟨routine350, routine350_ready⟩
  · exact ⟨routine351, routine351_ready⟩
end W9Machine.Chain
end
