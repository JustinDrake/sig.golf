import SigGolfCandidate.W9Machine.WctRoutineCheck15
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch15_checked :
    (routineBatch15.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch15_checked :
    (routineBatch15.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine480_ready : RoutineReady ⟨480, by decide⟩ routine480 := by
  wct_ready_start 480 15 0
  wct_cases [237989,237995,238001,238007,238013,238017,238023,238025,238029,966]
  · wct_piece 31 237989 28
  · wct_piece 31 237995 29
  · wct_piece 31 238001 30
  · wct_piece 31 238007 31
  · wct_piece 31 238013 32
  · wct_piece 31 238017 33
  · wct_piece 31 238023 34
  · wct_piece 31 238025 35
  · wct_piece 31 238029 36
  · wct_piece 0 966 57
theorem routine481_ready : RoutineReady ⟨481, by decide⟩ routine481 := by
  wct_ready_start 481 15 1
  wct_cases [238030,238036,238042,238048,238054,238060,238064,875,881]
  · wct_piece 31 238030 37
  · wct_piece 31 238036 38
  · wct_piece 31 238042 39
  · wct_piece 31 238048 40
  · wct_piece 31 238054 41
  · wct_piece 31 238060 42
  · wct_piece 31 238064 43
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine482_ready : RoutineReady ⟨482, by decide⟩ routine482 := by
  wct_ready_start 482 15 2
  wct_cases [238065,238071,238077,238083,238089,238095,238101,238105,966]
  · wct_piece 31 238065 44
  · wct_piece 31 238071 45
  · wct_piece 31 238077 46
  · wct_piece 31 238083 47
  · wct_piece 31 238089 48
  · wct_piece 31 238095 49
  · wct_piece 31 238101 50
  · wct_piece 31 238105 51
  · wct_piece 0 966 57
theorem routine483_ready : RoutineReady ⟨483, by decide⟩ routine483 := by
  wct_ready_start 483 15 3
  wct_cases [238106,238112,238118,5299,5305,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 31 238106 52
  · wct_piece 31 238112 53
  · wct_piece 31 238118 54
  · wct_piece 19 5299 8
  · wct_piece 19 5305 9
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine484_ready : RoutineReady ⟨484, by decide⟩ routine484 := by
  wct_ready_start 484 15 4
  wct_cases [238119,238125,238131,5315,5321,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 31 238119 55
  · wct_piece 31 238125 56
  · wct_piece 31 238131 57
  · wct_piece 19 5315 12
  · wct_piece 19 5321 13
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine485_ready : RoutineReady ⟨485, by decide⟩ routine485 := by
  wct_ready_start 485 15 5
  wct_cases [238132,238138,238144,238150,238156,238158,238162,238168,238172,966]
  · wct_piece 31 238132 58
  · wct_piece 31 238138 59
  · wct_piece 31 238144 60
  · wct_piece 31 238150 61
  · wct_piece 31 238156 62
  · wct_piece 31 238158 63
  · wct_piece 32 238162 0
  · wct_piece 32 238168 1
  · wct_piece 32 238172 2
  · wct_piece 0 966 57
theorem routine486_ready : RoutineReady ⟨486, by decide⟩ routine486 := by
  wct_ready_start 486 15 6
  wct_cases [238173,238179,238185,238191,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 32 238173 3
  · wct_piece 32 238179 4
  · wct_piece 32 238185 5
  · wct_piece 32 238191 6
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine487_ready : RoutineReady ⟨487, by decide⟩ routine487 := by
  wct_ready_start 487 15 7
  wct_cases [238192,238198,238204,5363,5369,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 32 238192 7
  · wct_piece 32 238198 8
  · wct_piece 32 238204 9
  · wct_piece 19 5363 24
  · wct_piece 19 5369 25
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine488_ready : RoutineReady ⟨488, by decide⟩ routine488 := by
  wct_ready_start 488 15 8
  wct_cases [238205,238211,238217,5379,5385,5387,5391,4391,2078,1120,805,811,814]
  · wct_piece 32 238205 10
  · wct_piece 32 238211 11
  · wct_piece 32 238217 12
  · wct_piece 19 5379 28
  · wct_piece 19 5385 29
  · wct_piece 19 5387 30
  · wct_piece 19 5391 31
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine489_ready : RoutineReady ⟨489, by decide⟩ routine489 := by
  wct_ready_start 489 15 9
  wct_cases [238218,238224,238230,235017,235023,235025,235029,4412,2099,1138,1144,875,881]
  · wct_piece 32 238218 13
  · wct_piece 32 238224 14
  · wct_piece 32 238230 15
  · wct_piece 19 235017 34
  · wct_piece 19 235023 35
  · wct_piece 19 235025 36
  · wct_piece 19 235029 37
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine490_ready : RoutineReady ⟨490, by decide⟩ routine490 := by
  wct_ready_start 490 15 10
  wct_cases [238231,238237,238243,235039,235045,235047,235051,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 32 238231 16
  · wct_piece 32 238237 17
  · wct_piece 32 238243 18
  · wct_piece 19 235039 40
  · wct_piece 19 235045 41
  · wct_piece 19 235047 42
  · wct_piece 19 235051 43
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine491_ready : RoutineReady ⟨491, by decide⟩ routine491 := by
  wct_ready_start 491 15 11
  wct_cases [238244,238250,238256,238262,238264,238268,238274,238278,875,881]
  · wct_piece 32 238244 19
  · wct_piece 32 238250 20
  · wct_piece 32 238256 21
  · wct_piece 32 238262 22
  · wct_piece 32 238264 23
  · wct_piece 32 238268 24
  · wct_piece 32 238274 25
  · wct_piece 32 238278 26
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine492_ready : RoutineReady ⟨492, by decide⟩ routine492 := by
  wct_ready_start 492 15 12
  wct_cases [238279,238285,238291,238297,238299,238303,238309,238315,238319,966]
  · wct_piece 32 238279 27
  · wct_piece 32 238285 28
  · wct_piece 32 238291 29
  · wct_piece 32 238297 30
  · wct_piece 32 238299 31
  · wct_piece 32 238303 32
  · wct_piece 32 238309 33
  · wct_piece 32 238315 34
  · wct_piece 32 238319 35
  · wct_piece 0 966 57
theorem routine493_ready : RoutineReady ⟨493, by decide⟩ routine493 := by
  wct_ready_start 493 15 13
  wct_cases [238320,238326,238332,235105,235111,235113,235117,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 32 238320 36
  · wct_piece 32 238326 37
  · wct_piece 32 238332 38
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
theorem routine494_ready : RoutineReady ⟨494, by decide⟩ routine494 := by
  wct_ready_start 494 15 14
  wct_cases [238333,238339,238345,238351,238354,4514,4520,4524,2681,1365,875,881]
  · wct_piece 32 238333 39
  · wct_piece 32 238339 40
  · wct_piece 32 238345 41
  · wct_piece 32 238351 42
  · wct_piece 32 238354 43
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine495_ready : RoutineReady ⟨495, by decide⟩ routine495 := by
  wct_ready_start 495 15 15
  wct_cases [238355,238361,238367,238373,238376,238382,238386,238392,238396]
  · wct_piece 32 238355 44
  · wct_piece 32 238361 45
  · wct_piece 32 238367 46
  · wct_piece 32 238373 47
  · wct_piece 32 238376 48
  · wct_piece 32 238382 49
  · wct_piece 32 238386 50
  · wct_piece 32 238392 51
  · wct_piece 32 238396 52
theorem routine496_ready : RoutineReady ⟨496, by decide⟩ routine496 := by
  wct_ready_start 496 15 16
  wct_cases [238402,238408,238414,238420,238423,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 32 238402 53
  · wct_piece 32 238408 54
  · wct_piece 32 238414 55
  · wct_piece 32 238420 56
  · wct_piece 32 238423 57
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine497_ready : RoutineReady ⟨497, by decide⟩ routine497 := by
  wct_ready_start 497 15 17
  wct_cases [238424,238430,238436,235194,235200,235203,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 32 238424 58
  · wct_piece 32 238430 59
  · wct_piece 32 238436 60
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
theorem routine498_ready : RoutineReady ⟨498, by decide⟩ routine498 := by
  wct_ready_start 498 15 18
  wct_cases [238437,238443,238449,235213,235219,235221,235223,235227,2681,1365,875,881]
  · wct_piece 32 238437 61
  · wct_piece 32 238443 62
  · wct_piece 32 238449 63
  · wct_piece 20 235213 22
  · wct_piece 20 235219 23
  · wct_piece 20 235221 24
  · wct_piece 20 235223 25
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine499_ready : RoutineReady ⟨499, by decide⟩ routine499 := by
  wct_ready_start 499 15 19
  wct_cases [238450,238456,238462,235237,235243,235245,235247,235251,2705,1386,1392,1396,966]
  · wct_piece 33 238450 0
  · wct_piece 33 238456 1
  · wct_piece 33 238462 2
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
theorem routine500_ready : RoutineReady ⟨500, by decide⟩ routine500 := by
  wct_ready_start 500 15 20
  wct_cases [238463,238469,238475,235261,235267,235269,235271,235275,2726,2732,2736,1585,966]
  · wct_piece 33 238463 3
  · wct_piece 33 238469 4
  · wct_piece 33 238475 5
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
theorem routine501_ready : RoutineReady ⟨501, by decide⟩ routine501 := by
  wct_ready_start 501 15 21
  wct_cases [238476,238482,238488,235285,235291,235293,235296,235302,235306,3101,1585,966]
  · wct_piece 33 238476 6
  · wct_piece 33 238482 7
  · wct_piece 33 238488 8
  · wct_piece 20 235285 43
  · wct_piece 20 235291 44
  · wct_piece 20 235293 45
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine502_ready : RoutineReady ⟨502, by decide⟩ routine502 := by
  wct_ready_start 502 15 22
  wct_cases [238489,238495,238501,238503,238507,235321,2751,1411,901,755,761,763,766]
  · wct_piece 33 238489 9
  · wct_piece 33 238495 10
  · wct_piece 33 238501 11
  · wct_piece 33 238503 12
  · wct_piece 33 238507 13
  · wct_piece 20 235321 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine503_ready : RoutineReady ⟨503, by decide⟩ routine503 := by
  wct_ready_start 503 15 23
  wct_cases [238508,238514,238520,238522,238526,235336,2766,1426,913,919,805,811,814]
  · wct_piece 33 238508 14
  · wct_piece 33 238514 15
  · wct_piece 33 238520 16
  · wct_piece 33 238522 17
  · wct_piece 33 238526 18
  · wct_piece 20 235336 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine504_ready : RoutineReady ⟨504, by decide⟩ routine504 := by
  wct_ready_start 504 15 24
  wct_cases [238527,238533,238539,238541,238545,235351,2781,1441,931,937,940,875,881]
  · wct_piece 33 238527 19
  · wct_piece 33 238533 20
  · wct_piece 33 238539 21
  · wct_piece 33 238541 22
  · wct_piece 33 238545 23
  · wct_piece 20 235351 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine505_ready : RoutineReady ⟨505, by decide⟩ routine505 := by
  wct_ready_start 505 15 25
  wct_cases [238546,238552,238558,238560,238564,235366,2796,1456,952,958,960,962,966]
  · wct_piece 33 238546 24
  · wct_piece 33 238552 25
  · wct_piece 33 238558 26
  · wct_piece 33 238560 27
  · wct_piece 33 238564 28
  · wct_piece 21 235366 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine506_ready : RoutineReady ⟨506, by decide⟩ routine506 := by
  wct_ready_start 506 15 26
  wct_cases [238565,238571,238577,238579,238583,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 33 238565 29
  · wct_piece 33 238571 30
  · wct_piece 33 238577 31
  · wct_piece 33 238579 32
  · wct_piece 33 238583 33
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine507_ready : RoutineReady ⟨507, by decide⟩ routine507 := by
  wct_ready_start 507 15 27
  wct_cases [238584,238590,238596,238598,238602,235396,2826,1490,1496,1138,1144,875,881]
  · wct_piece 33 238584 34
  · wct_piece 33 238590 35
  · wct_piece 33 238596 36
  · wct_piece 33 238598 37
  · wct_piece 33 238602 38
  · wct_piece 21 235396 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine508_ready : RoutineReady ⟨508, by decide⟩ routine508 := by
  wct_ready_start 508 15 28
  wct_cases [238603,238609,238615,238617,238621,235411,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 33 238603 39
  · wct_piece 33 238609 40
  · wct_piece 33 238615 41
  · wct_piece 33 238617 42
  · wct_piece 33 238621 43
  · wct_piece 21 235411 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine509_ready : RoutineReady ⟨509, by decide⟩ routine509 := by
  wct_ready_start 509 15 29
  wct_cases [238622,238628,238634,238636,238640,235426,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 33 238622 44
  · wct_piece 33 238628 45
  · wct_piece 33 238634 46
  · wct_piece 33 238636 47
  · wct_piece 33 238640 48
  · wct_piece 21 235426 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine510_ready : RoutineReady ⟨510, by decide⟩ routine510 := by
  wct_ready_start 510 15 30
  wct_cases [238641,238647,238653,238655,238659,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 33 238641 49
  · wct_piece 33 238647 50
  · wct_piece 33 238653 51
  · wct_piece 33 238655 52
  · wct_piece 33 238659 53
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine511_ready : RoutineReady ⟨511, by decide⟩ routine511 := by
  wct_ready_start 511 15 31
  wct_cases [238660,238666,238672,238674,238678,235456,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 33 238660 54
  · wct_piece 33 238666 55
  · wct_piece 33 238672 56
  · wct_piece 33 238674 57
  · wct_piece 33 238678 58
  · wct_piece 21 235456 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage15 (rank : Fin 728) (hlo : 480 ≤ rank.val) (hhi : rank.val < 512) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 480 ≤ n at hlo
  change n < 512 at hhi
  interval_cases n
  · exact ⟨routine480, routine480_ready⟩
  · exact ⟨routine481, routine481_ready⟩
  · exact ⟨routine482, routine482_ready⟩
  · exact ⟨routine483, routine483_ready⟩
  · exact ⟨routine484, routine484_ready⟩
  · exact ⟨routine485, routine485_ready⟩
  · exact ⟨routine486, routine486_ready⟩
  · exact ⟨routine487, routine487_ready⟩
  · exact ⟨routine488, routine488_ready⟩
  · exact ⟨routine489, routine489_ready⟩
  · exact ⟨routine490, routine490_ready⟩
  · exact ⟨routine491, routine491_ready⟩
  · exact ⟨routine492, routine492_ready⟩
  · exact ⟨routine493, routine493_ready⟩
  · exact ⟨routine494, routine494_ready⟩
  · exact ⟨routine495, routine495_ready⟩
  · exact ⟨routine496, routine496_ready⟩
  · exact ⟨routine497, routine497_ready⟩
  · exact ⟨routine498, routine498_ready⟩
  · exact ⟨routine499, routine499_ready⟩
  · exact ⟨routine500, routine500_ready⟩
  · exact ⟨routine501, routine501_ready⟩
  · exact ⟨routine502, routine502_ready⟩
  · exact ⟨routine503, routine503_ready⟩
  · exact ⟨routine504, routine504_ready⟩
  · exact ⟨routine505, routine505_ready⟩
  · exact ⟨routine506, routine506_ready⟩
  · exact ⟨routine507, routine507_ready⟩
  · exact ⟨routine508, routine508_ready⟩
  · exact ⟨routine509, routine509_ready⟩
  · exact ⟨routine510, routine510_ready⟩
  · exact ⟨routine511, routine511_ready⟩
end W9Machine.Chain
end
