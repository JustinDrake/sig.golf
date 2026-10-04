import SigGolfCandidate.W9Machine.WctRoutineCheck13
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch13_checked :
    (routineBatch13.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch13_checked :
    (routineBatch13.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine416_ready : RoutineReady ⟨416, by decide⟩ routine416 := by
  wct_ready_start 416 13 0
  wct_cases [237252,237258,4198,4204,4206,4210,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 26 237252 40
  · wct_piece 26 237258 41
  · wct_piece 14 4198 24
  · wct_piece 14 4204 25
  · wct_piece 14 4206 26
  · wct_piece 14 4210 27
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine417_ready : RoutineReady ⟨417, by decide⟩ routine417 := by
  wct_ready_start 417 13 1
  wct_cases [237259,237265,4217,4223,4226,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 26 237259 42
  · wct_piece 26 237265 43
  · wct_piece 14 4217 29
  · wct_piece 14 4223 30
  · wct_piece 14 4226 31
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine418_ready : RoutineReady ⟨418, by decide⟩ routine418 := by
  wct_ready_start 418 13 2
  wct_cases [237266,237272,237278,237281,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 26 237266 44
  · wct_piece 26 237272 45
  · wct_piece 26 237278 46
  · wct_piece 26 237281 47
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine419_ready : RoutineReady ⟨419, by decide⟩ routine419 := by
  wct_ready_start 419 13 3
  wct_cases [237282,237288,237294,237297,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 26 237282 48
  · wct_piece 26 237288 49
  · wct_piece 26 237294 50
  · wct_piece 26 237297 51
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine420_ready : RoutineReady ⟨420, by decide⟩ routine420 := by
  wct_ready_start 420 13 4
  wct_cases [237298,237304,237310,237313,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 26 237298 52
  · wct_piece 26 237304 53
  · wct_piece 26 237310 54
  · wct_piece 26 237313 55
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine421_ready : RoutineReady ⟨421, by decide⟩ routine421 := by
  wct_ready_start 421 13 5
  wct_cases [237314,237320,237326,237329,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 26 237314 56
  · wct_piece 26 237320 57
  · wct_piece 26 237326 58
  · wct_piece 26 237329 59
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine422_ready : RoutineReady ⟨422, by decide⟩ routine422 := by
  wct_ready_start 422 13 6
  wct_cases [237330,237336,4297,4303,4306,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 26 237330 60
  · wct_piece 26 237336 61
  · wct_piece 14 4297 49
  · wct_piece 14 4303 50
  · wct_piece 14 4306 51
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine423_ready : RoutineReady ⟨423, by decide⟩ routine423 := by
  wct_ready_start 423 13 7
  wct_cases [237337,237343,4313,4319,4322,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 26 237337 62
  · wct_piece 26 237343 63
  · wct_piece 14 4313 53
  · wct_piece 14 4319 54
  · wct_piece 14 4322 55
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine424_ready : RoutineReady ⟨424, by decide⟩ routine424 := by
  wct_ready_start 424 13 8
  wct_cases [237344,237350,237356,237359,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 27 237344 0
  · wct_piece 27 237350 1
  · wct_piece 27 237356 2
  · wct_piece 27 237359 3
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine425_ready : RoutineReady ⟨425, by decide⟩ routine425 := by
  wct_ready_start 425 13 9
  wct_cases [237360,237366,4345,4351,4354,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 27 237360 4
  · wct_piece 27 237366 5
  · wct_piece 14 4345 61
  · wct_piece 14 4351 62
  · wct_piece 14 4354 63
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine426_ready : RoutineReady ⟨426, by decide⟩ routine426 := by
  wct_ready_start 426 13 10
  wct_cases [237367,237373,4361,4367,4370,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 27 237367 6
  · wct_piece 27 237373 7
  · wct_piece 15 4361 1
  · wct_piece 15 4367 2
  · wct_piece 15 4370 3
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine427_ready : RoutineReady ⟨427, by decide⟩ routine427 := by
  wct_ready_start 427 13 11
  wct_cases [237374,237380,4377,4383,4385,4387,4391,2078,1120,805,811,814]
  · wct_piece 27 237374 8
  · wct_piece 27 237380 9
  · wct_piece 15 4377 5
  · wct_piece 15 4383 6
  · wct_piece 15 4385 7
  · wct_piece 15 4387 8
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine428_ready : RoutineReady ⟨428, by decide⟩ routine428 := by
  wct_ready_start 428 13 12
  wct_cases [237381,237387,4398,4404,4406,4408,4412,2099,1138,1144,875,881]
  · wct_piece 27 237381 10
  · wct_piece 27 237387 11
  · wct_piece 15 4398 11
  · wct_piece 15 4404 12
  · wct_piece 15 4406 13
  · wct_piece 15 4408 14
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine429_ready : RoutineReady ⟨429, by decide⟩ routine429 := by
  wct_ready_start 429 13 13
  wct_cases [237388,237394,4419,4425,4427,4429,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 27 237388 12
  · wct_piece 27 237394 13
  · wct_piece 15 4419 17
  · wct_piece 15 4425 18
  · wct_piece 15 4427 19
  · wct_piece 15 4429 20
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine430_ready : RoutineReady ⟨430, by decide⟩ routine430 := by
  wct_ready_start 430 13 14
  wct_cases [237395,237401,4440,4446,4448,4450,4454,2138,2144,2148,1365,875,881]
  · wct_piece 27 237395 14
  · wct_piece 27 237401 15
  · wct_piece 15 4440 23
  · wct_piece 15 4446 24
  · wct_piece 15 4448 25
  · wct_piece 15 4450 26
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine431_ready : RoutineReady ⟨431, by decide⟩ routine431 := by
  wct_ready_start 431 13 15
  wct_cases [237402,237408,4461,4467,4469,4471,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 27 237402 16
  · wct_piece 27 237408 17
  · wct_piece 15 4461 29
  · wct_piece 15 4467 30
  · wct_piece 15 4469 31
  · wct_piece 15 4471 32
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine432_ready : RoutineReady ⟨432, by decide⟩ routine432 := by
  wct_ready_start 432 13 16
  wct_cases [237409,237415,4482,4488,4490,4492,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 27 237409 18
  · wct_piece 27 237415 19
  · wct_piece 15 4482 35
  · wct_piece 15 4488 36
  · wct_piece 15 4490 37
  · wct_piece 15 4492 38
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine433_ready : RoutineReady ⟨433, by decide⟩ routine433 := by
  wct_ready_start 433 13 17
  wct_cases [237416,237422,4503,4509,4511,4514,4520,4524,2681,1365,875,881]
  · wct_piece 27 237416 20
  · wct_piece 27 237422 21
  · wct_piece 15 4503 41
  · wct_piece 15 4509 42
  · wct_piece 15 4511 43
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine434_ready : RoutineReady ⟨434, by decide⟩ routine434 := by
  wct_ready_start 434 13 18
  wct_cases [237423,237429,4531,4537,4539,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 27 237423 22
  · wct_piece 27 237429 23
  · wct_piece 15 4531 48
  · wct_piece 15 4537 49
  · wct_piece 15 4539 50
  · wct_piece 15 4542 51
  · wct_piece 15 4548 52
  · wct_piece 15 4552 53
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine435_ready : RoutineReady ⟨435, by decide⟩ routine435 := by
  wct_ready_start 435 13 19
  wct_cases [237430,237436,4559,4565,4567,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 27 237430 24
  · wct_piece 27 237436 25
  · wct_piece 15 4559 55
  · wct_piece 15 4565 56
  · wct_piece 15 4567 57
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine436_ready : RoutineReady ⟨436, by decide⟩ routine436 := by
  wct_ready_start 436 13 20
  wct_cases [237437,237443,4583,4589,4591,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 27 237437 26
  · wct_piece 27 237443 27
  · wct_piece 15 4583 61
  · wct_piece 15 4589 62
  · wct_piece 15 4591 63
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine437_ready : RoutineReady ⟨437, by decide⟩ routine437 := by
  wct_ready_start 437 13 21
  wct_cases [237444,237450,237456,237460,4619,2215,1187,829,835,755,761,763,766]
  · wct_piece 27 237444 28
  · wct_piece 27 237450 29
  · wct_piece 27 237456 30
  · wct_piece 27 237460 31
  · wct_piece 16 4619 7
  · wct_piece 6 2215 4
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine438_ready : RoutineReady ⟨438, by decide⟩ routine438 := by
  wct_ready_start 438 13 22
  wct_cases [237461,237467,237473,237477,4632,2228,1200,845,851,854,805,811,814]
  · wct_piece 27 237461 32
  · wct_piece 27 237467 33
  · wct_piece 27 237473 34
  · wct_piece 27 237477 35
  · wct_piece 16 4632 11
  · wct_piece 6 2228 8
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine439_ready : RoutineReady ⟨439, by decide⟩ routine439 := by
  wct_ready_start 439 13 23
  wct_cases [237478,237484,237490,237494,4645,2241,1213,864,870,872,875,881]
  · wct_piece 27 237478 36
  · wct_piece 27 237484 37
  · wct_piece 27 237490 38
  · wct_piece 27 237494 39
  · wct_piece 16 4645 15
  · wct_piece 6 2241 12
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine440_ready : RoutineReady ⟨440, by decide⟩ routine440 := by
  wct_ready_start 440 13 24
  wct_cases [237495,237501,237507,237511,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 27 237495 40
  · wct_piece 27 237501 41
  · wct_piece 27 237507 42
  · wct_piece 27 237511 43
  · wct_piece 6 2254 16
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine441_ready : RoutineReady ⟨441, by decide⟩ routine441 := by
  wct_ready_start 441 13 25
  wct_cases [237512,237518,237524,237528,2267,1243,1249,913,919,805,811,814]
  · wct_piece 27 237512 44
  · wct_piece 27 237518 45
  · wct_piece 27 237524 46
  · wct_piece 27 237528 47
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine442_ready : RoutineReady ⟨442, by decide⟩ routine442 := by
  wct_ready_start 442 13 26
  wct_cases [237529,237535,237541,237545,2280,1259,1265,931,937,940,875,881]
  · wct_piece 27 237529 48
  · wct_piece 27 237535 49
  · wct_piece 27 237541 50
  · wct_piece 27 237545 51
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine443_ready : RoutineReady ⟨443, by decide⟩ routine443 := by
  wct_ready_start 443 13 27
  wct_cases [237546,237552,237558,237562,4697,2293,1275,1281,952,958,960,962,966]
  · wct_piece 27 237546 52
  · wct_piece 27 237552 53
  · wct_piece 27 237558 54
  · wct_piece 27 237562 55
  · wct_piece 16 4697 31
  · wct_piece 6 2293 28
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine444_ready : RoutineReady ⟨444, by decide⟩ routine444 := by
  wct_ready_start 444 13 28
  wct_cases [237563,237569,237575,237579,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 27 237563 56
  · wct_piece 27 237569 57
  · wct_piece 27 237575 58
  · wct_piece 27 237579 59
  · wct_piece 6 2306 32
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine445_ready : RoutineReady ⟨445, by decide⟩ routine445 := by
  wct_ready_start 445 13 29
  wct_cases [237580,237586,237592,237596,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 27 237580 60
  · wct_piece 27 237586 61
  · wct_piece 27 237592 62
  · wct_piece 27 237596 63
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine446_ready : RoutineReady ⟨446, by decide⟩ routine446 := by
  wct_ready_start 446 13 30
  wct_cases [237597,237603,237609,237613,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 28 237597 0
  · wct_piece 28 237603 1
  · wct_piece 28 237609 2
  · wct_piece 28 237613 3
  · wct_piece 6 2332 40
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine447_ready : RoutineReady ⟨447, by decide⟩ routine447 := by
  wct_ready_start 447 13 31
  wct_cases [237614,237620,237626,237630,4749,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 28 237614 4
  · wct_piece 28 237620 5
  · wct_piece 28 237626 6
  · wct_piece 28 237630 7
  · wct_piece 16 4749 47
  · wct_piece 6 2345 44
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage13 (rank : Fin 728) (hlo : 416 ≤ rank.val) (hhi : rank.val < 448) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 416 ≤ n at hlo
  change n < 448 at hhi
  interval_cases n
  · exact ⟨routine416, routine416_ready⟩
  · exact ⟨routine417, routine417_ready⟩
  · exact ⟨routine418, routine418_ready⟩
  · exact ⟨routine419, routine419_ready⟩
  · exact ⟨routine420, routine420_ready⟩
  · exact ⟨routine421, routine421_ready⟩
  · exact ⟨routine422, routine422_ready⟩
  · exact ⟨routine423, routine423_ready⟩
  · exact ⟨routine424, routine424_ready⟩
  · exact ⟨routine425, routine425_ready⟩
  · exact ⟨routine426, routine426_ready⟩
  · exact ⟨routine427, routine427_ready⟩
  · exact ⟨routine428, routine428_ready⟩
  · exact ⟨routine429, routine429_ready⟩
  · exact ⟨routine430, routine430_ready⟩
  · exact ⟨routine431, routine431_ready⟩
  · exact ⟨routine432, routine432_ready⟩
  · exact ⟨routine433, routine433_ready⟩
  · exact ⟨routine434, routine434_ready⟩
  · exact ⟨routine435, routine435_ready⟩
  · exact ⟨routine436, routine436_ready⟩
  · exact ⟨routine437, routine437_ready⟩
  · exact ⟨routine438, routine438_ready⟩
  · exact ⟨routine439, routine439_ready⟩
  · exact ⟨routine440, routine440_ready⟩
  · exact ⟨routine441, routine441_ready⟩
  · exact ⟨routine442, routine442_ready⟩
  · exact ⟨routine443, routine443_ready⟩
  · exact ⟨routine444, routine444_ready⟩
  · exact ⟨routine445, routine445_ready⟩
  · exact ⟨routine446, routine446_ready⟩
  · exact ⟨routine447, routine447_ready⟩
end W9Machine.Chain
end
