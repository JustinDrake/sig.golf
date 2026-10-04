import SigGolfCandidate.W9Machine.WctRoutineCheck07
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch07_checked :
    (routineBatch07.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch07_checked :
    (routineBatch07.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine224_ready : RoutineReady ⟨224, by decide⟩ routine224 := by
  wct_ready_start 224 7 0
  wct_cases [4339,4345,4351,4354,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 14 4339 60
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
theorem routine225_ready : RoutineReady ⟨225, by decide⟩ routine225 := by
  wct_ready_start 225 7 1
  wct_cases [4355,4361,4367,4370,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 15 4355 0
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
theorem routine226_ready : RoutineReady ⟨226, by decide⟩ routine226 := by
  wct_ready_start 226 7 2
  wct_cases [4371,4377,4383,4385,4387,4391,2078,1120,805,811,814]
  · wct_piece 15 4371 4
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
theorem routine227_ready : RoutineReady ⟨227, by decide⟩ routine227 := by
  wct_ready_start 227 7 3
  wct_cases [4392,4398,4404,4406,4408,4412,2099,1138,1144,875,881]
  · wct_piece 15 4392 10
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
theorem routine228_ready : RoutineReady ⟨228, by decide⟩ routine228 := by
  wct_ready_start 228 7 4
  wct_cases [4413,4419,4425,4427,4429,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 15 4413 16
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
theorem routine229_ready : RoutineReady ⟨229, by decide⟩ routine229 := by
  wct_ready_start 229 7 5
  wct_cases [4434,4440,4446,4448,4450,4454,2138,2144,2148,1365,875,881]
  · wct_piece 15 4434 22
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
theorem routine230_ready : RoutineReady ⟨230, by decide⟩ routine230 := by
  wct_ready_start 230 7 6
  wct_cases [4455,4461,4467,4469,4471,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 15 4455 28
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
theorem routine231_ready : RoutineReady ⟨231, by decide⟩ routine231 := by
  wct_ready_start 231 7 7
  wct_cases [4476,4482,4488,4490,4492,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 15 4476 34
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
theorem routine232_ready : RoutineReady ⟨232, by decide⟩ routine232 := by
  wct_ready_start 232 7 8
  wct_cases [4497,4503,4509,4511,4514,4520,4524,2681,1365,875,881]
  · wct_piece 15 4497 40
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
theorem routine233_ready : RoutineReady ⟨233, by decide⟩ routine233 := by
  wct_ready_start 233 7 9
  wct_cases [4525,4531,4537,4539,4542,4548,4552,2705,1386,1392,1396,966]
  · wct_piece 15 4525 47
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
theorem routine234_ready : RoutineReady ⟨234, by decide⟩ routine234 := by
  wct_ready_start 234 7 10
  wct_cases [4553,4559,4565,4567,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 15 4553 54
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
theorem routine235_ready : RoutineReady ⟨235, by decide⟩ routine235 := by
  wct_ready_start 235 7 11
  wct_cases [4577,4583,4589,4591,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 15 4577 60
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
theorem routine236_ready : RoutineReady ⟨236, by decide⟩ routine236 := by
  wct_ready_start 236 7 12
  wct_cases [4607,4613,4615,4619,2215,1187,829,835,755,761,763,766]
  · wct_piece 16 4607 4
  · wct_piece 16 4613 5
  · wct_piece 16 4615 6
  · wct_piece 16 4619 7
  · wct_piece 6 2215 4
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine237_ready : RoutineReady ⟨237, by decide⟩ routine237 := by
  wct_ready_start 237 7 13
  wct_cases [4620,4626,4628,4632,2228,1200,845,851,854,805,811,814]
  · wct_piece 16 4620 8
  · wct_piece 16 4626 9
  · wct_piece 16 4628 10
  · wct_piece 16 4632 11
  · wct_piece 6 2228 8
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine238_ready : RoutineReady ⟨238, by decide⟩ routine238 := by
  wct_ready_start 238 7 14
  wct_cases [4633,4639,4641,4645,2241,1213,864,870,872,875,881]
  · wct_piece 16 4633 12
  · wct_piece 16 4639 13
  · wct_piece 16 4641 14
  · wct_piece 16 4645 15
  · wct_piece 6 2241 12
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine239_ready : RoutineReady ⟨239, by decide⟩ routine239 := by
  wct_ready_start 239 7 15
  wct_cases [4646,4652,4654,4658,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 16 4646 16
  · wct_piece 16 4652 17
  · wct_piece 16 4654 18
  · wct_piece 16 4658 19
  · wct_piece 6 2254 16
  · wct_piece 1 1223 60
  · wct_piece 1 1229 61
  · wct_piece 1 1233 62
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine240_ready : RoutineReady ⟨240, by decide⟩ routine240 := by
  wct_ready_start 240 7 16
  wct_cases [4659,4665,4667,4671,2267,1243,1249,913,919,805,811,814]
  · wct_piece 16 4659 20
  · wct_piece 16 4665 21
  · wct_piece 16 4667 22
  · wct_piece 16 4671 23
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine241_ready : RoutineReady ⟨241, by decide⟩ routine241 := by
  wct_ready_start 241 7 17
  wct_cases [4672,4678,4680,4684,2280,1259,1265,931,937,940,875,881]
  · wct_piece 16 4672 24
  · wct_piece 16 4678 25
  · wct_piece 16 4680 26
  · wct_piece 16 4684 27
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine242_ready : RoutineReady ⟨242, by decide⟩ routine242 := by
  wct_ready_start 242 7 18
  wct_cases [4685,4691,4693,4697,2293,1275,1281,952,958,960,962,966]
  · wct_piece 16 4685 28
  · wct_piece 16 4691 29
  · wct_piece 16 4693 30
  · wct_piece 16 4697 31
  · wct_piece 6 2293 28
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine243_ready : RoutineReady ⟨243, by decide⟩ routine243 := by
  wct_ready_start 243 7 19
  wct_cases [4698,4704,4706,4710,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 16 4698 32
  · wct_piece 16 4704 33
  · wct_piece 16 4706 34
  · wct_piece 16 4710 35
  · wct_piece 6 2306 32
  · wct_piece 2 1291 13
  · wct_piece 2 1297 14
  · wct_piece 2 1299 15
  · wct_piece 2 1303 16
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine244_ready : RoutineReady ⟨244, by decide⟩ routine244 := by
  wct_ready_start 244 7 20
  wct_cases [4711,4717,4719,4723,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 16 4711 36
  · wct_piece 16 4717 37
  · wct_piece 16 4719 38
  · wct_piece 16 4723 39
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine245_ready : RoutineReady ⟨245, by decide⟩ routine245 := by
  wct_ready_start 245 7 21
  wct_cases [4724,4730,4732,4736,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 16 4724 40
  · wct_piece 16 4730 41
  · wct_piece 16 4732 42
  · wct_piece 16 4736 43
  · wct_piece 6 2332 40
  · wct_piece 2 1332 24
  · wct_piece 2 1338 25
  · wct_piece 2 1341 26
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine246_ready : RoutineReady ⟨246, by decide⟩ routine246 := by
  wct_ready_start 246 7 22
  wct_cases [4737,4743,4745,4749,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 16 4737 44
  · wct_piece 16 4743 45
  · wct_piece 16 4745 46
  · wct_piece 16 4749 47
  · wct_piece 6 2345 44
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine247_ready : RoutineReady ⟨247, by decide⟩ routine247 := by
  wct_ready_start 247 7 23
  wct_cases [235008,235014,235016,235020,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 16 235008 48
  · wct_piece 16 235014 49
  · wct_piece 16 235016 50
  · wct_piece 16 235020 51
  · wct_piece 6 2358 48
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine248_ready : RoutineReady ⟨248, by decide⟩ routine248 := by
  wct_ready_start 248 7 24
  wct_cases [235021,235027,235029,235033,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 16 235021 52
  · wct_piece 16 235027 53
  · wct_piece 16 235029 54
  · wct_piece 16 235033 55
  · wct_piece 6 2368 51
  · wct_piece 6 2374 52
  · wct_piece 6 2378 53
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine249_ready : RoutineReady ⟨249, by decide⟩ routine249 := by
  wct_ready_start 249 7 25
  wct_cases [235034,235040,235042,235046,2388,2394,2398,1426,913,919,805,811,814]
  · wct_piece 16 235034 56
  · wct_piece 16 235040 57
  · wct_piece 16 235042 58
  · wct_piece 16 235046 59
  · wct_piece 6 2388 56
  · wct_piece 6 2394 57
  · wct_piece 6 2398 58
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine250_ready : RoutineReady ⟨250, by decide⟩ routine250 := by
  wct_ready_start 250 7 26
  wct_cases [235047,235053,235055,235059,2408,2414,2418,1441,931,937,940,875,881]
  · wct_piece 16 235047 60
  · wct_piece 16 235053 61
  · wct_piece 16 235055 62
  · wct_piece 16 235059 63
  · wct_piece 6 2408 61
  · wct_piece 6 2414 62
  · wct_piece 6 2418 63
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine251_ready : RoutineReady ⟨251, by decide⟩ routine251 := by
  wct_ready_start 251 7 27
  wct_cases [235060,235066,235068,235072,2428,2434,2438,1456,952,958,960,962,966]
  · wct_piece 17 235060 0
  · wct_piece 17 235066 1
  · wct_piece 17 235068 2
  · wct_piece 17 235072 3
  · wct_piece 7 2428 2
  · wct_piece 7 2434 3
  · wct_piece 7 2438 4
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine252_ready : RoutineReady ⟨252, by decide⟩ routine252 := by
  wct_ready_start 252 7 28
  wct_cases [235073,235079,235081,235085,2448,2454,1468,1474,1478,1120,805,811,814]
  · wct_piece 17 235073 4
  · wct_piece 17 235079 5
  · wct_piece 17 235081 6
  · wct_piece 17 235085 7
  · wct_piece 7 2448 7
  · wct_piece 7 2454 8
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine253_ready : RoutineReady ⟨253, by decide⟩ routine253 := by
  wct_ready_start 253 7 29
  wct_cases [235086,235092,235094,235098,2464,2470,1490,1496,1138,1144,875,881]
  · wct_piece 17 235086 8
  · wct_piece 17 235092 9
  · wct_piece 17 235094 10
  · wct_piece 17 235098 11
  · wct_piece 7 2464 11
  · wct_piece 7 2470 12
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine254_ready : RoutineReady ⟨254, by decide⟩ routine254 := by
  wct_ready_start 254 7 30
  wct_cases [235099,235105,235107,235111,2480,2486,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 17 235099 12
  · wct_piece 17 235105 13
  · wct_piece 17 235107 14
  · wct_piece 17 235111 15
  · wct_piece 7 2480 15
  · wct_piece 7 2486 16
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine255_ready : RoutineReady ⟨255, by decide⟩ routine255 := by
  wct_ready_start 255 7 31
  wct_cases [235112,235118,235120,235124,2496,2502,1526,1532,1534,1538,1365,875,881]
  · wct_piece 17 235112 16
  · wct_piece 17 235118 17
  · wct_piece 17 235120 18
  · wct_piece 17 235124 19
  · wct_piece 7 2496 19
  · wct_piece 7 2502 20
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
end W9Machine.Chain
end
