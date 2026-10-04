import SigGolfCandidate.W9Machine.WctRoutineCheck17
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch17_checked :
    (routineBatch17.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch17_checked :
    (routineBatch17.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine544_ready : RoutineReady ⟨544, by decide⟩ routine544 := by
  wct_ready_start 544 17 0
  wct_cases [240155,240161,240167,240169,240171,240175,240181,240185,240191,240195,966]
  · wct_piece 37 240155 4
  · wct_piece 37 240161 5
  · wct_piece 37 240167 6
  · wct_piece 37 240169 7
  · wct_piece 37 240171 8
  · wct_piece 37 240175 9
  · wct_piece 37 240181 10
  · wct_piece 37 240185 11
  · wct_piece 37 240191 12
  · wct_piece 37 240195 13
  · wct_piece 0 966 57
theorem routine545_ready : RoutineReady ⟨545, by decide⟩ routine545 := by
  wct_ready_start 545 17 1
  wct_cases [240196,240202,240208,240210,240212,240216,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 37 240196 14
  · wct_piece 37 240202 15
  · wct_piece 37 240208 16
  · wct_piece 37 240210 17
  · wct_piece 37 240212 18
  · wct_piece 37 240216 19
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine546_ready : RoutineReady ⟨546, by decide⟩ routine546 := by
  wct_ready_start 546 17 2
  wct_cases [240217,240223,240229,240231,240233,240237,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 37 240217 20
  · wct_piece 37 240223 21
  · wct_piece 37 240229 22
  · wct_piece 37 240231 23
  · wct_piece 37 240233 24
  · wct_piece 37 240237 25
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine547_ready : RoutineReady ⟨547, by decide⟩ routine547 := by
  wct_ready_start 547 17 3
  wct_cases [240238,240244,240250,240252,240255,240261,240265,235869,2681,1365,875,881]
  · wct_piece 37 240238 26
  · wct_piece 37 240244 27
  · wct_piece 37 240250 28
  · wct_piece 37 240252 29
  · wct_piece 37 240255 30
  · wct_piece 37 240261 31
  · wct_piece 37 240265 32
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine548_ready : RoutineReady ⟨548, by decide⟩ routine548 := by
  wct_ready_start 548 17 4
  wct_cases [240266,240272,240278,240280,240283,240289,240293,235893,2705,1386,1392,1396,966]
  · wct_piece 37 240266 33
  · wct_piece 37 240272 34
  · wct_piece 37 240278 35
  · wct_piece 37 240280 36
  · wct_piece 37 240283 37
  · wct_piece 37 240289 38
  · wct_piece 37 240293 39
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine549_ready : RoutineReady ⟨549, by decide⟩ routine549 := by
  wct_ready_start 549 17 5
  wct_cases [240294,240300,240306,240308,240311,240317,240321,235917,2726,2732,2736,1585,966]
  · wct_piece 37 240294 40
  · wct_piece 37 240300 41
  · wct_piece 37 240306 42
  · wct_piece 37 240308 43
  · wct_piece 37 240311 44
  · wct_piece 37 240317 45
  · wct_piece 37 240321 46
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine550_ready : RoutineReady ⟨550, by decide⟩ routine550 := by
  wct_ready_start 550 17 6
  wct_cases [240322,240328,240334,240336,240339,240345,235938,235944,235948,3101,1585,966]
  · wct_piece 37 240322 47
  · wct_piece 37 240328 48
  · wct_piece 37 240334 49
  · wct_piece 37 240336 50
  · wct_piece 37 240339 51
  · wct_piece 37 240345 52
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine551_ready : RoutineReady ⟨551, by decide⟩ routine551 := by
  wct_ready_start 551 17 7
  wct_cases [240346,240352,240358,240360,240363,240369,240371,240375,236571,3101,1585,966]
  · wct_piece 37 240346 53
  · wct_piece 37 240352 54
  · wct_piece 37 240358 55
  · wct_piece 37 240360 56
  · wct_piece 37 240363 57
  · wct_piece 37 240369 58
  · wct_piece 37 240371 59
  · wct_piece 37 240375 60
  · wct_piece 23 236571 47
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine552_ready : RoutineReady ⟨552, by decide⟩ routine552 := by
  wct_ready_start 552 17 8
  wct_cases [240376,240382,240384,4619,2215,1187,829,835,755,761,763,766]
  · wct_piece 37 240376 61
  · wct_piece 37 240382 62
  · wct_piece 37 240384 63
  · wct_piece 16 4619 7
  · wct_piece 6 2215 4
  · wct_piece 1 1187 49
  · wct_piece 0 829 20
  · wct_piece 0 835 21
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine553_ready : RoutineReady ⟨553, by decide⟩ routine553 := by
  wct_ready_start 553 17 9
  wct_cases [240385,240391,240393,4632,2228,1200,845,851,854,805,811,814]
  · wct_piece 38 240385 0
  · wct_piece 38 240391 1
  · wct_piece 38 240393 2
  · wct_piece 16 4632 11
  · wct_piece 6 2228 8
  · wct_piece 1 1200 53
  · wct_piece 0 845 24
  · wct_piece 0 851 25
  · wct_piece 0 854 26
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine554_ready : RoutineReady ⟨554, by decide⟩ routine554 := by
  wct_ready_start 554 17 10
  wct_cases [240394,240400,240402,4645,2241,1213,864,870,872,875,881]
  · wct_piece 38 240394 3
  · wct_piece 38 240400 4
  · wct_piece 38 240402 5
  · wct_piece 16 4645 15
  · wct_piece 6 2241 12
  · wct_piece 1 1213 57
  · wct_piece 0 864 29
  · wct_piece 0 870 30
  · wct_piece 0 872 31
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine555_ready : RoutineReady ⟨555, by decide⟩ routine555 := by
  wct_ready_start 555 17 11
  wct_cases [240403,240409,240411,4658,2254,1223,1229,1233,901,755,761,763,766]
  · wct_piece 38 240403 6
  · wct_piece 38 240409 7
  · wct_piece 38 240411 8
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
theorem routine556_ready : RoutineReady ⟨556, by decide⟩ routine556 := by
  wct_ready_start 556 17 12
  wct_cases [240412,240418,240420,4671,2267,1243,1249,913,919,805,811,814]
  · wct_piece 38 240412 9
  · wct_piece 38 240418 10
  · wct_piece 38 240420 11
  · wct_piece 16 4671 23
  · wct_piece 6 2267 20
  · wct_piece 2 1243 1
  · wct_piece 2 1249 2
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine557_ready : RoutineReady ⟨557, by decide⟩ routine557 := by
  wct_ready_start 557 17 13
  wct_cases [240421,240427,240429,4684,2280,1259,1265,931,937,940,875,881]
  · wct_piece 38 240421 12
  · wct_piece 38 240427 13
  · wct_piece 38 240429 14
  · wct_piece 16 4684 27
  · wct_piece 6 2280 24
  · wct_piece 2 1259 5
  · wct_piece 2 1265 6
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine558_ready : RoutineReady ⟨558, by decide⟩ routine558 := by
  wct_ready_start 558 17 14
  wct_cases [240430,240436,240438,4697,2293,1275,1281,952,958,960,962,966]
  · wct_piece 38 240430 15
  · wct_piece 38 240436 16
  · wct_piece 38 240438 17
  · wct_piece 16 4697 31
  · wct_piece 6 2293 28
  · wct_piece 2 1275 9
  · wct_piece 2 1281 10
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine559_ready : RoutineReady ⟨559, by decide⟩ routine559 := by
  wct_ready_start 559 17 15
  wct_cases [240439,240445,240447,4710,2306,1291,1297,1299,1303,1120,805,811,814]
  · wct_piece 38 240439 18
  · wct_piece 38 240445 19
  · wct_piece 38 240447 20
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
theorem routine560_ready : RoutineReady ⟨560, by decide⟩ routine560 := by
  wct_ready_start 560 17 16
  wct_cases [240448,240454,240456,4723,2319,1313,1319,1322,1138,1144,875,881]
  · wct_piece 38 240448 21
  · wct_piece 38 240454 22
  · wct_piece 38 240456 23
  · wct_piece 16 4723 39
  · wct_piece 6 2319 36
  · wct_piece 2 1313 19
  · wct_piece 2 1319 20
  · wct_piece 2 1322 21
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine561_ready : RoutineReady ⟨561, by decide⟩ routine561 := by
  wct_ready_start 561 17 17
  wct_cases [240457,240463,240465,4736,2332,1332,1338,1341,1162,1168,1170,1174,966]
  · wct_piece 38 240457 24
  · wct_piece 38 240463 25
  · wct_piece 38 240465 26
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
theorem routine562_ready : RoutineReady ⟨562, by decide⟩ routine562 := by
  wct_ready_start 562 17 18
  wct_cases [240466,240472,240474,4749,2345,1351,1357,1359,1361,1365,875,881]
  · wct_piece 38 240466 27
  · wct_piece 38 240472 28
  · wct_piece 38 240474 29
  · wct_piece 16 4749 47
  · wct_piece 6 2345 44
  · wct_piece 2 1351 29
  · wct_piece 2 1357 30
  · wct_piece 2 1359 31
  · wct_piece 2 1361 32
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine563_ready : RoutineReady ⟨563, by decide⟩ routine563 := by
  wct_ready_start 563 17 19
  wct_cases [240475,240481,240483,235020,2358,1375,1381,1383,1386,1392,1396,966]
  · wct_piece 38 240475 30
  · wct_piece 38 240481 31
  · wct_piece 38 240483 32
  · wct_piece 16 235020 51
  · wct_piece 6 2358 48
  · wct_piece 2 1375 36
  · wct_piece 2 1381 37
  · wct_piece 2 1383 38
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine564_ready : RoutineReady ⟨564, by decide⟩ routine564 := by
  wct_ready_start 564 17 20
  wct_cases [240484,240490,240492,235033,2368,2374,2378,1411,901,755,761,763,766]
  · wct_piece 38 240484 33
  · wct_piece 38 240490 34
  · wct_piece 38 240492 35
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
theorem routine565_ready : RoutineReady ⟨565, by decide⟩ routine565 := by
  wct_ready_start 565 17 21
  wct_cases [240493,240499,240501,235046,2388,2394,2398,1426,913,919,805,811,814]
  · wct_piece 38 240493 36
  · wct_piece 38 240499 37
  · wct_piece 38 240501 38
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
theorem routine566_ready : RoutineReady ⟨566, by decide⟩ routine566 := by
  wct_ready_start 566 17 22
  wct_cases [240502,240508,240510,235059,2408,2414,2418,1441,931,937,940,875,881]
  · wct_piece 38 240502 39
  · wct_piece 38 240508 40
  · wct_piece 38 240510 41
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
theorem routine567_ready : RoutineReady ⟨567, by decide⟩ routine567 := by
  wct_ready_start 567 17 23
  wct_cases [240511,240517,240519,235072,2428,2434,2438,1456,952,958,960,962,966]
  · wct_piece 38 240511 42
  · wct_piece 38 240517 43
  · wct_piece 38 240519 44
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
theorem routine568_ready : RoutineReady ⟨568, by decide⟩ routine568 := by
  wct_ready_start 568 17 24
  wct_cases [240520,240526,240528,235085,2448,2454,1468,1474,1478,1120,805,811,814]
  · wct_piece 38 240520 45
  · wct_piece 38 240526 46
  · wct_piece 38 240528 47
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
theorem routine569_ready : RoutineReady ⟨569, by decide⟩ routine569 := by
  wct_ready_start 569 17 25
  wct_cases [240529,240535,240537,235098,2464,2470,1490,1496,1138,1144,875,881]
  · wct_piece 38 240529 48
  · wct_piece 38 240535 49
  · wct_piece 38 240537 50
  · wct_piece 17 235098 11
  · wct_piece 7 2464 11
  · wct_piece 7 2470 12
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine570_ready : RoutineReady ⟨570, by decide⟩ routine570 := by
  wct_ready_start 570 17 26
  wct_cases [240538,240544,240546,235111,2480,2486,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 38 240538 51
  · wct_piece 38 240544 52
  · wct_piece 38 240546 53
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
theorem routine571_ready : RoutineReady ⟨571, by decide⟩ routine571 := by
  wct_ready_start 571 17 27
  wct_cases [240547,240553,240555,235124,2496,2502,1526,1532,1534,1538,1365,875,881]
  · wct_piece 38 240547 54
  · wct_piece 38 240553 55
  · wct_piece 38 240555 56
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
theorem routine572_ready : RoutineReady ⟨572, by decide⟩ routine572 := by
  wct_ready_start 572 17 28
  wct_cases [240556,240562,240564,235137,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 38 240556 57
  · wct_piece 38 240562 58
  · wct_piece 38 240564 59
  · wct_piece 17 235137 23
  · wct_piece 7 2512 23
  · wct_piece 7 2518 24
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine573_ready : RoutineReady ⟨573, by decide⟩ routine573 := by
  wct_ready_start 573 17 29
  wct_cases [240565,240571,240573,235150,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 38 240565 60
  · wct_piece 38 240571 61
  · wct_piece 38 240573 62
  · wct_piece 17 235150 27
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine574_ready : RoutineReady ⟨574, by decide⟩ routine574 := by
  wct_ready_start 574 17 30
  wct_cases [240574,240580,240582,235163,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 38 240574 63
  · wct_piece 39 240580 0
  · wct_piece 39 240582 1
  · wct_piece 17 235163 31
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine575_ready : RoutineReady ⟨575, by decide⟩ routine575 := by
  wct_ready_start 575 17 31
  wct_cases [240583,240589,240591,235176,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 39 240583 2
  · wct_piece 39 240589 3
  · wct_piece 39 240591 4
  · wct_piece 17 235176 35
  · wct_piece 7 2566 37
  · wct_piece 7 2572 38
  · wct_piece 7 2574 39
  · wct_piece 7 2578 40
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage17 (rank : Fin 728) (hlo : 544 ≤ rank.val) (hhi : rank.val < 576) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 544 ≤ n at hlo
  change n < 576 at hhi
  interval_cases n
  · exact ⟨routine544, routine544_ready⟩
  · exact ⟨routine545, routine545_ready⟩
  · exact ⟨routine546, routine546_ready⟩
  · exact ⟨routine547, routine547_ready⟩
  · exact ⟨routine548, routine548_ready⟩
  · exact ⟨routine549, routine549_ready⟩
  · exact ⟨routine550, routine550_ready⟩
  · exact ⟨routine551, routine551_ready⟩
  · exact ⟨routine552, routine552_ready⟩
  · exact ⟨routine553, routine553_ready⟩
  · exact ⟨routine554, routine554_ready⟩
  · exact ⟨routine555, routine555_ready⟩
  · exact ⟨routine556, routine556_ready⟩
  · exact ⟨routine557, routine557_ready⟩
  · exact ⟨routine558, routine558_ready⟩
  · exact ⟨routine559, routine559_ready⟩
  · exact ⟨routine560, routine560_ready⟩
  · exact ⟨routine561, routine561_ready⟩
  · exact ⟨routine562, routine562_ready⟩
  · exact ⟨routine563, routine563_ready⟩
  · exact ⟨routine564, routine564_ready⟩
  · exact ⟨routine565, routine565_ready⟩
  · exact ⟨routine566, routine566_ready⟩
  · exact ⟨routine567, routine567_ready⟩
  · exact ⟨routine568, routine568_ready⟩
  · exact ⟨routine569, routine569_ready⟩
  · exact ⟨routine570, routine570_ready⟩
  · exact ⟨routine571, routine571_ready⟩
  · exact ⟨routine572, routine572_ready⟩
  · exact ⟨routine573, routine573_ready⟩
  · exact ⟨routine574, routine574_ready⟩
  · exact ⟨routine575, routine575_ready⟩
end W9Machine.Chain
end
