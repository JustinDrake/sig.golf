import SigGolfCandidate.W9Machine.WctRoutineCheck09
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch09_checked :
    (routineBatch09.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch09_checked :
    (routineBatch09.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine288_ready : RoutineReady ⟨288, by decide⟩ routine288 := by
  wct_ready_start 288 9 0
  wct_cases [235008,235014,235017,235023,235025,235029,4412,2099,1138,1144,875,881]
  · wct_piece 19 235008 32
  · wct_piece 19 235014 33
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
theorem routine289_ready : RoutineReady ⟨289, by decide⟩ routine289 := by
  wct_ready_start 289 9 1
  wct_cases [235030,235036,235039,235045,235047,235051,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 19 235030 38
  · wct_piece 19 235036 39
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
theorem routine290_ready : RoutineReady ⟨290, by decide⟩ routine290 := by
  wct_ready_start 290 9 2
  wct_cases [235052,235058,235061,235067,235069,235073,4454,2138,2144,2148,1365,875,881]
  · wct_piece 19 235052 44
  · wct_piece 19 235058 45
  · wct_piece 19 235061 46
  · wct_piece 19 235067 47
  · wct_piece 19 235069 48
  · wct_piece 19 235073 49
  · wct_piece 15 4454 27
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine291_ready : RoutineReady ⟨291, by decide⟩ routine291 := by
  wct_ready_start 291 9 3
  wct_cases [235074,235080,235083,235089,235091,235095,4475,2166,2172,1386,1392,1396,966]
  · wct_piece 19 235074 50
  · wct_piece 19 235080 51
  · wct_piece 19 235083 52
  · wct_piece 19 235089 53
  · wct_piece 19 235091 54
  · wct_piece 19 235095 55
  · wct_piece 15 4475 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine292_ready : RoutineReady ⟨292, by decide⟩ routine292 := by
  wct_ready_start 292 9 4
  wct_cases [235096,235102,235105,235111,235113,235117,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 19 235096 56
  · wct_piece 19 235102 57
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
theorem routine293_ready : RoutineReady ⟨293, by decide⟩ routine293 := by
  wct_ready_start 293 9 5
  wct_cases [235118,235124,235127,235133,235136,4514,4520,4524,2681,1365,875,881]
  · wct_piece 19 235118 62
  · wct_piece 19 235124 63
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
theorem routine294_ready : RoutineReady ⟨294, by decide⟩ routine294 := by
  wct_ready_start 294 9 6
  wct_cases [235137,235143,235146,235152,235155,235161,235165,2705,1386,1392,1396,966]
  · wct_piece 20 235137 3
  · wct_piece 20 235143 4
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
theorem routine295_ready : RoutineReady ⟨295, by decide⟩ routine295 := by
  wct_ready_start 295 9 7
  wct_cases [235166,235172,235175,235181,235184,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 20 235166 10
  · wct_piece 20 235172 11
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
theorem routine296_ready : RoutineReady ⟨296, by decide⟩ routine296 := by
  wct_ready_start 296 9 8
  wct_cases [235185,235191,235194,235200,235203,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 20 235185 15
  · wct_piece 20 235191 16
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
theorem routine297_ready : RoutineReady ⟨297, by decide⟩ routine297 := by
  wct_ready_start 297 9 9
  wct_cases [235204,235210,235213,235219,235221,235223,235227,2681,1365,875,881]
  · wct_piece 20 235204 20
  · wct_piece 20 235210 21
  · wct_piece 20 235213 22
  · wct_piece 20 235219 23
  · wct_piece 20 235221 24
  · wct_piece 20 235223 25
  · wct_piece 20 235227 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine298_ready : RoutineReady ⟨298, by decide⟩ routine298 := by
  wct_ready_start 298 9 10
  wct_cases [235228,235234,235237,235243,235245,235247,235251,2705,1386,1392,1396,966]
  · wct_piece 20 235228 27
  · wct_piece 20 235234 28
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
theorem routine299_ready : RoutineReady ⟨299, by decide⟩ routine299 := by
  wct_ready_start 299 9 11
  wct_cases [235252,235258,235261,235267,235269,235271,235275,2726,2732,2736,1585,966]
  · wct_piece 20 235252 34
  · wct_piece 20 235258 35
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
theorem routine300_ready : RoutineReady ⟨300, by decide⟩ routine300 := by
  wct_ready_start 300 9 12
  wct_cases [235276,235282,235285,235291,235293,235296,235302,235306,3101,1585,966]
  · wct_piece 20 235276 41
  · wct_piece 20 235282 42
  · wct_piece 20 235285 43
  · wct_piece 20 235291 44
  · wct_piece 20 235293 45
  · wct_piece 20 235296 46
  · wct_piece 20 235302 47
  · wct_piece 20 235306 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine301_ready : RoutineReady ⟨301, by decide⟩ routine301 := by
  wct_ready_start 301 9 13
  wct_cases [235307,235313,235315,235317,235321,2751,1411,901,755,761,763,766]
  · wct_piece 20 235307 49
  · wct_piece 20 235313 50
  · wct_piece 20 235315 51
  · wct_piece 20 235317 52
  · wct_piece 20 235321 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine302_ready : RoutineReady ⟨302, by decide⟩ routine302 := by
  wct_ready_start 302 9 14
  wct_cases [235322,235328,235330,235332,235336,2766,1426,913,919,805,811,814]
  · wct_piece 20 235322 54
  · wct_piece 20 235328 55
  · wct_piece 20 235330 56
  · wct_piece 20 235332 57
  · wct_piece 20 235336 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine303_ready : RoutineReady ⟨303, by decide⟩ routine303 := by
  wct_ready_start 303 9 15
  wct_cases [235337,235343,235345,235347,235351,2781,1441,931,937,940,875,881]
  · wct_piece 20 235337 59
  · wct_piece 20 235343 60
  · wct_piece 20 235345 61
  · wct_piece 20 235347 62
  · wct_piece 20 235351 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine304_ready : RoutineReady ⟨304, by decide⟩ routine304 := by
  wct_ready_start 304 9 16
  wct_cases [235352,235358,235360,235362,235366,2796,1456,952,958,960,962,966]
  · wct_piece 21 235352 0
  · wct_piece 21 235358 1
  · wct_piece 21 235360 2
  · wct_piece 21 235362 3
  · wct_piece 21 235366 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine305_ready : RoutineReady ⟨305, by decide⟩ routine305 := by
  wct_ready_start 305 9 17
  wct_cases [235367,235373,235375,235377,235381,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 21 235367 5
  · wct_piece 21 235373 6
  · wct_piece 21 235375 7
  · wct_piece 21 235377 8
  · wct_piece 21 235381 9
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine306_ready : RoutineReady ⟨306, by decide⟩ routine306 := by
  wct_ready_start 306 9 18
  wct_cases [235382,235388,235390,235392,235396,2826,1490,1496,1138,1144,875,881]
  · wct_piece 21 235382 10
  · wct_piece 21 235388 11
  · wct_piece 21 235390 12
  · wct_piece 21 235392 13
  · wct_piece 21 235396 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine307_ready : RoutineReady ⟨307, by decide⟩ routine307 := by
  wct_ready_start 307 9 19
  wct_cases [235397,235403,235405,235407,235411,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 21 235397 15
  · wct_piece 21 235403 16
  · wct_piece 21 235405 17
  · wct_piece 21 235407 18
  · wct_piece 21 235411 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine308_ready : RoutineReady ⟨308, by decide⟩ routine308 := by
  wct_ready_start 308 9 20
  wct_cases [235412,235418,235420,235422,235426,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 21 235412 20
  · wct_piece 21 235418 21
  · wct_piece 21 235420 22
  · wct_piece 21 235422 23
  · wct_piece 21 235426 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine309_ready : RoutineReady ⟨309, by decide⟩ routine309 := by
  wct_ready_start 309 9 21
  wct_cases [235427,235433,235435,235437,235441,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 21 235427 25
  · wct_piece 21 235433 26
  · wct_piece 21 235435 27
  · wct_piece 21 235437 28
  · wct_piece 21 235441 29
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine310_ready : RoutineReady ⟨310, by decide⟩ routine310 := by
  wct_ready_start 310 9 22
  wct_cases [235442,235448,235450,235452,235456,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 21 235442 30
  · wct_piece 21 235448 31
  · wct_piece 21 235450 32
  · wct_piece 21 235452 33
  · wct_piece 21 235456 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine311_ready : RoutineReady ⟨311, by decide⟩ routine311 := by
  wct_ready_start 311 9 23
  wct_cases [235457,235463,235465,235467,235471,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 21 235457 35
  · wct_piece 21 235463 36
  · wct_piece 21 235465 37
  · wct_piece 21 235467 38
  · wct_piece 21 235471 39
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine312_ready : RoutineReady ⟨312, by decide⟩ routine312 := by
  wct_ready_start 312 9 24
  wct_cases [235472,235478,235480,235482,235486,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 21 235472 40
  · wct_piece 21 235478 41
  · wct_piece 21 235480 42
  · wct_piece 21 235482 43
  · wct_piece 21 235486 44
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine313_ready : RoutineReady ⟨313, by decide⟩ routine313 := by
  wct_ready_start 313 9 25
  wct_cases [235487,235493,235495,235497,235501,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 21 235487 45
  · wct_piece 21 235493 46
  · wct_piece 21 235495 47
  · wct_piece 21 235497 48
  · wct_piece 21 235501 49
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine314_ready : RoutineReady ⟨314, by decide⟩ routine314 := by
  wct_ready_start 314 9 26
  wct_cases [235502,235508,235510,235512,235516,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 21 235502 50
  · wct_piece 21 235508 51
  · wct_piece 21 235510 52
  · wct_piece 21 235512 53
  · wct_piece 21 235516 54
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine315_ready : RoutineReady ⟨315, by decide⟩ routine315 := by
  wct_ready_start 315 9 27
  wct_cases [235517,235523,235525,235527,235531,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 21 235517 55
  · wct_piece 21 235523 56
  · wct_piece 21 235525 57
  · wct_piece 21 235527 58
  · wct_piece 21 235531 59
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine316_ready : RoutineReady ⟨316, by decide⟩ routine316 := by
  wct_ready_start 316 9 28
  wct_cases [235532,235538,235540,235542,235546,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 21 235532 60
  · wct_piece 21 235538 61
  · wct_piece 21 235540 62
  · wct_piece 21 235542 63
  · wct_piece 22 235546 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine317_ready : RoutineReady ⟨317, by decide⟩ routine317 := by
  wct_ready_start 317 9 29
  wct_cases [235547,235553,235555,235557,235561,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 22 235547 1
  · wct_piece 22 235553 2
  · wct_piece 22 235555 3
  · wct_piece 22 235557 4
  · wct_piece 22 235561 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine318_ready : RoutineReady ⟨318, by decide⟩ routine318 := by
  wct_ready_start 318 9 30
  wct_cases [235562,235568,235570,235572,235576,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 22 235562 6
  · wct_piece 22 235568 7
  · wct_piece 22 235570 8
  · wct_piece 22 235572 9
  · wct_piece 22 235576 10
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine319_ready : RoutineReady ⟨319, by decide⟩ routine319 := by
  wct_ready_start 319 9 31
  wct_cases [235577,235583,235585,235587,235591,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 22 235577 11
  · wct_piece 22 235583 12
  · wct_piece 22 235585 13
  · wct_piece 22 235587 14
  · wct_piece 22 235591 15
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage09 (rank : Fin 728) (hlo : 288 ≤ rank.val) (hhi : rank.val < 320) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 288 ≤ n at hlo
  change n < 320 at hhi
  interval_cases n
  · exact ⟨routine288, routine288_ready⟩
  · exact ⟨routine289, routine289_ready⟩
  · exact ⟨routine290, routine290_ready⟩
  · exact ⟨routine291, routine291_ready⟩
  · exact ⟨routine292, routine292_ready⟩
  · exact ⟨routine293, routine293_ready⟩
  · exact ⟨routine294, routine294_ready⟩
  · exact ⟨routine295, routine295_ready⟩
  · exact ⟨routine296, routine296_ready⟩
  · exact ⟨routine297, routine297_ready⟩
  · exact ⟨routine298, routine298_ready⟩
  · exact ⟨routine299, routine299_ready⟩
  · exact ⟨routine300, routine300_ready⟩
  · exact ⟨routine301, routine301_ready⟩
  · exact ⟨routine302, routine302_ready⟩
  · exact ⟨routine303, routine303_ready⟩
  · exact ⟨routine304, routine304_ready⟩
  · exact ⟨routine305, routine305_ready⟩
  · exact ⟨routine306, routine306_ready⟩
  · exact ⟨routine307, routine307_ready⟩
  · exact ⟨routine308, routine308_ready⟩
  · exact ⟨routine309, routine309_ready⟩
  · exact ⟨routine310, routine310_ready⟩
  · exact ⟨routine311, routine311_ready⟩
  · exact ⟨routine312, routine312_ready⟩
  · exact ⟨routine313, routine313_ready⟩
  · exact ⟨routine314, routine314_ready⟩
  · exact ⟨routine315, routine315_ready⟩
  · exact ⟨routine316, routine316_ready⟩
  · exact ⟨routine317, routine317_ready⟩
  · exact ⟨routine318, routine318_ready⟩
  · exact ⟨routine319, routine319_ready⟩
end W9Machine.Chain
end
