import SigGolfCandidate.W9Machine.WctRoutineCheck06
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch06_checked :
    (routineBatch06.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch06_checked :
    (routineBatch06.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine192_ready : RoutineReady ⟨192, by decide⟩ routine192 := by
  wct_ready_start 192 6 0
  wct_cases [3839,3845,3851,2464,2470,1490,1496,1138,1144,875,881]
  · wct_piece 13 3839 0
  · wct_piece 13 3845 1
  · wct_piece 13 3851 2
  · wct_piece 7 2464 11
  · wct_piece 7 2470 12
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine193_ready : RoutineReady ⟨193, by decide⟩ routine193 := by
  wct_ready_start 193 6 1
  wct_cases [3852,3858,3864,2480,2486,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 13 3852 3
  · wct_piece 13 3858 4
  · wct_piece 13 3864 5
  · wct_piece 7 2480 15
  · wct_piece 7 2486 16
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine194_ready : RoutineReady ⟨194, by decide⟩ routine194 := by
  wct_ready_start 194 6 2
  wct_cases [3865,3871,3877,2496,2502,1526,1532,1534,1538,1365,875,881]
  · wct_piece 13 3865 6
  · wct_piece 13 3871 7
  · wct_piece 13 3877 8
  · wct_piece 7 2496 19
  · wct_piece 7 2502 20
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine195_ready : RoutineReady ⟨195, by decide⟩ routine195 := by
  wct_ready_start 195 6 3
  wct_cases [3878,3884,3890,2512,2518,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 13 3878 9
  · wct_piece 13 3884 10
  · wct_piece 13 3890 11
  · wct_piece 7 2512 23
  · wct_piece 7 2518 24
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine196_ready : RoutineReady ⟨196, by decide⟩ routine196 := by
  wct_ready_start 196 6 4
  wct_cases [3891,3897,3903,2528,2534,1571,1577,1579,1581,1585,966]
  · wct_piece 13 3891 12
  · wct_piece 13 3897 13
  · wct_piece 13 3903 14
  · wct_piece 7 2528 27
  · wct_piece 7 2534 28
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine197_ready : RoutineReady ⟨197, by decide⟩ routine197 := by
  wct_ready_start 197 6 5
  wct_cases [3904,3910,3916,2544,2550,2552,2556,2078,1120,805,811,814]
  · wct_piece 13 3904 15
  · wct_piece 13 3910 16
  · wct_piece 13 3916 17
  · wct_piece 7 2544 31
  · wct_piece 7 2550 32
  · wct_piece 7 2552 33
  · wct_piece 7 2556 34
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine198_ready : RoutineReady ⟨198, by decide⟩ routine198 := by
  wct_ready_start 198 6 6
  wct_cases [3917,3923,3929,2566,2572,2574,2578,2099,1138,1144,875,881]
  · wct_piece 13 3917 18
  · wct_piece 13 3923 19
  · wct_piece 13 3929 20
  · wct_piece 7 2566 37
  · wct_piece 7 2572 38
  · wct_piece 7 2574 39
  · wct_piece 7 2578 40
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine199_ready : RoutineReady ⟨199, by decide⟩ routine199 := by
  wct_ready_start 199 6 7
  wct_cases [3930,3936,3942,2588,2594,2596,2600,2120,1162,1168,1170,1174,966]
  · wct_piece 13 3930 21
  · wct_piece 13 3936 22
  · wct_piece 13 3942 23
  · wct_piece 7 2588 43
  · wct_piece 7 2594 44
  · wct_piece 7 2596 45
  · wct_piece 7 2600 46
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine200_ready : RoutineReady ⟨200, by decide⟩ routine200 := by
  wct_ready_start 200 6 8
  wct_cases [3943,3949,3955,2610,2616,2619,2138,2144,2148,1365,875,881]
  · wct_piece 13 3943 24
  · wct_piece 13 3949 25
  · wct_piece 13 3955 26
  · wct_piece 7 2610 49
  · wct_piece 7 2616 50
  · wct_piece 7 2619 51
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine201_ready : RoutineReady ⟨201, by decide⟩ routine201 := by
  wct_ready_start 201 6 9
  wct_cases [3956,3962,3968,2629,2635,2638,2166,2172,1386,1392,1396,966]
  · wct_piece 13 3956 27
  · wct_piece 13 3962 28
  · wct_piece 13 3968 29
  · wct_piece 7 2629 54
  · wct_piece 7 2635 55
  · wct_piece 7 2638 56
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine202_ready : RoutineReady ⟨202, by decide⟩ routine202 := by
  wct_ready_start 202 6 10
  wct_cases [3969,3975,3981,2648,2654,2657,2190,2196,2198,2202,1585,966]
  · wct_piece 13 3969 30
  · wct_piece 13 3975 31
  · wct_piece 13 3981 32
  · wct_piece 7 2648 59
  · wct_piece 7 2654 60
  · wct_piece 7 2657 61
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine203_ready : RoutineReady ⟨203, by decide⟩ routine203 := by
  wct_ready_start 203 6 11
  wct_cases [3982,3988,3994,2667,2673,2675,2677,2681,1365,875,881]
  · wct_piece 13 3982 33
  · wct_piece 13 3988 34
  · wct_piece 13 3994 35
  · wct_piece 8 2667 0
  · wct_piece 8 2673 1
  · wct_piece 8 2675 2
  · wct_piece 8 2677 3
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine204_ready : RoutineReady ⟨204, by decide⟩ routine204 := by
  wct_ready_start 204 6 12
  wct_cases [3995,4001,4007,2691,2697,2699,2701,2705,1386,1392,1396,966]
  · wct_piece 13 3995 36
  · wct_piece 13 4001 37
  · wct_piece 13 4007 38
  · wct_piece 8 2691 7
  · wct_piece 8 2697 8
  · wct_piece 8 2699 9
  · wct_piece 8 2701 10
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine205_ready : RoutineReady ⟨205, by decide⟩ routine205 := by
  wct_ready_start 205 6 13
  wct_cases [4008,4014,4020,2715,2721,2723,2726,2732,2736,1585,966]
  · wct_piece 13 4008 39
  · wct_piece 13 4014 40
  · wct_piece 13 4020 41
  · wct_piece 8 2715 14
  · wct_piece 8 2721 15
  · wct_piece 8 2723 16
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine206_ready : RoutineReady ⟨206, by decide⟩ routine206 := by
  wct_ready_start 206 6 14
  wct_cases [4021,4027,4033,4035,4039,2751,1411,901,755,761,763,766]
  · wct_piece 13 4021 42
  · wct_piece 13 4027 43
  · wct_piece 13 4033 44
  · wct_piece 13 4035 45
  · wct_piece 13 4039 46
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine207_ready : RoutineReady ⟨207, by decide⟩ routine207 := by
  wct_ready_start 207 6 15
  wct_cases [4040,4046,4052,4054,4058,2766,1426,913,919,805,811,814]
  · wct_piece 13 4040 47
  · wct_piece 13 4046 48
  · wct_piece 13 4052 49
  · wct_piece 13 4054 50
  · wct_piece 13 4058 51
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine208_ready : RoutineReady ⟨208, by decide⟩ routine208 := by
  wct_ready_start 208 6 16
  wct_cases [4059,4065,4071,4073,4077,2781,1441,931,937,940,875,881]
  · wct_piece 13 4059 52
  · wct_piece 13 4065 53
  · wct_piece 13 4071 54
  · wct_piece 13 4073 55
  · wct_piece 13 4077 56
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine209_ready : RoutineReady ⟨209, by decide⟩ routine209 := by
  wct_ready_start 209 6 17
  wct_cases [4078,4084,4090,4092,4096,2796,1456,952,958,960,962,966]
  · wct_piece 13 4078 57
  · wct_piece 13 4084 58
  · wct_piece 13 4090 59
  · wct_piece 13 4092 60
  · wct_piece 13 4096 61
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine210_ready : RoutineReady ⟨210, by decide⟩ routine210 := by
  wct_ready_start 210 6 18
  wct_cases [4097,4103,4109,4111,4115,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 13 4097 62
  · wct_piece 13 4103 63
  · wct_piece 14 4109 0
  · wct_piece 14 4111 1
  · wct_piece 14 4115 2
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine211_ready : RoutineReady ⟨211, by decide⟩ routine211 := by
  wct_ready_start 211 6 19
  wct_cases [4116,4122,4128,4130,4134,2826,1490,1496,1138,1144,875,881]
  · wct_piece 14 4116 3
  · wct_piece 14 4122 4
  · wct_piece 14 4128 5
  · wct_piece 14 4130 6
  · wct_piece 14 4134 7
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine212_ready : RoutineReady ⟨212, by decide⟩ routine212 := by
  wct_ready_start 212 6 20
  wct_cases [4135,4141,4147,4149,4153,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 14 4135 8
  · wct_piece 14 4141 9
  · wct_piece 14 4147 10
  · wct_piece 14 4149 11
  · wct_piece 14 4153 12
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine213_ready : RoutineReady ⟨213, by decide⟩ routine213 := by
  wct_ready_start 213 6 21
  wct_cases [4154,4160,4166,4168,4172,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 14 4154 13
  · wct_piece 14 4160 14
  · wct_piece 14 4166 15
  · wct_piece 14 4168 16
  · wct_piece 14 4172 17
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine214_ready : RoutineReady ⟨214, by decide⟩ routine214 := by
  wct_ready_start 214 6 22
  wct_cases [4173,4179,4185,4187,4191,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 14 4173 18
  · wct_piece 14 4179 19
  · wct_piece 14 4185 20
  · wct_piece 14 4187 21
  · wct_piece 14 4191 22
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine215_ready : RoutineReady ⟨215, by decide⟩ routine215 := by
  wct_ready_start 215 6 23
  wct_cases [4192,4198,4204,4206,4210,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 14 4192 23
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
theorem routine216_ready : RoutineReady ⟨216, by decide⟩ routine216 := by
  wct_ready_start 216 6 24
  wct_cases [4211,4217,4223,4226,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 14 4211 28
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
theorem routine217_ready : RoutineReady ⟨217, by decide⟩ routine217 := by
  wct_ready_start 217 6 25
  wct_cases [4227,4233,4239,4242,2920,2926,2930,2099,1138,1144,875,881]
  · wct_piece 14 4227 32
  · wct_piece 14 4233 33
  · wct_piece 14 4239 34
  · wct_piece 14 4242 35
  · wct_piece 9 2920 15
  · wct_piece 9 2926 16
  · wct_piece 9 2930 17
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine218_ready : RoutineReady ⟨218, by decide⟩ routine218 := by
  wct_ready_start 218 6 26
  wct_cases [4243,4249,4255,4258,2942,2948,2952,2120,1162,1168,1170,1174,966]
  · wct_piece 14 4243 36
  · wct_piece 14 4249 37
  · wct_piece 14 4255 38
  · wct_piece 14 4258 39
  · wct_piece 9 2942 21
  · wct_piece 9 2948 22
  · wct_piece 9 2952 23
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine219_ready : RoutineReady ⟨219, by decide⟩ routine219 := by
  wct_ready_start 219 6 27
  wct_cases [4259,4265,4271,4274,2964,2970,2138,2144,2148,1365,875,881]
  · wct_piece 14 4259 40
  · wct_piece 14 4265 41
  · wct_piece 14 4271 42
  · wct_piece 14 4274 43
  · wct_piece 9 2964 27
  · wct_piece 9 2970 28
  · wct_piece 5 2138 48
  · wct_piece 5 2144 49
  · wct_piece 5 2148 50
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine220_ready : RoutineReady ⟨220, by decide⟩ routine220 := by
  wct_ready_start 220 6 28
  wct_cases [4275,4281,4287,4290,2982,2988,2166,2172,1386,1392,1396,966]
  · wct_piece 14 4275 44
  · wct_piece 14 4281 45
  · wct_piece 14 4287 46
  · wct_piece 14 4290 47
  · wct_piece 9 2982 32
  · wct_piece 9 2988 33
  · wct_piece 5 2166 55
  · wct_piece 5 2172 56
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine221_ready : RoutineReady ⟨221, by decide⟩ routine221 := by
  wct_ready_start 221 6 29
  wct_cases [4291,4297,4303,4306,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 14 4291 48
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
theorem routine222_ready : RoutineReady ⟨222, by decide⟩ routine222 := by
  wct_ready_start 222 6 30
  wct_cases [4307,4313,4319,4322,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 14 4307 52
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
theorem routine223_ready : RoutineReady ⟨223, by decide⟩ routine223 := by
  wct_ready_start 223 6 31
  wct_cases [4323,4329,4335,4338,3042,3048,3050,3054,2705,1386,1392,1396,966]
  · wct_piece 14 4323 56
  · wct_piece 14 4329 57
  · wct_piece 14 4335 58
  · wct_piece 14 4338 59
  · wct_piece 9 3042 49
  · wct_piece 9 3048 50
  · wct_piece 9 3050 51
  · wct_piece 9 3054 52
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
end W9Machine.Chain
end
