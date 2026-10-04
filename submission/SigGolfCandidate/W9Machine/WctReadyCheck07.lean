import SigGolfCandidate.W9Machine.WctRoutineModel
import SigGolfCandidate.W9Machine.WctChainCheck12
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine224 : ChainRoutine := ⟨224, [0, 1, 2, 2, 1, 0, 0], [piece4062, piece4067, piece4072, piece4075, piece2834, piece2839, piece2842, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine225 : ChainRoutine := ⟨225, [0, 1, 2, 3, 0, 0, 0], [piece4076, piece4081, piece4086, piece4089, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine226 : ChainRoutine := ⟨226, [0, 1, 3, 0, 0, 0, 2], [piece4090, piece4095, piece4100, piece4102, piece4104, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine227 : ChainRoutine := ⟨227, [0, 1, 3, 0, 0, 1, 1], [piece4109, piece4114, piece4119, piece4121, piece4123, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine228 : ChainRoutine := ⟨228, [0, 1, 3, 0, 0, 2, 0], [piece4128, piece4133, piece4138, piece4140, piece4142, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine229 : ChainRoutine := ⟨229, [0, 1, 3, 0, 1, 0, 1], [piece4147, piece4152, piece4157, piece4159, piece4161, piece4165, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine230 : ChainRoutine := ⟨230, [0, 1, 3, 0, 1, 1, 0], [piece4166, piece4171, piece4176, piece4178, piece4180, piece4184, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine231 : ChainRoutine := ⟨231, [0, 1, 3, 0, 2, 0, 0], [piece4185, piece4190, piece4195, piece4197, piece4199, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine232 : ChainRoutine := ⟨232, [0, 1, 3, 1, 0, 0, 1], [piece4204, piece4209, piece4214, piece4216, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine233 : ChainRoutine := ⟨233, [0, 1, 3, 1, 0, 1, 0], [piece4229, piece4234, piece4239, piece4241, piece4244, piece4249, piece4253, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine234 : ChainRoutine := ⟨234, [0, 1, 3, 1, 1, 0, 0], [piece4254, piece4259, piece4264, piece4266, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine235 : ChainRoutine := ⟨235, [0, 1, 3, 2, 0, 0, 0], [piece4275, piece4280, piece4285, piece4287, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine236 : ChainRoutine := ⟨236, [0, 2, 0, 0, 0, 1, 3], [piece4302, piece4307, piece4309, piece4313, piece2060, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine237 : ChainRoutine := ⟨237, [0, 2, 0, 0, 0, 2, 2], [piece4314, piece4319, piece4321, piece4325, piece2072, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine238 : ChainRoutine := ⟨238, [0, 2, 0, 0, 0, 3, 1], [piece4326, piece4331, piece4333, piece4337, piece2084, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine239 : ChainRoutine := ⟨239, [0, 2, 0, 0, 1, 0, 3], [piece4338, piece4343, piece4345, piece4349, piece2096, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine240 : ChainRoutine := ⟨240, [0, 2, 0, 0, 1, 1, 2], [piece4350, piece4355, piece4357, piece4361, piece2108, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine241 : ChainRoutine := ⟨241, [0, 2, 0, 0, 1, 2, 1], [piece4362, piece4367, piece4369, piece4373, piece2120, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine242 : ChainRoutine := ⟨242, [0, 2, 0, 0, 1, 3, 0], [piece4374, piece4379, piece4381, piece4385, piece2132, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine243 : ChainRoutine := ⟨243, [0, 2, 0, 0, 2, 0, 2], [piece4386, piece4391, piece4393, piece4397, piece2144, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine244 : ChainRoutine := ⟨244, [0, 2, 0, 0, 2, 1, 1], [piece4398, piece4403, piece4405, piece4409, piece2156, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine245 : ChainRoutine := ⟨245, [0, 2, 0, 0, 2, 2, 0], [piece4410, piece4415, piece4417, piece4421, piece2168, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine246 : ChainRoutine := ⟨246, [0, 2, 0, 0, 3, 0, 1], [piece4422, piece4427, piece4429, piece4433, piece2180, piece1288, piece1293, piece1295, piece1297, piece1301, piece862, piece867]⟩
def routine247 : ChainRoutine := ⟨247, [0, 2, 0, 0, 3, 1, 0], [piece4434, piece4439, piece4441, piece4445, piece2192, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece945]⟩
def routine248 : ChainRoutine := ⟨248, [0, 2, 0, 1, 0, 0, 3], [piece4446, piece4451, piece4453, piece4457, piece2201, piece2206, piece2210, piece1343, piece886, piece754, piece759, piece761, piece764]⟩
def routine249 : ChainRoutine := ⟨249, [0, 2, 0, 1, 0, 1, 2], [piece4458, piece4463, piece4465, piece4469, piece4474, piece4478, piece1357, piece897, piece902, piece799, piece804, piece807]⟩
def routine250 : ChainRoutine := ⟨250, [0, 2, 0, 1, 0, 2, 1], [piece4479, piece4484, piece4486, piece4490, piece4495, piece4499, piece1371, piece913, piece918, piece921, piece862, piece867]⟩
def routine251 : ChainRoutine := ⟨251, [0, 2, 0, 1, 0, 3, 0], [piece4500, piece4505, piece4507, piece4511, piece2255, piece2260, piece2264, piece1385, piece932, piece937, piece939, piece941, piece945]⟩
def routine252 : ChainRoutine := ⟨252, [0, 2, 0, 1, 1, 0, 2], [piece4512, piece4517, piece4519, piece4523, piece4528, piece1396, piece1401, piece1405, piece1081, piece799, piece804, piece807]⟩
def routine253 : ChainRoutine := ⟨253, [0, 2, 0, 1, 1, 1, 1], [piece4529, piece4534, piece4536, piece4540, piece2287, piece2292, piece1416, piece1421, piece1097, piece1102, piece862, piece867]⟩
def routine254 : ChainRoutine := ⟨254, [0, 2, 0, 1, 1, 2, 0], [piece4541, piece4546, piece4548, piece4552, piece2301, piece2306, piece1432, piece1437, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine255 : ChainRoutine := ⟨255, [0, 2, 0, 1, 2, 0, 1], [piece4553, piece4558, piece4560, piece4564, piece2315, piece2320, piece1448, piece1453, piece1455, piece1459, piece1301, piece862, piece867]⟩
def routineBatch07 : List ChainRoutine := [routine224, routine225, routine226, routine227, routine228, routine229, routine230, routine231, routine232, routine233, routine234, routine235, routine236, routine237, routine238, routine239, routine240, routine241, routine242, routine243, routine244, routine245, routine246, routine247, routine248, routine249, routine250, routine251, routine252, routine253, routine254, routine255]
theorem routineBatch07_checked : (routineBatch07.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

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
  wct_cases [4062,4067,4072,4075,2834,2839,2842,2522,2527,2531,1502,945]
  · wct_piece 15 4062 20
  · wct_piece 15 4067 21
  · wct_piece 15 4072 22
  · wct_piece 15 4075 23
  · wct_piece 9 2834 56
  · wct_piece 9 2839 57
  · wct_piece 9 2842 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine225_ready : RoutineReady ⟨225, by decide⟩ routine225 := by
  wct_ready_start 225 7 1
  wct_cases [4076,4081,4086,4089,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 15 4076 24
  · wct_piece 15 4081 25
  · wct_piece 15 4086 26
  · wct_piece 15 4089 27
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine226_ready : RoutineReady ⟨226, by decide⟩ routine226 := by
  wct_ready_start 226 7 2
  wct_cases [4090,4095,4100,4102,4104,4108,1937,1081,799,804,807]
  · wct_piece 15 4090 28
  · wct_piece 15 4095 29
  · wct_piece 15 4100 30
  · wct_piece 15 4102 31
  · wct_piece 15 4104 32
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine227_ready : RoutineReady ⟨227, by decide⟩ routine227 := by
  wct_ready_start 227 7 3
  wct_cases [4109,4114,4119,4121,4123,4127,1956,1097,1102,862,867]
  · wct_piece 15 4109 34
  · wct_piece 15 4114 35
  · wct_piece 15 4119 36
  · wct_piece 15 4121 37
  · wct_piece 15 4123 38
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine228_ready : RoutineReady ⟨228, by decide⟩ routine228 := by
  wct_ready_start 228 7 4
  wct_cases [4128,4133,4138,4140,4142,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 15 4128 40
  · wct_piece 15 4133 41
  · wct_piece 15 4138 42
  · wct_piece 15 4140 43
  · wct_piece 15 4142 44
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine229_ready : RoutineReady ⟨229, by decide⟩ routine229 := by
  wct_ready_start 229 7 5
  wct_cases [4147,4152,4157,4159,4161,4165,1991,1996,2000,1301,862,867]
  · wct_piece 15 4147 46
  · wct_piece 15 4152 47
  · wct_piece 15 4157 48
  · wct_piece 15 4159 49
  · wct_piece 15 4161 50
  · wct_piece 15 4165 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine230_ready : RoutineReady ⟨230, by decide⟩ routine230 := by
  wct_ready_start 230 7 6
  wct_cases [4166,4171,4176,4178,4180,4184,2016,2021,1320,1325,1329,945]
  · wct_piece 15 4166 52
  · wct_piece 15 4171 53
  · wct_piece 15 4176 54
  · wct_piece 15 4178 55
  · wct_piece 15 4180 56
  · wct_piece 15 4184 57
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine231_ready : RoutineReady ⟨231, by decide⟩ routine231 := by
  wct_ready_start 231 7 7
  wct_cases [4185,4190,4195,4197,4199,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 15 4185 58
  · wct_piece 15 4190 59
  · wct_piece 15 4195 60
  · wct_piece 15 4197 61
  · wct_piece 15 4199 62
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine232_ready : RoutineReady ⟨232, by decide⟩ routine232 := by
  wct_ready_start 232 7 8
  wct_cases [4204,4209,4214,4216,4219,4224,4228,2481,1301,862,867]
  · wct_piece 16 4204 0
  · wct_piece 16 4209 1
  · wct_piece 16 4214 2
  · wct_piece 16 4216 3
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine233_ready : RoutineReady ⟨233, by decide⟩ routine233 := by
  wct_ready_start 233 7 9
  wct_cases [4229,4234,4239,4241,4244,4249,4253,2503,1320,1325,1329,945]
  · wct_piece 16 4229 7
  · wct_piece 16 4234 8
  · wct_piece 16 4239 9
  · wct_piece 16 4241 10
  · wct_piece 16 4244 11
  · wct_piece 16 4249 12
  · wct_piece 16 4253 13
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine234_ready : RoutineReady ⟨234, by decide⟩ routine234 := by
  wct_ready_start 234 7 10
  wct_cases [4254,4259,4264,4266,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 16 4254 14
  · wct_piece 16 4259 15
  · wct_piece 16 4264 16
  · wct_piece 16 4266 17
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine235_ready : RoutineReady ⟨235, by decide⟩ routine235 := by
  wct_ready_start 235 7 11
  wct_cases [4275,4280,4285,4287,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 16 4275 20
  · wct_piece 16 4280 21
  · wct_piece 16 4285 22
  · wct_piece 16 4287 23
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine236_ready : RoutineReady ⟨236, by decide⟩ routine236 := by
  wct_ready_start 236 7 12
  wct_cases [4302,4307,4309,4313,2060,1141,821,826,754,759,761,764]
  · wct_piece 16 4302 28
  · wct_piece 16 4307 29
  · wct_piece 16 4309 30
  · wct_piece 16 4313 31
  · wct_piece 6 2060 4
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine237_ready : RoutineReady ⟨237, by decide⟩ routine237 := by
  wct_ready_start 237 7 13
  wct_cases [4314,4319,4321,4325,2072,1153,835,840,843,799,804,807]
  · wct_piece 16 4314 32
  · wct_piece 16 4319 33
  · wct_piece 16 4321 34
  · wct_piece 16 4325 35
  · wct_piece 6 2072 8
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine238_ready : RoutineReady ⟨238, by decide⟩ routine238 := by
  wct_ready_start 238 7 14
  wct_cases [4326,4331,4333,4337,2084,1165,852,857,859,862,867]
  · wct_piece 16 4326 36
  · wct_piece 16 4331 37
  · wct_piece 16 4333 38
  · wct_piece 16 4337 39
  · wct_piece 6 2084 12
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine239_ready : RoutineReady ⟨239, by decide⟩ routine239 := by
  wct_ready_start 239 7 15
  wct_cases [4338,4343,4345,4349,2096,1174,1179,1183,886,754,759,761,764]
  · wct_piece 16 4338 40
  · wct_piece 16 4343 41
  · wct_piece 16 4345 42
  · wct_piece 16 4349 43
  · wct_piece 6 2096 16
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine240_ready : RoutineReady ⟨240, by decide⟩ routine240 := by
  wct_ready_start 240 7 16
  wct_cases [4350,4355,4357,4361,2108,1192,1197,897,902,799,804,807]
  · wct_piece 16 4350 44
  · wct_piece 16 4355 45
  · wct_piece 16 4357 46
  · wct_piece 16 4361 47
  · wct_piece 6 2108 20
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine241_ready : RoutineReady ⟨241, by decide⟩ routine241 := by
  wct_ready_start 241 7 17
  wct_cases [4362,4367,4369,4373,2120,1206,1211,913,918,921,862,867]
  · wct_piece 16 4362 48
  · wct_piece 16 4367 49
  · wct_piece 16 4369 50
  · wct_piece 16 4373 51
  · wct_piece 6 2120 24
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine242_ready : RoutineReady ⟨242, by decide⟩ routine242 := by
  wct_ready_start 242 7 18
  wct_cases [4374,4379,4381,4385,2132,1220,1225,932,937,939,941,945]
  · wct_piece 16 4374 52
  · wct_piece 16 4379 53
  · wct_piece 16 4381 54
  · wct_piece 16 4385 55
  · wct_piece 6 2132 28
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine243_ready : RoutineReady ⟨243, by decide⟩ routine243 := by
  wct_ready_start 243 7 19
  wct_cases [4386,4391,4393,4397,2144,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 16 4386 56
  · wct_piece 16 4391 57
  · wct_piece 16 4393 58
  · wct_piece 16 4397 59
  · wct_piece 6 2144 32
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine244_ready : RoutineReady ⟨244, by decide⟩ routine244 := by
  wct_ready_start 244 7 20
  wct_cases [4398,4403,4405,4409,2156,1254,1259,1262,1097,1102,862,867]
  · wct_piece 16 4398 60
  · wct_piece 16 4403 61
  · wct_piece 16 4405 62
  · wct_piece 16 4409 63
  · wct_piece 6 2156 36
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine245_ready : RoutineReady ⟨245, by decide⟩ routine245 := by
  wct_ready_start 245 7 21
  wct_cases [4410,4415,4417,4421,2168,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 17 4410 0
  · wct_piece 17 4415 1
  · wct_piece 17 4417 2
  · wct_piece 17 4421 3
  · wct_piece 6 2168 40
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine246_ready : RoutineReady ⟨246, by decide⟩ routine246 := by
  wct_ready_start 246 7 22
  wct_cases [4422,4427,4429,4433,2180,1288,1293,1295,1297,1301,862,867]
  · wct_piece 17 4422 4
  · wct_piece 17 4427 5
  · wct_piece 17 4429 6
  · wct_piece 17 4433 7
  · wct_piece 6 2180 44
  · wct_piece 2 1288 29
  · wct_piece 2 1293 30
  · wct_piece 2 1295 31
  · wct_piece 2 1297 32
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine247_ready : RoutineReady ⟨247, by decide⟩ routine247 := by
  wct_ready_start 247 7 23
  wct_cases [4434,4439,4441,4445,2192,1310,1315,1317,1320,1325,1329,945]
  · wct_piece 17 4434 8
  · wct_piece 17 4439 9
  · wct_piece 17 4441 10
  · wct_piece 17 4445 11
  · wct_piece 6 2192 48
  · wct_piece 2 1310 36
  · wct_piece 2 1315 37
  · wct_piece 2 1317 38
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine248_ready : RoutineReady ⟨248, by decide⟩ routine248 := by
  wct_ready_start 248 7 24
  wct_cases [4446,4451,4453,4457,2201,2206,2210,1343,886,754,759,761,764]
  · wct_piece 17 4446 12
  · wct_piece 17 4451 13
  · wct_piece 17 4453 14
  · wct_piece 17 4457 15
  · wct_piece 6 2201 51
  · wct_piece 6 2206 52
  · wct_piece 6 2210 53
  · wct_piece 2 1343 46
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine249_ready : RoutineReady ⟨249, by decide⟩ routine249 := by
  wct_ready_start 249 7 25
  wct_cases [4458,4463,4465,4469,4474,4478,1357,897,902,799,804,807]
  · wct_piece 17 4458 16
  · wct_piece 17 4463 17
  · wct_piece 17 4465 18
  · wct_piece 17 4469 19
  · wct_piece 17 4474 20
  · wct_piece 17 4478 21
  · wct_piece 2 1357 51
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine250_ready : RoutineReady ⟨250, by decide⟩ routine250 := by
  wct_ready_start 250 7 26
  wct_cases [4479,4484,4486,4490,4495,4499,1371,913,918,921,862,867]
  · wct_piece 17 4479 22
  · wct_piece 17 4484 23
  · wct_piece 17 4486 24
  · wct_piece 17 4490 25
  · wct_piece 17 4495 26
  · wct_piece 17 4499 27
  · wct_piece 2 1371 56
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine251_ready : RoutineReady ⟨251, by decide⟩ routine251 := by
  wct_ready_start 251 7 27
  wct_cases [4500,4505,4507,4511,2255,2260,2264,1385,932,937,939,941,945]
  · wct_piece 17 4500 28
  · wct_piece 17 4505 29
  · wct_piece 17 4507 30
  · wct_piece 17 4511 31
  · wct_piece 7 2255 2
  · wct_piece 7 2260 3
  · wct_piece 7 2264 4
  · wct_piece 2 1385 61
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine252_ready : RoutineReady ⟨252, by decide⟩ routine252 := by
  wct_ready_start 252 7 28
  wct_cases [4512,4517,4519,4523,4528,1396,1401,1405,1081,799,804,807]
  · wct_piece 17 4512 32
  · wct_piece 17 4517 33
  · wct_piece 17 4519 34
  · wct_piece 17 4523 35
  · wct_piece 17 4528 36
  · wct_piece 3 1396 1
  · wct_piece 3 1401 2
  · wct_piece 3 1405 3
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine253_ready : RoutineReady ⟨253, by decide⟩ routine253 := by
  wct_ready_start 253 7 29
  wct_cases [4529,4534,4536,4540,2287,2292,1416,1421,1097,1102,862,867]
  · wct_piece 17 4529 37
  · wct_piece 17 4534 38
  · wct_piece 17 4536 39
  · wct_piece 17 4540 40
  · wct_piece 7 2287 11
  · wct_piece 7 2292 12
  · wct_piece 3 1416 7
  · wct_piece 3 1421 8
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine254_ready : RoutineReady ⟨254, by decide⟩ routine254 := by
  wct_ready_start 254 7 30
  wct_cases [4541,4546,4548,4552,2301,2306,1432,1437,1118,1123,1125,1129,945]
  · wct_piece 17 4541 41
  · wct_piece 17 4546 42
  · wct_piece 17 4548 43
  · wct_piece 17 4552 44
  · wct_piece 7 2301 15
  · wct_piece 7 2306 16
  · wct_piece 3 1432 12
  · wct_piece 3 1437 13
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine255_ready : RoutineReady ⟨255, by decide⟩ routine255 := by
  wct_ready_start 255 7 31
  wct_cases [4553,4558,4560,4564,2315,2320,1448,1453,1455,1459,1301,862,867]
  · wct_piece 17 4553 45
  · wct_piece 17 4558 46
  · wct_piece 17 4560 47
  · wct_piece 17 4564 48
  · wct_piece 7 2315 19
  · wct_piece 7 2320 20
  · wct_piece 3 1448 17
  · wct_piece 3 1453 18
  · wct_piece 3 1455 19
  · wct_piece 3 1459 20
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
end W9Machine.Chain
end
