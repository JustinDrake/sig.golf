import SigGolfCandidate.W9Machine.WctRoutineModel
import SigGolfCandidate.W9Machine.WctChainCheck12

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine0 : ChainRoutine :=
  ⟨0, [0, 0, 0, 0, 0, 3, 3], [piece744, piece750, piece752, piece755, piece761, piece763, piece766]⟩
def routine1 : ChainRoutine :=
  ⟨1, [0, 0, 0, 0, 1, 2, 3], [piece772, piece778, piece784, piece787, piece755, piece761, piece763, piece766]⟩
def routine2 : ChainRoutine :=
  ⟨2, [0, 0, 0, 0, 1, 3, 2], [piece788, piece794, piece800, piece802, piece805, piece811, piece814]⟩
def routine3 : ChainRoutine :=
  ⟨3, [0, 0, 0, 0, 2, 1, 3], [piece820, piece826, piece829, piece835, piece755, piece761, piece763, piece766]⟩
def routine4 : ChainRoutine :=
  ⟨4, [0, 0, 0, 0, 2, 2, 2], [piece836, piece842, piece845, piece851, piece854, piece805, piece811, piece814]⟩
def routine5 : ChainRoutine :=
  ⟨5, [0, 0, 0, 0, 2, 3, 1], [piece855, piece861, piece864, piece870, piece872, piece875, piece881]⟩
def routine6 : ChainRoutine :=
  ⟨6, [0, 0, 0, 0, 3, 0, 3], [piece887, piece893, piece895, piece897, piece901, piece755, piece761, piece763, piece766]⟩
def routine7 : ChainRoutine :=
  ⟨7, [0, 0, 0, 0, 3, 1, 2], [piece902, piece908, piece910, piece913, piece919, piece805, piece811, piece814]⟩
def routine8 : ChainRoutine :=
  ⟨8, [0, 0, 0, 0, 3, 2, 1], [piece920, piece926, piece928, piece931, piece937, piece940, piece875, piece881]⟩
def routine9 : ChainRoutine :=
  ⟨9, [0, 0, 0, 0, 3, 3, 0], [piece941, piece947, piece949, piece952, piece958, piece960, piece962, piece966]⟩
def routine10 : ChainRoutine :=
  ⟨10, [0, 0, 0, 1, 0, 2, 3], [piece972, piece978, piece982, piece778, piece784, piece787, piece755, piece761, piece763, piece766]⟩
def routine11 : ChainRoutine :=
  ⟨11, [0, 0, 0, 1, 0, 3, 2], [piece983, piece989, piece993, piece794, piece800, piece802, piece805, piece811, piece814]⟩
def routine12 : ChainRoutine :=
  ⟨12, [0, 0, 0, 1, 1, 1, 3], [piece994, piece1000, piece1006, piece829, piece835, piece755, piece761, piece763, piece766]⟩
def routine13 : ChainRoutine :=
  ⟨13, [0, 0, 0, 1, 1, 2, 2], [piece1007, piece1013, piece1019, piece845, piece851, piece854, piece805, piece811, piece814]⟩
def routine14 : ChainRoutine :=
  ⟨14, [0, 0, 0, 1, 1, 3, 1], [piece1020, piece1026, piece1032, piece864, piece870, piece872, piece875, piece881]⟩
def routine15 : ChainRoutine :=
  ⟨15, [0, 0, 0, 1, 2, 0, 3], [piece1033, piece1039, piece1045, piece1047, piece1051, piece901, piece755, piece761, piece763, piece766]⟩
def routine16 : ChainRoutine :=
  ⟨16, [0, 0, 0, 1, 2, 1, 2], [piece1052, piece1058, piece1064, piece1067, piece913, piece919, piece805, piece811, piece814]⟩
def routine17 : ChainRoutine :=
  ⟨17, [0, 0, 0, 1, 2, 2, 1], [piece1068, piece1074, piece1080, piece1083, piece931, piece937, piece940, piece875, piece881]⟩
def routine18 : ChainRoutine :=
  ⟨18, [0, 0, 0, 1, 2, 3, 0], [piece1084, piece1090, piece1096, piece1099, piece952, piece958, piece960, piece962, piece966]⟩
def routine19 : ChainRoutine :=
  ⟨19, [0, 0, 0, 1, 3, 0, 2], [piece1100, piece1106, piece1112, piece1114, piece1116, piece1120, piece805, piece811, piece814]⟩
def routine20 : ChainRoutine :=
  ⟨20, [0, 0, 0, 1, 3, 1, 1], [piece1121, piece1127, piece1133, piece1135, piece1138, piece1144, piece875, piece881]⟩
def routine21 : ChainRoutine :=
  ⟨21, [0, 0, 0, 1, 3, 2, 0], [piece1145, piece1151, piece1157, piece1159, piece1162, piece1168, piece1170, piece1174, piece966]⟩
def routine22 : ChainRoutine :=
  ⟨22, [0, 0, 0, 2, 0, 1, 3], [piece1175, piece1181, piece1183, piece1187, piece829, piece835, piece755, piece761, piece763, piece766]⟩
def routine23 : ChainRoutine :=
  ⟨23, [0, 0, 0, 2, 0, 2, 2], [piece1188, piece1194, piece1196, piece1200, piece845, piece851, piece854, piece805, piece811, piece814]⟩
def routine24 : ChainRoutine :=
  ⟨24, [0, 0, 0, 2, 0, 3, 1], [piece1201, piece1207, piece1209, piece1213, piece864, piece870, piece872, piece875, piece881]⟩
def routine25 : ChainRoutine :=
  ⟨25, [0, 0, 0, 2, 1, 0, 3], [piece1214, piece1220, piece1223, piece1229, piece1233, piece901, piece755, piece761, piece763, piece766]⟩
def routine26 : ChainRoutine :=
  ⟨26, [0, 0, 0, 2, 1, 1, 2], [piece1234, piece1240, piece1243, piece1249, piece913, piece919, piece805, piece811, piece814]⟩
def routine27 : ChainRoutine :=
  ⟨27, [0, 0, 0, 2, 1, 2, 1], [piece1250, piece1256, piece1259, piece1265, piece931, piece937, piece940, piece875, piece881]⟩
def routine28 : ChainRoutine :=
  ⟨28, [0, 0, 0, 2, 1, 3, 0], [piece1266, piece1272, piece1275, piece1281, piece952, piece958, piece960, piece962, piece966]⟩
def routine29 : ChainRoutine :=
  ⟨29, [0, 0, 0, 2, 2, 0, 2], [piece1282, piece1288, piece1291, piece1297, piece1299, piece1303, piece1120, piece805, piece811, piece814]⟩
def routine30 : ChainRoutine :=
  ⟨30, [0, 0, 0, 2, 2, 1, 1], [piece1304, piece1310, piece1313, piece1319, piece1322, piece1138, piece1144, piece875, piece881]⟩
def routine31 : ChainRoutine :=
  ⟨31, [0, 0, 0, 2, 2, 2, 0], [piece1323, piece1329, piece1332, piece1338, piece1341, piece1162, piece1168, piece1170, piece1174, piece966]⟩
def routineBatch00 : List ChainRoutine := [routine0, routine1, routine2, routine3, routine4, routine5, routine6, routine7, routine8, routine9, routine10, routine11, routine12, routine13, routine14, routine15, routine16, routine17, routine18, routine19, routine20, routine21, routine22, routine23, routine24, routine25, routine26, routine27, routine28, routine29, routine30, routine31]
theorem routineBatch00_checked :
    (routineBatch00.all ChainRoutine.checked) = true := by
  decide +kernel
end W9Machine
