import SigGolfCandidate.W9Machine.WctChainPieces

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def piece744 : ChainPiece :=
  ⟨744, [0x20040513, 0x23040613, 0x940e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 0⟩
def piece750 : ChainPiece :=
  ⟨750, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece752 : ChainPiece :=
  ⟨752, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece755 : ChainPiece :=
  ⟨755, [0x1c040513, 0x1f040613, 0x980e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 448 496 6 0⟩
def piece761 : ChainPiece :=
  ⟨761, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece763 : ChainPiece :=
  ⟨763, [0x00750a23, 0x3e040613, 0x00000073], .rung 2 (some 992)⟩
def piece766 : ChainPiece :=
  ⟨766, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece772 : ChainPiece :=
  ⟨772, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece778 : ChainPiece :=
  ⟨778, [0x20040513, 0x23040613, 0x948e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 1⟩
def piece784 : ChainPiece :=
  ⟨784, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece787 : ChainPiece :=
  ⟨787, [0xf81ff06f], .jump 755⟩
def piece788 : ChainPiece :=
  ⟨788, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece794 : ChainPiece :=
  ⟨794, [0x20040513, 0x23040613, 0x940e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 0⟩
def piece800 : ChainPiece :=
  ⟨800, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece802 : ChainPiece :=
  ⟨802, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece805 : ChainPiece :=
  ⟨805, [0x1c040513, 0x1f040613, 0x988e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 448 496 6 1⟩
def piece811 : ChainPiece :=
  ⟨811, [0x00750a23, 0x3e040613, 0x00000073], .rung 2 (some 992)⟩
def piece814 : ChainPiece :=
  ⟨814, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece820 : ChainPiece :=
  ⟨820, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece826 : ChainPiece :=
  ⟨826, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece829 : ChainPiece :=
  ⟨829, [0x20040513, 0x3d040613, 0x950e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 976 5 2⟩
def piece835 : ChainPiece :=
  ⟨835, [0xec1ff06f], .jump 755⟩
def piece836 : ChainPiece :=
  ⟨836, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece842 : ChainPiece :=
  ⟨842, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece845 : ChainPiece :=
  ⟨845, [0x20040513, 0x23040613, 0x948e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 1⟩
def piece851 : ChainPiece :=
  ⟨851, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece854 : ChainPiece :=
  ⟨854, [0xf3dff06f], .jump 805⟩
def piece855 : ChainPiece :=
  ⟨855, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece861 : ChainPiece :=
  ⟨861, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece864 : ChainPiece :=
  ⟨864, [0x20040513, 0x23040613, 0x940e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 0⟩
def piece870 : ChainPiece :=
  ⟨870, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece872 : ChainPiece :=
  ⟨872, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece875 : ChainPiece :=
  ⟨875, [0x1c040513, 0x3e040613, 0x990e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 448 992 6 2⟩
def piece881 : ChainPiece :=
  ⟨881, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece887 : ChainPiece :=
  ⟨887, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece893 : ChainPiece :=
  ⟨893, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece895 : ChainPiece :=
  ⟨895, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece897 : ChainPiece :=
  ⟨897, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece901 : ChainPiece :=
  ⟨901, [0xdb9ff06f], .jump 755⟩
def piece902 : ChainPiece :=
  ⟨902, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece908 : ChainPiece :=
  ⟨908, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece910 : ChainPiece :=
  ⟨910, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece913 : ChainPiece :=
  ⟨913, [0x20040513, 0x3d040613, 0x950e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 976 5 2⟩
def piece919 : ChainPiece :=
  ⟨919, [0xe39ff06f], .jump 805⟩
def piece920 : ChainPiece :=
  ⟨920, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece926 : ChainPiece :=
  ⟨926, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece928 : ChainPiece :=
  ⟨928, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece931 : ChainPiece :=
  ⟨931, [0x20040513, 0x23040613, 0x948e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 1⟩
def piece937 : ChainPiece :=
  ⟨937, [0x00750a23, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece940 : ChainPiece :=
  ⟨940, [0xefdff06f], .jump 875⟩
def piece941 : ChainPiece :=
  ⟨941, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece947 : ChainPiece :=
  ⟨947, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece949 : ChainPiece :=
  ⟨949, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece952 : ChainPiece :=
  ⟨952, [0x20040513, 0x23040613, 0x940e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 0⟩
def piece958 : ChainPiece :=
  ⟨958, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece960 : ChainPiece :=
  ⟨960, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece962 : ChainPiece :=
  ⟨962, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece966 : ChainPiece :=
  ⟨966, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece972 : ChainPiece :=
  ⟨972, [0x28040513, 0x2b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 2⟩
def piece978 : ChainPiece :=
  ⟨978, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece982 : ChainPiece :=
  ⟨982, [0xcd1ff06f], .jump 778⟩
def piece983 : ChainPiece :=
  ⟨983, [0x28040513, 0x2b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 2⟩
def piece989 : ChainPiece :=
  ⟨989, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece993 : ChainPiece :=
  ⟨993, [0xce5ff06f], .jump 794⟩
def chainBatch00 : List ChainPiece :=
  [piece744, piece750, piece752, piece755, piece761, piece763, piece766, piece772, piece778, piece784, piece787, piece788, piece794, piece800, piece802, piece805, piece811, piece814, piece820, piece826, piece829, piece835, piece836, piece842, piece845, piece851, piece854, piece855, piece861, piece864, piece870, piece872, piece875, piece881, piece887, piece893, piece895, piece897, piece901, piece902, piece908, piece910, piece913, piece919, piece920, piece926, piece928, piece931, piece937, piece940, piece941, piece947, piece949, piece952, piece958, piece960, piece962, piece966, piece972, piece978, piece982, piece983, piece989, piece993]
theorem chainBatch00_checked : (chainBatch00.all ChainPiece.checked) = true := by
  decide +kernel
def piece994 : ChainPiece :=
  ⟨994, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1000 : ChainPiece :=
  ⟨1000, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1006 : ChainPiece :=
  ⟨1006, [0xd3dff06f], .jump 829⟩
def piece1007 : ChainPiece :=
  ⟨1007, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1013 : ChainPiece :=
  ⟨1013, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1019 : ChainPiece :=
  ⟨1019, [0xd49ff06f], .jump 845⟩
def piece1020 : ChainPiece :=
  ⟨1020, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1026 : ChainPiece :=
  ⟨1026, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1032 : ChainPiece :=
  ⟨1032, [0xd61ff06f], .jump 864⟩
def piece1033 : ChainPiece :=
  ⟨1033, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1039 : ChainPiece :=
  ⟨1039, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1045 : ChainPiece :=
  ⟨1045, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1047 : ChainPiece :=
  ⟨1047, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1051 : ChainPiece :=
  ⟨1051, [0xda9ff06f], .jump 901⟩
def piece1052 : ChainPiece :=
  ⟨1052, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1058 : ChainPiece :=
  ⟨1058, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1064 : ChainPiece :=
  ⟨1064, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1067 : ChainPiece :=
  ⟨1067, [0xd99ff06f], .jump 913⟩
def piece1068 : ChainPiece :=
  ⟨1068, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1074 : ChainPiece :=
  ⟨1074, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1080 : ChainPiece :=
  ⟨1080, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1083 : ChainPiece :=
  ⟨1083, [0xda1ff06f], .jump 931⟩
def piece1084 : ChainPiece :=
  ⟨1084, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1090 : ChainPiece :=
  ⟨1090, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1096 : ChainPiece :=
  ⟨1096, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1099 : ChainPiece :=
  ⟨1099, [0xdb5ff06f], .jump 952⟩
def piece1100 : ChainPiece :=
  ⟨1100, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1106 : ChainPiece :=
  ⟨1106, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1112 : ChainPiece :=
  ⟨1112, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1114 : ChainPiece :=
  ⟨1114, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1116 : ChainPiece :=
  ⟨1116, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1120 : ChainPiece :=
  ⟨1120, [0xb15ff06f], .jump 805⟩
def piece1121 : ChainPiece :=
  ⟨1121, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1127 : ChainPiece :=
  ⟨1127, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1133 : ChainPiece :=
  ⟨1133, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1135 : ChainPiece :=
  ⟨1135, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1138 : ChainPiece :=
  ⟨1138, [0x20040513, 0x3d040613, 0x950e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 976 5 2⟩
def piece1144 : ChainPiece :=
  ⟨1144, [0xbcdff06f], .jump 875⟩
def piece1145 : ChainPiece :=
  ⟨1145, [0x28040513, 0x3b040613, 0x8d0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 944 3 2⟩
def piece1151 : ChainPiece :=
  ⟨1151, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1157 : ChainPiece :=
  ⟨1157, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1159 : ChainPiece :=
  ⟨1159, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1162 : ChainPiece :=
  ⟨1162, [0x20040513, 0x23040613, 0x948e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 1⟩
def piece1168 : ChainPiece :=
  ⟨1168, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1170 : ChainPiece :=
  ⟨1170, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece1174 : ChainPiece :=
  ⟨1174, [0xcc1ff06f], .jump 966⟩
def piece1175 : ChainPiece :=
  ⟨1175, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1181 : ChainPiece :=
  ⟨1181, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1183 : ChainPiece :=
  ⟨1183, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1187 : ChainPiece :=
  ⟨1187, [0xa69ff06f], .jump 829⟩
def piece1188 : ChainPiece :=
  ⟨1188, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1194 : ChainPiece :=
  ⟨1194, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1196 : ChainPiece :=
  ⟨1196, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1200 : ChainPiece :=
  ⟨1200, [0xa75ff06f], .jump 845⟩
def piece1201 : ChainPiece :=
  ⟨1201, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1207 : ChainPiece :=
  ⟨1207, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1209 : ChainPiece :=
  ⟨1209, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1213 : ChainPiece :=
  ⟨1213, [0xa8dff06f], .jump 864⟩
def piece1214 : ChainPiece :=
  ⟨1214, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1220 : ChainPiece :=
  ⟨1220, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1223 : ChainPiece :=
  ⟨1223, [0x24040513, 0x27040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 2⟩
def piece1229 : ChainPiece :=
  ⟨1229, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1233 : ChainPiece :=
  ⟨1233, [0xad1ff06f], .jump 901⟩
def piece1234 : ChainPiece :=
  ⟨1234, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def chainBatch01 : List ChainPiece :=
  [piece994, piece1000, piece1006, piece1007, piece1013, piece1019, piece1020, piece1026, piece1032, piece1033, piece1039, piece1045, piece1047, piece1051, piece1052, piece1058, piece1064, piece1067, piece1068, piece1074, piece1080, piece1083, piece1084, piece1090, piece1096, piece1099, piece1100, piece1106, piece1112, piece1114, piece1116, piece1120, piece1121, piece1127, piece1133, piece1135, piece1138, piece1144, piece1145, piece1151, piece1157, piece1159, piece1162, piece1168, piece1170, piece1174, piece1175, piece1181, piece1183, piece1187, piece1188, piece1194, piece1196, piece1200, piece1201, piece1207, piece1209, piece1213, piece1214, piece1220, piece1223, piece1229, piece1233, piece1234]
theorem chainBatch01_checked : (chainBatch01.all ChainPiece.checked) = true := by
  decide +kernel
def piece1240 : ChainPiece :=
  ⟨1240, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1243 : ChainPiece :=
  ⟨1243, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1249 : ChainPiece :=
  ⟨1249, [0xac1ff06f], .jump 913⟩
def piece1250 : ChainPiece :=
  ⟨1250, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1256 : ChainPiece :=
  ⟨1256, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1259 : ChainPiece :=
  ⟨1259, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1265 : ChainPiece :=
  ⟨1265, [0xac9ff06f], .jump 931⟩
def piece1266 : ChainPiece :=
  ⟨1266, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1272 : ChainPiece :=
  ⟨1272, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1275 : ChainPiece :=
  ⟨1275, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1281 : ChainPiece :=
  ⟨1281, [0xaddff06f], .jump 952⟩
def piece1282 : ChainPiece :=
  ⟨1282, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1288 : ChainPiece :=
  ⟨1288, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1291 : ChainPiece :=
  ⟨1291, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1297 : ChainPiece :=
  ⟨1297, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1299 : ChainPiece :=
  ⟨1299, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1303 : ChainPiece :=
  ⟨1303, [0xd25ff06f], .jump 1120⟩
def piece1304 : ChainPiece :=
  ⟨1304, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1310 : ChainPiece :=
  ⟨1310, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1313 : ChainPiece :=
  ⟨1313, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1319 : ChainPiece :=
  ⟨1319, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1322 : ChainPiece :=
  ⟨1322, [0xd21ff06f], .jump 1138⟩
def piece1323 : ChainPiece :=
  ⟨1323, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1329 : ChainPiece :=
  ⟨1329, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1332 : ChainPiece :=
  ⟨1332, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1338 : ChainPiece :=
  ⟨1338, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1341 : ChainPiece :=
  ⟨1341, [0xd35ff06f], .jump 1162⟩
def piece1342 : ChainPiece :=
  ⟨1342, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1348 : ChainPiece :=
  ⟨1348, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1351 : ChainPiece :=
  ⟨1351, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1357 : ChainPiece :=
  ⟨1357, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1359 : ChainPiece :=
  ⟨1359, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1361 : ChainPiece :=
  ⟨1361, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1365 : ChainPiece :=
  ⟨1365, [0x859ff06f], .jump 875⟩
def piece1366 : ChainPiece :=
  ⟨1366, [0x28040513, 0x2b040613, 0x8c8e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 1⟩
def piece1372 : ChainPiece :=
  ⟨1372, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1375 : ChainPiece :=
  ⟨1375, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1381 : ChainPiece :=
  ⟨1381, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1383 : ChainPiece :=
  ⟨1383, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1386 : ChainPiece :=
  ⟨1386, [0x20040513, 0x23040613, 0x950e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 512 560 5 2⟩
def piece1392 : ChainPiece :=
  ⟨1392, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece1396 : ChainPiece :=
  ⟨1396, [0x949ff06f], .jump 966⟩
def piece1397 : ChainPiece :=
  ⟨1397, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1403 : ChainPiece :=
  ⟨1403, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1405 : ChainPiece :=
  ⟨1405, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1407 : ChainPiece :=
  ⟨1407, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1411 : ChainPiece :=
  ⟨1411, [0x809ff06f], .jump 901⟩
def piece1412 : ChainPiece :=
  ⟨1412, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1418 : ChainPiece :=
  ⟨1418, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1420 : ChainPiece :=
  ⟨1420, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1422 : ChainPiece :=
  ⟨1422, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1426 : ChainPiece :=
  ⟨1426, [0xffcff06f], .jump 913⟩
def piece1427 : ChainPiece :=
  ⟨1427, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1433 : ChainPiece :=
  ⟨1433, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1435 : ChainPiece :=
  ⟨1435, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1437 : ChainPiece :=
  ⟨1437, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1441 : ChainPiece :=
  ⟨1441, [0x809ff06f], .jump 931⟩
def piece1442 : ChainPiece :=
  ⟨1442, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1448 : ChainPiece :=
  ⟨1448, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1450 : ChainPiece :=
  ⟨1450, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1452 : ChainPiece :=
  ⟨1452, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1456 : ChainPiece :=
  ⟨1456, [0x821ff06f], .jump 952⟩
def piece1457 : ChainPiece :=
  ⟨1457, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1463 : ChainPiece :=
  ⟨1463, [0x00650a23, 0x00000073], .rung 1 none⟩
def chainBatch02 : List ChainPiece :=
  [piece1240, piece1243, piece1249, piece1250, piece1256, piece1259, piece1265, piece1266, piece1272, piece1275, piece1281, piece1282, piece1288, piece1291, piece1297, piece1299, piece1303, piece1304, piece1310, piece1313, piece1319, piece1322, piece1323, piece1329, piece1332, piece1338, piece1341, piece1342, piece1348, piece1351, piece1357, piece1359, piece1361, piece1365, piece1366, piece1372, piece1375, piece1381, piece1383, piece1386, piece1392, piece1396, piece1397, piece1403, piece1405, piece1407, piece1411, piece1412, piece1418, piece1420, piece1422, piece1426, piece1427, piece1433, piece1435, piece1437, piece1441, piece1442, piece1448, piece1450, piece1452, piece1456, piece1457, piece1463]
theorem chainBatch02_checked : (chainBatch02.all ChainPiece.checked) = true := by
  decide +kernel
def piece1465 : ChainPiece :=
  ⟨1465, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1468 : ChainPiece :=
  ⟨1468, [0x24040513, 0x27040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 2⟩
def piece1474 : ChainPiece :=
  ⟨1474, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1478 : ChainPiece :=
  ⟨1478, [0xa69ff06f], .jump 1120⟩
def piece1479 : ChainPiece :=
  ⟨1479, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1485 : ChainPiece :=
  ⟨1485, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1487 : ChainPiece :=
  ⟨1487, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1490 : ChainPiece :=
  ⟨1490, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1496 : ChainPiece :=
  ⟨1496, [0xa69ff06f], .jump 1138⟩
def piece1497 : ChainPiece :=
  ⟨1497, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1503 : ChainPiece :=
  ⟨1503, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1505 : ChainPiece :=
  ⟨1505, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1508 : ChainPiece :=
  ⟨1508, [0x24040513, 0x3c040613, 0x910e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 960 4 2⟩
def piece1514 : ChainPiece :=
  ⟨1514, [0xa81ff06f], .jump 1162⟩
def piece1515 : ChainPiece :=
  ⟨1515, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1521 : ChainPiece :=
  ⟨1521, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1523 : ChainPiece :=
  ⟨1523, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1526 : ChainPiece :=
  ⟨1526, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1532 : ChainPiece :=
  ⟨1532, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1534 : ChainPiece :=
  ⟨1534, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1538 : ChainPiece :=
  ⟨1538, [0xd4dff06f], .jump 1365⟩
def piece1539 : ChainPiece :=
  ⟨1539, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1545 : ChainPiece :=
  ⟨1545, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1547 : ChainPiece :=
  ⟨1547, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1550 : ChainPiece :=
  ⟨1550, [0x24040513, 0x27040613, 0x908e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 1⟩
def piece1556 : ChainPiece :=
  ⟨1556, [0x00750a23, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1559 : ChainPiece :=
  ⟨1559, [0xd4dff06f], .jump 1386⟩
def piece1560 : ChainPiece :=
  ⟨1560, [0x28040513, 0x2b040613, 0x8c0e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 640 688 3 0⟩
def piece1566 : ChainPiece :=
  ⟨1566, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1568 : ChainPiece :=
  ⟨1568, [0x00750a23, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1571 : ChainPiece :=
  ⟨1571, [0x24040513, 0x27040613, 0x900e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 576 624 4 0⟩
def piece1577 : ChainPiece :=
  ⟨1577, [0x00650a23, 0x00000073], .rung 1 none⟩
def piece1579 : ChainPiece :=
  ⟨1579, [0x00750a23, 0x00000073], .rung 2 none⟩
def piece1581 : ChainPiece :=
  ⟨1581, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1585 : ChainPiece :=
  ⟨1585, [0xe54ff06f], .jump 966⟩
def piece1586 : ChainPiece :=
  ⟨1586, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1592 : ChainPiece :=
  ⟨1592, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1596 : ChainPiece :=
  ⟨1596, [0xe68ff06f], .jump 982⟩
def piece1597 : ChainPiece :=
  ⟨1597, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1603 : ChainPiece :=
  ⟨1603, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1607 : ChainPiece :=
  ⟨1607, [0xe68ff06f], .jump 993⟩
def piece1608 : ChainPiece :=
  ⟨1608, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1614 : ChainPiece :=
  ⟨1614, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1618 : ChainPiece :=
  ⟨1618, [0xe58ff06f], .jump 1000⟩
def piece1619 : ChainPiece :=
  ⟨1619, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1625 : ChainPiece :=
  ⟨1625, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1629 : ChainPiece :=
  ⟨1629, [0xe60ff06f], .jump 1013⟩
def piece1630 : ChainPiece :=
  ⟨1630, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1636 : ChainPiece :=
  ⟨1636, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1640 : ChainPiece :=
  ⟨1640, [0xe68ff06f], .jump 1026⟩
def piece1641 : ChainPiece :=
  ⟨1641, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1647 : ChainPiece :=
  ⟨1647, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1651 : ChainPiece :=
  ⟨1651, [0xe70ff06f], .jump 1039⟩
def piece1652 : ChainPiece :=
  ⟨1652, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1658 : ChainPiece :=
  ⟨1658, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1662 : ChainPiece :=
  ⟨1662, [0xe90ff06f], .jump 1058⟩
def piece1663 : ChainPiece :=
  ⟨1663, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1669 : ChainPiece :=
  ⟨1669, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1673 : ChainPiece :=
  ⟨1673, [0xea4ff06f], .jump 1074⟩
def piece1674 : ChainPiece :=
  ⟨1674, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1680 : ChainPiece :=
  ⟨1680, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1684 : ChainPiece :=
  ⟨1684, [0xeb8ff06f], .jump 1090⟩
def piece1685 : ChainPiece :=
  ⟨1685, [0x2c040513, 0x2f040613, 0x890e3c83, 0x01953823, 0x00453c23, 0x00000073], .head 704 752 2 2⟩
def piece1691 : ChainPiece :=
  ⟨1691, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def chainBatch03 : List ChainPiece :=
  [piece1465, piece1468, piece1474, piece1478, piece1479, piece1485, piece1487, piece1490, piece1496, piece1497, piece1503, piece1505, piece1508, piece1514, piece1515, piece1521, piece1523, piece1526, piece1532, piece1534, piece1538, piece1539, piece1545, piece1547, piece1550, piece1556, piece1559, piece1560, piece1566, piece1568, piece1571, piece1577, piece1579, piece1581, piece1585, piece1586, piece1592, piece1596, piece1597, piece1603, piece1607, piece1608, piece1614, piece1618, piece1619, piece1625, piece1629, piece1630, piece1636, piece1640, piece1641, piece1647, piece1651, piece1652, piece1658, piece1662, piece1663, piece1669, piece1673, piece1674, piece1680, piece1684, piece1685, piece1691]
theorem chainBatch03_checked : (chainBatch03.all ChainPiece.checked) = true := by
  decide +kernel
end W9Machine
