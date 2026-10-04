import SigGolfCandidate.W9Machine.WctChainPieces

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def piece744 : ChainPiece :=
  ⟨744, [0x20040513, 0x23040613, 0x094f8c93, 0x01953823, 0x00000073], .head 512 560 5 0⟩
def piece749 : ChainPiece :=
  ⟨749, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece751 : ChainPiece :=
  ⟨751, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece754 : ChainPiece :=
  ⟨754, [0x1c040513, 0x1f040613, 0x098f8c93, 0x01953823, 0x00000073], .head 448 496 6 0⟩
def piece759 : ChainPiece :=
  ⟨759, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece761 : ChainPiece :=
  ⟨761, [0x00d508a3, 0x3e040613, 0x00000073], .rung 2 (some 992)⟩
def piece764 : ChainPiece :=
  ⟨764, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece770 : ChainPiece :=
  ⟨770, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece775 : ChainPiece :=
  ⟨775, [0x20040513, 0x23040613, 0x194f8c93, 0x01953823, 0x00000073], .head 512 560 5 1⟩
def piece780 : ChainPiece :=
  ⟨780, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece783 : ChainPiece :=
  ⟨783, [0xf8dff06f], .jump 754⟩
def piece784 : ChainPiece :=
  ⟨784, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece789 : ChainPiece :=
  ⟨789, [0x20040513, 0x23040613, 0x094f8c93, 0x01953823, 0x00000073], .head 512 560 5 0⟩
def piece794 : ChainPiece :=
  ⟨794, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece796 : ChainPiece :=
  ⟨796, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece799 : ChainPiece :=
  ⟨799, [0x1c040513, 0x1f040613, 0x198f8c93, 0x01953823, 0x00000073], .head 448 496 6 1⟩
def piece804 : ChainPiece :=
  ⟨804, [0x00d508a3, 0x3e040613, 0x00000073], .rung 2 (some 992)⟩
def piece807 : ChainPiece :=
  ⟨807, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece813 : ChainPiece :=
  ⟨813, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece818 : ChainPiece :=
  ⟨818, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece821 : ChainPiece :=
  ⟨821, [0x20040513, 0x3d040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 976 5 2⟩
def piece826 : ChainPiece :=
  ⟨826, [0xee1ff06f], .jump 754⟩
def piece827 : ChainPiece :=
  ⟨827, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece832 : ChainPiece :=
  ⟨832, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece835 : ChainPiece :=
  ⟨835, [0x20040513, 0x23040613, 0x194f8c93, 0x01953823, 0x00000073], .head 512 560 5 1⟩
def piece840 : ChainPiece :=
  ⟨840, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece843 : ChainPiece :=
  ⟨843, [0xf51ff06f], .jump 799⟩
def piece844 : ChainPiece :=
  ⟨844, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece849 : ChainPiece :=
  ⟨849, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece852 : ChainPiece :=
  ⟨852, [0x20040513, 0x23040613, 0x094f8c93, 0x01953823, 0x00000073], .head 512 560 5 0⟩
def piece857 : ChainPiece :=
  ⟨857, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece859 : ChainPiece :=
  ⟨859, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece862 : ChainPiece :=
  ⟨862, [0x1c040513, 0x3e040613, 0x298f8c93, 0x01953823, 0x00000073], .head 448 992 6 2⟩
def piece867 : ChainPiece :=
  ⟨867, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece873 : ChainPiece :=
  ⟨873, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece878 : ChainPiece :=
  ⟨878, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece880 : ChainPiece :=
  ⟨880, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece882 : ChainPiece :=
  ⟨882, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece886 : ChainPiece :=
  ⟨886, [0xdf1ff06f], .jump 754⟩
def piece887 : ChainPiece :=
  ⟨887, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece892 : ChainPiece :=
  ⟨892, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece894 : ChainPiece :=
  ⟨894, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece897 : ChainPiece :=
  ⟨897, [0x20040513, 0x3d040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 976 5 2⟩
def piece902 : ChainPiece :=
  ⟨902, [0xe65ff06f], .jump 799⟩
def piece903 : ChainPiece :=
  ⟨903, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece908 : ChainPiece :=
  ⟨908, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece910 : ChainPiece :=
  ⟨910, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece913 : ChainPiece :=
  ⟨913, [0x20040513, 0x23040613, 0x194f8c93, 0x01953823, 0x00000073], .head 512 560 5 1⟩
def piece918 : ChainPiece :=
  ⟨918, [0x00d508a3, 0x3d040613, 0x00000073], .rung 2 (some 976)⟩
def piece921 : ChainPiece :=
  ⟨921, [0xf15ff06f], .jump 862⟩
def piece922 : ChainPiece :=
  ⟨922, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece927 : ChainPiece :=
  ⟨927, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece929 : ChainPiece :=
  ⟨929, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece932 : ChainPiece :=
  ⟨932, [0x20040513, 0x23040613, 0x094f8c93, 0x01953823, 0x00000073], .head 512 560 5 0⟩
def piece937 : ChainPiece :=
  ⟨937, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece939 : ChainPiece :=
  ⟨939, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece941 : ChainPiece :=
  ⟨941, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece945 : ChainPiece :=
  ⟨945, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece951 : ChainPiece :=
  ⟨951, [0x28040513, 0x2b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 688 3 2⟩
def piece956 : ChainPiece :=
  ⟨956, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece960 : ChainPiece :=
  ⟨960, [0xd1dff06f], .jump 775⟩
def piece961 : ChainPiece :=
  ⟨961, [0x28040513, 0x2b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 688 3 2⟩
def piece966 : ChainPiece :=
  ⟨966, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece970 : ChainPiece :=
  ⟨970, [0xd2dff06f], .jump 789⟩
def chainBatch00 : List ChainPiece :=
  [piece744, piece749, piece751, piece754, piece759, piece761, piece764, piece770, piece775, piece780, piece783, piece784, piece789, piece794, piece796, piece799, piece804, piece807, piece813, piece818, piece821, piece826, piece827, piece832, piece835, piece840, piece843, piece844, piece849, piece852, piece857, piece859, piece862, piece867, piece873, piece878, piece880, piece882, piece886, piece887, piece892, piece894, piece897, piece902, piece903, piece908, piece910, piece913, piece918, piece921, piece922, piece927, piece929, piece932, piece937, piece939, piece941, piece945, piece951, piece956, piece960, piece961, piece966, piece970]
theorem chainBatch00_checked : (chainBatch00.all ChainPiece.checked) = true := by
  decide +kernel
def piece971 : ChainPiece :=
  ⟨971, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece976 : ChainPiece :=
  ⟨976, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece981 : ChainPiece :=
  ⟨981, [0xd81ff06f], .jump 821⟩
def piece982 : ChainPiece :=
  ⟨982, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece987 : ChainPiece :=
  ⟨987, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece992 : ChainPiece :=
  ⟨992, [0xd8dff06f], .jump 835⟩
def piece993 : ChainPiece :=
  ⟨993, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece998 : ChainPiece :=
  ⟨998, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1003 : ChainPiece :=
  ⟨1003, [0xda5ff06f], .jump 852⟩
def piece1004 : ChainPiece :=
  ⟨1004, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1009 : ChainPiece :=
  ⟨1009, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1014 : ChainPiece :=
  ⟨1014, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1016 : ChainPiece :=
  ⟨1016, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1020 : ChainPiece :=
  ⟨1020, [0xde9ff06f], .jump 886⟩
def piece1021 : ChainPiece :=
  ⟨1021, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1026 : ChainPiece :=
  ⟨1026, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1031 : ChainPiece :=
  ⟨1031, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1034 : ChainPiece :=
  ⟨1034, [0xdddff06f], .jump 897⟩
def piece1035 : ChainPiece :=
  ⟨1035, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1040 : ChainPiece :=
  ⟨1040, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1045 : ChainPiece :=
  ⟨1045, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1048 : ChainPiece :=
  ⟨1048, [0xde5ff06f], .jump 913⟩
def piece1049 : ChainPiece :=
  ⟨1049, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1054 : ChainPiece :=
  ⟨1054, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1059 : ChainPiece :=
  ⟨1059, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1062 : ChainPiece :=
  ⟨1062, [0xdf9ff06f], .jump 932⟩
def piece1063 : ChainPiece :=
  ⟨1063, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1068 : ChainPiece :=
  ⟨1068, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1073 : ChainPiece :=
  ⟨1073, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1075 : ChainPiece :=
  ⟨1075, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1077 : ChainPiece :=
  ⟨1077, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1081 : ChainPiece :=
  ⟨1081, [0xb99ff06f], .jump 799⟩
def piece1082 : ChainPiece :=
  ⟨1082, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1087 : ChainPiece :=
  ⟨1087, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1092 : ChainPiece :=
  ⟨1092, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1094 : ChainPiece :=
  ⟨1094, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1097 : ChainPiece :=
  ⟨1097, [0x20040513, 0x3d040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 976 5 2⟩
def piece1102 : ChainPiece :=
  ⟨1102, [0xc41ff06f], .jump 862⟩
def piece1103 : ChainPiece :=
  ⟨1103, [0x28040513, 0x3b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 944 3 2⟩
def piece1108 : ChainPiece :=
  ⟨1108, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1113 : ChainPiece :=
  ⟨1113, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1115 : ChainPiece :=
  ⟨1115, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1118 : ChainPiece :=
  ⟨1118, [0x20040513, 0x23040613, 0x194f8c93, 0x01953823, 0x00000073], .head 512 560 5 1⟩
def piece1123 : ChainPiece :=
  ⟨1123, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1125 : ChainPiece :=
  ⟨1125, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece1129 : ChainPiece :=
  ⟨1129, [0xd21ff06f], .jump 945⟩
def piece1130 : ChainPiece :=
  ⟨1130, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1135 : ChainPiece :=
  ⟨1135, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1137 : ChainPiece :=
  ⟨1137, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1141 : ChainPiece :=
  ⟨1141, [0xb01ff06f], .jump 821⟩
def piece1142 : ChainPiece :=
  ⟨1142, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1147 : ChainPiece :=
  ⟨1147, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1149 : ChainPiece :=
  ⟨1149, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1153 : ChainPiece :=
  ⟨1153, [0xb09ff06f], .jump 835⟩
def piece1154 : ChainPiece :=
  ⟨1154, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1159 : ChainPiece :=
  ⟨1159, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1161 : ChainPiece :=
  ⟨1161, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1165 : ChainPiece :=
  ⟨1165, [0xb1dff06f], .jump 852⟩
def piece1166 : ChainPiece :=
  ⟨1166, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1171 : ChainPiece :=
  ⟨1171, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1174 : ChainPiece :=
  ⟨1174, [0x24040513, 0x27040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 624 4 2⟩
def piece1179 : ChainPiece :=
  ⟨1179, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1183 : ChainPiece :=
  ⟨1183, [0xb5dff06f], .jump 886⟩
def piece1184 : ChainPiece :=
  ⟨1184, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def chainBatch01 : List ChainPiece :=
  [piece971, piece976, piece981, piece982, piece987, piece992, piece993, piece998, piece1003, piece1004, piece1009, piece1014, piece1016, piece1020, piece1021, piece1026, piece1031, piece1034, piece1035, piece1040, piece1045, piece1048, piece1049, piece1054, piece1059, piece1062, piece1063, piece1068, piece1073, piece1075, piece1077, piece1081, piece1082, piece1087, piece1092, piece1094, piece1097, piece1102, piece1103, piece1108, piece1113, piece1115, piece1118, piece1123, piece1125, piece1129, piece1130, piece1135, piece1137, piece1141, piece1142, piece1147, piece1149, piece1153, piece1154, piece1159, piece1161, piece1165, piece1166, piece1171, piece1174, piece1179, piece1183, piece1184]
theorem chainBatch01_checked : (chainBatch01.all ChainPiece.checked) = true := by
  decide +kernel
def piece1189 : ChainPiece :=
  ⟨1189, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1192 : ChainPiece :=
  ⟨1192, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1197 : ChainPiece :=
  ⟨1197, [0xb51ff06f], .jump 897⟩
def piece1198 : ChainPiece :=
  ⟨1198, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1203 : ChainPiece :=
  ⟨1203, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1206 : ChainPiece :=
  ⟨1206, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1211 : ChainPiece :=
  ⟨1211, [0xb59ff06f], .jump 913⟩
def piece1212 : ChainPiece :=
  ⟨1212, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1217 : ChainPiece :=
  ⟨1217, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1220 : ChainPiece :=
  ⟨1220, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1225 : ChainPiece :=
  ⟨1225, [0xb6dff06f], .jump 932⟩
def piece1226 : ChainPiece :=
  ⟨1226, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1231 : ChainPiece :=
  ⟨1231, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1234 : ChainPiece :=
  ⟨1234, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1239 : ChainPiece :=
  ⟨1239, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1241 : ChainPiece :=
  ⟨1241, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1245 : ChainPiece :=
  ⟨1245, [0xd71ff06f], .jump 1081⟩
def piece1246 : ChainPiece :=
  ⟨1246, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1251 : ChainPiece :=
  ⟨1251, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1254 : ChainPiece :=
  ⟨1254, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1259 : ChainPiece :=
  ⟨1259, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1262 : ChainPiece :=
  ⟨1262, [0xd6dff06f], .jump 1097⟩
def piece1263 : ChainPiece :=
  ⟨1263, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1268 : ChainPiece :=
  ⟨1268, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1271 : ChainPiece :=
  ⟨1271, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1276 : ChainPiece :=
  ⟨1276, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1279 : ChainPiece :=
  ⟨1279, [0xd7dff06f], .jump 1118⟩
def piece1280 : ChainPiece :=
  ⟨1280, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1285 : ChainPiece :=
  ⟨1285, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1288 : ChainPiece :=
  ⟨1288, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1293 : ChainPiece :=
  ⟨1293, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1295 : ChainPiece :=
  ⟨1295, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1297 : ChainPiece :=
  ⟨1297, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1301 : ChainPiece :=
  ⟨1301, [0x925ff06f], .jump 862⟩
def piece1302 : ChainPiece :=
  ⟨1302, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece1307 : ChainPiece :=
  ⟨1307, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1310 : ChainPiece :=
  ⟨1310, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1315 : ChainPiece :=
  ⟨1315, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1317 : ChainPiece :=
  ⟨1317, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1320 : ChainPiece :=
  ⟨1320, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece1325 : ChainPiece :=
  ⟨1325, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece1329 : ChainPiece :=
  ⟨1329, [0xa01ff06f], .jump 945⟩
def piece1330 : ChainPiece :=
  ⟨1330, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1335 : ChainPiece :=
  ⟨1335, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1337 : ChainPiece :=
  ⟨1337, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1339 : ChainPiece :=
  ⟨1339, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1343 : ChainPiece :=
  ⟨1343, [0x8ddff06f], .jump 886⟩
def piece1344 : ChainPiece :=
  ⟨1344, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1349 : ChainPiece :=
  ⟨1349, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1351 : ChainPiece :=
  ⟨1351, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1353 : ChainPiece :=
  ⟨1353, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1357 : ChainPiece :=
  ⟨1357, [0x8d1ff06f], .jump 897⟩
def piece1358 : ChainPiece :=
  ⟨1358, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1363 : ChainPiece :=
  ⟨1363, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1365 : ChainPiece :=
  ⟨1365, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1367 : ChainPiece :=
  ⟨1367, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1371 : ChainPiece :=
  ⟨1371, [0x8d9ff06f], .jump 913⟩
def piece1372 : ChainPiece :=
  ⟨1372, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1377 : ChainPiece :=
  ⟨1377, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1379 : ChainPiece :=
  ⟨1379, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1381 : ChainPiece :=
  ⟨1381, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece1385 : ChainPiece :=
  ⟨1385, [0x8edff06f], .jump 932⟩
def piece1386 : ChainPiece :=
  ⟨1386, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1391 : ChainPiece :=
  ⟨1391, [0x007508a3, 0x00000073], .rung 1 none⟩
def chainBatch02 : List ChainPiece :=
  [piece1189, piece1192, piece1197, piece1198, piece1203, piece1206, piece1211, piece1212, piece1217, piece1220, piece1225, piece1226, piece1231, piece1234, piece1239, piece1241, piece1245, piece1246, piece1251, piece1254, piece1259, piece1262, piece1263, piece1268, piece1271, piece1276, piece1279, piece1280, piece1285, piece1288, piece1293, piece1295, piece1297, piece1301, piece1302, piece1307, piece1310, piece1315, piece1317, piece1320, piece1325, piece1329, piece1330, piece1335, piece1337, piece1339, piece1343, piece1344, piece1349, piece1351, piece1353, piece1357, piece1358, piece1363, piece1365, piece1367, piece1371, piece1372, piece1377, piece1379, piece1381, piece1385, piece1386, piece1391]
theorem chainBatch02_checked : (chainBatch02.all ChainPiece.checked) = true := by
  decide +kernel
def piece1393 : ChainPiece :=
  ⟨1393, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1396 : ChainPiece :=
  ⟨1396, [0x24040513, 0x27040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 624 4 2⟩
def piece1401 : ChainPiece :=
  ⟨1401, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1405 : ChainPiece :=
  ⟨1405, [0xaf1ff06f], .jump 1081⟩
def piece1406 : ChainPiece :=
  ⟨1406, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1411 : ChainPiece :=
  ⟨1411, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1413 : ChainPiece :=
  ⟨1413, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1416 : ChainPiece :=
  ⟨1416, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1421 : ChainPiece :=
  ⟨1421, [0xaf1ff06f], .jump 1097⟩
def piece1422 : ChainPiece :=
  ⟨1422, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1427 : ChainPiece :=
  ⟨1427, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1429 : ChainPiece :=
  ⟨1429, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1432 : ChainPiece :=
  ⟨1432, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece1437 : ChainPiece :=
  ⟨1437, [0xb05ff06f], .jump 1118⟩
def piece1438 : ChainPiece :=
  ⟨1438, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1443 : ChainPiece :=
  ⟨1443, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1445 : ChainPiece :=
  ⟨1445, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1448 : ChainPiece :=
  ⟨1448, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1453 : ChainPiece :=
  ⟨1453, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1455 : ChainPiece :=
  ⟨1455, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1459 : ChainPiece :=
  ⟨1459, [0xd89ff06f], .jump 1301⟩
def piece1460 : ChainPiece :=
  ⟨1460, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1465 : ChainPiece :=
  ⟨1465, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1467 : ChainPiece :=
  ⟨1467, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1470 : ChainPiece :=
  ⟨1470, [0x24040513, 0x27040613, 0x190f8c93, 0x01953823, 0x00000073], .head 576 624 4 1⟩
def piece1475 : ChainPiece :=
  ⟨1475, [0x00d508a3, 0x3c040613, 0x00000073], .rung 2 (some 960)⟩
def piece1478 : ChainPiece :=
  ⟨1478, [0xd89ff06f], .jump 1320⟩
def piece1479 : ChainPiece :=
  ⟨1479, [0x28040513, 0x2b040613, 0x08cf8c93, 0x01953823, 0x00000073], .head 640 688 3 0⟩
def piece1484 : ChainPiece :=
  ⟨1484, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1486 : ChainPiece :=
  ⟨1486, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece1489 : ChainPiece :=
  ⟨1489, [0x24040513, 0x27040613, 0x090f8c93, 0x01953823, 0x00000073], .head 576 624 4 0⟩
def piece1494 : ChainPiece :=
  ⟨1494, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece1496 : ChainPiece :=
  ⟨1496, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece1498 : ChainPiece :=
  ⟨1498, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece1502 : ChainPiece :=
  ⟨1502, [0xf4cff06f], .jump 945⟩
def piece1503 : ChainPiece :=
  ⟨1503, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1508 : ChainPiece :=
  ⟨1508, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1512 : ChainPiece :=
  ⟨1512, [0xf60ff06f], .jump 960⟩
def piece1513 : ChainPiece :=
  ⟨1513, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1518 : ChainPiece :=
  ⟨1518, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1522 : ChainPiece :=
  ⟨1522, [0xf60ff06f], .jump 970⟩
def piece1523 : ChainPiece :=
  ⟨1523, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1528 : ChainPiece :=
  ⟨1528, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1532 : ChainPiece :=
  ⟨1532, [0xf50ff06f], .jump 976⟩
def piece1533 : ChainPiece :=
  ⟨1533, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1538 : ChainPiece :=
  ⟨1538, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1542 : ChainPiece :=
  ⟨1542, [0xf54ff06f], .jump 987⟩
def piece1543 : ChainPiece :=
  ⟨1543, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1548 : ChainPiece :=
  ⟨1548, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1552 : ChainPiece :=
  ⟨1552, [0xf58ff06f], .jump 998⟩
def piece1553 : ChainPiece :=
  ⟨1553, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1558 : ChainPiece :=
  ⟨1558, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1562 : ChainPiece :=
  ⟨1562, [0xf5cff06f], .jump 1009⟩
def piece1563 : ChainPiece :=
  ⟨1563, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1568 : ChainPiece :=
  ⟨1568, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1572 : ChainPiece :=
  ⟨1572, [0xf78ff06f], .jump 1026⟩
def piece1573 : ChainPiece :=
  ⟨1573, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1578 : ChainPiece :=
  ⟨1578, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1582 : ChainPiece :=
  ⟨1582, [0xf88ff06f], .jump 1040⟩
def piece1583 : ChainPiece :=
  ⟨1583, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1588 : ChainPiece :=
  ⟨1588, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece1592 : ChainPiece :=
  ⟨1592, [0xf98ff06f], .jump 1054⟩
def piece1593 : ChainPiece :=
  ⟨1593, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece1598 : ChainPiece :=
  ⟨1598, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def chainBatch03 : List ChainPiece :=
  [piece1393, piece1396, piece1401, piece1405, piece1406, piece1411, piece1413, piece1416, piece1421, piece1422, piece1427, piece1429, piece1432, piece1437, piece1438, piece1443, piece1445, piece1448, piece1453, piece1455, piece1459, piece1460, piece1465, piece1467, piece1470, piece1475, piece1478, piece1479, piece1484, piece1486, piece1489, piece1494, piece1496, piece1498, piece1502, piece1503, piece1508, piece1512, piece1513, piece1518, piece1522, piece1523, piece1528, piece1532, piece1533, piece1538, piece1542, piece1543, piece1548, piece1552, piece1553, piece1558, piece1562, piece1563, piece1568, piece1572, piece1573, piece1578, piece1582, piece1583, piece1588, piece1592, piece1593, piece1598]
theorem chainBatch03_checked : (chainBatch03.all ChainPiece.checked) = true := by
  decide +kernel
end W9Machine
