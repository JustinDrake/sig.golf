import SigGolfCandidate.W9Machine.WctChainCheck10

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def piece240641 : ChainPiece :=
  ⟨240641, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece240646 : ChainPiece :=
  ⟨240646, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece240650 : ChainPiece :=
  ⟨240650, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece240655 : ChainPiece :=
  ⟨240655, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240657 : ChainPiece :=
  ⟨240657, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece240661 : ChainPiece :=
  ⟨240661, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece240666 : ChainPiece :=
  ⟨240666, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece240670 : ChainPiece :=
  ⟨240670, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece240676 : ChainPiece :=
  ⟨240676, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240681 : ChainPiece :=
  ⟨240681, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240683 : ChainPiece :=
  ⟨240683, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece240688 : ChainPiece :=
  ⟨240688, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece240692 : ChainPiece :=
  ⟨240692, [0x28040513, 0x2b040613, 0x18cf8c93, 0x01953823, 0x00000073], .head 640 688 3 1⟩
def piece240697 : ChainPiece :=
  ⟨240697, [0x00d508a3, 0x3b040613, 0x00000073], .rung 2 (some 944)⟩
def piece240700 : ChainPiece :=
  ⟨240700, [0xe781706f], .jump 2522⟩
def piece240701 : ChainPiece :=
  ⟨240701, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240706 : ChainPiece :=
  ⟨240706, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240708 : ChainPiece :=
  ⟨240708, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece240713 : ChainPiece :=
  ⟨240713, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece240717 : ChainPiece :=
  ⟨240717, [0xd50fb06f], .jump 235937⟩
def piece240718 : ChainPiece :=
  ⟨240718, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240723 : ChainPiece :=
  ⟨240723, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240725 : ChainPiece :=
  ⟨240725, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240730 : ChainPiece :=
  ⟨240730, [0xd48fb06f], .jump 235948⟩
def piece240731 : ChainPiece :=
  ⟨240731, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240736 : ChainPiece :=
  ⟨240736, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240738 : ChainPiece :=
  ⟨240738, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240743 : ChainPiece :=
  ⟨240743, [0xd64fb06f], .jump 235968⟩
def piece240744 : ChainPiece :=
  ⟨240744, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240749 : ChainPiece :=
  ⟨240749, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240751 : ChainPiece :=
  ⟨240751, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240756 : ChainPiece :=
  ⟨240756, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece240761 : ChainPiece :=
  ⟨240761, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240765 : ChainPiece :=
  ⟨240765, [0xed51806f], .jump 4146⟩
def piece240766 : ChainPiece :=
  ⟨240766, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240771 : ChainPiece :=
  ⟨240771, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240773 : ChainPiece :=
  ⟨240773, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240778 : ChainPiece :=
  ⟨240778, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece240783 : ChainPiece :=
  ⟨240783, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240787 : ChainPiece :=
  ⟨240787, [0x24040513, 0x27040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 624 4 2⟩
def piece240792 : ChainPiece :=
  ⟨240792, [0x27043183, 0x27843703, 0x3c343023, 0x3ce43423], .copy 576 960⟩
def piece240796 : ChainPiece :=
  ⟨240796, [0xb091506f], .jump 862⟩
def piece240797 : ChainPiece :=
  ⟨240797, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240802 : ChainPiece :=
  ⟨240802, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240804 : ChainPiece :=
  ⟨240804, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240809 : ChainPiece :=
  ⟨240809, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece240814 : ChainPiece :=
  ⟨240814, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240818 : ChainPiece :=
  ⟨240818, [0x24040513, 0x3c040613, 0x290f8c93, 0x01953823, 0x00000073], .head 576 960 4 2⟩
def piece240823 : ChainPiece :=
  ⟨240823, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece240828 : ChainPiece :=
  ⟨240828, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece240832 : ChainPiece :=
  ⟨240832, [0xbc51506f], .jump 945⟩
def piece240833 : ChainPiece :=
  ⟨240833, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240838 : ChainPiece :=
  ⟨240838, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240840 : ChainPiece :=
  ⟨240840, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240845 : ChainPiece :=
  ⟨240845, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece240850 : ChainPiece :=
  ⟨240850, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240854 : ChainPiece :=
  ⟨240854, [0xe551806f], .jump 4203⟩
def piece240855 : ChainPiece :=
  ⟨240855, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240860 : ChainPiece :=
  ⟨240860, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240862 : ChainPiece :=
  ⟨240862, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240867 : ChainPiece :=
  ⟨240867, [0xd04fb06f], .jump 236068⟩
def piece240868 : ChainPiece :=
  ⟨240868, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240873 : ChainPiece :=
  ⟨240873, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240875 : ChainPiece :=
  ⟨240875, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def chainBatch44 : List ChainPiece :=
  [piece240641, piece240646, piece240650, piece240655, piece240657, piece240661, piece240666, piece240670, piece240676, piece240681, piece240683, piece240688, piece240692, piece240697, piece240700, piece240701, piece240706, piece240708, piece240713, piece240717, piece240718, piece240723, piece240725, piece240730, piece240731, piece240736, piece240738, piece240743, piece240744, piece240749, piece240751, piece240756, piece240761, piece240765, piece240766, piece240771, piece240773, piece240778, piece240783, piece240787, piece240792, piece240796, piece240797, piece240802, piece240804, piece240809, piece240814, piece240818, piece240823, piece240828, piece240832, piece240833, piece240838, piece240840, piece240845, piece240850, piece240854, piece240855, piece240860, piece240862, piece240867, piece240868, piece240873, piece240875]
theorem chainBatch44_checked : (chainBatch44.all ChainPiece.checked) = true := by
  decide +kernel
def piece240880 : ChainPiece :=
  ⟨240880, [0x2c040513, 0x3a040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 928 2 2⟩
def piece240885 : ChainPiece :=
  ⟨240885, [0x28040513, 0x2b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 688 3 2⟩
def piece240890 : ChainPiece :=
  ⟨240890, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece240894 : ChainPiece :=
  ⟨240894, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece240899 : ChainPiece :=
  ⟨240899, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece240903 : ChainPiece :=
  ⟨240903, [0xaa91506f], .jump 945⟩
def piece240904 : ChainPiece :=
  ⟨240904, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240909 : ChainPiece :=
  ⟨240909, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240911 : ChainPiece :=
  ⟨240911, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240916 : ChainPiece :=
  ⟨240916, [0xce4fb06f], .jump 236109⟩
def piece240917 : ChainPiece :=
  ⟨240917, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240922 : ChainPiece :=
  ⟨240922, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240924 : ChainPiece :=
  ⟨240924, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240929 : ChainPiece :=
  ⟨240929, [0xcf0fb06f], .jump 236125⟩
def piece240930 : ChainPiece :=
  ⟨240930, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240935 : ChainPiece :=
  ⟨240935, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240937 : ChainPiece :=
  ⟨240937, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240942 : ChainPiece :=
  ⟨240942, [0xcfcfb06f], .jump 236141⟩
def piece240943 : ChainPiece :=
  ⟨240943, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240948 : ChainPiece :=
  ⟨240948, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240950 : ChainPiece :=
  ⟨240950, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240955 : ChainPiece :=
  ⟨240955, [0x2c040513, 0x2f040613, 0x188f8c93, 0x01953823, 0x00000073], .head 704 752 2 1⟩
def piece240960 : ChainPiece :=
  ⟨240960, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240962 : ChainPiece :=
  ⟨240962, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240966 : ChainPiece :=
  ⟨240966, [0xbf5fa06f], .jump 235587⟩
def piece240967 : ChainPiece :=
  ⟨240967, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240972 : ChainPiece :=
  ⟨240972, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240974 : ChainPiece :=
  ⟨240974, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece240979 : ChainPiece :=
  ⟨240979, [0x2c040513, 0x2f040613, 0x188f8c93, 0x01953823, 0x00000073], .head 704 752 2 1⟩
def piece240984 : ChainPiece :=
  ⟨240984, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240986 : ChainPiece :=
  ⟨240986, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece240990 : ChainPiece :=
  ⟨240990, [0xbedfa06f], .jump 235609⟩
def piece240991 : ChainPiece :=
  ⟨240991, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece240996 : ChainPiece :=
  ⟨240996, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece240998 : ChainPiece :=
  ⟨240998, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece241003 : ChainPiece :=
  ⟨241003, [0xd10fb06f], .jump 236207⟩
def piece241004 : ChainPiece :=
  ⟨241004, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241009 : ChainPiece :=
  ⟨241009, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241011 : ChainPiece :=
  ⟨241011, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece241016 : ChainPiece :=
  ⟨241016, [0xd28fb06f], .jump 236226⟩
def piece241017 : ChainPiece :=
  ⟨241017, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241022 : ChainPiece :=
  ⟨241022, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241024 : ChainPiece :=
  ⟨241024, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241029 : ChainPiece :=
  ⟨241029, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241031 : ChainPiece :=
  ⟨241031, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241035 : ChainPiece :=
  ⟨241035, [0xedcfe06f], .jump 239426⟩
def piece241036 : ChainPiece :=
  ⟨241036, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241041 : ChainPiece :=
  ⟨241041, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241043 : ChainPiece :=
  ⟨241043, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241048 : ChainPiece :=
  ⟨241048, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241050 : ChainPiece :=
  ⟨241050, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241054 : ChainPiece :=
  ⟨241054, [0xedcfe06f], .jump 239445⟩
def piece241055 : ChainPiece :=
  ⟨241055, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241060 : ChainPiece :=
  ⟨241060, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241062 : ChainPiece :=
  ⟨241062, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241067 : ChainPiece :=
  ⟨241067, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241069 : ChainPiece :=
  ⟨241069, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241073 : ChainPiece :=
  ⟨241073, [0xedcfe06f], .jump 239464⟩
def piece241074 : ChainPiece :=
  ⟨241074, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241079 : ChainPiece :=
  ⟨241079, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241081 : ChainPiece :=
  ⟨241081, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241086 : ChainPiece :=
  ⟨241086, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241088 : ChainPiece :=
  ⟨241088, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241092 : ChainPiece :=
  ⟨241092, [0xa051806f], .jump 4165⟩
def chainBatch45 : List ChainPiece :=
  [piece240880, piece240885, piece240890, piece240894, piece240899, piece240903, piece240904, piece240909, piece240911, piece240916, piece240917, piece240922, piece240924, piece240929, piece240930, piece240935, piece240937, piece240942, piece240943, piece240948, piece240950, piece240955, piece240960, piece240962, piece240966, piece240967, piece240972, piece240974, piece240979, piece240984, piece240986, piece240990, piece240991, piece240996, piece240998, piece241003, piece241004, piece241009, piece241011, piece241016, piece241017, piece241022, piece241024, piece241029, piece241031, piece241035, piece241036, piece241041, piece241043, piece241048, piece241050, piece241054, piece241055, piece241060, piece241062, piece241067, piece241069, piece241073, piece241074, piece241079, piece241081, piece241086, piece241088, piece241092]
theorem chainBatch45_checked : (chainBatch45.all ChainPiece.checked) = true := by
  decide +kernel
def piece241093 : ChainPiece :=
  ⟨241093, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241098 : ChainPiece :=
  ⟨241098, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241100 : ChainPiece :=
  ⟨241100, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241105 : ChainPiece :=
  ⟨241105, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241107 : ChainPiece :=
  ⟨241107, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241111 : ChainPiece :=
  ⟨241111, [0xa051806f], .jump 4184⟩
def piece241112 : ChainPiece :=
  ⟨241112, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241117 : ChainPiece :=
  ⟨241117, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241119 : ChainPiece :=
  ⟨241119, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241124 : ChainPiece :=
  ⟨241124, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241126 : ChainPiece :=
  ⟨241126, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241130 : ChainPiece :=
  ⟨241130, [0xedcfe06f], .jump 239521⟩
def piece241131 : ChainPiece :=
  ⟨241131, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241136 : ChainPiece :=
  ⟨241136, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241138 : ChainPiece :=
  ⟨241138, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241143 : ChainPiece :=
  ⟨241143, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241145 : ChainPiece :=
  ⟨241145, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241149 : ChainPiece :=
  ⟨241149, [0x9f91806f], .jump 4219⟩
def piece241150 : ChainPiece :=
  ⟨241150, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241155 : ChainPiece :=
  ⟨241155, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241157 : ChainPiece :=
  ⟨241157, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241162 : ChainPiece :=
  ⟨241162, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241164 : ChainPiece :=
  ⟨241164, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241168 : ChainPiece :=
  ⟨241168, [0x28040513, 0x2b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 688 3 2⟩
def piece241173 : ChainPiece :=
  ⟨241173, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece241177 : ChainPiece :=
  ⟨241177, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece241182 : ChainPiece :=
  ⟨241182, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece241186 : ChainPiece :=
  ⟨241186, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece241192 : ChainPiece :=
  ⟨241192, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241197 : ChainPiece :=
  ⟨241197, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241199 : ChainPiece :=
  ⟨241199, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241204 : ChainPiece :=
  ⟨241204, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241206 : ChainPiece :=
  ⟨241206, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241210 : ChainPiece :=
  ⟨241210, [0x9cd1806f], .jump 4269⟩
def piece241211 : ChainPiece :=
  ⟨241211, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241216 : ChainPiece :=
  ⟨241216, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241218 : ChainPiece :=
  ⟨241218, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241223 : ChainPiece :=
  ⟨241223, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241225 : ChainPiece :=
  ⟨241225, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241229 : ChainPiece :=
  ⟨241229, [0xedcfe06f], .jump 239620⟩
def piece241230 : ChainPiece :=
  ⟨241230, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241235 : ChainPiece :=
  ⟨241235, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241237 : ChainPiece :=
  ⟨241237, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241242 : ChainPiece :=
  ⟨241242, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241245 : ChainPiece :=
  ⟨241245, [0xedcfe06f], .jump 239636⟩
def piece241246 : ChainPiece :=
  ⟨241246, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241251 : ChainPiece :=
  ⟨241251, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241253 : ChainPiece :=
  ⟨241253, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241258 : ChainPiece :=
  ⟨241258, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241261 : ChainPiece :=
  ⟨241261, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece241266 : ChainPiece :=
  ⟨241266, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece241270 : ChainPiece :=
  ⟨241270, [0xd451606f], .jump 2503⟩
def piece241271 : ChainPiece :=
  ⟨241271, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241276 : ChainPiece :=
  ⟨241276, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241278 : ChainPiece :=
  ⟨241278, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241283 : ChainPiece :=
  ⟨241283, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241286 : ChainPiece :=
  ⟨241286, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece241291 : ChainPiece :=
  ⟨241291, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece241295 : ChainPiece :=
  ⟨241295, [0xd2d1606f], .jump 2522⟩
def piece241296 : ChainPiece :=
  ⟨241296, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241301 : ChainPiece :=
  ⟨241301, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241303 : ChainPiece :=
  ⟨241303, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241308 : ChainPiece :=
  ⟨241308, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241311 : ChainPiece :=
  ⟨241311, [0xf00fe06f], .jump 239711⟩
def chainBatch46 : List ChainPiece :=
  [piece241093, piece241098, piece241100, piece241105, piece241107, piece241111, piece241112, piece241117, piece241119, piece241124, piece241126, piece241130, piece241131, piece241136, piece241138, piece241143, piece241145, piece241149, piece241150, piece241155, piece241157, piece241162, piece241164, piece241168, piece241173, piece241177, piece241182, piece241186, piece241192, piece241197, piece241199, piece241204, piece241206, piece241210, piece241211, piece241216, piece241218, piece241223, piece241225, piece241229, piece241230, piece241235, piece241237, piece241242, piece241245, piece241246, piece241251, piece241253, piece241258, piece241261, piece241266, piece241270, piece241271, piece241276, piece241278, piece241283, piece241286, piece241291, piece241295, piece241296, piece241301, piece241303, piece241308, piece241311]
theorem chainBatch46_checked : (chainBatch46.all ChainPiece.checked) = true := by
  decide +kernel
def piece241312 : ChainPiece :=
  ⟨241312, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241317 : ChainPiece :=
  ⟨241317, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241319 : ChainPiece :=
  ⟨241319, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece241324 : ChainPiece :=
  ⟨241324, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241327 : ChainPiece :=
  ⟨241327, [0xf14fe06f], .jump 239732⟩
def piece241328 : ChainPiece :=
  ⟨241328, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241333 : ChainPiece :=
  ⟨241333, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241335 : ChainPiece :=
  ⟨241335, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece241340 : ChainPiece :=
  ⟨241340, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241342 : ChainPiece :=
  ⟨241342, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241344 : ChainPiece :=
  ⟨241344, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241348 : ChainPiece :=
  ⟨241348, [0xda4fa06f], .jump 235565⟩
def piece241349 : ChainPiece :=
  ⟨241349, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241354 : ChainPiece :=
  ⟨241354, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241356 : ChainPiece :=
  ⟨241356, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece241361 : ChainPiece :=
  ⟨241361, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241363 : ChainPiece :=
  ⟨241363, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241365 : ChainPiece :=
  ⟨241365, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241369 : ChainPiece :=
  ⟨241369, [0xda8fa06f], .jump 235587⟩
def piece241370 : ChainPiece :=
  ⟨241370, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241375 : ChainPiece :=
  ⟨241375, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241377 : ChainPiece :=
  ⟨241377, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece241382 : ChainPiece :=
  ⟨241382, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241384 : ChainPiece :=
  ⟨241384, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241386 : ChainPiece :=
  ⟨241386, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241390 : ChainPiece :=
  ⟨241390, [0xdacfa06f], .jump 235609⟩
def piece241391 : ChainPiece :=
  ⟨241391, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241396 : ChainPiece :=
  ⟨241396, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241398 : ChainPiece :=
  ⟨241398, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece241403 : ChainPiece :=
  ⟨241403, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241405 : ChainPiece :=
  ⟨241405, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241407 : ChainPiece :=
  ⟨241407, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241411 : ChainPiece :=
  ⟨241411, [0xda4fa06f], .jump 235628⟩
def piece241412 : ChainPiece :=
  ⟨241412, [0x34040513, 0x37040613, 0x180f8c93, 0x01953823, 0x00000073], .head 832 880 0 1⟩
def piece241417 : ChainPiece :=
  ⟨241417, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241419 : ChainPiece :=
  ⟨241419, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece241424 : ChainPiece :=
  ⟨241424, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241426 : ChainPiece :=
  ⟨241426, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece241429 : ChainPiece :=
  ⟨241429, [0x2c040513, 0x2f040613, 0x288f8c93, 0x01953823, 0x00000073], .head 704 752 2 2⟩
def piece241434 : ChainPiece :=
  ⟨241434, [0x2f043183, 0x2f843703, 0x3a343023, 0x3ae43423], .copy 704 928⟩
def piece241438 : ChainPiece :=
  ⟨241438, [0xec5fa06f], .jump 236239⟩
def piece241439 : ChainPiece :=
  ⟨241439, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241444 : ChainPiece :=
  ⟨241444, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241446 : ChainPiece :=
  ⟨241446, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241448 : ChainPiece :=
  ⟨241448, [0xd6cfa06f], .jump 235651⟩
def piece241449 : ChainPiece :=
  ⟨241449, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241454 : ChainPiece :=
  ⟨241454, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241456 : ChainPiece :=
  ⟨241456, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241458 : ChainPiece :=
  ⟨241458, [0xd7cfa06f], .jump 235665⟩
def piece241459 : ChainPiece :=
  ⟨241459, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241464 : ChainPiece :=
  ⟨241464, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241466 : ChainPiece :=
  ⟨241466, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241468 : ChainPiece :=
  ⟨241468, [0xd8cfa06f], .jump 235679⟩
def piece241469 : ChainPiece :=
  ⟨241469, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241474 : ChainPiece :=
  ⟨241474, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241476 : ChainPiece :=
  ⟨241476, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241478 : ChainPiece :=
  ⟨241478, [0xd9cfa06f], .jump 235693⟩
def piece241479 : ChainPiece :=
  ⟨241479, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241484 : ChainPiece :=
  ⟨241484, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241486 : ChainPiece :=
  ⟨241486, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241488 : ChainPiece :=
  ⟨241488, [0xdacfa06f], .jump 235707⟩
def piece241489 : ChainPiece :=
  ⟨241489, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241494 : ChainPiece :=
  ⟨241494, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241496 : ChainPiece :=
  ⟨241496, [0x00d508a3, 0x00000073], .rung 2 none⟩
def chainBatch47 : List ChainPiece :=
  [piece241312, piece241317, piece241319, piece241324, piece241327, piece241328, piece241333, piece241335, piece241340, piece241342, piece241344, piece241348, piece241349, piece241354, piece241356, piece241361, piece241363, piece241365, piece241369, piece241370, piece241375, piece241377, piece241382, piece241384, piece241386, piece241390, piece241391, piece241396, piece241398, piece241403, piece241405, piece241407, piece241411, piece241412, piece241417, piece241419, piece241424, piece241426, piece241429, piece241434, piece241438, piece241439, piece241444, piece241446, piece241448, piece241449, piece241454, piece241456, piece241458, piece241459, piece241464, piece241466, piece241468, piece241469, piece241474, piece241476, piece241478, piece241479, piece241484, piece241486, piece241488, piece241489, piece241494, piece241496]
theorem chainBatch47_checked : (chainBatch47.all ChainPiece.checked) = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def piece241498 : ChainPiece :=
  ⟨241498, [0xdbcfa06f], .jump 235721⟩
def piece241499 : ChainPiece :=
  ⟨241499, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241504 : ChainPiece :=
  ⟨241504, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241506 : ChainPiece :=
  ⟨241506, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241508 : ChainPiece :=
  ⟨241508, [0xdccfa06f], .jump 235735⟩
def piece241509 : ChainPiece :=
  ⟨241509, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241514 : ChainPiece :=
  ⟨241514, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241516 : ChainPiece :=
  ⟨241516, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241518 : ChainPiece :=
  ⟨241518, [0xddcfa06f], .jump 235749⟩
def piece241519 : ChainPiece :=
  ⟨241519, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241524 : ChainPiece :=
  ⟨241524, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241526 : ChainPiece :=
  ⟨241526, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241528 : ChainPiece :=
  ⟨241528, [0xdecfa06f], .jump 235763⟩
def piece241529 : ChainPiece :=
  ⟨241529, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241534 : ChainPiece :=
  ⟨241534, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241536 : ChainPiece :=
  ⟨241536, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241538 : ChainPiece :=
  ⟨241538, [0xdfcfa06f], .jump 235777⟩
def piece241539 : ChainPiece :=
  ⟨241539, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241544 : ChainPiece :=
  ⟨241544, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241546 : ChainPiece :=
  ⟨241546, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241548 : ChainPiece :=
  ⟨241548, [0xe0cfa06f], .jump 235791⟩
def piece241549 : ChainPiece :=
  ⟨241549, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241554 : ChainPiece :=
  ⟨241554, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241556 : ChainPiece :=
  ⟨241556, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241558 : ChainPiece :=
  ⟨241558, [0xe1cfa06f], .jump 235805⟩
def piece241559 : ChainPiece :=
  ⟨241559, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241564 : ChainPiece :=
  ⟨241564, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241566 : ChainPiece :=
  ⟨241566, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241568 : ChainPiece :=
  ⟨241568, [0xe2cfa06f], .jump 235819⟩
def piece241569 : ChainPiece :=
  ⟨241569, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241574 : ChainPiece :=
  ⟨241574, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241576 : ChainPiece :=
  ⟨241576, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241578 : ChainPiece :=
  ⟨241578, [0xe60fa06f], .jump 235842⟩
def piece241579 : ChainPiece :=
  ⟨241579, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241584 : ChainPiece :=
  ⟨241584, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241586 : ChainPiece :=
  ⟨241586, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241588 : ChainPiece :=
  ⟨241588, [0xe70fa06f], .jump 235856⟩
def piece241589 : ChainPiece :=
  ⟨241589, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241594 : ChainPiece :=
  ⟨241594, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241596 : ChainPiece :=
  ⟨241596, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241598 : ChainPiece :=
  ⟨241598, [0xe80fa06f], .jump 235870⟩
def piece241599 : ChainPiece :=
  ⟨241599, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241604 : ChainPiece :=
  ⟨241604, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241606 : ChainPiece :=
  ⟨241606, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241608 : ChainPiece :=
  ⟨241608, [0xe90fa06f], .jump 235884⟩
def piece241609 : ChainPiece :=
  ⟨241609, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241614 : ChainPiece :=
  ⟨241614, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241616 : ChainPiece :=
  ⟨241616, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241618 : ChainPiece :=
  ⟨241618, [0xea0fa06f], .jump 235898⟩
def piece241619 : ChainPiece :=
  ⟨241619, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241624 : ChainPiece :=
  ⟨241624, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241626 : ChainPiece :=
  ⟨241626, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241628 : ChainPiece :=
  ⟨241628, [0xedcfa06f], .jump 235923⟩
def piece241629 : ChainPiece :=
  ⟨241629, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241634 : ChainPiece :=
  ⟨241634, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241636 : ChainPiece :=
  ⟨241636, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241638 : ChainPiece :=
  ⟨241638, [0xeecfa06f], .jump 235937⟩
def piece241639 : ChainPiece :=
  ⟨241639, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241644 : ChainPiece :=
  ⟨241644, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241646 : ChainPiece :=
  ⟨241646, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241648 : ChainPiece :=
  ⟨241648, [0xef0fa06f], .jump 235948⟩
def piece241649 : ChainPiece :=
  ⟨241649, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241654 : ChainPiece :=
  ⟨241654, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241656 : ChainPiece :=
  ⟨241656, [0x00d508a3, 0x00000073], .rung 2 none⟩
def chainBatch48 : List ChainPiece :=
  [piece241498, piece241499, piece241504, piece241506, piece241508, piece241509, piece241514, piece241516, piece241518, piece241519, piece241524, piece241526, piece241528, piece241529, piece241534, piece241536, piece241538, piece241539, piece241544, piece241546, piece241548, piece241549, piece241554, piece241556, piece241558, piece241559, piece241564, piece241566, piece241568, piece241569, piece241574, piece241576, piece241578, piece241579, piece241584, piece241586, piece241588, piece241589, piece241594, piece241596, piece241598, piece241599, piece241604, piece241606, piece241608, piece241609, piece241614, piece241616, piece241618, piece241619, piece241624, piece241626, piece241628, piece241629, piece241634, piece241636, piece241638, piece241639, piece241644, piece241646, piece241648, piece241649, piece241654, piece241656]
theorem chainBatch48_checked : (chainBatch48.all ChainPiece.checked) = true := by
  decide +kernel
def piece241658 : ChainPiece :=
  ⟨241658, [0xf18fa06f], .jump 235968⟩
def piece241659 : ChainPiece :=
  ⟨241659, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241664 : ChainPiece :=
  ⟨241664, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241666 : ChainPiece :=
  ⟨241666, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241668 : ChainPiece :=
  ⟨241668, [0xf40fa06f], .jump 235988⟩
def piece241669 : ChainPiece :=
  ⟨241669, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241674 : ChainPiece :=
  ⟨241674, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241676 : ChainPiece :=
  ⟨241676, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241678 : ChainPiece :=
  ⟨241678, [0xf68fa06f], .jump 236008⟩
def piece241679 : ChainPiece :=
  ⟨241679, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241684 : ChainPiece :=
  ⟨241684, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241686 : ChainPiece :=
  ⟨241686, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241688 : ChainPiece :=
  ⟨241688, [0xf90fa06f], .jump 236028⟩
def piece241689 : ChainPiece :=
  ⟨241689, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241694 : ChainPiece :=
  ⟨241694, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241696 : ChainPiece :=
  ⟨241696, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241698 : ChainPiece :=
  ⟨241698, [0xfb8fa06f], .jump 236048⟩
def piece241699 : ChainPiece :=
  ⟨241699, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241704 : ChainPiece :=
  ⟨241704, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241706 : ChainPiece :=
  ⟨241706, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241708 : ChainPiece :=
  ⟨241708, [0xfe0fa06f], .jump 236068⟩
def piece241709 : ChainPiece :=
  ⟨241709, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241714 : ChainPiece :=
  ⟨241714, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241716 : ChainPiece :=
  ⟨241716, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241718 : ChainPiece :=
  ⟨241718, [0xff8fa06f], .jump 236084⟩
def piece241719 : ChainPiece :=
  ⟨241719, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241724 : ChainPiece :=
  ⟨241724, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241726 : ChainPiece :=
  ⟨241726, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241728 : ChainPiece :=
  ⟨241728, [0x835fa06f], .jump 236109⟩
def piece241729 : ChainPiece :=
  ⟨241729, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241734 : ChainPiece :=
  ⟨241734, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241736 : ChainPiece :=
  ⟨241736, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241738 : ChainPiece :=
  ⟨241738, [0x84dfa06f], .jump 236125⟩
def piece241739 : ChainPiece :=
  ⟨241739, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241744 : ChainPiece :=
  ⟨241744, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241746 : ChainPiece :=
  ⟨241746, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241748 : ChainPiece :=
  ⟨241748, [0x865fa06f], .jump 236141⟩
def piece241749 : ChainPiece :=
  ⟨241749, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241754 : ChainPiece :=
  ⟨241754, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241756 : ChainPiece :=
  ⟨241756, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241758 : ChainPiece :=
  ⟨241758, [0x895fa06f], .jump 236163⟩
def piece241759 : ChainPiece :=
  ⟨241759, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241764 : ChainPiece :=
  ⟨241764, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241766 : ChainPiece :=
  ⟨241766, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241768 : ChainPiece :=
  ⟨241768, [0x8c5fa06f], .jump 236185⟩
def piece241769 : ChainPiece :=
  ⟨241769, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241774 : ChainPiece :=
  ⟨241774, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241776 : ChainPiece :=
  ⟨241776, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241778 : ChainPiece :=
  ⟨241778, [0x8f5fa06f], .jump 236207⟩
def piece241779 : ChainPiece :=
  ⟨241779, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241784 : ChainPiece :=
  ⟨241784, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241786 : ChainPiece :=
  ⟨241786, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241788 : ChainPiece :=
  ⟨241788, [0x919fa06f], .jump 236226⟩
def piece241789 : ChainPiece :=
  ⟨241789, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241794 : ChainPiece :=
  ⟨241794, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241796 : ChainPiece :=
  ⟨241796, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241798 : ChainPiece :=
  ⟨241798, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241803 : ChainPiece :=
  ⟨241803, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241807 : ChainPiece :=
  ⟨241807, [0xacdfd06f], .jump 239426⟩
def piece241808 : ChainPiece :=
  ⟨241808, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241813 : ChainPiece :=
  ⟨241813, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241815 : ChainPiece :=
  ⟨241815, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241817 : ChainPiece :=
  ⟨241817, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241822 : ChainPiece :=
  ⟨241822, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def chainBatch49 : List ChainPiece :=
  [piece241658, piece241659, piece241664, piece241666, piece241668, piece241669, piece241674, piece241676, piece241678, piece241679, piece241684, piece241686, piece241688, piece241689, piece241694, piece241696, piece241698, piece241699, piece241704, piece241706, piece241708, piece241709, piece241714, piece241716, piece241718, piece241719, piece241724, piece241726, piece241728, piece241729, piece241734, piece241736, piece241738, piece241739, piece241744, piece241746, piece241748, piece241749, piece241754, piece241756, piece241758, piece241759, piece241764, piece241766, piece241768, piece241769, piece241774, piece241776, piece241778, piece241779, piece241784, piece241786, piece241788, piece241789, piece241794, piece241796, piece241798, piece241803, piece241807, piece241808, piece241813, piece241815, piece241817, piece241822]
theorem chainBatch49_checked : (chainBatch49.all ChainPiece.checked) = true := by
  decide +kernel
def piece241826 : ChainPiece :=
  ⟨241826, [0xacdfd06f], .jump 239445⟩
def piece241827 : ChainPiece :=
  ⟨241827, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241832 : ChainPiece :=
  ⟨241832, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241834 : ChainPiece :=
  ⟨241834, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241836 : ChainPiece :=
  ⟨241836, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241841 : ChainPiece :=
  ⟨241841, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241845 : ChainPiece :=
  ⟨241845, [0xacdfd06f], .jump 239464⟩
def piece241846 : ChainPiece :=
  ⟨241846, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241851 : ChainPiece :=
  ⟨241851, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241853 : ChainPiece :=
  ⟨241853, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241855 : ChainPiece :=
  ⟨241855, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241860 : ChainPiece :=
  ⟨241860, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241864 : ChainPiece :=
  ⟨241864, [0xdf51706f], .jump 4165⟩
def piece241865 : ChainPiece :=
  ⟨241865, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241870 : ChainPiece :=
  ⟨241870, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241872 : ChainPiece :=
  ⟨241872, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241874 : ChainPiece :=
  ⟨241874, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241879 : ChainPiece :=
  ⟨241879, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241883 : ChainPiece :=
  ⟨241883, [0xdf51706f], .jump 4184⟩
def piece241884 : ChainPiece :=
  ⟨241884, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241889 : ChainPiece :=
  ⟨241889, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241891 : ChainPiece :=
  ⟨241891, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241893 : ChainPiece :=
  ⟨241893, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241898 : ChainPiece :=
  ⟨241898, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241902 : ChainPiece :=
  ⟨241902, [0xacdfd06f], .jump 239521⟩
def piece241903 : ChainPiece :=
  ⟨241903, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241908 : ChainPiece :=
  ⟨241908, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241910 : ChainPiece :=
  ⟨241910, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241912 : ChainPiece :=
  ⟨241912, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241917 : ChainPiece :=
  ⟨241917, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241921 : ChainPiece :=
  ⟨241921, [0xde91706f], .jump 4219⟩
def piece241922 : ChainPiece :=
  ⟨241922, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241927 : ChainPiece :=
  ⟨241927, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241929 : ChainPiece :=
  ⟨241929, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241931 : ChainPiece :=
  ⟨241931, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241936 : ChainPiece :=
  ⟨241936, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241940 : ChainPiece :=
  ⟨241940, [0x28040513, 0x2b040613, 0x28cf8c93, 0x01953823, 0x00000073], .head 640 688 3 2⟩
def piece241945 : ChainPiece :=
  ⟨241945, [0x2b043183, 0x2b843703, 0x3a343823, 0x3ae43c23], .copy 640 944⟩
def piece241949 : ChainPiece :=
  ⟨241949, [0x20040513, 0x23040613, 0x294f8c93, 0x01953823, 0x00000073], .head 512 560 5 2⟩
def piece241954 : ChainPiece :=
  ⟨241954, [0x23043183, 0x23843703, 0x3c343823, 0x3ce43c23], .copy 512 976⟩
def piece241958 : ChainPiece :=
  ⟨241958, [0x9c8e3c83, 0x39943023, 0x38443423, 0x37040513, 0x08000593, 0x000b8067], .leaf⟩
def piece241964 : ChainPiece :=
  ⟨241964, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241969 : ChainPiece :=
  ⟨241969, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241971 : ChainPiece :=
  ⟨241971, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241973 : ChainPiece :=
  ⟨241973, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241978 : ChainPiece :=
  ⟨241978, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece241982 : ChainPiece :=
  ⟨241982, [0xdbd1706f], .jump 4269⟩
def piece241983 : ChainPiece :=
  ⟨241983, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece241988 : ChainPiece :=
  ⟨241988, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece241990 : ChainPiece :=
  ⟨241990, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece241992 : ChainPiece :=
  ⟨241992, [0x30040513, 0x33040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 816 1 2⟩
def piece241997 : ChainPiece :=
  ⟨241997, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242001 : ChainPiece :=
  ⟨242001, [0xacdfd06f], .jump 239620⟩
def piece242002 : ChainPiece :=
  ⟨242002, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242007 : ChainPiece :=
  ⟨242007, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242009 : ChainPiece :=
  ⟨242009, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242011 : ChainPiece :=
  ⟨242011, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece242016 : ChainPiece :=
  ⟨242016, [0xad1fd06f], .jump 239636⟩
def piece242017 : ChainPiece :=
  ⟨242017, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242022 : ChainPiece :=
  ⟨242022, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242024 : ChainPiece :=
  ⟨242024, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242026 : ChainPiece :=
  ⟨242026, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece242031 : ChainPiece :=
  ⟨242031, [0xaf9fd06f], .jump 239661⟩
def piece242032 : ChainPiece :=
  ⟨242032, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def chainBatch50 : List ChainPiece :=
  [piece241826, piece241827, piece241832, piece241834, piece241836, piece241841, piece241845, piece241846, piece241851, piece241853, piece241855, piece241860, piece241864, piece241865, piece241870, piece241872, piece241874, piece241879, piece241883, piece241884, piece241889, piece241891, piece241893, piece241898, piece241902, piece241903, piece241908, piece241910, piece241912, piece241917, piece241921, piece241922, piece241927, piece241929, piece241931, piece241936, piece241940, piece241945, piece241949, piece241954, piece241958, piece241964, piece241969, piece241971, piece241973, piece241978, piece241982, piece241983, piece241988, piece241990, piece241992, piece241997, piece242001, piece242002, piece242007, piece242009, piece242011, piece242016, piece242017, piece242022, piece242024, piece242026, piece242031, piece242032]
theorem chainBatch50_checked : (chainBatch50.all ChainPiece.checked) = true := by
  decide +kernel
def piece242037 : ChainPiece :=
  ⟨242037, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242039 : ChainPiece :=
  ⟨242039, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242041 : ChainPiece :=
  ⟨242041, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece242046 : ChainPiece :=
  ⟨242046, [0xb21fd06f], .jump 239686⟩
def piece242047 : ChainPiece :=
  ⟨242047, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242052 : ChainPiece :=
  ⟨242052, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242054 : ChainPiece :=
  ⟨242054, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242056 : ChainPiece :=
  ⟨242056, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece242061 : ChainPiece :=
  ⟨242061, [0xb49fd06f], .jump 239711⟩
def piece242062 : ChainPiece :=
  ⟨242062, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242067 : ChainPiece :=
  ⟨242067, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242069 : ChainPiece :=
  ⟨242069, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242071 : ChainPiece :=
  ⟨242071, [0x30040513, 0x39040613, 0x284f8c93, 0x01953823, 0x00000073], .head 768 912 1 2⟩
def piece242076 : ChainPiece :=
  ⟨242076, [0xb61fd06f], .jump 239732⟩
def piece242077 : ChainPiece :=
  ⟨242077, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242082 : ChainPiece :=
  ⟨242082, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242084 : ChainPiece :=
  ⟨242084, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242086 : ChainPiece :=
  ⟨242086, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece242091 : ChainPiece :=
  ⟨242091, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242093 : ChainPiece :=
  ⟨242093, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242097 : ChainPiece :=
  ⟨242097, [0xc4cff06f], .jump 241348⟩
def piece242098 : ChainPiece :=
  ⟨242098, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242103 : ChainPiece :=
  ⟨242103, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242105 : ChainPiece :=
  ⟨242105, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242107 : ChainPiece :=
  ⟨242107, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece242112 : ChainPiece :=
  ⟨242112, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242114 : ChainPiece :=
  ⟨242114, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242118 : ChainPiece :=
  ⟨242118, [0xc4cff06f], .jump 241369⟩
def piece242119 : ChainPiece :=
  ⟨242119, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242124 : ChainPiece :=
  ⟨242124, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242126 : ChainPiece :=
  ⟨242126, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242128 : ChainPiece :=
  ⟨242128, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece242133 : ChainPiece :=
  ⟨242133, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242135 : ChainPiece :=
  ⟨242135, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242139 : ChainPiece :=
  ⟨242139, [0xc4cff06f], .jump 241390⟩
def piece242140 : ChainPiece :=
  ⟨242140, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242145 : ChainPiece :=
  ⟨242145, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242147 : ChainPiece :=
  ⟨242147, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242149 : ChainPiece :=
  ⟨242149, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece242154 : ChainPiece :=
  ⟨242154, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242156 : ChainPiece :=
  ⟨242156, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242160 : ChainPiece :=
  ⟨242160, [0xc4cff06f], .jump 241411⟩
def piece242161 : ChainPiece :=
  ⟨242161, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242166 : ChainPiece :=
  ⟨242166, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242168 : ChainPiece :=
  ⟨242168, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242170 : ChainPiece :=
  ⟨242170, [0x30040513, 0x33040613, 0x184f8c93, 0x01953823, 0x00000073], .head 768 816 1 1⟩
def piece242175 : ChainPiece :=
  ⟨242175, [0x00d508a3, 0x39040613, 0x00000073], .rung 2 (some 912)⟩
def piece242178 : ChainPiece :=
  ⟨242178, [0xc4cff06f], .jump 241429⟩
def piece242179 : ChainPiece :=
  ⟨242179, [0x34040513, 0x37040613, 0x080f8c93, 0x01953823, 0x00000073], .head 832 880 0 0⟩
def piece242184 : ChainPiece :=
  ⟨242184, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242186 : ChainPiece :=
  ⟨242186, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242188 : ChainPiece :=
  ⟨242188, [0x30040513, 0x33040613, 0x084f8c93, 0x01953823, 0x00000073], .head 768 816 1 0⟩
def piece242193 : ChainPiece :=
  ⟨242193, [0x007508a3, 0x00000073], .rung 1 none⟩
def piece242195 : ChainPiece :=
  ⟨242195, [0x00d508a3, 0x00000073], .rung 2 none⟩
def piece242197 : ChainPiece :=
  ⟨242197, [0x33043183, 0x33843703, 0x38343823, 0x38e43c23], .copy 768 912⟩
def piece242201 : ChainPiece :=
  ⟨242201, [0xad8fa06f], .jump 236239⟩
def chainBatch51 : List ChainPiece :=
  [piece242037, piece242039, piece242041, piece242046, piece242047, piece242052, piece242054, piece242056, piece242061, piece242062, piece242067, piece242069, piece242071, piece242076, piece242077, piece242082, piece242084, piece242086, piece242091, piece242093, piece242097, piece242098, piece242103, piece242105, piece242107, piece242112, piece242114, piece242118, piece242119, piece242124, piece242126, piece242128, piece242133, piece242135, piece242139, piece242140, piece242145, piece242147, piece242149, piece242154, piece242156, piece242160, piece242161, piece242166, piece242168, piece242170, piece242175, piece242178, piece242179, piece242184, piece242186, piece242188, piece242193, piece242195, piece242197, piece242201]
theorem chainBatch51_checked : (chainBatch51.all ChainPiece.checked) = true := by
  decide +kernel
end W9Machine
end
