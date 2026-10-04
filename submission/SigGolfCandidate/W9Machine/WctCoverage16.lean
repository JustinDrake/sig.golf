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
def routine512 : ChainRoutine := ⟨512, [1, 2, 0, 1, 0, 0, 2], [piece238771, piece238776, piece238781, piece238783, piece238787, piece238792, piece238796, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine513 : ChainRoutine := ⟨513, [1, 2, 0, 1, 0, 1, 1], [piece238797, piece238802, piece238807, piece238809, piece238813, piece238818, piece238822, piece238827, piece862, piece867]⟩
def routine514 : ChainRoutine := ⟨514, [1, 2, 0, 1, 0, 2, 0], [piece238828, piece238833, piece238838, piece238840, piece238844, piece238849, piece238853, piece238858, piece238860, piece238864]⟩
def routine515 : ChainRoutine := ⟨515, [1, 2, 0, 1, 1, 0, 1], [piece238870, piece238875, piece238880, piece238882, piece238886, piece238891, piece238896, piece238900, piece862, piece867]⟩
def routine516 : ChainRoutine := ⟨516, [1, 2, 0, 1, 1, 1, 0], [piece238901, piece238906, piece238911, piece238913, piece238917, piece238922, piece238927, piece238932, piece238936, piece945]⟩
def routine517 : ChainRoutine := ⟨517, [1, 2, 0, 1, 2, 0, 0], [piece238937, piece238942, piece238947, piece238949, piece238953, piece2774, piece2779, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine518 : ChainRoutine := ⟨518, [1, 2, 0, 2, 0, 0, 1], [piece238954, piece238959, piece238964, piece238966, piece238970, piece2790, piece2795, piece2797, piece2801, piece2481, piece1301, piece862, piece867]⟩
def routine519 : ChainRoutine := ⟨519, [1, 2, 0, 2, 0, 1, 0], [piece238971, piece238976, piece238981, piece238983, piece238987, piece238992, piece238994, piece238998, piece239003, piece239007]⟩
def routine520 : ChainRoutine := ⟨520, [1, 2, 0, 2, 1, 0, 0], [piece239013, piece239018, piece239023, piece239025, piece239029, piece239034, piece239037, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine521 : ChainRoutine := ⟨521, [1, 2, 0, 3, 0, 0, 0], [piece239038, piece239043, piece239048, piece239050, piece239054, piece235937, piece2853, piece2858, piece2860, piece2862, piece2866, piece1502, piece945]⟩
def routine522 : ChainRoutine := ⟨522, [1, 2, 1, 0, 0, 0, 2], [piece239055, piece239060, piece239065, piece239068, piece235948, piece235953, piece235957, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine523 : ChainRoutine := ⟨523, [1, 2, 1, 0, 0, 1, 1], [piece239069, piece239074, piece239079, piece239082, piece239087, piece239091, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine524 : ChainRoutine := ⟨524, [1, 2, 1, 0, 0, 2, 0], [piece239092, piece239097, piece239102, piece239105, piece239110, piece239114, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine525 : ChainRoutine := ⟨525, [1, 2, 1, 0, 1, 0, 1], [piece239115, piece239120, piece239125, piece239128, piece239133, piece239137, piece239142, piece239146, piece239151]⟩
def routine526 : ChainRoutine := ⟨526, [1, 2, 1, 0, 1, 1, 0], [piece239157, piece239162, piece239167, piece239170, piece239175, piece239179, piece239184, piece239189, piece239193]⟩
def routine527 : ChainRoutine := ⟨527, [1, 2, 1, 0, 2, 0, 0], [piece239199, piece239204, piece239209, piece239212, piece239217, piece239221, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine528 : ChainRoutine := ⟨528, [1, 2, 1, 1, 0, 0, 1], [piece239222, piece239227, piece239232, piece239235, piece239240, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine529 : ChainRoutine := ⟨529, [1, 2, 1, 1, 0, 1, 0], [piece239241, piece239246, piece239251, piece239254, piece239259, piece239264, piece239268, piece239273, piece239277]⟩
def routine530 : ChainRoutine := ⟨530, [1, 2, 1, 1, 1, 0, 0], [piece239283, piece239288, piece239293, piece239296, piece239301, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine531 : ChainRoutine := ⟨531, [1, 2, 1, 2, 0, 0, 0], [piece239302, piece239307, piece239312, piece239315, piece236125, piece236130, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine532 : ChainRoutine := ⟨532, [1, 2, 2, 0, 0, 0, 1], [piece239316, piece239321, piece239326, piece239329, piece236141, piece236146, piece236148, piece236152, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine533 : ChainRoutine := ⟨533, [1, 2, 2, 0, 0, 1, 0], [piece239330, piece239335, piece239340, piece239343, piece239348, piece239350, piece239354, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine534 : ChainRoutine := ⟨534, [1, 2, 2, 0, 1, 0, 0], [piece239355, piece239360, piece239365, piece239368, piece239373, piece239375, piece239379, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine535 : ChainRoutine := ⟨535, [1, 2, 2, 1, 0, 0, 0], [piece239380, piece239385, piece239390, piece239393, piece236207, piece236212, piece236215, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine536 : ChainRoutine := ⟨536, [1, 2, 3, 0, 0, 0, 0], [piece239394, piece239399, piece239404, piece239407, piece236226, piece236231, piece236233, piece236235, piece236239, piece2866, piece1502, piece945]⟩
def routine537 : ChainRoutine := ⟨537, [1, 3, 0, 0, 0, 0, 2], [piece239408, piece239413, piece239418, piece239420, piece239422, piece239426, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine538 : ChainRoutine := ⟨538, [1, 3, 0, 0, 0, 1, 1], [piece239427, piece239432, piece239437, piece239439, piece239441, piece239445, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine539 : ChainRoutine := ⟨539, [1, 3, 0, 0, 0, 2, 0], [piece239446, piece239451, piece239456, piece239458, piece239460, piece239464, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine540 : ChainRoutine := ⟨540, [1, 3, 0, 0, 1, 0, 1], [piece239465, piece239470, piece239475, piece239477, piece239479, piece239483, piece4165, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine541 : ChainRoutine := ⟨541, [1, 3, 0, 0, 1, 1, 0], [piece239484, piece239489, piece239494, piece239496, piece239498, piece239502, piece4184, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine542 : ChainRoutine := ⟨542, [1, 3, 0, 0, 2, 0, 0], [piece239503, piece239508, piece239513, piece239515, piece239517, piece239521, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine543 : ChainRoutine := ⟨543, [1, 3, 0, 1, 0, 0, 1], [piece239522, piece239527, piece239532, piece239534, piece239536, piece239540, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routineBatch16 : List ChainRoutine := [routine512, routine513, routine514, routine515, routine516, routine517, routine518, routine519, routine520, routine521, routine522, routine523, routine524, routine525, routine526, routine527, routine528, routine529, routine530, routine531, routine532, routine533, routine534, routine535, routine536, routine537, routine538, routine539, routine540, routine541, routine542, routine543]
theorem routineBatch16_checked : (routineBatch16.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch16_checked :
    (routineBatch16.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch16_checked :
    (routineBatch16.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine512_ready : RoutineReady ⟨512, by decide⟩ routine512 := by
  wct_ready_start 512 16 0
  wct_cases [238771,238776,238781,238783,238787,238792,238796,1937,1081,799,804,807]
  · wct_piece 35 238771 15
  · wct_piece 35 238776 16
  · wct_piece 35 238781 17
  · wct_piece 35 238783 18
  · wct_piece 35 238787 19
  · wct_piece 35 238792 20
  · wct_piece 35 238796 21
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine513_ready : RoutineReady ⟨513, by decide⟩ routine513 := by
  wct_ready_start 513 16 1
  wct_cases [238797,238802,238807,238809,238813,238818,238822,238827,862,867]
  · wct_piece 35 238797 22
  · wct_piece 35 238802 23
  · wct_piece 35 238807 24
  · wct_piece 35 238809 25
  · wct_piece 35 238813 26
  · wct_piece 35 238818 27
  · wct_piece 35 238822 28
  · wct_piece 35 238827 29
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine514_ready : RoutineReady ⟨514, by decide⟩ routine514 := by
  wct_ready_start 514 16 2
  wct_cases [238828,238833,238838,238840,238844,238849,238853,238858,238860,238864]
  · wct_piece 35 238828 30
  · wct_piece 35 238833 31
  · wct_piece 35 238838 32
  · wct_piece 35 238840 33
  · wct_piece 35 238844 34
  · wct_piece 35 238849 35
  · wct_piece 35 238853 36
  · wct_piece 35 238858 37
  · wct_piece 35 238860 38
  · wct_piece 35 238864 39
theorem routine515_ready : RoutineReady ⟨515, by decide⟩ routine515 := by
  wct_ready_start 515 16 3
  wct_cases [238870,238875,238880,238882,238886,238891,238896,238900,862,867]
  · wct_piece 35 238870 40
  · wct_piece 35 238875 41
  · wct_piece 35 238880 42
  · wct_piece 35 238882 43
  · wct_piece 35 238886 44
  · wct_piece 35 238891 45
  · wct_piece 35 238896 46
  · wct_piece 35 238900 47
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine516_ready : RoutineReady ⟨516, by decide⟩ routine516 := by
  wct_ready_start 516 16 4
  wct_cases [238901,238906,238911,238913,238917,238922,238927,238932,238936,945]
  · wct_piece 35 238901 48
  · wct_piece 35 238906 49
  · wct_piece 35 238911 50
  · wct_piece 35 238913 51
  · wct_piece 35 238917 52
  · wct_piece 35 238922 53
  · wct_piece 35 238927 54
  · wct_piece 35 238932 55
  · wct_piece 35 238936 56
  · wct_piece 0 945 57
theorem routine517_ready : RoutineReady ⟨517, by decide⟩ routine517 := by
  wct_ready_start 517 16 5
  wct_cases [238937,238942,238947,238949,238953,2774,2779,2037,2042,2044,2048,1502,945]
  · wct_piece 35 238937 57
  · wct_piece 35 238942 58
  · wct_piece 35 238947 59
  · wct_piece 35 238949 60
  · wct_piece 35 238953 61
  · wct_piece 9 2774 37
  · wct_piece 9 2779 38
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine518_ready : RoutineReady ⟨518, by decide⟩ routine518 := by
  wct_ready_start 518 16 6
  wct_cases [238954,238959,238964,238966,238970,2790,2795,2797,2801,2481,1301,862,867]
  · wct_piece 35 238954 62
  · wct_piece 35 238959 63
  · wct_piece 36 238964 0
  · wct_piece 36 238966 1
  · wct_piece 36 238970 2
  · wct_piece 9 2790 42
  · wct_piece 9 2795 43
  · wct_piece 9 2797 44
  · wct_piece 9 2801 45
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine519_ready : RoutineReady ⟨519, by decide⟩ routine519 := by
  wct_ready_start 519 16 7
  wct_cases [238971,238976,238981,238983,238987,238992,238994,238998,239003,239007]
  · wct_piece 36 238971 3
  · wct_piece 36 238976 4
  · wct_piece 36 238981 5
  · wct_piece 36 238983 6
  · wct_piece 36 238987 7
  · wct_piece 36 238992 8
  · wct_piece 36 238994 9
  · wct_piece 36 238998 10
  · wct_piece 36 239003 11
  · wct_piece 36 239007 12
theorem routine520_ready : RoutineReady ⟨520, by decide⟩ routine520 := by
  wct_ready_start 520 16 8
  wct_cases [239013,239018,239023,239025,239029,239034,239037,2522,2527,2531,1502,945]
  · wct_piece 36 239013 13
  · wct_piece 36 239018 14
  · wct_piece 36 239023 15
  · wct_piece 36 239025 16
  · wct_piece 36 239029 17
  · wct_piece 36 239034 18
  · wct_piece 36 239037 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine521_ready : RoutineReady ⟨521, by decide⟩ routine521 := by
  wct_ready_start 521 16 9
  wct_cases [239038,239043,239048,239050,239054,235937,2853,2858,2860,2862,2866,1502,945]
  · wct_piece 36 239038 20
  · wct_piece 36 239043 21
  · wct_piece 36 239048 22
  · wct_piece 36 239050 23
  · wct_piece 36 239054 24
  · wct_piece 23 235937 7
  · wct_piece 9 2853 62
  · wct_piece 9 2858 63
  · wct_piece 10 2860 0
  · wct_piece 10 2862 1
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine522_ready : RoutineReady ⟨522, by decide⟩ routine522 := by
  wct_ready_start 522 16 10
  wct_cases [239055,239060,239065,239068,235948,235953,235957,4108,1937,1081,799,804,807]
  · wct_piece 36 239055 25
  · wct_piece 36 239060 26
  · wct_piece 36 239065 27
  · wct_piece 36 239068 28
  · wct_piece 23 235948 11
  · wct_piece 23 235953 12
  · wct_piece 23 235957 13
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine523_ready : RoutineReady ⟨523, by decide⟩ routine523 := by
  wct_ready_start 523 16 11
  wct_cases [239069,239074,239079,239082,239087,239091,4127,1956,1097,1102,862,867]
  · wct_piece 36 239069 29
  · wct_piece 36 239074 30
  · wct_piece 36 239079 31
  · wct_piece 36 239082 32
  · wct_piece 36 239087 33
  · wct_piece 36 239091 34
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine524_ready : RoutineReady ⟨524, by decide⟩ routine524 := by
  wct_ready_start 524 16 12
  wct_cases [239092,239097,239102,239105,239110,239114,1975,1118,1123,1125,1129,945]
  · wct_piece 36 239092 35
  · wct_piece 36 239097 36
  · wct_piece 36 239102 37
  · wct_piece 36 239105 38
  · wct_piece 36 239110 39
  · wct_piece 36 239114 40
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine525_ready : RoutineReady ⟨525, by decide⟩ routine525 := by
  wct_ready_start 525 16 13
  wct_cases [239115,239120,239125,239128,239133,239137,239142,239146,239151]
  · wct_piece 36 239115 41
  · wct_piece 36 239120 42
  · wct_piece 36 239125 43
  · wct_piece 36 239128 44
  · wct_piece 36 239133 45
  · wct_piece 36 239137 46
  · wct_piece 36 239142 47
  · wct_piece 36 239146 48
  · wct_piece 36 239151 49
theorem routine526_ready : RoutineReady ⟨526, by decide⟩ routine526 := by
  wct_ready_start 526 16 14
  wct_cases [239157,239162,239167,239170,239175,239179,239184,239189,239193]
  · wct_piece 36 239157 50
  · wct_piece 36 239162 51
  · wct_piece 36 239167 52
  · wct_piece 36 239170 53
  · wct_piece 36 239175 54
  · wct_piece 36 239179 55
  · wct_piece 36 239184 56
  · wct_piece 36 239189 57
  · wct_piece 36 239193 58
theorem routine527_ready : RoutineReady ⟨527, by decide⟩ routine527 := by
  wct_ready_start 527 16 15
  wct_cases [239199,239204,239209,239212,239217,239221,2037,2042,2044,2048,1502,945]
  · wct_piece 36 239199 59
  · wct_piece 36 239204 60
  · wct_piece 36 239209 61
  · wct_piece 36 239212 62
  · wct_piece 36 239217 63
  · wct_piece 37 239221 0
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine528_ready : RoutineReady ⟨528, by decide⟩ routine528 := by
  wct_ready_start 528 16 16
  wct_cases [239222,239227,239232,239235,239240,4219,4224,4228,2481,1301,862,867]
  · wct_piece 37 239222 1
  · wct_piece 37 239227 2
  · wct_piece 37 239232 3
  · wct_piece 37 239235 4
  · wct_piece 37 239240 5
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine529_ready : RoutineReady ⟨529, by decide⟩ routine529 := by
  wct_ready_start 529 16 17
  wct_cases [239241,239246,239251,239254,239259,239264,239268,239273,239277]
  · wct_piece 37 239241 6
  · wct_piece 37 239246 7
  · wct_piece 37 239251 8
  · wct_piece 37 239254 9
  · wct_piece 37 239259 10
  · wct_piece 37 239264 11
  · wct_piece 37 239268 12
  · wct_piece 37 239273 13
  · wct_piece 37 239277 14
theorem routine530_ready : RoutineReady ⟨530, by decide⟩ routine530 := by
  wct_ready_start 530 16 18
  wct_cases [239283,239288,239293,239296,239301,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 37 239283 15
  · wct_piece 37 239288 16
  · wct_piece 37 239293 17
  · wct_piece 37 239296 18
  · wct_piece 37 239301 19
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine531_ready : RoutineReady ⟨531, by decide⟩ routine531 := by
  wct_ready_start 531 16 19
  wct_cases [239302,239307,239312,239315,236125,236130,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 37 239302 20
  · wct_piece 37 239307 21
  · wct_piece 37 239312 22
  · wct_piece 37 239315 23
  · wct_piece 24 236125 0
  · wct_piece 24 236130 1
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine532_ready : RoutineReady ⟨532, by decide⟩ routine532 := by
  wct_ready_start 532 16 20
  wct_cases [239316,239321,239326,239329,236141,236146,236148,236152,235565,2481,1301,862,867]
  · wct_piece 37 239316 24
  · wct_piece 37 239321 25
  · wct_piece 37 239326 26
  · wct_piece 37 239329 27
  · wct_piece 24 236141 5
  · wct_piece 24 236146 6
  · wct_piece 24 236148 7
  · wct_piece 24 236152 8
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine533_ready : RoutineReady ⟨533, by decide⟩ routine533 := by
  wct_ready_start 533 16 21
  wct_cases [239330,239335,239340,239343,239348,239350,239354,2503,1320,1325,1329,945]
  · wct_piece 37 239330 28
  · wct_piece 37 239335 29
  · wct_piece 37 239340 30
  · wct_piece 37 239343 31
  · wct_piece 37 239348 32
  · wct_piece 37 239350 33
  · wct_piece 37 239354 34
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine534_ready : RoutineReady ⟨534, by decide⟩ routine534 := by
  wct_ready_start 534 16 22
  wct_cases [239355,239360,239365,239368,239373,239375,239379,2522,2527,2531,1502,945]
  · wct_piece 37 239355 35
  · wct_piece 37 239360 36
  · wct_piece 37 239365 37
  · wct_piece 37 239368 38
  · wct_piece 37 239373 39
  · wct_piece 37 239375 40
  · wct_piece 37 239379 41
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine535_ready : RoutineReady ⟨535, by decide⟩ routine535 := by
  wct_ready_start 535 16 23
  wct_cases [239380,239385,239390,239393,236207,236212,236215,235628,235633,235637,2866,1502,945]
  · wct_piece 37 239380 42
  · wct_piece 37 239385 43
  · wct_piece 37 239390 44
  · wct_piece 37 239393 45
  · wct_piece 24 236207 26
  · wct_piece 24 236212 27
  · wct_piece 24 236215 28
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine536_ready : RoutineReady ⟨536, by decide⟩ routine536 := by
  wct_ready_start 536 16 24
  wct_cases [239394,239399,239404,239407,236226,236231,236233,236235,236239,2866,1502,945]
  · wct_piece 37 239394 46
  · wct_piece 37 239399 47
  · wct_piece 37 239404 48
  · wct_piece 37 239407 49
  · wct_piece 24 236226 32
  · wct_piece 24 236231 33
  · wct_piece 24 236233 34
  · wct_piece 24 236235 35
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine537_ready : RoutineReady ⟨537, by decide⟩ routine537 := by
  wct_ready_start 537 16 25
  wct_cases [239408,239413,239418,239420,239422,239426,4108,1937,1081,799,804,807]
  · wct_piece 37 239408 50
  · wct_piece 37 239413 51
  · wct_piece 37 239418 52
  · wct_piece 37 239420 53
  · wct_piece 37 239422 54
  · wct_piece 37 239426 55
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine538_ready : RoutineReady ⟨538, by decide⟩ routine538 := by
  wct_ready_start 538 16 26
  wct_cases [239427,239432,239437,239439,239441,239445,4127,1956,1097,1102,862,867]
  · wct_piece 37 239427 56
  · wct_piece 37 239432 57
  · wct_piece 37 239437 58
  · wct_piece 37 239439 59
  · wct_piece 37 239441 60
  · wct_piece 37 239445 61
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine539_ready : RoutineReady ⟨539, by decide⟩ routine539 := by
  wct_ready_start 539 16 27
  wct_cases [239446,239451,239456,239458,239460,239464,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 37 239446 62
  · wct_piece 37 239451 63
  · wct_piece 38 239456 0
  · wct_piece 38 239458 1
  · wct_piece 38 239460 2
  · wct_piece 38 239464 3
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine540_ready : RoutineReady ⟨540, by decide⟩ routine540 := by
  wct_ready_start 540 16 28
  wct_cases [239465,239470,239475,239477,239479,239483,4165,1991,1996,2000,1301,862,867]
  · wct_piece 38 239465 4
  · wct_piece 38 239470 5
  · wct_piece 38 239475 6
  · wct_piece 38 239477 7
  · wct_piece 38 239479 8
  · wct_piece 38 239483 9
  · wct_piece 15 4165 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine541_ready : RoutineReady ⟨541, by decide⟩ routine541 := by
  wct_ready_start 541 16 29
  wct_cases [239484,239489,239494,239496,239498,239502,4184,2016,2021,1320,1325,1329,945]
  · wct_piece 38 239484 10
  · wct_piece 38 239489 11
  · wct_piece 38 239494 12
  · wct_piece 38 239496 13
  · wct_piece 38 239498 14
  · wct_piece 38 239502 15
  · wct_piece 15 4184 57
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine542_ready : RoutineReady ⟨542, by decide⟩ routine542 := by
  wct_ready_start 542 16 30
  wct_cases [239503,239508,239513,239515,239517,239521,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 38 239503 16
  · wct_piece 38 239508 17
  · wct_piece 38 239513 18
  · wct_piece 38 239515 19
  · wct_piece 38 239517 20
  · wct_piece 38 239521 21
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine543_ready : RoutineReady ⟨543, by decide⟩ routine543 := by
  wct_ready_start 543 16 31
  wct_cases [239522,239527,239532,239534,239536,239540,4219,4224,4228,2481,1301,862,867]
  · wct_piece 38 239522 22
  · wct_piece 38 239527 23
  · wct_piece 38 239532 24
  · wct_piece 38 239534 25
  · wct_piece 38 239536 26
  · wct_piece 38 239540 27
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage16 (rank : Fin 728) (hlo : 512 ≤ rank.val) (hhi : rank.val < 544) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 512 ≤ n at hlo
  change n < 544 at hhi
  interval_cases n
  · exact ⟨routine512, routine512_ready⟩
  · exact ⟨routine513, routine513_ready⟩
  · exact ⟨routine514, routine514_ready⟩
  · exact ⟨routine515, routine515_ready⟩
  · exact ⟨routine516, routine516_ready⟩
  · exact ⟨routine517, routine517_ready⟩
  · exact ⟨routine518, routine518_ready⟩
  · exact ⟨routine519, routine519_ready⟩
  · exact ⟨routine520, routine520_ready⟩
  · exact ⟨routine521, routine521_ready⟩
  · exact ⟨routine522, routine522_ready⟩
  · exact ⟨routine523, routine523_ready⟩
  · exact ⟨routine524, routine524_ready⟩
  · exact ⟨routine525, routine525_ready⟩
  · exact ⟨routine526, routine526_ready⟩
  · exact ⟨routine527, routine527_ready⟩
  · exact ⟨routine528, routine528_ready⟩
  · exact ⟨routine529, routine529_ready⟩
  · exact ⟨routine530, routine530_ready⟩
  · exact ⟨routine531, routine531_ready⟩
  · exact ⟨routine532, routine532_ready⟩
  · exact ⟨routine533, routine533_ready⟩
  · exact ⟨routine534, routine534_ready⟩
  · exact ⟨routine535, routine535_ready⟩
  · exact ⟨routine536, routine536_ready⟩
  · exact ⟨routine537, routine537_ready⟩
  · exact ⟨routine538, routine538_ready⟩
  · exact ⟨routine539, routine539_ready⟩
  · exact ⟨routine540, routine540_ready⟩
  · exact ⟨routine541, routine541_ready⟩
  · exact ⟨routine542, routine542_ready⟩
  · exact ⟨routine543, routine543_ready⟩
end W9Machine.Chain
end
