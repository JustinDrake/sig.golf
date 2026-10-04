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
def routine640 : ChainRoutine := ⟨640, [2, 1, 1, 0, 1, 0, 1], [piece240766, piece240771, piece240773, piece240778, piece240783, piece240787, piece240792, piece240796, piece862, piece867]⟩
def routine641 : ChainRoutine := ⟨641, [2, 1, 1, 0, 1, 1, 0], [piece240797, piece240802, piece240804, piece240809, piece240814, piece240818, piece240823, piece240828, piece240832, piece945]⟩
def routine642 : ChainRoutine := ⟨642, [2, 1, 1, 0, 2, 0, 0], [piece240833, piece240838, piece240840, piece240845, piece240850, piece240854, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine643 : ChainRoutine := ⟨643, [2, 1, 1, 1, 0, 0, 1], [piece240855, piece240860, piece240862, piece240867, piece236068, piece236073, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine644 : ChainRoutine := ⟨644, [2, 1, 1, 1, 0, 1, 0], [piece240868, piece240873, piece240875, piece240880, piece240885, piece240890, piece240894, piece240899, piece240903, piece945]⟩
def routine645 : ChainRoutine := ⟨645, [2, 1, 1, 1, 1, 0, 0], [piece240904, piece240909, piece240911, piece240916, piece236109, piece236114, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine646 : ChainRoutine := ⟨646, [2, 1, 1, 2, 0, 0, 0], [piece240917, piece240922, piece240924, piece240929, piece236125, piece236130, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine647 : ChainRoutine := ⟨647, [2, 1, 2, 0, 0, 0, 1], [piece240930, piece240935, piece240937, piece240942, piece236141, piece236146, piece236148, piece236152, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine648 : ChainRoutine := ⟨648, [2, 1, 2, 0, 0, 1, 0], [piece240943, piece240948, piece240950, piece240955, piece240960, piece240962, piece240966, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine649 : ChainRoutine := ⟨649, [2, 1, 2, 0, 1, 0, 0], [piece240967, piece240972, piece240974, piece240979, piece240984, piece240986, piece240990, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine650 : ChainRoutine := ⟨650, [2, 1, 2, 1, 0, 0, 0], [piece240991, piece240996, piece240998, piece241003, piece236207, piece236212, piece236215, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine651 : ChainRoutine := ⟨651, [2, 1, 3, 0, 0, 0, 0], [piece241004, piece241009, piece241011, piece241016, piece236226, piece236231, piece236233, piece236235, piece236239, piece2866, piece1502, piece945]⟩
def routine652 : ChainRoutine := ⟨652, [2, 2, 0, 0, 0, 0, 2], [piece241017, piece241022, piece241024, piece241029, piece241031, piece241035, piece239426, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine653 : ChainRoutine := ⟨653, [2, 2, 0, 0, 0, 1, 1], [piece241036, piece241041, piece241043, piece241048, piece241050, piece241054, piece239445, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine654 : ChainRoutine := ⟨654, [2, 2, 0, 0, 0, 2, 0], [piece241055, piece241060, piece241062, piece241067, piece241069, piece241073, piece239464, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine655 : ChainRoutine := ⟨655, [2, 2, 0, 0, 1, 0, 1], [piece241074, piece241079, piece241081, piece241086, piece241088, piece241092, piece4165, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine656 : ChainRoutine := ⟨656, [2, 2, 0, 0, 1, 1, 0], [piece241093, piece241098, piece241100, piece241105, piece241107, piece241111, piece4184, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine657 : ChainRoutine := ⟨657, [2, 2, 0, 0, 2, 0, 0], [piece241112, piece241117, piece241119, piece241124, piece241126, piece241130, piece239521, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine658 : ChainRoutine := ⟨658, [2, 2, 0, 1, 0, 0, 1], [piece241131, piece241136, piece241138, piece241143, piece241145, piece241149, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine659 : ChainRoutine := ⟨659, [2, 2, 0, 1, 0, 1, 0], [piece241150, piece241155, piece241157, piece241162, piece241164, piece241168, piece241173, piece241177, piece241182, piece241186]⟩
def routine660 : ChainRoutine := ⟨660, [2, 2, 0, 1, 1, 0, 0], [piece241192, piece241197, piece241199, piece241204, piece241206, piece241210, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine661 : ChainRoutine := ⟨661, [2, 2, 0, 2, 0, 0, 0], [piece241211, piece241216, piece241218, piece241223, piece241225, piece241229, piece239620, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine662 : ChainRoutine := ⟨662, [2, 2, 1, 0, 0, 0, 1], [piece241230, piece241235, piece241237, piece241242, piece241245, piece239636, piece239641, piece239645, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine663 : ChainRoutine := ⟨663, [2, 2, 1, 0, 0, 1, 0], [piece241246, piece241251, piece241253, piece241258, piece241261, piece241266, piece241270, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine664 : ChainRoutine := ⟨664, [2, 2, 1, 0, 1, 0, 0], [piece241271, piece241276, piece241278, piece241283, piece241286, piece241291, piece241295, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine665 : ChainRoutine := ⟨665, [2, 2, 1, 1, 0, 0, 0], [piece241296, piece241301, piece241303, piece241308, piece241311, piece239711, piece239716, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine666 : ChainRoutine := ⟨666, [2, 2, 2, 0, 0, 0, 0], [piece241312, piece241317, piece241319, piece241324, piece241327, piece239732, piece239737, piece239739, piece239743, piece236239, piece2866, piece1502, piece945]⟩
def routine667 : ChainRoutine := ⟨667, [2, 3, 0, 0, 0, 0, 1], [piece241328, piece241333, piece241335, piece241340, piece241342, piece241344, piece241348, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine668 : ChainRoutine := ⟨668, [2, 3, 0, 0, 0, 1, 0], [piece241349, piece241354, piece241356, piece241361, piece241363, piece241365, piece241369, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine669 : ChainRoutine := ⟨669, [2, 3, 0, 0, 1, 0, 0], [piece241370, piece241375, piece241377, piece241382, piece241384, piece241386, piece241390, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine670 : ChainRoutine := ⟨670, [2, 3, 0, 1, 0, 0, 0], [piece241391, piece241396, piece241398, piece241403, piece241405, piece241407, piece241411, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine671 : ChainRoutine := ⟨671, [2, 3, 1, 0, 0, 0, 0], [piece241412, piece241417, piece241419, piece241424, piece241426, piece241429, piece241434, piece241438, piece236239, piece2866, piece1502, piece945]⟩
def routineBatch20 : List ChainRoutine := [routine640, routine641, routine642, routine643, routine644, routine645, routine646, routine647, routine648, routine649, routine650, routine651, routine652, routine653, routine654, routine655, routine656, routine657, routine658, routine659, routine660, routine661, routine662, routine663, routine664, routine665, routine666, routine667, routine668, routine669, routine670, routine671]
theorem routineBatch20_checked : (routineBatch20.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch20_checked :
    (routineBatch20.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch20_checked :
    (routineBatch20.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine640_ready : RoutineReady ⟨640, by decide⟩ routine640 := by
  wct_ready_start 640 20 0
  wct_cases [240766,240771,240773,240778,240783,240787,240792,240796,862,867]
  · wct_piece 44 240766 34
  · wct_piece 44 240771 35
  · wct_piece 44 240773 36
  · wct_piece 44 240778 37
  · wct_piece 44 240783 38
  · wct_piece 44 240787 39
  · wct_piece 44 240792 40
  · wct_piece 44 240796 41
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine641_ready : RoutineReady ⟨641, by decide⟩ routine641 := by
  wct_ready_start 641 20 1
  wct_cases [240797,240802,240804,240809,240814,240818,240823,240828,240832,945]
  · wct_piece 44 240797 42
  · wct_piece 44 240802 43
  · wct_piece 44 240804 44
  · wct_piece 44 240809 45
  · wct_piece 44 240814 46
  · wct_piece 44 240818 47
  · wct_piece 44 240823 48
  · wct_piece 44 240828 49
  · wct_piece 44 240832 50
  · wct_piece 0 945 57
theorem routine642_ready : RoutineReady ⟨642, by decide⟩ routine642 := by
  wct_ready_start 642 20 2
  wct_cases [240833,240838,240840,240845,240850,240854,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 44 240833 51
  · wct_piece 44 240838 52
  · wct_piece 44 240840 53
  · wct_piece 44 240845 54
  · wct_piece 44 240850 55
  · wct_piece 44 240854 56
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine643_ready : RoutineReady ⟨643, by decide⟩ routine643 := by
  wct_ready_start 643 20 3
  wct_cases [240855,240860,240862,240867,236068,236073,4219,4224,4228,2481,1301,862,867]
  · wct_piece 44 240855 57
  · wct_piece 44 240860 58
  · wct_piece 44 240862 59
  · wct_piece 44 240867 60
  · wct_piece 23 236068 47
  · wct_piece 23 236073 48
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine644_ready : RoutineReady ⟨644, by decide⟩ routine644 := by
  wct_ready_start 644 20 4
  wct_cases [240868,240873,240875,240880,240885,240890,240894,240899,240903,945]
  · wct_piece 44 240868 61
  · wct_piece 44 240873 62
  · wct_piece 44 240875 63
  · wct_piece 45 240880 0
  · wct_piece 45 240885 1
  · wct_piece 45 240890 2
  · wct_piece 45 240894 3
  · wct_piece 45 240899 4
  · wct_piece 45 240903 5
  · wct_piece 0 945 57
theorem routine645_ready : RoutineReady ⟨645, by decide⟩ routine645 := by
  wct_ready_start 645 20 5
  wct_cases [240904,240909,240911,240916,236109,236114,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 45 240904 6
  · wct_piece 45 240909 7
  · wct_piece 45 240911 8
  · wct_piece 45 240916 9
  · wct_piece 23 236109 59
  · wct_piece 23 236114 60
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine646_ready : RoutineReady ⟨646, by decide⟩ routine646 := by
  wct_ready_start 646 20 6
  wct_cases [240917,240922,240924,240929,236125,236130,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 45 240917 10
  · wct_piece 45 240922 11
  · wct_piece 45 240924 12
  · wct_piece 45 240929 13
  · wct_piece 24 236125 0
  · wct_piece 24 236130 1
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine647_ready : RoutineReady ⟨647, by decide⟩ routine647 := by
  wct_ready_start 647 20 7
  wct_cases [240930,240935,240937,240942,236141,236146,236148,236152,235565,2481,1301,862,867]
  · wct_piece 45 240930 14
  · wct_piece 45 240935 15
  · wct_piece 45 240937 16
  · wct_piece 45 240942 17
  · wct_piece 24 236141 5
  · wct_piece 24 236146 6
  · wct_piece 24 236148 7
  · wct_piece 24 236152 8
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine648_ready : RoutineReady ⟨648, by decide⟩ routine648 := by
  wct_ready_start 648 20 8
  wct_cases [240943,240948,240950,240955,240960,240962,240966,235587,2503,1320,1325,1329,945]
  · wct_piece 45 240943 18
  · wct_piece 45 240948 19
  · wct_piece 45 240950 20
  · wct_piece 45 240955 21
  · wct_piece 45 240960 22
  · wct_piece 45 240962 23
  · wct_piece 45 240966 24
  · wct_piece 21 235587 15
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine649_ready : RoutineReady ⟨649, by decide⟩ routine649 := by
  wct_ready_start 649 20 9
  wct_cases [240967,240972,240974,240979,240984,240986,240990,235609,2522,2527,2531,1502,945]
  · wct_piece 45 240967 25
  · wct_piece 45 240972 26
  · wct_piece 45 240974 27
  · wct_piece 45 240979 28
  · wct_piece 45 240984 29
  · wct_piece 45 240986 30
  · wct_piece 45 240990 31
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine650_ready : RoutineReady ⟨650, by decide⟩ routine650 := by
  wct_ready_start 650 20 10
  wct_cases [240991,240996,240998,241003,236207,236212,236215,235628,235633,235637,2866,1502,945]
  · wct_piece 45 240991 32
  · wct_piece 45 240996 33
  · wct_piece 45 240998 34
  · wct_piece 45 241003 35
  · wct_piece 24 236207 26
  · wct_piece 24 236212 27
  · wct_piece 24 236215 28
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine651_ready : RoutineReady ⟨651, by decide⟩ routine651 := by
  wct_ready_start 651 20 11
  wct_cases [241004,241009,241011,241016,236226,236231,236233,236235,236239,2866,1502,945]
  · wct_piece 45 241004 36
  · wct_piece 45 241009 37
  · wct_piece 45 241011 38
  · wct_piece 45 241016 39
  · wct_piece 24 236226 32
  · wct_piece 24 236231 33
  · wct_piece 24 236233 34
  · wct_piece 24 236235 35
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine652_ready : RoutineReady ⟨652, by decide⟩ routine652 := by
  wct_ready_start 652 20 12
  wct_cases [241017,241022,241024,241029,241031,241035,239426,4108,1937,1081,799,804,807]
  · wct_piece 45 241017 40
  · wct_piece 45 241022 41
  · wct_piece 45 241024 42
  · wct_piece 45 241029 43
  · wct_piece 45 241031 44
  · wct_piece 45 241035 45
  · wct_piece 37 239426 55
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine653_ready : RoutineReady ⟨653, by decide⟩ routine653 := by
  wct_ready_start 653 20 13
  wct_cases [241036,241041,241043,241048,241050,241054,239445,4127,1956,1097,1102,862,867]
  · wct_piece 45 241036 46
  · wct_piece 45 241041 47
  · wct_piece 45 241043 48
  · wct_piece 45 241048 49
  · wct_piece 45 241050 50
  · wct_piece 45 241054 51
  · wct_piece 37 239445 61
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine654_ready : RoutineReady ⟨654, by decide⟩ routine654 := by
  wct_ready_start 654 20 14
  wct_cases [241055,241060,241062,241067,241069,241073,239464,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 45 241055 52
  · wct_piece 45 241060 53
  · wct_piece 45 241062 54
  · wct_piece 45 241067 55
  · wct_piece 45 241069 56
  · wct_piece 45 241073 57
  · wct_piece 38 239464 3
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine655_ready : RoutineReady ⟨655, by decide⟩ routine655 := by
  wct_ready_start 655 20 15
  wct_cases [241074,241079,241081,241086,241088,241092,4165,1991,1996,2000,1301,862,867]
  · wct_piece 45 241074 58
  · wct_piece 45 241079 59
  · wct_piece 45 241081 60
  · wct_piece 45 241086 61
  · wct_piece 45 241088 62
  · wct_piece 45 241092 63
  · wct_piece 15 4165 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine656_ready : RoutineReady ⟨656, by decide⟩ routine656 := by
  wct_ready_start 656 20 16
  wct_cases [241093,241098,241100,241105,241107,241111,4184,2016,2021,1320,1325,1329,945]
  · wct_piece 46 241093 0
  · wct_piece 46 241098 1
  · wct_piece 46 241100 2
  · wct_piece 46 241105 3
  · wct_piece 46 241107 4
  · wct_piece 46 241111 5
  · wct_piece 15 4184 57
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine657_ready : RoutineReady ⟨657, by decide⟩ routine657 := by
  wct_ready_start 657 20 17
  wct_cases [241112,241117,241119,241124,241126,241130,239521,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 46 241112 6
  · wct_piece 46 241117 7
  · wct_piece 46 241119 8
  · wct_piece 46 241124 9
  · wct_piece 46 241126 10
  · wct_piece 46 241130 11
  · wct_piece 38 239521 21
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine658_ready : RoutineReady ⟨658, by decide⟩ routine658 := by
  wct_ready_start 658 20 18
  wct_cases [241131,241136,241138,241143,241145,241149,4219,4224,4228,2481,1301,862,867]
  · wct_piece 46 241131 12
  · wct_piece 46 241136 13
  · wct_piece 46 241138 14
  · wct_piece 46 241143 15
  · wct_piece 46 241145 16
  · wct_piece 46 241149 17
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine659_ready : RoutineReady ⟨659, by decide⟩ routine659 := by
  wct_ready_start 659 20 19
  wct_cases [241150,241155,241157,241162,241164,241168,241173,241177,241182,241186]
  · wct_piece 46 241150 18
  · wct_piece 46 241155 19
  · wct_piece 46 241157 20
  · wct_piece 46 241162 21
  · wct_piece 46 241164 22
  · wct_piece 46 241168 23
  · wct_piece 46 241173 24
  · wct_piece 46 241177 25
  · wct_piece 46 241182 26
  · wct_piece 46 241186 27
theorem routine660_ready : RoutineReady ⟨660, by decide⟩ routine660 := by
  wct_ready_start 660 20 20
  wct_cases [241192,241197,241199,241204,241206,241210,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 46 241192 28
  · wct_piece 46 241197 29
  · wct_piece 46 241199 30
  · wct_piece 46 241204 31
  · wct_piece 46 241206 32
  · wct_piece 46 241210 33
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine661_ready : RoutineReady ⟨661, by decide⟩ routine661 := by
  wct_ready_start 661 20 21
  wct_cases [241211,241216,241218,241223,241225,241229,239620,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 46 241211 34
  · wct_piece 46 241216 35
  · wct_piece 46 241218 36
  · wct_piece 46 241223 37
  · wct_piece 46 241225 38
  · wct_piece 46 241229 39
  · wct_piece 38 239620 49
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine662_ready : RoutineReady ⟨662, by decide⟩ routine662 := by
  wct_ready_start 662 20 22
  wct_cases [241230,241235,241237,241242,241245,239636,239641,239645,235565,2481,1301,862,867]
  · wct_piece 46 241230 40
  · wct_piece 46 241235 41
  · wct_piece 46 241237 42
  · wct_piece 46 241242 43
  · wct_piece 46 241245 44
  · wct_piece 38 239636 54
  · wct_piece 38 239641 55
  · wct_piece 38 239645 56
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine663_ready : RoutineReady ⟨663, by decide⟩ routine663 := by
  wct_ready_start 663 20 23
  wct_cases [241246,241251,241253,241258,241261,241266,241270,2503,1320,1325,1329,945]
  · wct_piece 46 241246 45
  · wct_piece 46 241251 46
  · wct_piece 46 241253 47
  · wct_piece 46 241258 48
  · wct_piece 46 241261 49
  · wct_piece 46 241266 50
  · wct_piece 46 241270 51
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine664_ready : RoutineReady ⟨664, by decide⟩ routine664 := by
  wct_ready_start 664 20 24
  wct_cases [241271,241276,241278,241283,241286,241291,241295,2522,2527,2531,1502,945]
  · wct_piece 46 241271 52
  · wct_piece 46 241276 53
  · wct_piece 46 241278 54
  · wct_piece 46 241283 55
  · wct_piece 46 241286 56
  · wct_piece 46 241291 57
  · wct_piece 46 241295 58
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine665_ready : RoutineReady ⟨665, by decide⟩ routine665 := by
  wct_ready_start 665 20 25
  wct_cases [241296,241301,241303,241308,241311,239711,239716,235628,235633,235637,2866,1502,945]
  · wct_piece 46 241296 59
  · wct_piece 46 241301 60
  · wct_piece 46 241303 61
  · wct_piece 46 241308 62
  · wct_piece 46 241311 63
  · wct_piece 39 239711 11
  · wct_piece 39 239716 12
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine666_ready : RoutineReady ⟨666, by decide⟩ routine666 := by
  wct_ready_start 666 20 26
  wct_cases [241312,241317,241319,241324,241327,239732,239737,239739,239743,236239,2866,1502,945]
  · wct_piece 47 241312 0
  · wct_piece 47 241317 1
  · wct_piece 47 241319 2
  · wct_piece 47 241324 3
  · wct_piece 47 241327 4
  · wct_piece 39 239732 17
  · wct_piece 39 239737 18
  · wct_piece 39 239739 19
  · wct_piece 39 239743 20
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine667_ready : RoutineReady ⟨667, by decide⟩ routine667 := by
  wct_ready_start 667 20 27
  wct_cases [241328,241333,241335,241340,241342,241344,241348,235565,2481,1301,862,867]
  · wct_piece 47 241328 5
  · wct_piece 47 241333 6
  · wct_piece 47 241335 7
  · wct_piece 47 241340 8
  · wct_piece 47 241342 9
  · wct_piece 47 241344 10
  · wct_piece 47 241348 11
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine668_ready : RoutineReady ⟨668, by decide⟩ routine668 := by
  wct_ready_start 668 20 28
  wct_cases [241349,241354,241356,241361,241363,241365,241369,235587,2503,1320,1325,1329,945]
  · wct_piece 47 241349 12
  · wct_piece 47 241354 13
  · wct_piece 47 241356 14
  · wct_piece 47 241361 15
  · wct_piece 47 241363 16
  · wct_piece 47 241365 17
  · wct_piece 47 241369 18
  · wct_piece 21 235587 15
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine669_ready : RoutineReady ⟨669, by decide⟩ routine669 := by
  wct_ready_start 669 20 29
  wct_cases [241370,241375,241377,241382,241384,241386,241390,235609,2522,2527,2531,1502,945]
  · wct_piece 47 241370 19
  · wct_piece 47 241375 20
  · wct_piece 47 241377 21
  · wct_piece 47 241382 22
  · wct_piece 47 241384 23
  · wct_piece 47 241386 24
  · wct_piece 47 241390 25
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine670_ready : RoutineReady ⟨670, by decide⟩ routine670 := by
  wct_ready_start 670 20 30
  wct_cases [241391,241396,241398,241403,241405,241407,241411,235628,235633,235637,2866,1502,945]
  · wct_piece 47 241391 26
  · wct_piece 47 241396 27
  · wct_piece 47 241398 28
  · wct_piece 47 241403 29
  · wct_piece 47 241405 30
  · wct_piece 47 241407 31
  · wct_piece 47 241411 32
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine671_ready : RoutineReady ⟨671, by decide⟩ routine671 := by
  wct_ready_start 671 20 31
  wct_cases [241412,241417,241419,241424,241426,241429,241434,241438,236239,2866,1502,945]
  · wct_piece 47 241412 33
  · wct_piece 47 241417 34
  · wct_piece 47 241419 35
  · wct_piece 47 241424 36
  · wct_piece 47 241426 37
  · wct_piece 47 241429 38
  · wct_piece 47 241434 39
  · wct_piece 47 241438 40
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage20 (rank : Fin 728) (hlo : 640 ≤ rank.val) (hhi : rank.val < 672) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 640 ≤ n at hlo
  change n < 672 at hhi
  interval_cases n
  · exact ⟨routine640, routine640_ready⟩
  · exact ⟨routine641, routine641_ready⟩
  · exact ⟨routine642, routine642_ready⟩
  · exact ⟨routine643, routine643_ready⟩
  · exact ⟨routine644, routine644_ready⟩
  · exact ⟨routine645, routine645_ready⟩
  · exact ⟨routine646, routine646_ready⟩
  · exact ⟨routine647, routine647_ready⟩
  · exact ⟨routine648, routine648_ready⟩
  · exact ⟨routine649, routine649_ready⟩
  · exact ⟨routine650, routine650_ready⟩
  · exact ⟨routine651, routine651_ready⟩
  · exact ⟨routine652, routine652_ready⟩
  · exact ⟨routine653, routine653_ready⟩
  · exact ⟨routine654, routine654_ready⟩
  · exact ⟨routine655, routine655_ready⟩
  · exact ⟨routine656, routine656_ready⟩
  · exact ⟨routine657, routine657_ready⟩
  · exact ⟨routine658, routine658_ready⟩
  · exact ⟨routine659, routine659_ready⟩
  · exact ⟨routine660, routine660_ready⟩
  · exact ⟨routine661, routine661_ready⟩
  · exact ⟨routine662, routine662_ready⟩
  · exact ⟨routine663, routine663_ready⟩
  · exact ⟨routine664, routine664_ready⟩
  · exact ⟨routine665, routine665_ready⟩
  · exact ⟨routine666, routine666_ready⟩
  · exact ⟨routine667, routine667_ready⟩
  · exact ⟨routine668, routine668_ready⟩
  · exact ⟨routine669, routine669_ready⟩
  · exact ⟨routine670, routine670_ready⟩
  · exact ⟨routine671, routine671_ready⟩
end W9Machine.Chain
end
