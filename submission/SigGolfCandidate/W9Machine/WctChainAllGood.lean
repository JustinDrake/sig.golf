import SigGolfCandidate.W9Machine.WctRoutineModel
import SigGolfCandidate.W9Machine.WctChainCheck12
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence
import SigGolfCandidate.W9Machine.WctReadyCheck18
import SigGolfCandidate.W9Machine.WctReadyCheck07
import SigGolfCandidate.W9Machine.WctReadyCheck06
import SigGolfCandidate.W9Machine.WctReadyCheck05
import SigGolfCandidate.W9Machine.WctReadyCheck04
import SigGolfCandidate.W9Machine.WctReadyCheck03
import SigGolfCandidate.W9Machine.WctReadyCheck02
import SigGolfCandidate.W9Machine.WctReadyCheck01
import SigGolfCandidate.W9Machine.WctCoverage08
import SigGolfCandidate.W9Machine.WctCoverage09
import SigGolfCandidate.W9Machine.WctCoverage10
import SigGolfCandidate.W9Machine.WctCoverage11
import SigGolfCandidate.W9Machine.WctCoverage12
import SigGolfCandidate.W9Machine.WctCoverage13
import SigGolfCandidate.W9Machine.WctCoverage14
import SigGolfCandidate.W9Machine.WctCoverage15
import SigGolfCandidate.W9Machine.WctCoverage16
import SigGolfCandidate.W9Machine.WctCoverage17
import SigGolfCandidate.W9Machine.WctCoverage19
import SigGolfCandidate.W9Machine.WctCoverage20
import SigGolfCandidate.W9Machine.WctCoverage21
import SigGolfCandidate.W9Machine.WctChainAssembly

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine704 : ChainRoutine := ⟨704, [3, 0, 2, 0, 1, 0, 0], [piece241759, piece241764, piece241766, piece241768, piece236185, piece236190, piece236192, piece236196, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine705 : ChainRoutine := ⟨705, [3, 0, 2, 1, 0, 0, 0], [piece241769, piece241774, piece241776, piece241778, piece236207, piece236212, piece236215, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine706 : ChainRoutine := ⟨706, [3, 0, 3, 0, 0, 0, 0], [piece241779, piece241784, piece241786, piece241788, piece236226, piece236231, piece236233, piece236235, piece236239, piece2866, piece1502, piece945]⟩
def routine707 : ChainRoutine := ⟨707, [3, 1, 0, 0, 0, 0, 2], [piece241789, piece241794, piece241796, piece241798, piece241803, piece241807, piece239426, piece4108, piece1937, piece1081, piece799, piece804, piece807]⟩
def routine708 : ChainRoutine := ⟨708, [3, 1, 0, 0, 0, 1, 1], [piece241808, piece241813, piece241815, piece241817, piece241822, piece241826, piece239445, piece4127, piece1956, piece1097, piece1102, piece862, piece867]⟩
def routine709 : ChainRoutine := ⟨709, [3, 1, 0, 0, 0, 2, 0], [piece241827, piece241832, piece241834, piece241836, piece241841, piece241845, piece239464, piece4146, piece1975, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine710 : ChainRoutine := ⟨710, [3, 1, 0, 0, 1, 0, 1], [piece241846, piece241851, piece241853, piece241855, piece241860, piece241864, piece4165, piece1991, piece1996, piece2000, piece1301, piece862, piece867]⟩
def routine711 : ChainRoutine := ⟨711, [3, 1, 0, 0, 1, 1, 0], [piece241865, piece241870, piece241872, piece241874, piece241879, piece241883, piece4184, piece2016, piece2021, piece1320, piece1325, piece1329, piece945]⟩
def routine712 : ChainRoutine := ⟨712, [3, 1, 0, 0, 2, 0, 0], [piece241884, piece241889, piece241891, piece241893, piece241898, piece241902, piece239521, piece4203, piece2037, piece2042, piece2044, piece2048, piece1502, piece945]⟩
def routine713 : ChainRoutine := ⟨713, [3, 1, 0, 1, 0, 0, 1], [piece241903, piece241908, piece241910, piece241912, piece241917, piece241921, piece4219, piece4224, piece4228, piece2481, piece1301, piece862, piece867]⟩
def routine714 : ChainRoutine := ⟨714, [3, 1, 0, 1, 0, 1, 0], [piece241922, piece241927, piece241929, piece241931, piece241936, piece241940, piece241945, piece241949, piece241954, piece241958]⟩
def routine715 : ChainRoutine := ⟨715, [3, 1, 0, 1, 1, 0, 0], [piece241964, piece241969, piece241971, piece241973, piece241978, piece241982, piece4269, piece4274, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine716 : ChainRoutine := ⟨716, [3, 1, 0, 2, 0, 0, 0], [piece241983, piece241988, piece241990, piece241992, piece241997, piece242001, piece239620, piece4290, piece4295, piece4297, piece4301, piece2866, piece1502, piece945]⟩
def routine717 : ChainRoutine := ⟨717, [3, 1, 1, 0, 0, 0, 1], [piece242002, piece242007, piece242009, piece242011, piece242016, piece239636, piece239641, piece239645, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine718 : ChainRoutine := ⟨718, [3, 1, 1, 0, 0, 1, 0], [piece242017, piece242022, piece242024, piece242026, piece242031, piece239661, piece239666, piece239670, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine719 : ChainRoutine := ⟨719, [3, 1, 1, 0, 1, 0, 0], [piece242032, piece242037, piece242039, piece242041, piece242046, piece239686, piece239691, piece239695, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine720 : ChainRoutine := ⟨720, [3, 1, 1, 1, 0, 0, 0], [piece242047, piece242052, piece242054, piece242056, piece242061, piece239711, piece239716, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine721 : ChainRoutine := ⟨721, [3, 1, 2, 0, 0, 0, 0], [piece242062, piece242067, piece242069, piece242071, piece242076, piece239732, piece239737, piece239739, piece239743, piece236239, piece2866, piece1502, piece945]⟩
def routine722 : ChainRoutine := ⟨722, [3, 2, 0, 0, 0, 0, 1], [piece242077, piece242082, piece242084, piece242086, piece242091, piece242093, piece242097, piece241348, piece235565, piece2481, piece1301, piece862, piece867]⟩
def routine723 : ChainRoutine := ⟨723, [3, 2, 0, 0, 0, 1, 0], [piece242098, piece242103, piece242105, piece242107, piece242112, piece242114, piece242118, piece241369, piece235587, piece2503, piece1320, piece1325, piece1329, piece945]⟩
def routine724 : ChainRoutine := ⟨724, [3, 2, 0, 0, 1, 0, 0], [piece242119, piece242124, piece242126, piece242128, piece242133, piece242135, piece242139, piece241390, piece235609, piece2522, piece2527, piece2531, piece1502, piece945]⟩
def routine725 : ChainRoutine := ⟨725, [3, 2, 0, 1, 0, 0, 0], [piece242140, piece242145, piece242147, piece242149, piece242154, piece242156, piece242160, piece241411, piece235628, piece235633, piece235637, piece2866, piece1502, piece945]⟩
def routine726 : ChainRoutine := ⟨726, [3, 2, 1, 0, 0, 0, 0], [piece242161, piece242166, piece242168, piece242170, piece242175, piece242178, piece241429, piece241434, piece241438, piece236239, piece2866, piece1502, piece945]⟩
def routine727 : ChainRoutine := ⟨727, [3, 3, 0, 0, 0, 0, 0], [piece242179, piece242184, piece242186, piece242188, piece242193, piece242195, piece242197, piece242201, piece236239, piece2866, piece1502, piece945]⟩
def routineBatch22 : List ChainRoutine := [routine704, routine705, routine706, routine707, routine708, routine709, routine710, routine711, routine712, routine713, routine714, routine715, routine716, routine717, routine718, routine719, routine720, routine721, routine722, routine723, routine724, routine725, routine726, routine727]
theorem routineBatch22_checked : (routineBatch22.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch22_checked :
    (routineBatch22.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch22_checked :
    (routineBatch22.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine704_ready : RoutineReady ⟨704, by decide⟩ routine704 := by
  wct_ready_start 704 22 0
  wct_cases [241759,241764,241766,241768,236185,236190,236192,236196,235609,2522,2527,2531,1502,945]
  · wct_piece 49 241759 41
  · wct_piece 49 241764 42
  · wct_piece 49 241766 43
  · wct_piece 49 241768 44
  · wct_piece 24 236185 19
  · wct_piece 24 236190 20
  · wct_piece 24 236192 21
  · wct_piece 24 236196 22
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine705_ready : RoutineReady ⟨705, by decide⟩ routine705 := by
  wct_ready_start 705 22 1
  wct_cases [241769,241774,241776,241778,236207,236212,236215,235628,235633,235637,2866,1502,945]
  · wct_piece 49 241769 45
  · wct_piece 49 241774 46
  · wct_piece 49 241776 47
  · wct_piece 49 241778 48
  · wct_piece 24 236207 26
  · wct_piece 24 236212 27
  · wct_piece 24 236215 28
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine706_ready : RoutineReady ⟨706, by decide⟩ routine706 := by
  wct_ready_start 706 22 2
  wct_cases [241779,241784,241786,241788,236226,236231,236233,236235,236239,2866,1502,945]
  · wct_piece 49 241779 49
  · wct_piece 49 241784 50
  · wct_piece 49 241786 51
  · wct_piece 49 241788 52
  · wct_piece 24 236226 32
  · wct_piece 24 236231 33
  · wct_piece 24 236233 34
  · wct_piece 24 236235 35
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine707_ready : RoutineReady ⟨707, by decide⟩ routine707 := by
  wct_ready_start 707 22 3
  wct_cases [241789,241794,241796,241798,241803,241807,239426,4108,1937,1081,799,804,807]
  · wct_piece 49 241789 53
  · wct_piece 49 241794 54
  · wct_piece 49 241796 55
  · wct_piece 49 241798 56
  · wct_piece 49 241803 57
  · wct_piece 49 241807 58
  · wct_piece 37 239426 55
  · wct_piece 15 4108 33
  · wct_piece 5 1937 31
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine708_ready : RoutineReady ⟨708, by decide⟩ routine708 := by
  wct_ready_start 708 22 4
  wct_cases [241808,241813,241815,241817,241822,241826,239445,4127,1956,1097,1102,862,867]
  · wct_piece 49 241808 59
  · wct_piece 49 241813 60
  · wct_piece 49 241815 61
  · wct_piece 49 241817 62
  · wct_piece 49 241822 63
  · wct_piece 50 241826 0
  · wct_piece 37 239445 61
  · wct_piece 15 4127 39
  · wct_piece 5 1956 37
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine709_ready : RoutineReady ⟨709, by decide⟩ routine709 := by
  wct_ready_start 709 22 5
  wct_cases [241827,241832,241834,241836,241841,241845,239464,4146,1975,1118,1123,1125,1129,945]
  · wct_piece 50 241827 1
  · wct_piece 50 241832 2
  · wct_piece 50 241834 3
  · wct_piece 50 241836 4
  · wct_piece 50 241841 5
  · wct_piece 50 241845 6
  · wct_piece 38 239464 3
  · wct_piece 15 4146 45
  · wct_piece 5 1975 43
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine710_ready : RoutineReady ⟨710, by decide⟩ routine710 := by
  wct_ready_start 710 22 6
  wct_cases [241846,241851,241853,241855,241860,241864,4165,1991,1996,2000,1301,862,867]
  · wct_piece 50 241846 7
  · wct_piece 50 241851 8
  · wct_piece 50 241853 9
  · wct_piece 50 241855 10
  · wct_piece 50 241860 11
  · wct_piece 50 241864 12
  · wct_piece 15 4165 51
  · wct_piece 5 1991 48
  · wct_piece 5 1996 49
  · wct_piece 5 2000 50
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine711_ready : RoutineReady ⟨711, by decide⟩ routine711 := by
  wct_ready_start 711 22 7
  wct_cases [241865,241870,241872,241874,241879,241883,4184,2016,2021,1320,1325,1329,945]
  · wct_piece 50 241865 13
  · wct_piece 50 241870 14
  · wct_piece 50 241872 15
  · wct_piece 50 241874 16
  · wct_piece 50 241879 17
  · wct_piece 50 241883 18
  · wct_piece 15 4184 57
  · wct_piece 5 2016 55
  · wct_piece 5 2021 56
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine712_ready : RoutineReady ⟨712, by decide⟩ routine712 := by
  wct_ready_start 712 22 8
  wct_cases [241884,241889,241891,241893,241898,241902,239521,4203,2037,2042,2044,2048,1502,945]
  · wct_piece 50 241884 19
  · wct_piece 50 241889 20
  · wct_piece 50 241891 21
  · wct_piece 50 241893 22
  · wct_piece 50 241898 23
  · wct_piece 50 241902 24
  · wct_piece 38 239521 21
  · wct_piece 15 4203 63
  · wct_piece 5 2037 61
  · wct_piece 5 2042 62
  · wct_piece 5 2044 63
  · wct_piece 6 2048 0
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine713_ready : RoutineReady ⟨713, by decide⟩ routine713 := by
  wct_ready_start 713 22 9
  wct_cases [241903,241908,241910,241912,241917,241921,4219,4224,4228,2481,1301,862,867]
  · wct_piece 50 241903 25
  · wct_piece 50 241908 26
  · wct_piece 50 241910 27
  · wct_piece 50 241912 28
  · wct_piece 50 241917 29
  · wct_piece 50 241921 30
  · wct_piece 16 4219 4
  · wct_piece 16 4224 5
  · wct_piece 16 4228 6
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine714_ready : RoutineReady ⟨714, by decide⟩ routine714 := by
  wct_ready_start 714 22 10
  wct_cases [241922,241927,241929,241931,241936,241940,241945,241949,241954,241958]
  · wct_piece 50 241922 31
  · wct_piece 50 241927 32
  · wct_piece 50 241929 33
  · wct_piece 50 241931 34
  · wct_piece 50 241936 35
  · wct_piece 50 241940 36
  · wct_piece 50 241945 37
  · wct_piece 50 241949 38
  · wct_piece 50 241954 39
  · wct_piece 50 241958 40
theorem routine715_ready : RoutineReady ⟨715, by decide⟩ routine715 := by
  wct_ready_start 715 22 11
  wct_cases [241964,241969,241971,241973,241978,241982,4269,4274,2522,2527,2531,1502,945]
  · wct_piece 50 241964 41
  · wct_piece 50 241969 42
  · wct_piece 50 241971 43
  · wct_piece 50 241973 44
  · wct_piece 50 241978 45
  · wct_piece 50 241982 46
  · wct_piece 16 4269 18
  · wct_piece 16 4274 19
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine716_ready : RoutineReady ⟨716, by decide⟩ routine716 := by
  wct_ready_start 716 22 12
  wct_cases [241983,241988,241990,241992,241997,242001,239620,4290,4295,4297,4301,2866,1502,945]
  · wct_piece 50 241983 47
  · wct_piece 50 241988 48
  · wct_piece 50 241990 49
  · wct_piece 50 241992 50
  · wct_piece 50 241997 51
  · wct_piece 50 242001 52
  · wct_piece 38 239620 49
  · wct_piece 16 4290 24
  · wct_piece 16 4295 25
  · wct_piece 16 4297 26
  · wct_piece 16 4301 27
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine717_ready : RoutineReady ⟨717, by decide⟩ routine717 := by
  wct_ready_start 717 22 13
  wct_cases [242002,242007,242009,242011,242016,239636,239641,239645,235565,2481,1301,862,867]
  · wct_piece 50 242002 53
  · wct_piece 50 242007 54
  · wct_piece 50 242009 55
  · wct_piece 50 242011 56
  · wct_piece 50 242016 57
  · wct_piece 38 239636 54
  · wct_piece 38 239641 55
  · wct_piece 38 239645 56
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine718_ready : RoutineReady ⟨718, by decide⟩ routine718 := by
  wct_ready_start 718 22 14
  wct_cases [242017,242022,242024,242026,242031,239661,239666,239670,2503,1320,1325,1329,945]
  · wct_piece 50 242017 58
  · wct_piece 50 242022 59
  · wct_piece 50 242024 60
  · wct_piece 50 242026 61
  · wct_piece 50 242031 62
  · wct_piece 38 239661 61
  · wct_piece 38 239666 62
  · wct_piece 38 239670 63
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine719_ready : RoutineReady ⟨719, by decide⟩ routine719 := by
  wct_ready_start 719 22 15
  wct_cases [242032,242037,242039,242041,242046,239686,239691,239695,2522,2527,2531,1502,945]
  · wct_piece 50 242032 63
  · wct_piece 51 242037 0
  · wct_piece 51 242039 1
  · wct_piece 51 242041 2
  · wct_piece 51 242046 3
  · wct_piece 39 239686 4
  · wct_piece 39 239691 5
  · wct_piece 39 239695 6
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine720_ready : RoutineReady ⟨720, by decide⟩ routine720 := by
  wct_ready_start 720 22 16
  wct_cases [242047,242052,242054,242056,242061,239711,239716,235628,235633,235637,2866,1502,945]
  · wct_piece 51 242047 4
  · wct_piece 51 242052 5
  · wct_piece 51 242054 6
  · wct_piece 51 242056 7
  · wct_piece 51 242061 8
  · wct_piece 39 239711 11
  · wct_piece 39 239716 12
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine721_ready : RoutineReady ⟨721, by decide⟩ routine721 := by
  wct_ready_start 721 22 17
  wct_cases [242062,242067,242069,242071,242076,239732,239737,239739,239743,236239,2866,1502,945]
  · wct_piece 51 242062 9
  · wct_piece 51 242067 10
  · wct_piece 51 242069 11
  · wct_piece 51 242071 12
  · wct_piece 51 242076 13
  · wct_piece 39 239732 17
  · wct_piece 39 239737 18
  · wct_piece 39 239739 19
  · wct_piece 39 239743 20
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine722_ready : RoutineReady ⟨722, by decide⟩ routine722 := by
  wct_ready_start 722 22 18
  wct_cases [242077,242082,242084,242086,242091,242093,242097,241348,235565,2481,1301,862,867]
  · wct_piece 51 242077 14
  · wct_piece 51 242082 15
  · wct_piece 51 242084 16
  · wct_piece 51 242086 17
  · wct_piece 51 242091 18
  · wct_piece 51 242093 19
  · wct_piece 51 242097 20
  · wct_piece 47 241348 11
  · wct_piece 21 235565 8
  · wct_piece 8 2481 4
  · wct_piece 2 1301 33
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine723_ready : RoutineReady ⟨723, by decide⟩ routine723 := by
  wct_ready_start 723 22 19
  wct_cases [242098,242103,242105,242107,242112,242114,242118,241369,235587,2503,1320,1325,1329,945]
  · wct_piece 51 242098 21
  · wct_piece 51 242103 22
  · wct_piece 51 242105 23
  · wct_piece 51 242107 24
  · wct_piece 51 242112 25
  · wct_piece 51 242114 26
  · wct_piece 51 242118 27
  · wct_piece 47 241369 18
  · wct_piece 21 235587 15
  · wct_piece 8 2503 11
  · wct_piece 2 1320 39
  · wct_piece 2 1325 40
  · wct_piece 2 1329 41
  · wct_piece 0 945 57
theorem routine724_ready : RoutineReady ⟨724, by decide⟩ routine724 := by
  wct_ready_start 724 22 20
  wct_cases [242119,242124,242126,242128,242133,242135,242139,241390,235609,2522,2527,2531,1502,945]
  · wct_piece 51 242119 28
  · wct_piece 51 242124 29
  · wct_piece 51 242126 30
  · wct_piece 51 242128 31
  · wct_piece 51 242133 32
  · wct_piece 51 242135 33
  · wct_piece 51 242139 34
  · wct_piece 47 241390 25
  · wct_piece 21 235609 22
  · wct_piece 8 2522 17
  · wct_piece 8 2527 18
  · wct_piece 8 2531 19
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine725_ready : RoutineReady ⟨725, by decide⟩ routine725 := by
  wct_ready_start 725 22 21
  wct_cases [242140,242145,242147,242149,242154,242156,242160,241411,235628,235633,235637,2866,1502,945]
  · wct_piece 51 242140 35
  · wct_piece 51 242145 36
  · wct_piece 51 242147 37
  · wct_piece 51 242149 38
  · wct_piece 51 242154 39
  · wct_piece 51 242156 40
  · wct_piece 51 242160 41
  · wct_piece 47 241411 32
  · wct_piece 21 235628 28
  · wct_piece 21 235633 29
  · wct_piece 21 235637 30
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine726_ready : RoutineReady ⟨726, by decide⟩ routine726 := by
  wct_ready_start 726 22 22
  wct_cases [242161,242166,242168,242170,242175,242178,241429,241434,241438,236239,2866,1502,945]
  · wct_piece 51 242161 42
  · wct_piece 51 242166 43
  · wct_piece 51 242168 44
  · wct_piece 51 242170 45
  · wct_piece 51 242175 46
  · wct_piece 51 242178 47
  · wct_piece 47 241429 38
  · wct_piece 47 241434 39
  · wct_piece 47 241438 40
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
theorem routine727_ready : RoutineReady ⟨727, by decide⟩ routine727 := by
  wct_ready_start 727 22 23
  wct_cases [242179,242184,242186,242188,242193,242195,242197,242201,236239,2866,1502,945]
  · wct_piece 51 242179 48
  · wct_piece 51 242184 49
  · wct_piece 51 242186 50
  · wct_piece 51 242188 51
  · wct_piece 51 242193 52
  · wct_piece 51 242195 53
  · wct_piece 51 242197 54
  · wct_piece 51 242201 55
  · wct_piece 24 236239 36
  · wct_piece 10 2866 2
  · wct_piece 3 1502 34
  · wct_piece 0 945 57
end W9Machine.Chain
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine0 : ChainRoutine := ⟨0, [0, 0, 0, 0, 0, 3, 3], [piece744, piece749, piece751, piece754, piece759, piece761, piece764]⟩
def routine1 : ChainRoutine := ⟨1, [0, 0, 0, 0, 1, 2, 3], [piece770, piece775, piece780, piece783, piece754, piece759, piece761, piece764]⟩
def routine2 : ChainRoutine := ⟨2, [0, 0, 0, 0, 1, 3, 2], [piece784, piece789, piece794, piece796, piece799, piece804, piece807]⟩
def routine3 : ChainRoutine := ⟨3, [0, 0, 0, 0, 2, 1, 3], [piece813, piece818, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine4 : ChainRoutine := ⟨4, [0, 0, 0, 0, 2, 2, 2], [piece827, piece832, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine5 : ChainRoutine := ⟨5, [0, 0, 0, 0, 2, 3, 1], [piece844, piece849, piece852, piece857, piece859, piece862, piece867]⟩
def routine6 : ChainRoutine := ⟨6, [0, 0, 0, 0, 3, 0, 3], [piece873, piece878, piece880, piece882, piece886, piece754, piece759, piece761, piece764]⟩
def routine7 : ChainRoutine := ⟨7, [0, 0, 0, 0, 3, 1, 2], [piece887, piece892, piece894, piece897, piece902, piece799, piece804, piece807]⟩
def routine8 : ChainRoutine := ⟨8, [0, 0, 0, 0, 3, 2, 1], [piece903, piece908, piece910, piece913, piece918, piece921, piece862, piece867]⟩
def routine9 : ChainRoutine := ⟨9, [0, 0, 0, 0, 3, 3, 0], [piece922, piece927, piece929, piece932, piece937, piece939, piece941, piece945]⟩
def routine10 : ChainRoutine := ⟨10, [0, 0, 0, 1, 0, 2, 3], [piece951, piece956, piece960, piece775, piece780, piece783, piece754, piece759, piece761, piece764]⟩
def routine11 : ChainRoutine := ⟨11, [0, 0, 0, 1, 0, 3, 2], [piece961, piece966, piece970, piece789, piece794, piece796, piece799, piece804, piece807]⟩
def routine12 : ChainRoutine := ⟨12, [0, 0, 0, 1, 1, 1, 3], [piece971, piece976, piece981, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine13 : ChainRoutine := ⟨13, [0, 0, 0, 1, 1, 2, 2], [piece982, piece987, piece992, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine14 : ChainRoutine := ⟨14, [0, 0, 0, 1, 1, 3, 1], [piece993, piece998, piece1003, piece852, piece857, piece859, piece862, piece867]⟩
def routine15 : ChainRoutine := ⟨15, [0, 0, 0, 1, 2, 0, 3], [piece1004, piece1009, piece1014, piece1016, piece1020, piece886, piece754, piece759, piece761, piece764]⟩
def routine16 : ChainRoutine := ⟨16, [0, 0, 0, 1, 2, 1, 2], [piece1021, piece1026, piece1031, piece1034, piece897, piece902, piece799, piece804, piece807]⟩
def routine17 : ChainRoutine := ⟨17, [0, 0, 0, 1, 2, 2, 1], [piece1035, piece1040, piece1045, piece1048, piece913, piece918, piece921, piece862, piece867]⟩
def routine18 : ChainRoutine := ⟨18, [0, 0, 0, 1, 2, 3, 0], [piece1049, piece1054, piece1059, piece1062, piece932, piece937, piece939, piece941, piece945]⟩
def routine19 : ChainRoutine := ⟨19, [0, 0, 0, 1, 3, 0, 2], [piece1063, piece1068, piece1073, piece1075, piece1077, piece1081, piece799, piece804, piece807]⟩
def routine20 : ChainRoutine := ⟨20, [0, 0, 0, 1, 3, 1, 1], [piece1082, piece1087, piece1092, piece1094, piece1097, piece1102, piece862, piece867]⟩
def routine21 : ChainRoutine := ⟨21, [0, 0, 0, 1, 3, 2, 0], [piece1103, piece1108, piece1113, piece1115, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routine22 : ChainRoutine := ⟨22, [0, 0, 0, 2, 0, 1, 3], [piece1130, piece1135, piece1137, piece1141, piece821, piece826, piece754, piece759, piece761, piece764]⟩
def routine23 : ChainRoutine := ⟨23, [0, 0, 0, 2, 0, 2, 2], [piece1142, piece1147, piece1149, piece1153, piece835, piece840, piece843, piece799, piece804, piece807]⟩
def routine24 : ChainRoutine := ⟨24, [0, 0, 0, 2, 0, 3, 1], [piece1154, piece1159, piece1161, piece1165, piece852, piece857, piece859, piece862, piece867]⟩
def routine25 : ChainRoutine := ⟨25, [0, 0, 0, 2, 1, 0, 3], [piece1166, piece1171, piece1174, piece1179, piece1183, piece886, piece754, piece759, piece761, piece764]⟩
def routine26 : ChainRoutine := ⟨26, [0, 0, 0, 2, 1, 1, 2], [piece1184, piece1189, piece1192, piece1197, piece897, piece902, piece799, piece804, piece807]⟩
def routine27 : ChainRoutine := ⟨27, [0, 0, 0, 2, 1, 2, 1], [piece1198, piece1203, piece1206, piece1211, piece913, piece918, piece921, piece862, piece867]⟩
def routine28 : ChainRoutine := ⟨28, [0, 0, 0, 2, 1, 3, 0], [piece1212, piece1217, piece1220, piece1225, piece932, piece937, piece939, piece941, piece945]⟩
def routine29 : ChainRoutine := ⟨29, [0, 0, 0, 2, 2, 0, 2], [piece1226, piece1231, piece1234, piece1239, piece1241, piece1245, piece1081, piece799, piece804, piece807]⟩
def routine30 : ChainRoutine := ⟨30, [0, 0, 0, 2, 2, 1, 1], [piece1246, piece1251, piece1254, piece1259, piece1262, piece1097, piece1102, piece862, piece867]⟩
def routine31 : ChainRoutine := ⟨31, [0, 0, 0, 2, 2, 2, 0], [piece1263, piece1268, piece1271, piece1276, piece1279, piece1118, piece1123, piece1125, piece1129, piece945]⟩
def routineBatch00 : List ChainRoutine := [routine0, routine1, routine2, routine3, routine4, routine5, routine6, routine7, routine8, routine9, routine10, routine11, routine12, routine13, routine14, routine15, routine16, routine17, routine18, routine19, routine20, routine21, routine22, routine23, routine24, routine25, routine26, routine27, routine28, routine29, routine30, routine31]
theorem routineBatch00_checked : (routineBatch00.all ChainRoutine.checked) = true := by decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch00_checked :
    (routineBatch00.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch00_checked :
    (routineBatch00.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine0_ready : RoutineReady ⟨0, by decide⟩ routine0 := by
  wct_ready_start 0 0 0
  wct_cases [744,749,751,754,759,761,764]
  · wct_piece 0 744 0
  · wct_piece 0 749 1
  · wct_piece 0 751 2
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine1_ready : RoutineReady ⟨1, by decide⟩ routine1 := by
  wct_ready_start 1 0 1
  wct_cases [770,775,780,783,754,759,761,764]
  · wct_piece 0 770 7
  · wct_piece 0 775 8
  · wct_piece 0 780 9
  · wct_piece 0 783 10
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine2_ready : RoutineReady ⟨2, by decide⟩ routine2 := by
  wct_ready_start 2 0 2
  wct_cases [784,789,794,796,799,804,807]
  · wct_piece 0 784 11
  · wct_piece 0 789 12
  · wct_piece 0 794 13
  · wct_piece 0 796 14
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine3_ready : RoutineReady ⟨3, by decide⟩ routine3 := by
  wct_ready_start 3 0 3
  wct_cases [813,818,821,826,754,759,761,764]
  · wct_piece 0 813 18
  · wct_piece 0 818 19
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine4_ready : RoutineReady ⟨4, by decide⟩ routine4 := by
  wct_ready_start 4 0 4
  wct_cases [827,832,835,840,843,799,804,807]
  · wct_piece 0 827 22
  · wct_piece 0 832 23
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine5_ready : RoutineReady ⟨5, by decide⟩ routine5 := by
  wct_ready_start 5 0 5
  wct_cases [844,849,852,857,859,862,867]
  · wct_piece 0 844 27
  · wct_piece 0 849 28
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine6_ready : RoutineReady ⟨6, by decide⟩ routine6 := by
  wct_ready_start 6 0 6
  wct_cases [873,878,880,882,886,754,759,761,764]
  · wct_piece 0 873 34
  · wct_piece 0 878 35
  · wct_piece 0 880 36
  · wct_piece 0 882 37
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine7_ready : RoutineReady ⟨7, by decide⟩ routine7 := by
  wct_ready_start 7 0 7
  wct_cases [887,892,894,897,902,799,804,807]
  · wct_piece 0 887 39
  · wct_piece 0 892 40
  · wct_piece 0 894 41
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine8_ready : RoutineReady ⟨8, by decide⟩ routine8 := by
  wct_ready_start 8 0 8
  wct_cases [903,908,910,913,918,921,862,867]
  · wct_piece 0 903 44
  · wct_piece 0 908 45
  · wct_piece 0 910 46
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine9_ready : RoutineReady ⟨9, by decide⟩ routine9 := by
  wct_ready_start 9 0 9
  wct_cases [922,927,929,932,937,939,941,945]
  · wct_piece 0 922 50
  · wct_piece 0 927 51
  · wct_piece 0 929 52
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine10_ready : RoutineReady ⟨10, by decide⟩ routine10 := by
  wct_ready_start 10 0 10
  wct_cases [951,956,960,775,780,783,754,759,761,764]
  · wct_piece 0 951 58
  · wct_piece 0 956 59
  · wct_piece 0 960 60
  · wct_piece 0 775 8
  · wct_piece 0 780 9
  · wct_piece 0 783 10
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine11_ready : RoutineReady ⟨11, by decide⟩ routine11 := by
  wct_ready_start 11 0 11
  wct_cases [961,966,970,789,794,796,799,804,807]
  · wct_piece 0 961 61
  · wct_piece 0 966 62
  · wct_piece 0 970 63
  · wct_piece 0 789 12
  · wct_piece 0 794 13
  · wct_piece 0 796 14
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine12_ready : RoutineReady ⟨12, by decide⟩ routine12 := by
  wct_ready_start 12 0 12
  wct_cases [971,976,981,821,826,754,759,761,764]
  · wct_piece 1 971 0
  · wct_piece 1 976 1
  · wct_piece 1 981 2
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine13_ready : RoutineReady ⟨13, by decide⟩ routine13 := by
  wct_ready_start 13 0 13
  wct_cases [982,987,992,835,840,843,799,804,807]
  · wct_piece 1 982 3
  · wct_piece 1 987 4
  · wct_piece 1 992 5
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine14_ready : RoutineReady ⟨14, by decide⟩ routine14 := by
  wct_ready_start 14 0 14
  wct_cases [993,998,1003,852,857,859,862,867]
  · wct_piece 1 993 6
  · wct_piece 1 998 7
  · wct_piece 1 1003 8
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine15_ready : RoutineReady ⟨15, by decide⟩ routine15 := by
  wct_ready_start 15 0 15
  wct_cases [1004,1009,1014,1016,1020,886,754,759,761,764]
  · wct_piece 1 1004 9
  · wct_piece 1 1009 10
  · wct_piece 1 1014 11
  · wct_piece 1 1016 12
  · wct_piece 1 1020 13
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine16_ready : RoutineReady ⟨16, by decide⟩ routine16 := by
  wct_ready_start 16 0 16
  wct_cases [1021,1026,1031,1034,897,902,799,804,807]
  · wct_piece 1 1021 14
  · wct_piece 1 1026 15
  · wct_piece 1 1031 16
  · wct_piece 1 1034 17
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine17_ready : RoutineReady ⟨17, by decide⟩ routine17 := by
  wct_ready_start 17 0 17
  wct_cases [1035,1040,1045,1048,913,918,921,862,867]
  · wct_piece 1 1035 18
  · wct_piece 1 1040 19
  · wct_piece 1 1045 20
  · wct_piece 1 1048 21
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine18_ready : RoutineReady ⟨18, by decide⟩ routine18 := by
  wct_ready_start 18 0 18
  wct_cases [1049,1054,1059,1062,932,937,939,941,945]
  · wct_piece 1 1049 22
  · wct_piece 1 1054 23
  · wct_piece 1 1059 24
  · wct_piece 1 1062 25
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine19_ready : RoutineReady ⟨19, by decide⟩ routine19 := by
  wct_ready_start 19 0 19
  wct_cases [1063,1068,1073,1075,1077,1081,799,804,807]
  · wct_piece 1 1063 26
  · wct_piece 1 1068 27
  · wct_piece 1 1073 28
  · wct_piece 1 1075 29
  · wct_piece 1 1077 30
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine20_ready : RoutineReady ⟨20, by decide⟩ routine20 := by
  wct_ready_start 20 0 20
  wct_cases [1082,1087,1092,1094,1097,1102,862,867]
  · wct_piece 1 1082 32
  · wct_piece 1 1087 33
  · wct_piece 1 1092 34
  · wct_piece 1 1094 35
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine21_ready : RoutineReady ⟨21, by decide⟩ routine21 := by
  wct_ready_start 21 0 21
  wct_cases [1103,1108,1113,1115,1118,1123,1125,1129,945]
  · wct_piece 1 1103 38
  · wct_piece 1 1108 39
  · wct_piece 1 1113 40
  · wct_piece 1 1115 41
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
theorem routine22_ready : RoutineReady ⟨22, by decide⟩ routine22 := by
  wct_ready_start 22 0 22
  wct_cases [1130,1135,1137,1141,821,826,754,759,761,764]
  · wct_piece 1 1130 46
  · wct_piece 1 1135 47
  · wct_piece 1 1137 48
  · wct_piece 1 1141 49
  · wct_piece 0 821 20
  · wct_piece 0 826 21
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine23_ready : RoutineReady ⟨23, by decide⟩ routine23 := by
  wct_ready_start 23 0 23
  wct_cases [1142,1147,1149,1153,835,840,843,799,804,807]
  · wct_piece 1 1142 50
  · wct_piece 1 1147 51
  · wct_piece 1 1149 52
  · wct_piece 1 1153 53
  · wct_piece 0 835 24
  · wct_piece 0 840 25
  · wct_piece 0 843 26
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine24_ready : RoutineReady ⟨24, by decide⟩ routine24 := by
  wct_ready_start 24 0 24
  wct_cases [1154,1159,1161,1165,852,857,859,862,867]
  · wct_piece 1 1154 54
  · wct_piece 1 1159 55
  · wct_piece 1 1161 56
  · wct_piece 1 1165 57
  · wct_piece 0 852 29
  · wct_piece 0 857 30
  · wct_piece 0 859 31
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine25_ready : RoutineReady ⟨25, by decide⟩ routine25 := by
  wct_ready_start 25 0 25
  wct_cases [1166,1171,1174,1179,1183,886,754,759,761,764]
  · wct_piece 1 1166 58
  · wct_piece 1 1171 59
  · wct_piece 1 1174 60
  · wct_piece 1 1179 61
  · wct_piece 1 1183 62
  · wct_piece 0 886 38
  · wct_piece 0 754 3
  · wct_piece 0 759 4
  · wct_piece 0 761 5
  · wct_piece 0 764 6
theorem routine26_ready : RoutineReady ⟨26, by decide⟩ routine26 := by
  wct_ready_start 26 0 26
  wct_cases [1184,1189,1192,1197,897,902,799,804,807]
  · wct_piece 1 1184 63
  · wct_piece 2 1189 0
  · wct_piece 2 1192 1
  · wct_piece 2 1197 2
  · wct_piece 0 897 42
  · wct_piece 0 902 43
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine27_ready : RoutineReady ⟨27, by decide⟩ routine27 := by
  wct_ready_start 27 0 27
  wct_cases [1198,1203,1206,1211,913,918,921,862,867]
  · wct_piece 2 1198 3
  · wct_piece 2 1203 4
  · wct_piece 2 1206 5
  · wct_piece 2 1211 6
  · wct_piece 0 913 47
  · wct_piece 0 918 48
  · wct_piece 0 921 49
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine28_ready : RoutineReady ⟨28, by decide⟩ routine28 := by
  wct_ready_start 28 0 28
  wct_cases [1212,1217,1220,1225,932,937,939,941,945]
  · wct_piece 2 1212 7
  · wct_piece 2 1217 8
  · wct_piece 2 1220 9
  · wct_piece 2 1225 10
  · wct_piece 0 932 53
  · wct_piece 0 937 54
  · wct_piece 0 939 55
  · wct_piece 0 941 56
  · wct_piece 0 945 57
theorem routine29_ready : RoutineReady ⟨29, by decide⟩ routine29 := by
  wct_ready_start 29 0 29
  wct_cases [1226,1231,1234,1239,1241,1245,1081,799,804,807]
  · wct_piece 2 1226 11
  · wct_piece 2 1231 12
  · wct_piece 2 1234 13
  · wct_piece 2 1239 14
  · wct_piece 2 1241 15
  · wct_piece 2 1245 16
  · wct_piece 1 1081 31
  · wct_piece 0 799 15
  · wct_piece 0 804 16
  · wct_piece 0 807 17
theorem routine30_ready : RoutineReady ⟨30, by decide⟩ routine30 := by
  wct_ready_start 30 0 30
  wct_cases [1246,1251,1254,1259,1262,1097,1102,862,867]
  · wct_piece 2 1246 17
  · wct_piece 2 1251 18
  · wct_piece 2 1254 19
  · wct_piece 2 1259 20
  · wct_piece 2 1262 21
  · wct_piece 1 1097 36
  · wct_piece 1 1102 37
  · wct_piece 0 862 32
  · wct_piece 0 867 33
theorem routine31_ready : RoutineReady ⟨31, by decide⟩ routine31 := by
  wct_ready_start 31 0 31
  wct_cases [1263,1268,1271,1276,1279,1118,1123,1125,1129,945]
  · wct_piece 2 1263 22
  · wct_piece 2 1268 23
  · wct_piece 2 1271 24
  · wct_piece 2 1276 25
  · wct_piece 2 1279 26
  · wct_piece 1 1118 42
  · wct_piece 1 1123 43
  · wct_piece 1 1125 44
  · wct_piece 1 1129 45
  · wct_piece 0 945 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage18 (rank : Fin 728) (hlo : 576 ≤ rank.val) (hhi : rank.val < 608) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 576 ≤ n at hlo
  change n < 608 at hhi
  interval_cases n
  · exact ⟨routine576, routine576_ready⟩
  · exact ⟨routine577, routine577_ready⟩
  · exact ⟨routine578, routine578_ready⟩
  · exact ⟨routine579, routine579_ready⟩
  · exact ⟨routine580, routine580_ready⟩
  · exact ⟨routine581, routine581_ready⟩
  · exact ⟨routine582, routine582_ready⟩
  · exact ⟨routine583, routine583_ready⟩
  · exact ⟨routine584, routine584_ready⟩
  · exact ⟨routine585, routine585_ready⟩
  · exact ⟨routine586, routine586_ready⟩
  · exact ⟨routine587, routine587_ready⟩
  · exact ⟨routine588, routine588_ready⟩
  · exact ⟨routine589, routine589_ready⟩
  · exact ⟨routine590, routine590_ready⟩
  · exact ⟨routine591, routine591_ready⟩
  · exact ⟨routine592, routine592_ready⟩
  · exact ⟨routine593, routine593_ready⟩
  · exact ⟨routine594, routine594_ready⟩
  · exact ⟨routine595, routine595_ready⟩
  · exact ⟨routine596, routine596_ready⟩
  · exact ⟨routine597, routine597_ready⟩
  · exact ⟨routine598, routine598_ready⟩
  · exact ⟨routine599, routine599_ready⟩
  · exact ⟨routine600, routine600_ready⟩
  · exact ⟨routine601, routine601_ready⟩
  · exact ⟨routine602, routine602_ready⟩
  · exact ⟨routine603, routine603_ready⟩
  · exact ⟨routine604, routine604_ready⟩
  · exact ⟨routine605, routine605_ready⟩
  · exact ⟨routine606, routine606_ready⟩
  · exact ⟨routine607, routine607_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage07 (rank : Fin 728) (hlo : 224 ≤ rank.val) (hhi : rank.val < 256) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 224 ≤ n at hlo
  change n < 256 at hhi
  interval_cases n
  · exact ⟨routine224, routine224_ready⟩
  · exact ⟨routine225, routine225_ready⟩
  · exact ⟨routine226, routine226_ready⟩
  · exact ⟨routine227, routine227_ready⟩
  · exact ⟨routine228, routine228_ready⟩
  · exact ⟨routine229, routine229_ready⟩
  · exact ⟨routine230, routine230_ready⟩
  · exact ⟨routine231, routine231_ready⟩
  · exact ⟨routine232, routine232_ready⟩
  · exact ⟨routine233, routine233_ready⟩
  · exact ⟨routine234, routine234_ready⟩
  · exact ⟨routine235, routine235_ready⟩
  · exact ⟨routine236, routine236_ready⟩
  · exact ⟨routine237, routine237_ready⟩
  · exact ⟨routine238, routine238_ready⟩
  · exact ⟨routine239, routine239_ready⟩
  · exact ⟨routine240, routine240_ready⟩
  · exact ⟨routine241, routine241_ready⟩
  · exact ⟨routine242, routine242_ready⟩
  · exact ⟨routine243, routine243_ready⟩
  · exact ⟨routine244, routine244_ready⟩
  · exact ⟨routine245, routine245_ready⟩
  · exact ⟨routine246, routine246_ready⟩
  · exact ⟨routine247, routine247_ready⟩
  · exact ⟨routine248, routine248_ready⟩
  · exact ⟨routine249, routine249_ready⟩
  · exact ⟨routine250, routine250_ready⟩
  · exact ⟨routine251, routine251_ready⟩
  · exact ⟨routine252, routine252_ready⟩
  · exact ⟨routine253, routine253_ready⟩
  · exact ⟨routine254, routine254_ready⟩
  · exact ⟨routine255, routine255_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage06 (rank : Fin 728) (hlo : 192 ≤ rank.val) (hhi : rank.val < 224) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 192 ≤ n at hlo
  change n < 224 at hhi
  interval_cases n
  · exact ⟨routine192, routine192_ready⟩
  · exact ⟨routine193, routine193_ready⟩
  · exact ⟨routine194, routine194_ready⟩
  · exact ⟨routine195, routine195_ready⟩
  · exact ⟨routine196, routine196_ready⟩
  · exact ⟨routine197, routine197_ready⟩
  · exact ⟨routine198, routine198_ready⟩
  · exact ⟨routine199, routine199_ready⟩
  · exact ⟨routine200, routine200_ready⟩
  · exact ⟨routine201, routine201_ready⟩
  · exact ⟨routine202, routine202_ready⟩
  · exact ⟨routine203, routine203_ready⟩
  · exact ⟨routine204, routine204_ready⟩
  · exact ⟨routine205, routine205_ready⟩
  · exact ⟨routine206, routine206_ready⟩
  · exact ⟨routine207, routine207_ready⟩
  · exact ⟨routine208, routine208_ready⟩
  · exact ⟨routine209, routine209_ready⟩
  · exact ⟨routine210, routine210_ready⟩
  · exact ⟨routine211, routine211_ready⟩
  · exact ⟨routine212, routine212_ready⟩
  · exact ⟨routine213, routine213_ready⟩
  · exact ⟨routine214, routine214_ready⟩
  · exact ⟨routine215, routine215_ready⟩
  · exact ⟨routine216, routine216_ready⟩
  · exact ⟨routine217, routine217_ready⟩
  · exact ⟨routine218, routine218_ready⟩
  · exact ⟨routine219, routine219_ready⟩
  · exact ⟨routine220, routine220_ready⟩
  · exact ⟨routine221, routine221_ready⟩
  · exact ⟨routine222, routine222_ready⟩
  · exact ⟨routine223, routine223_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage05 (rank : Fin 728) (hlo : 160 ≤ rank.val) (hhi : rank.val < 192) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 160 ≤ n at hlo
  change n < 192 at hhi
  interval_cases n
  · exact ⟨routine160, routine160_ready⟩
  · exact ⟨routine161, routine161_ready⟩
  · exact ⟨routine162, routine162_ready⟩
  · exact ⟨routine163, routine163_ready⟩
  · exact ⟨routine164, routine164_ready⟩
  · exact ⟨routine165, routine165_ready⟩
  · exact ⟨routine166, routine166_ready⟩
  · exact ⟨routine167, routine167_ready⟩
  · exact ⟨routine168, routine168_ready⟩
  · exact ⟨routine169, routine169_ready⟩
  · exact ⟨routine170, routine170_ready⟩
  · exact ⟨routine171, routine171_ready⟩
  · exact ⟨routine172, routine172_ready⟩
  · exact ⟨routine173, routine173_ready⟩
  · exact ⟨routine174, routine174_ready⟩
  · exact ⟨routine175, routine175_ready⟩
  · exact ⟨routine176, routine176_ready⟩
  · exact ⟨routine177, routine177_ready⟩
  · exact ⟨routine178, routine178_ready⟩
  · exact ⟨routine179, routine179_ready⟩
  · exact ⟨routine180, routine180_ready⟩
  · exact ⟨routine181, routine181_ready⟩
  · exact ⟨routine182, routine182_ready⟩
  · exact ⟨routine183, routine183_ready⟩
  · exact ⟨routine184, routine184_ready⟩
  · exact ⟨routine185, routine185_ready⟩
  · exact ⟨routine186, routine186_ready⟩
  · exact ⟨routine187, routine187_ready⟩
  · exact ⟨routine188, routine188_ready⟩
  · exact ⟨routine189, routine189_ready⟩
  · exact ⟨routine190, routine190_ready⟩
  · exact ⟨routine191, routine191_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage04 (rank : Fin 728) (hlo : 128 ≤ rank.val) (hhi : rank.val < 160) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 128 ≤ n at hlo
  change n < 160 at hhi
  interval_cases n
  · exact ⟨routine128, routine128_ready⟩
  · exact ⟨routine129, routine129_ready⟩
  · exact ⟨routine130, routine130_ready⟩
  · exact ⟨routine131, routine131_ready⟩
  · exact ⟨routine132, routine132_ready⟩
  · exact ⟨routine133, routine133_ready⟩
  · exact ⟨routine134, routine134_ready⟩
  · exact ⟨routine135, routine135_ready⟩
  · exact ⟨routine136, routine136_ready⟩
  · exact ⟨routine137, routine137_ready⟩
  · exact ⟨routine138, routine138_ready⟩
  · exact ⟨routine139, routine139_ready⟩
  · exact ⟨routine140, routine140_ready⟩
  · exact ⟨routine141, routine141_ready⟩
  · exact ⟨routine142, routine142_ready⟩
  · exact ⟨routine143, routine143_ready⟩
  · exact ⟨routine144, routine144_ready⟩
  · exact ⟨routine145, routine145_ready⟩
  · exact ⟨routine146, routine146_ready⟩
  · exact ⟨routine147, routine147_ready⟩
  · exact ⟨routine148, routine148_ready⟩
  · exact ⟨routine149, routine149_ready⟩
  · exact ⟨routine150, routine150_ready⟩
  · exact ⟨routine151, routine151_ready⟩
  · exact ⟨routine152, routine152_ready⟩
  · exact ⟨routine153, routine153_ready⟩
  · exact ⟨routine154, routine154_ready⟩
  · exact ⟨routine155, routine155_ready⟩
  · exact ⟨routine156, routine156_ready⟩
  · exact ⟨routine157, routine157_ready⟩
  · exact ⟨routine158, routine158_ready⟩
  · exact ⟨routine159, routine159_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage03 (rank : Fin 728) (hlo : 96 ≤ rank.val) (hhi : rank.val < 128) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 96 ≤ n at hlo
  change n < 128 at hhi
  interval_cases n
  · exact ⟨routine96, routine96_ready⟩
  · exact ⟨routine97, routine97_ready⟩
  · exact ⟨routine98, routine98_ready⟩
  · exact ⟨routine99, routine99_ready⟩
  · exact ⟨routine100, routine100_ready⟩
  · exact ⟨routine101, routine101_ready⟩
  · exact ⟨routine102, routine102_ready⟩
  · exact ⟨routine103, routine103_ready⟩
  · exact ⟨routine104, routine104_ready⟩
  · exact ⟨routine105, routine105_ready⟩
  · exact ⟨routine106, routine106_ready⟩
  · exact ⟨routine107, routine107_ready⟩
  · exact ⟨routine108, routine108_ready⟩
  · exact ⟨routine109, routine109_ready⟩
  · exact ⟨routine110, routine110_ready⟩
  · exact ⟨routine111, routine111_ready⟩
  · exact ⟨routine112, routine112_ready⟩
  · exact ⟨routine113, routine113_ready⟩
  · exact ⟨routine114, routine114_ready⟩
  · exact ⟨routine115, routine115_ready⟩
  · exact ⟨routine116, routine116_ready⟩
  · exact ⟨routine117, routine117_ready⟩
  · exact ⟨routine118, routine118_ready⟩
  · exact ⟨routine119, routine119_ready⟩
  · exact ⟨routine120, routine120_ready⟩
  · exact ⟨routine121, routine121_ready⟩
  · exact ⟨routine122, routine122_ready⟩
  · exact ⟨routine123, routine123_ready⟩
  · exact ⟨routine124, routine124_ready⟩
  · exact ⟨routine125, routine125_ready⟩
  · exact ⟨routine126, routine126_ready⟩
  · exact ⟨routine127, routine127_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage02 (rank : Fin 728) (hlo : 64 ≤ rank.val) (hhi : rank.val < 96) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 64 ≤ n at hlo
  change n < 96 at hhi
  interval_cases n
  · exact ⟨routine64, routine64_ready⟩
  · exact ⟨routine65, routine65_ready⟩
  · exact ⟨routine66, routine66_ready⟩
  · exact ⟨routine67, routine67_ready⟩
  · exact ⟨routine68, routine68_ready⟩
  · exact ⟨routine69, routine69_ready⟩
  · exact ⟨routine70, routine70_ready⟩
  · exact ⟨routine71, routine71_ready⟩
  · exact ⟨routine72, routine72_ready⟩
  · exact ⟨routine73, routine73_ready⟩
  · exact ⟨routine74, routine74_ready⟩
  · exact ⟨routine75, routine75_ready⟩
  · exact ⟨routine76, routine76_ready⟩
  · exact ⟨routine77, routine77_ready⟩
  · exact ⟨routine78, routine78_ready⟩
  · exact ⟨routine79, routine79_ready⟩
  · exact ⟨routine80, routine80_ready⟩
  · exact ⟨routine81, routine81_ready⟩
  · exact ⟨routine82, routine82_ready⟩
  · exact ⟨routine83, routine83_ready⟩
  · exact ⟨routine84, routine84_ready⟩
  · exact ⟨routine85, routine85_ready⟩
  · exact ⟨routine86, routine86_ready⟩
  · exact ⟨routine87, routine87_ready⟩
  · exact ⟨routine88, routine88_ready⟩
  · exact ⟨routine89, routine89_ready⟩
  · exact ⟨routine90, routine90_ready⟩
  · exact ⟨routine91, routine91_ready⟩
  · exact ⟨routine92, routine92_ready⟩
  · exact ⟨routine93, routine93_ready⟩
  · exact ⟨routine94, routine94_ready⟩
  · exact ⟨routine95, routine95_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage01 (rank : Fin 728) (hlo : 32 ≤ rank.val) (hhi : rank.val < 64) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 32 ≤ n at hlo
  change n < 64 at hhi
  interval_cases n
  · exact ⟨routine32, routine32_ready⟩
  · exact ⟨routine33, routine33_ready⟩
  · exact ⟨routine34, routine34_ready⟩
  · exact ⟨routine35, routine35_ready⟩
  · exact ⟨routine36, routine36_ready⟩
  · exact ⟨routine37, routine37_ready⟩
  · exact ⟨routine38, routine38_ready⟩
  · exact ⟨routine39, routine39_ready⟩
  · exact ⟨routine40, routine40_ready⟩
  · exact ⟨routine41, routine41_ready⟩
  · exact ⟨routine42, routine42_ready⟩
  · exact ⟨routine43, routine43_ready⟩
  · exact ⟨routine44, routine44_ready⟩
  · exact ⟨routine45, routine45_ready⟩
  · exact ⟨routine46, routine46_ready⟩
  · exact ⟨routine47, routine47_ready⟩
  · exact ⟨routine48, routine48_ready⟩
  · exact ⟨routine49, routine49_ready⟩
  · exact ⟨routine50, routine50_ready⟩
  · exact ⟨routine51, routine51_ready⟩
  · exact ⟨routine52, routine52_ready⟩
  · exact ⟨routine53, routine53_ready⟩
  · exact ⟨routine54, routine54_ready⟩
  · exact ⟨routine55, routine55_ready⟩
  · exact ⟨routine56, routine56_ready⟩
  · exact ⟨routine57, routine57_ready⟩
  · exact ⟨routine58, routine58_ready⟩
  · exact ⟨routine59, routine59_ready⟩
  · exact ⟨routine60, routine60_ready⟩
  · exact ⟨routine61, routine61_ready⟩
  · exact ⟨routine62, routine62_ready⟩
  · exact ⟨routine63, routine63_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage00 (rank : Fin 728) (hlo : 0 ≤ rank.val) (hhi : rank.val < 32) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 0 ≤ n at hlo
  change n < 32 at hhi
  interval_cases n
  · exact ⟨routine0, routine0_ready⟩
  · exact ⟨routine1, routine1_ready⟩
  · exact ⟨routine2, routine2_ready⟩
  · exact ⟨routine3, routine3_ready⟩
  · exact ⟨routine4, routine4_ready⟩
  · exact ⟨routine5, routine5_ready⟩
  · exact ⟨routine6, routine6_ready⟩
  · exact ⟨routine7, routine7_ready⟩
  · exact ⟨routine8, routine8_ready⟩
  · exact ⟨routine9, routine9_ready⟩
  · exact ⟨routine10, routine10_ready⟩
  · exact ⟨routine11, routine11_ready⟩
  · exact ⟨routine12, routine12_ready⟩
  · exact ⟨routine13, routine13_ready⟩
  · exact ⟨routine14, routine14_ready⟩
  · exact ⟨routine15, routine15_ready⟩
  · exact ⟨routine16, routine16_ready⟩
  · exact ⟨routine17, routine17_ready⟩
  · exact ⟨routine18, routine18_ready⟩
  · exact ⟨routine19, routine19_ready⟩
  · exact ⟨routine20, routine20_ready⟩
  · exact ⟨routine21, routine21_ready⟩
  · exact ⟨routine22, routine22_ready⟩
  · exact ⟨routine23, routine23_ready⟩
  · exact ⟨routine24, routine24_ready⟩
  · exact ⟨routine25, routine25_ready⟩
  · exact ⟨routine26, routine26_ready⟩
  · exact ⟨routine27, routine27_ready⟩
  · exact ⟨routine28, routine28_ready⟩
  · exact ⟨routine29, routine29_ready⟩
  · exact ⟨routine30, routine30_ready⟩
  · exact ⟨routine31, routine31_ready⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage22 (rank : Fin 728) (hlo : 704 ≤ rank.val) (hhi : rank.val < 728) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 704 ≤ n at hlo
  change n < 728 at hhi
  interval_cases n
  · exact ⟨routine704, routine704_ready⟩
  · exact ⟨routine705, routine705_ready⟩
  · exact ⟨routine706, routine706_ready⟩
  · exact ⟨routine707, routine707_ready⟩
  · exact ⟨routine708, routine708_ready⟩
  · exact ⟨routine709, routine709_ready⟩
  · exact ⟨routine710, routine710_ready⟩
  · exact ⟨routine711, routine711_ready⟩
  · exact ⟨routine712, routine712_ready⟩
  · exact ⟨routine713, routine713_ready⟩
  · exact ⟨routine714, routine714_ready⟩
  · exact ⟨routine715, routine715_ready⟩
  · exact ⟨routine716, routine716_ready⟩
  · exact ⟨routine717, routine717_ready⟩
  · exact ⟨routine718, routine718_ready⟩
  · exact ⟨routine719, routine719_ready⟩
  · exact ⟨routine720, routine720_ready⟩
  · exact ⟨routine721, routine721_ready⟩
  · exact ⟨routine722, routine722_ready⟩
  · exact ⟨routine723, routine723_ready⟩
  · exact ⟨routine724, routine724_ready⟩
  · exact ⟨routine725, routine725_ready⟩
  · exact ⟨routine726, routine726_ready⟩
  · exact ⟨routine727, routine727_ready⟩
end W9Machine.Chain
end

section
























namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem allRoutines_ready : ∀ rank : Fin 728, ∃ r, RoutineReady rank r := by
  intro rank
  by_cases h0 : rank.val < 32
  · exact coverage00 rank (by omega) h0
  by_cases h1 : rank.val < 64
  · exact coverage01 rank (by omega) h1
  by_cases h2 : rank.val < 96
  · exact coverage02 rank (by omega) h2
  by_cases h3 : rank.val < 128
  · exact coverage03 rank (by omega) h3
  by_cases h4 : rank.val < 160
  · exact coverage04 rank (by omega) h4
  by_cases h5 : rank.val < 192
  · exact coverage05 rank (by omega) h5
  by_cases h6 : rank.val < 224
  · exact coverage06 rank (by omega) h6
  by_cases h7 : rank.val < 256
  · exact coverage07 rank (by omega) h7
  by_cases h8 : rank.val < 288
  · exact coverage08 rank (by omega) h8
  by_cases h9 : rank.val < 320
  · exact coverage09 rank (by omega) h9
  by_cases h10 : rank.val < 352
  · exact coverage10 rank (by omega) h10
  by_cases h11 : rank.val < 384
  · exact coverage11 rank (by omega) h11
  by_cases h12 : rank.val < 416
  · exact coverage12 rank (by omega) h12
  by_cases h13 : rank.val < 448
  · exact coverage13 rank (by omega) h13
  by_cases h14 : rank.val < 480
  · exact coverage14 rank (by omega) h14
  by_cases h15 : rank.val < 512
  · exact coverage15 rank (by omega) h15
  by_cases h16 : rank.val < 544
  · exact coverage16 rank (by omega) h16
  by_cases h17 : rank.val < 576
  · exact coverage17 rank (by omega) h17
  by_cases h18 : rank.val < 608
  · exact coverage18 rank (by omega) h18
  by_cases h19 : rank.val < 640
  · exact coverage19 rank (by omega) h19
  by_cases h20 : rank.val < 672
  · exact coverage20 rank (by omega) h20
  by_cases h21 : rank.val < 704
  · exact coverage21 rank (by omega) h21
  exact coverage22 rank (by omega) rank.isLt
theorem allGood_of (S : SourceEquivalent) (E : EndpointsCorrect) : AllGood Frozen.layout := by
  exact allGood_of_ready S E allRoutines_ready
end W9Machine.Chain
end
