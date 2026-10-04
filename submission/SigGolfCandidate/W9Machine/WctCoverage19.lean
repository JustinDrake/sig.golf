import SigGolfCandidate.W9Machine.WctRoutineCheck19
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.Packaging.ReadySyntax
import SigGolfCandidate.W9Machine.WctRoutineEvidence
import SigGolfCandidate.W9Machine.WctAllPieceEvidence

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guardBatch19_checked :
    (routineBatch19.all fun r => planGuard r.pieces {}) = true := by
  decide +kernel
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem terminalBatch19_checked :
    (routineBatch19.all Chain.terminalChecked) = true := by
  decide +kernel
end W9Machine
end

section





namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem routine608_ready : RoutineReady ⟨608, by decide⟩ routine608 := by
  wct_ready_start 608 19 0
  wct_cases [240880,240886,240888,235747,235753,235755,235759,4496,2190,2196,2198,2202,1585,966]
  · wct_piece 40 240880 37
  · wct_piece 40 240886 38
  · wct_piece 40 240888 39
  · wct_piece 19 235747 58
  · wct_piece 19 235753 59
  · wct_piece 19 235755 60
  · wct_piece 19 235759 61
  · wct_piece 15 4496 39
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine609_ready : RoutineReady ⟨609, by decide⟩ routine609 := by
  wct_ready_start 609 19 1
  wct_cases [240889,240895,240897,235769,235775,235778,4514,4520,4524,2681,1365,875,881]
  · wct_piece 40 240889 40
  · wct_piece 40 240895 41
  · wct_piece 40 240897 42
  · wct_piece 20 235769 0
  · wct_piece 20 235775 1
  · wct_piece 20 235778 2
  · wct_piece 15 4514 44
  · wct_piece 15 4520 45
  · wct_piece 15 4524 46
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine610_ready : RoutineReady ⟨610, by decide⟩ routine610 := by
  wct_ready_start 610 19 2
  wct_cases [240898,240904,240906,235788,235794,235797,235803,235807,2705,1386,1392,1396,966]
  · wct_piece 40 240898 43
  · wct_piece 40 240904 44
  · wct_piece 40 240906 45
  · wct_piece 20 235788 5
  · wct_piece 20 235794 6
  · wct_piece 20 235797 7
  · wct_piece 20 235803 8
  · wct_piece 20 235807 9
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine611_ready : RoutineReady ⟨611, by decide⟩ routine611 := by
  wct_ready_start 611 19 3
  wct_cases [240907,240913,240915,235817,235823,235826,4570,4576,2726,2732,2736,1585,966]
  · wct_piece 40 240907 46
  · wct_piece 40 240913 47
  · wct_piece 40 240915 48
  · wct_piece 20 235817 12
  · wct_piece 20 235823 13
  · wct_piece 20 235826 14
  · wct_piece 15 4570 58
  · wct_piece 15 4576 59
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine612_ready : RoutineReady ⟨612, by decide⟩ routine612 := by
  wct_ready_start 612 19 4
  wct_cases [240916,240922,240924,235836,235842,235845,4594,4600,4602,4606,3101,1585,966]
  · wct_piece 40 240916 49
  · wct_piece 40 240922 50
  · wct_piece 40 240924 51
  · wct_piece 20 235836 17
  · wct_piece 20 235842 18
  · wct_piece 20 235845 19
  · wct_piece 16 4594 0
  · wct_piece 16 4600 1
  · wct_piece 16 4602 2
  · wct_piece 16 4606 3
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine613_ready : RoutineReady ⟨613, by decide⟩ routine613 := by
  wct_ready_start 613 19 5
  wct_cases [240925,240931,240933,235855,235861,235863,235865,235869,2681,1365,875,881]
  · wct_piece 40 240925 52
  · wct_piece 40 240931 53
  · wct_piece 40 240933 54
  · wct_piece 20 235855 22
  · wct_piece 20 235861 23
  · wct_piece 20 235863 24
  · wct_piece 20 235865 25
  · wct_piece 20 235869 26
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine614_ready : RoutineReady ⟨614, by decide⟩ routine614 := by
  wct_ready_start 614 19 6
  wct_cases [240934,240940,240942,235879,235885,235887,235889,235893,2705,1386,1392,1396,966]
  · wct_piece 40 240934 55
  · wct_piece 40 240940 56
  · wct_piece 40 240942 57
  · wct_piece 20 235879 29
  · wct_piece 20 235885 30
  · wct_piece 20 235887 31
  · wct_piece 20 235889 32
  · wct_piece 20 235893 33
  · wct_piece 8 2705 11
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine615_ready : RoutineReady ⟨615, by decide⟩ routine615 := by
  wct_ready_start 615 19 7
  wct_cases [240943,240949,240951,235903,235909,235911,235913,235917,2726,2732,2736,1585,966]
  · wct_piece 40 240943 58
  · wct_piece 40 240949 59
  · wct_piece 40 240951 60
  · wct_piece 20 235903 36
  · wct_piece 20 235909 37
  · wct_piece 20 235911 38
  · wct_piece 20 235913 39
  · wct_piece 20 235917 40
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine616_ready : RoutineReady ⟨616, by decide⟩ routine616 := by
  wct_ready_start 616 19 8
  wct_cases [240952,240958,240960,235927,235933,235935,235938,235944,235948,3101,1585,966]
  · wct_piece 40 240952 61
  · wct_piece 40 240958 62
  · wct_piece 40 240960 63
  · wct_piece 20 235927 43
  · wct_piece 20 235933 44
  · wct_piece 20 235935 45
  · wct_piece 20 235938 46
  · wct_piece 20 235944 47
  · wct_piece 20 235948 48
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine617_ready : RoutineReady ⟨617, by decide⟩ routine617 := by
  wct_ready_start 617 19 9
  wct_cases [240961,240967,240969,240975,240979,235963,2751,1411,901,755,761,763,766]
  · wct_piece 41 240961 0
  · wct_piece 41 240967 1
  · wct_piece 41 240969 2
  · wct_piece 41 240975 3
  · wct_piece 41 240979 4
  · wct_piece 20 235963 53
  · wct_piece 8 2751 24
  · wct_piece 2 1411 46
  · wct_piece 0 901 38
  · wct_piece 0 755 3
  · wct_piece 0 761 4
  · wct_piece 0 763 5
  · wct_piece 0 766 6
theorem routine618_ready : RoutineReady ⟨618, by decide⟩ routine618 := by
  wct_ready_start 618 19 10
  wct_cases [240980,240986,240988,240994,240998,235978,2766,1426,913,919,805,811,814]
  · wct_piece 41 240980 5
  · wct_piece 41 240986 6
  · wct_piece 41 240988 7
  · wct_piece 41 240994 8
  · wct_piece 41 240998 9
  · wct_piece 20 235978 58
  · wct_piece 8 2766 29
  · wct_piece 2 1426 51
  · wct_piece 0 913 42
  · wct_piece 0 919 43
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine619_ready : RoutineReady ⟨619, by decide⟩ routine619 := by
  wct_ready_start 619 19 11
  wct_cases [240999,241005,241007,241013,241017,235993,2781,1441,931,937,940,875,881]
  · wct_piece 41 240999 10
  · wct_piece 41 241005 11
  · wct_piece 41 241007 12
  · wct_piece 41 241013 13
  · wct_piece 41 241017 14
  · wct_piece 20 235993 63
  · wct_piece 8 2781 34
  · wct_piece 2 1441 56
  · wct_piece 0 931 47
  · wct_piece 0 937 48
  · wct_piece 0 940 49
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine620_ready : RoutineReady ⟨620, by decide⟩ routine620 := by
  wct_ready_start 620 19 12
  wct_cases [241018,241024,241026,241032,241036,236008,2796,1456,952,958,960,962,966]
  · wct_piece 41 241018 15
  · wct_piece 41 241024 16
  · wct_piece 41 241026 17
  · wct_piece 41 241032 18
  · wct_piece 41 241036 19
  · wct_piece 21 236008 4
  · wct_piece 8 2796 39
  · wct_piece 2 1456 61
  · wct_piece 0 952 53
  · wct_piece 0 958 54
  · wct_piece 0 960 55
  · wct_piece 0 962 56
  · wct_piece 0 966 57
theorem routine621_ready : RoutineReady ⟨621, by decide⟩ routine621 := by
  wct_ready_start 621 19 13
  wct_cases [241037,241043,241045,241051,241055,2811,1468,1474,1478,1120,805,811,814]
  · wct_piece 41 241037 20
  · wct_piece 41 241043 21
  · wct_piece 41 241045 22
  · wct_piece 41 241051 23
  · wct_piece 41 241055 24
  · wct_piece 8 2811 44
  · wct_piece 3 1468 1
  · wct_piece 3 1474 2
  · wct_piece 3 1478 3
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine622_ready : RoutineReady ⟨622, by decide⟩ routine622 := by
  wct_ready_start 622 19 14
  wct_cases [241056,241062,241064,241070,241074,236038,2826,1490,1496,1138,1144,875,881]
  · wct_piece 41 241056 25
  · wct_piece 41 241062 26
  · wct_piece 41 241064 27
  · wct_piece 41 241070 28
  · wct_piece 41 241074 29
  · wct_piece 21 236038 14
  · wct_piece 8 2826 49
  · wct_piece 3 1490 7
  · wct_piece 3 1496 8
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine623_ready : RoutineReady ⟨623, by decide⟩ routine623 := by
  wct_ready_start 623 19 15
  wct_cases [241075,241081,241083,241089,241093,236053,2841,1508,1514,1162,1168,1170,1174,966]
  · wct_piece 41 241075 30
  · wct_piece 41 241081 31
  · wct_piece 41 241083 32
  · wct_piece 41 241089 33
  · wct_piece 41 241093 34
  · wct_piece 21 236053 19
  · wct_piece 8 2841 54
  · wct_piece 3 1508 12
  · wct_piece 3 1514 13
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
theorem routine624_ready : RoutineReady ⟨624, by decide⟩ routine624 := by
  wct_ready_start 624 19 16
  wct_cases [241094,241100,241102,241108,241112,236068,2856,1526,1532,1534,1538,1365,875,881]
  · wct_piece 41 241094 35
  · wct_piece 41 241100 36
  · wct_piece 41 241102 37
  · wct_piece 41 241108 38
  · wct_piece 41 241112 39
  · wct_piece 21 236068 24
  · wct_piece 8 2856 59
  · wct_piece 3 1526 17
  · wct_piece 3 1532 18
  · wct_piece 3 1534 19
  · wct_piece 3 1538 20
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine625_ready : RoutineReady ⟨625, by decide⟩ routine625 := by
  wct_ready_start 625 19 17
  wct_cases [241113,241119,241121,241127,241131,2871,1550,1556,1559,1386,1392,1396,966]
  · wct_piece 41 241113 40
  · wct_piece 41 241119 41
  · wct_piece 41 241121 42
  · wct_piece 41 241127 43
  · wct_piece 41 241131 44
  · wct_piece 9 2871 0
  · wct_piece 3 1550 24
  · wct_piece 3 1556 25
  · wct_piece 3 1559 26
  · wct_piece 2 1386 39
  · wct_piece 2 1392 40
  · wct_piece 2 1396 41
  · wct_piece 0 966 57
theorem routine626_ready : RoutineReady ⟨626, by decide⟩ routine626 := by
  wct_ready_start 626 19 18
  wct_cases [241132,241138,241140,241146,241150,236098,2886,1571,1577,1579,1581,1585,966]
  · wct_piece 41 241132 45
  · wct_piece 41 241138 46
  · wct_piece 41 241140 47
  · wct_piece 41 241146 48
  · wct_piece 41 241150 49
  · wct_piece 21 236098 34
  · wct_piece 9 2886 5
  · wct_piece 3 1571 30
  · wct_piece 3 1577 31
  · wct_piece 3 1579 32
  · wct_piece 3 1581 33
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine627_ready : RoutineReady ⟨627, by decide⟩ routine627 := by
  wct_ready_start 627 19 19
  wct_cases [241151,241157,241159,241165,241169,2898,2904,2908,2078,1120,805,811,814]
  · wct_piece 41 241151 50
  · wct_piece 41 241157 51
  · wct_piece 41 241159 52
  · wct_piece 41 241165 53
  · wct_piece 41 241169 54
  · wct_piece 9 2898 9
  · wct_piece 9 2904 10
  · wct_piece 9 2908 11
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine628_ready : RoutineReady ⟨628, by decide⟩ routine628 := by
  wct_ready_start 628 19 20
  wct_cases [241170,241176,241178,241184,241188,241194,241198,241204,875,881]
  · wct_piece 41 241170 55
  · wct_piece 41 241176 56
  · wct_piece 41 241178 57
  · wct_piece 41 241184 58
  · wct_piece 41 241188 59
  · wct_piece 41 241194 60
  · wct_piece 41 241198 61
  · wct_piece 41 241204 62
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine629_ready : RoutineReady ⟨629, by decide⟩ routine629 := by
  wct_ready_start 629 19 21
  wct_cases [241205,241211,241213,241219,241223,241229,241233,241239,241241,241245,966]
  · wct_piece 41 241205 63
  · wct_piece 42 241211 0
  · wct_piece 42 241213 1
  · wct_piece 42 241219 2
  · wct_piece 42 241223 3
  · wct_piece 42 241229 4
  · wct_piece 42 241233 5
  · wct_piece 42 241239 6
  · wct_piece 42 241241 7
  · wct_piece 42 241245 8
  · wct_piece 0 966 57
theorem routine630_ready : RoutineReady ⟨630, by decide⟩ routine630 := by
  wct_ready_start 630 19 22
  wct_cases [241246,241252,241254,241260,241264,241270,241276,241280,875,881]
  · wct_piece 42 241246 9
  · wct_piece 42 241252 10
  · wct_piece 42 241254 11
  · wct_piece 42 241260 12
  · wct_piece 42 241264 13
  · wct_piece 42 241270 14
  · wct_piece 42 241276 15
  · wct_piece 42 241280 16
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine631_ready : RoutineReady ⟨631, by decide⟩ routine631 := by
  wct_ready_start 631 19 23
  wct_cases [241281,241287,241289,241295,241299,241305,241311,241317,241321,966]
  · wct_piece 42 241281 17
  · wct_piece 42 241287 18
  · wct_piece 42 241289 19
  · wct_piece 42 241295 20
  · wct_piece 42 241299 21
  · wct_piece 42 241305 22
  · wct_piece 42 241311 23
  · wct_piece 42 241317 24
  · wct_piece 42 241321 25
  · wct_piece 0 966 57
theorem routine632_ready : RoutineReady ⟨632, by decide⟩ routine632 := by
  wct_ready_start 632 19 24
  wct_cases [241322,241328,241330,241336,241340,236188,3000,3006,2190,2196,2198,2202,1585,966]
  · wct_piece 42 241322 26
  · wct_piece 42 241328 27
  · wct_piece 42 241330 28
  · wct_piece 42 241336 29
  · wct_piece 42 241340 30
  · wct_piece 22 236188 0
  · wct_piece 9 3000 37
  · wct_piece 9 3006 38
  · wct_piece 5 2190 61
  · wct_piece 5 2196 62
  · wct_piece 5 2198 63
  · wct_piece 6 2202 0
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine633_ready : RoutineReady ⟨633, by decide⟩ routine633 := by
  wct_ready_start 633 19 25
  wct_cases [241341,241347,241349,241355,241359,236203,3018,3024,3026,3030,2681,1365,875,881]
  · wct_piece 42 241341 31
  · wct_piece 42 241347 32
  · wct_piece 42 241349 33
  · wct_piece 42 241355 34
  · wct_piece 42 241359 35
  · wct_piece 22 236203 5
  · wct_piece 9 3018 42
  · wct_piece 9 3024 43
  · wct_piece 9 3026 44
  · wct_piece 9 3030 45
  · wct_piece 8 2681 4
  · wct_piece 2 1365 33
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine634_ready : RoutineReady ⟨634, by decide⟩ routine634 := by
  wct_ready_start 634 19 26
  wct_cases [241360,241366,241368,241374,241378,241384,241386,241390,241396,241400,966]
  · wct_piece 42 241360 36
  · wct_piece 42 241366 37
  · wct_piece 42 241368 38
  · wct_piece 42 241374 39
  · wct_piece 42 241378 40
  · wct_piece 42 241384 41
  · wct_piece 42 241386 42
  · wct_piece 42 241390 43
  · wct_piece 42 241396 44
  · wct_piece 42 241400 45
  · wct_piece 0 966 57
theorem routine635_ready : RoutineReady ⟨635, by decide⟩ routine635 := by
  wct_ready_start 635 19 27
  wct_cases [241401,241407,241409,241415,241419,3066,3072,3075,2726,2732,2736,1585,966]
  · wct_piece 42 241401 46
  · wct_piece 42 241407 47
  · wct_piece 42 241409 48
  · wct_piece 42 241415 49
  · wct_piece 42 241419 50
  · wct_piece 9 3066 56
  · wct_piece 9 3072 57
  · wct_piece 9 3075 58
  · wct_piece 8 2726 17
  · wct_piece 8 2732 18
  · wct_piece 8 2736 19
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine636_ready : RoutineReady ⟨636, by decide⟩ routine636 := by
  wct_ready_start 636 19 28
  wct_cases [241420,241426,241428,241434,241438,236248,3087,3093,3095,3097,3101,1585,966]
  · wct_piece 42 241420 51
  · wct_piece 42 241426 52
  · wct_piece 42 241428 53
  · wct_piece 42 241434 54
  · wct_piece 42 241438 55
  · wct_piece 22 236248 20
  · wct_piece 9 3087 62
  · wct_piece 9 3093 63
  · wct_piece 10 3095 0
  · wct_piece 10 3097 1
  · wct_piece 10 3101 2
  · wct_piece 3 1585 34
  · wct_piece 0 966 57
theorem routine637_ready : RoutineReady ⟨637, by decide⟩ routine637 := by
  wct_ready_start 637 19 29
  wct_cases [241439,241445,241447,241453,236260,236266,236270,4391,2078,1120,805,811,814]
  · wct_piece 42 241439 56
  · wct_piece 42 241445 57
  · wct_piece 42 241447 58
  · wct_piece 42 241453 59
  · wct_piece 22 236260 24
  · wct_piece 22 236266 25
  · wct_piece 22 236270 26
  · wct_piece 15 4391 9
  · wct_piece 5 2078 31
  · wct_piece 1 1120 31
  · wct_piece 0 805 15
  · wct_piece 0 811 16
  · wct_piece 0 814 17
theorem routine638_ready : RoutineReady ⟨638, by decide⟩ routine638 := by
  wct_ready_start 638 19 30
  wct_cases [241454,241460,241462,241468,236282,236288,236292,4412,2099,1138,1144,875,881]
  · wct_piece 42 241454 60
  · wct_piece 42 241460 61
  · wct_piece 42 241462 62
  · wct_piece 42 241468 63
  · wct_piece 22 236282 30
  · wct_piece 22 236288 31
  · wct_piece 22 236292 32
  · wct_piece 15 4412 15
  · wct_piece 5 2099 37
  · wct_piece 1 1138 36
  · wct_piece 1 1144 37
  · wct_piece 0 875 32
  · wct_piece 0 881 33
theorem routine639_ready : RoutineReady ⟨639, by decide⟩ routine639 := by
  wct_ready_start 639 19 31
  wct_cases [241469,241475,241477,241483,236304,236310,236314,4433,2120,1162,1168,1170,1174,966]
  · wct_piece 43 241469 0
  · wct_piece 43 241475 1
  · wct_piece 43 241477 2
  · wct_piece 43 241483 3
  · wct_piece 22 236304 36
  · wct_piece 22 236310 37
  · wct_piece 22 236314 38
  · wct_piece 15 4433 21
  · wct_piece 5 2120 43
  · wct_piece 1 1162 42
  · wct_piece 1 1168 43
  · wct_piece 1 1170 44
  · wct_piece 1 1174 45
  · wct_piece 0 966 57
end W9Machine.Chain
end

section

namespace W9Machine.Chain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage19 (rank : Fin 728) (hlo : 608 ≤ rank.val) (hhi : rank.val < 640) :
    ∃ r, RoutineReady rank r := by
  rcases rank with ⟨n, hn⟩
  change 608 ≤ n at hlo
  change n < 640 at hhi
  interval_cases n
  · exact ⟨routine608, routine608_ready⟩
  · exact ⟨routine609, routine609_ready⟩
  · exact ⟨routine610, routine610_ready⟩
  · exact ⟨routine611, routine611_ready⟩
  · exact ⟨routine612, routine612_ready⟩
  · exact ⟨routine613, routine613_ready⟩
  · exact ⟨routine614, routine614_ready⟩
  · exact ⟨routine615, routine615_ready⟩
  · exact ⟨routine616, routine616_ready⟩
  · exact ⟨routine617, routine617_ready⟩
  · exact ⟨routine618, routine618_ready⟩
  · exact ⟨routine619, routine619_ready⟩
  · exact ⟨routine620, routine620_ready⟩
  · exact ⟨routine621, routine621_ready⟩
  · exact ⟨routine622, routine622_ready⟩
  · exact ⟨routine623, routine623_ready⟩
  · exact ⟨routine624, routine624_ready⟩
  · exact ⟨routine625, routine625_ready⟩
  · exact ⟨routine626, routine626_ready⟩
  · exact ⟨routine627, routine627_ready⟩
  · exact ⟨routine628, routine628_ready⟩
  · exact ⟨routine629, routine629_ready⟩
  · exact ⟨routine630, routine630_ready⟩
  · exact ⟨routine631, routine631_ready⟩
  · exact ⟨routine632, routine632_ready⟩
  · exact ⟨routine633, routine633_ready⟩
  · exact ⟨routine634, routine634_ready⟩
  · exact ⟨routine635, routine635_ready⟩
  · exact ⟨routine636, routine636_ready⟩
  · exact ⟨routine637, routine637_ready⟩
  · exact ⟨routine638, routine638_ready⟩
  · exact ⟨routine639, routine639_ready⟩
end W9Machine.Chain
end
