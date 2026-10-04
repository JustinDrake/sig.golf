import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Keygen.Blocks
import SigGolfCandidate.T3M.Keygen.Init
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
def seg_0 : List (BitVec 32) := [659,528055,134967,0x400f0f13,963331,9352067,7286819,8336419,528055,17731219,134967,0x410f0f13,963331,9352067,7286819,8336419,784339055]
def seg_46 : List (BitVec 32) := [115]
def seg_47 : List (BitVec 32) := [134711,0x3e0e0e13,134839,0x400e8e93,930563,963459,0x7a731463]
def seg_54 : List (BitVec 32) := [9319171,9352067,0x78731e63]
def seg_57 : List (BitVec 32) := [17707779,17740675,0x78731863]
def seg_60 : List (BitVec 32) := [26096387,26129283,0x78731263]
def seg_63 : List (BitVec 32) := [0x8000e93,134967,963331,9352067,7286819,8336419,0x9000e93,134967,34541331,963331,9352067,7286819,8336419,134967,34551843,34552867,0x8000e93,134967,0x80f0f13,963331,9352067,7286819,8336419,0x9000e93,134967,0xa0f0f13,963331,9352067,7286819,8336419,134967,0x80f0f13,34551843,34552867,0x70100313,915,134711,0x80e0e13,7223331,8272931,67112595,134967,0xc0f0f13,963331,9352067,7286819,8336419,83889811,134967,0xd0f0f13,963331,9352067,7286819,8336419,132407,0x8050513,0x8000593,132663,268830227]
def seg_122 : List (BitVec 32) := [115]
def seg_123 : List (BitVec 32) := [134839,269389459,32567,963331,9352067,7286819,8336419,134839,269389459,134967,302976787,963331,9352067,7286819,8336419,67112595,134967,336531219,963331,9352067,7286819,8336419,83889811,134967,353308435,963331,9352067,7286819,8336419,2451]
def seg_153 : List (BitVec 32) := [1615859823,1617529443]
def seg_155 : List (BitVec 32) := [4919,0xc0130313,34182035,134711,302910995,7223331,8272931,132407,302318867,67110291,132663,369493523]
def seg_167 : List (BitVec 32) := [115]
def seg_168 : List (BitVec 32) := [0x74010ef]
def seg_169 : List (BitVec 32) := [431715]
def seg_170 : List (BitVec 32) := [1673619,0xfb9ff06f]
def seg_172 : List (BitVec 32) := [134711,370019859,930947,34903187,34919571,134711,0x550e0e13,0x9e3023,196919,30775,369625107,32055,17632531,1043]
def seg_186 : List (BitVec 32) := [7340819,711218275]
def seg_188 : List (BitVec 32) := [2323]
def seg_189 : List (BitVec 32) := [4919,0x80030313,0xe695663]
def seg_192 : List (BitVec 32) := [1667859,67310691]
def seg_194 : List (BitVec 32) := [1662483,4919,0x80130313,17047315,31679283,295827,34479891,31712179,134711,7223331,8272931,4791827,263735,29754931,132407,67110291]
def seg_210 : List (BitVec 32) := [115]
def seg_211 : List (BitVec 32) := [4791827,265911,31329843,134967,772738835,930563,9319299,7286819,8336419,4919,0x90130313,17047315,31679283,0x4750106f]
def seg_225 : List (BitVec 32) := [33857299,31679283,134711,739118611,7223331,8272931,132407,738526483,67110291,132663,805701139]
def seg_236 : List (BitVec 32) := [115]
def seg_237 : List (BitVec 32) := [7735,0x800e0e13,19795507,5119507,3018291,134839,806260371,963331,9352067,7221283,8270883,1640723,0xf11ff06f]
def seg_250 : List (BitVec 32) := [0xb00793,6839,0xa01a8a93,17047315,32172723,0x59d000ef]
def seg_256 : List (BitVec 32) := [4461331,3412883,7537459,134327,0x4a0c8c93,7113907,2451]
def seg_263 : List (BitVec 32) := [3146515,40492131]
def seg_265 : List (BitVec 32) := [3773203,26411827,209667,4395795,263095,7540275,930563,9319299,7155747,8205347,17632531,1673619,0xfc9ff06f]
def seg_278 : List (BitVec 32) := [7342995,2451]
def seg_280 : List (BitVec 32) := [3146515,0xc69d463]
def seg_282 : List (BitVec 32) := [3773203,26411827,211459,5047,0x80038393,7998003,2707,2098067,7965283]
def seg_291 : List (BitVec 32) := [8600195,5047,0x80038393,8030899]
def seg_295 : List (BitVec 32) := [756499]
def seg_296 : List (BitVec 32) := [34278499]
def seg_297 : List (BitVec 32) := [0xfffb0b13,23745331,1274771,0xfe0388e3]
def seg_301 : List (BitVec 32) := [1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,0xfcdff06f]
def seg_310 : List (BitVec 32) := [2835]
def seg_311 : List (BitVec 32) := [7340819,74141795]
def seg_313 : List (BitVec 32) := [23745331,1274771,33789539]
def seg_316 : List (BitVec 32) := [1262355,23778227,40076387]
def seg_319 : List (BitVec 32) := [4398611,3018291,930563,9319299,6828067,7877667,17303571]
def seg_326 : List (BitVec 32) := [1772307,0xfc1ff06f]
def seg_328 : List (BitVec 32) := [723859,1673619,0xf39ff06f]
def seg_331 : List (BitVec 32) := [7342867]
def seg_332 : List (BitVec 32) := [0xb00313,40589411]
def seg_334 : List (BitVec 32) := [23745331,1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,1772307,0xfd1ff06f]
def seg_345 : List (BitVec 32) := [4464147,263267]
def seg_347 : List (BitVec 32) := [17698323]
def seg_348 : List (BitVec 32) := [134839,839814803,31329843,16855811,25244547,7221283,8270883,1311763,0xd59ff06f]
def seg_357 : List (BitVec 32) := [4919,0xb0130313,295827,134711,839781907,7223331,8272931,132407,839189779,0x8000593,132663,973473299]
def seg_369 : List (BitVec 32) := [115]
def seg_370 : List (BitVec 32) := [134839,974032531,134967,638521107,963331,9352067,7286819,8336419,135479,3987,45092115,3475,3146771,6293395,34871,772278291,0xc200893,134711,0x550e0e13,930563,218003,66063891,29620531,591635,6509715,0x3ec000ef]
def seg_396 : List (BitVec 32) := [0x425000ef]
def seg_397 : List (BitVec 32) := [2098195,6293395,34871,0xfd080813,0xc300893,134711,0x550e0e13,930563,6509459,66063891,29620531,591635,0xc35493,989855983]
def seg_411 : List (BitVec 32) := [0x3e9000ef]
def seg_412 : List (BitVec 32) := [1049619,7341971,34871,0xcb080813,0xc300893,134711,0x550e0e13,930563,0xc35393,0x7f00e13,29620531,591635,20141203,926941423]
def seg_426 : List (BitVec 32) := [986710255]
def seg_427 : List (BitVec 32) := [1043,1171,56626451,53480851,0x7e00893,134711,0x550e0e13,930563,20140947,7735,0xfffe0e13,29620531,591635,864026863]
def seg_441 : List (BitVec 32) := [1052563,133943,0x420b0b13,35767,0x890b8b93,344981743]
def seg_447 : List (BitVec 32) := [0x7690006f]
def seg_456 : List (BitVec 32) := [1530131,1657107,1644819,138167,0xa00b8b93,134327,537693331,273678575]
def seg_464 : List (BitVec 32) := [1640723,138167,0xa00b8b93,134327,588024979,0xed000ef]
def seg_470 : List (BitVec 32) := [1662483,5047,0x80038393,8261171,806355731,918419,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_485 : List (BitVec 32) := [115]
def seg_486 : List (BitVec 32) := [134839,604933779,36663,0xc40f0f13,963331,9352067,7286819,8336419,2099987,35895,0xc50c0c13,0x40000a13]
def seg_498 : List (BitVec 32) := [0xc00313,0xa6b5263]
def seg_500 : List (BitVec 32) := [23551539,1986067,4919,0xd0130313,34283283,31679283,34476947,134711,7223331,8272931,132407,67110291,132663,0x6060613]
def seg_514 : List (BitVec 32) := [115]
def seg_515 : List (BitVec 32) := [23548723,1262355,5047,0x80038393,7537459,1711635,0x41c30333,4395795,37815,33784723,7537459,209795,8601091,134839,0x60e8e93,963331,9354883,6538163,31346227,8138787,30159907,17566739,1726995,1772307,0xf5dff06f]
def seg_540 : List (BitVec 32) := [633380975,1299]
def seg_542 : List (BitVec 32) := [115]
def seg_1173 : List (BitVec 32) := [33299,1683]
def seg_1175 : List (BitVec 32) := [1049363,0xf31333,73846883]
def seg_1178 : List (BitVec 32) := [428307,133943,0x460b0b13,138167,0xa00b8b93,0xe69863]
def seg_1184 : List (BitVec 32) := [133943,0x420b0b13,527251]
def seg_1187 : List (BitVec 32) := [0xd303b3,4428691,2329779,0xda9ff0ef]
def seg_1191 : List (BitVec 32) := [1476243,0xfbdff06f]
def seg_1193 : List (BitVec 32) := [17046163,807070355,0xeedff0ef]
def seg_1196 : List (BitVec 32) := [1683,1049363,0xf31333,0xe309b3,5051283,7867443]
def seg_1202 : List (BitVec 32) := [49731683]
def seg_1203 : List (BitVec 32) := [0xd9de33,1986067,5119507,3018291,930563,9319299,7090211,8139811,17566739,1476243,0xfd5ff06f]
def seg_1214 : List (BitVec 32) := [134967,638521107,33633027,42021763,7286819,8336419,2143326319]
def seg_2074 : List (BitVec 32) := [0x03013303, 0x03813383, 0x026f3823, 0x027f3c23, 0x00020067]
def seg_543 : List (BitVec 32) := [1049235,1049875]
def seg_545 : List (BitVec 32) := [115]
def ker_546 : List (BitVec 32) := [22022803,2579,134327,0x4a0c8c93,7340819,376066659,5903123,3806099,0x40730333,21168947,32703251,6509459,3380115,134711,370019859,29590451,245251,8633987,66286355,7233075,2006675,66061203,0x406383b3,8298163,31354419,33555383,0xfff38393,8289843,0xfe7313,7541523,5135123,0x7fb7b13,0xbe5b93,0x7fbfb93,19815443,0x7fc7c13,23844963,721811,756499,232339,24926307,754579,789395,232467,23844963,721811,756499,232339,0xd7b0463,0xd8b8263,24855475,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,25936819,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,4885139,23266227,8171555,24314803,8172579,25363379,8173603,25988243,1706515,0xe9dff06f,0x7400313,7001699,1050259,32871,1683,32871,17044243,0x40136313,295827,34152211,31712179,134711,638455315,7223331,8272931,2451,4195127,0xe2698ce3,134711,638455315,54403107,132407,637863187,67110291,132663,705037843,115,134711,705564179,930563,9319299,3219,537136227,65265171,0x540e1263,7568915,30182579,3366419,8289811,30182579,6512147,8289811,30182579,9657875,8289811,30182579,0xc35e13,8289811,30182579,0xf35e13,8289811,30182579,19095059,8289811,30182579,22240787,8289811,30182579,25386515,8289811,30182579,28532243,8289811,30182579,31677971,8289811,30182579,34823699,8289811,30182579,37969427,8289811,30182579,41115155,8289811,30182579,44260883,8289811,30182579,47406611,8289811,30182579,50552339,8289811,30182579,53698067,8289811,30182579,56843795,8289811,30182579,59989523,8289811,30182579,63135251,8289811,30182579,66280979,1285779,8322707,31354419,30182579,2350611,8289811,30182579,5496339,8289811,30182579,8642067,8289811,30182579,0xb3de13,8289811,30182579,0xe3de13,8289811,30182579,18079251,8289811,30182579,21224979,8289811,30182579,24370707,8289811,30182579,27516435,8289811,30182579,30662163,8289811,30182579,33807891,8289811,30182579,36953619,8289811,30182579,40099347,8289811,30182579,43245075,8289811,30182579,46390803,8289811,30182579,49536531,8289811,30182579,52682259,8289811,30182579,55827987,8289811,30182579,58973715,8289811,30182579,62119443,8289811,30182579,0x41988e33,8392339,870219363,738197615,64216595,839784547,0xffff37,200211,0x7fe7e93,32411315,969859,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,1285779,30338611,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,4095635,31231155,3038867,4128403,31231155,5136019,31231155,0x411c8eb3,437163619,2579,133815,0x420a8a93,0x80f0f13,0x7f37e13,3022355,32378419,945795,31096867,9363091,31096995,9363091,31097123,7557907,60005907,29582131,7590803,3836563,1706515,18497043,0xfc0e10e3,3374611,30048291,2315027,3374611,30048419,2315027,3374611,30048547,32871,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,854675,263267,0xfffd0a93,2579,89806435,7343635,3149459,28989027,3149331,2100883,29589299,134711,0x420e0e13,21892659,32374819,30626611,67112467,0x41de0e33,29597235,29582131,30659507,1706515,0xfb9ff06f,265315,0x41988e33,134839,0x420e8e93,22974131,30310435,32871,1673619,0xa71ff06f]
def seg_1221 : List (BitVec 32) := [131895,394474243,0xe35313,7566099,0xee031663,0xd60ff06f]
def seg_17 : List (BitVec 32) := [40759,0xfe0f0f13,963331,9352067,7286819,8336419,0x9000e93,40759,963331,9352067,7286819,8336419,40759,0xfe0f0f13,34551843,34552867,4919,0xe0130313,915,40503,0xfe0e0e13,7223331,8272931,38199,0xfe050513,34231,67470739,132663,0x3e060613]
def seg_448 : List (BitVec 32) := [133943,0x460b0b13,138167,0xa00b8b93,36023,0xc30c8c93,1526035,307233007]
def seg_1227 : List (BitVec 32) := [134711,921107,3767,0x80e8e93,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,0xe0130313,7223331,932899,132407,328979,67110291,460343,394771,115,1049363,33755923,7224355,460343,33949203,115,0xfff00913,3758355,657847,625043,461623,723731,134327,0x3e0c8c93,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb023,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb423,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb823,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecbc23]
def seg_1432 : List (BitVec 32) := [0xa5dfe06f]
def seg_1433 : List (BitVec 32) := [2835,35895,0xbf0c0c13,6711,657939]
def seg_1438 : List (BitVec 32) := [23551539,1986067,920467,4919,0xd0130313,34280339,7562035,1823635,33788819,134711,921107,7223331,8272931,132407,328979,67110291,132663,0x6060613]
def seg_1456 : List (BitVec 32) := [115]
def seg_1457 : List (BitVec 32) := [11831,921107,1711763,0x41de0e33,25038387,5119507,528055,34508435,31329843,1834643,5152403,0xce8eb3,930563,963459,7553843,7090211,9319171,9352067,7553843,7091235,17566739,1726995,1772307,0xc00313,0xf46b6ae3]
def seg_1482 : List (BitVec 32) := [0x948ff06f]
def kerCode : List (BitVec 32) := seg_543 ++ seg_545 ++ ker_546
def seg_2045 : List (BitVec 32) := [0x40090393,0x40038393,0xff3ff13,9379603,8639379,31712179,7735,0xf0fe0e13,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,0x555e0e13,29622067,2039571,1299347,29619123,31712179,50566035,0xb20fe06f]
def seg_1483 : List (BitVec 32) := Keygen.packedHelper ++ List.drop 25 [0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013]
def signL : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, seg_543), (545, seg_545), (546, ker_546), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, Keygen.maxDigitCode), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signL_ok : layoutOk 0 signL = true := by decide +kernel
abbrev image : Image := Images.signImage
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_46 : CodeAt image (pcOf 46) seg_46 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_47 : CodeAt image (pcOf 47) seg_47 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_54 : CodeAt image (pcOf 54) seg_54 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_57 : CodeAt image (pcOf 57) seg_57 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_60 : CodeAt image (pcOf 60) seg_60 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_63 : CodeAt image (pcOf 63) seg_63 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_122 : CodeAt image (pcOf 122) seg_122 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_123 : CodeAt image (pcOf 123) seg_123 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_155 : CodeAt image (pcOf 155) seg_155 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_167 : CodeAt image (pcOf 167) seg_167 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_168 : CodeAt image (pcOf 168) seg_168 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_169 : CodeAt image (pcOf 169) seg_169 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_170 : CodeAt image (pcOf 170) seg_170 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_172 : CodeAt image (pcOf 172) seg_172 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_186 : CodeAt image (pcOf 186) seg_186 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_188 : CodeAt image (pcOf 188) seg_188 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_189 : CodeAt image (pcOf 189) seg_189 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_192 : CodeAt image (pcOf 192) seg_192 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_194 : CodeAt image (pcOf 194) seg_194 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_210 : CodeAt image (pcOf 210) seg_210 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_211 : CodeAt image (pcOf 211) seg_211 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_236 : CodeAt image (pcOf 236) seg_236 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_237 : CodeAt image (pcOf 237) seg_237 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_250 : CodeAt image (pcOf 250) seg_250 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_256 : CodeAt image (pcOf 256) seg_256 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_263 : CodeAt image (pcOf 263) seg_263 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_265 : CodeAt image (pcOf 265) seg_265 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_278 : CodeAt image (pcOf 278) seg_278 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_280 : CodeAt image (pcOf 280) seg_280 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_282 : CodeAt image (pcOf 282) seg_282 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_291 : CodeAt image (pcOf 291) seg_291 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_296 : CodeAt image (pcOf 296) seg_296 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_297 : CodeAt image (pcOf 297) seg_297 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_301 : CodeAt image (pcOf 301) seg_301 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_310 : CodeAt image (pcOf 310) seg_310 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_311 : CodeAt image (pcOf 311) seg_311 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_313 : CodeAt image (pcOf 313) seg_313 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_316 : CodeAt image (pcOf 316) seg_316 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_319 : CodeAt image (pcOf 319) seg_319 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_326 : CodeAt image (pcOf 326) seg_326 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_328 : CodeAt image (pcOf 328) seg_328 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_331 : CodeAt image (pcOf 331) seg_331 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_332 : CodeAt image (pcOf 332) seg_332 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_334 : CodeAt image (pcOf 334) seg_334 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_345 : CodeAt image (pcOf 345) seg_345 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_347 : CodeAt image (pcOf 347) seg_347 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_348 : CodeAt image (pcOf 348) seg_348 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_357 : CodeAt image (pcOf 357) seg_357 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_369 : CodeAt image (pcOf 369) seg_369 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_370 : CodeAt image (pcOf 370) seg_370 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_396 : CodeAt image (pcOf 396) seg_396 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_397 : CodeAt image (pcOf 397) seg_397 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_411 : CodeAt image (pcOf 411) seg_411 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_412 : CodeAt image (pcOf 412) seg_412 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_426 : CodeAt image (pcOf 426) seg_426 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_427 : CodeAt image (pcOf 427) seg_427 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_441 : CodeAt image (pcOf 441) seg_441 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_447 : CodeAt image (pcOf 447) seg_447 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_456 : CodeAt image (pcOf 456) seg_456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_464 : CodeAt image (pcOf 464) seg_464 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_470 : CodeAt image (pcOf 470) seg_470 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_485 : CodeAt image (pcOf 485) seg_485 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_486 : CodeAt image (pcOf 486) seg_486 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_498 : CodeAt image (pcOf 498) seg_498 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_500 : CodeAt image (pcOf 500) seg_500 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_514 : CodeAt image (pcOf 514) seg_514 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_515 : CodeAt image (pcOf 515) seg_515 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_542 : CodeAt image (pcOf 542) seg_542 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_543 : CodeAt image (pcOf 543) seg_543 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_545 : CodeAt image (pcOf 545) seg_545 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_546 : CodeAt image (pcOf 546) ker_546 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_subCode : CodeAt image (pcOf 1013) Keygen.subCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1173 : CodeAt image (pcOf 1173) seg_1173 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1175 : CodeAt image (pcOf 1175) seg_1175 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1178 : CodeAt image (pcOf 1178) seg_1178 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1184 : CodeAt image (pcOf 1184) seg_1184 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1187 : CodeAt image (pcOf 1187) seg_1187 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1191 : CodeAt image (pcOf 1191) seg_1191 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1193 : CodeAt image (pcOf 1193) seg_1193 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1196 : CodeAt image (pcOf 1196) seg_1196 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1202 : CodeAt image (pcOf 1202) seg_1202 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1203 : CodeAt image (pcOf 1203) seg_1203 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1214 : CodeAt image (pcOf 1214) seg_1214 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_17 : CodeAt image (pcOf 17) seg_17 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_448 : CodeAt image (pcOf 448) seg_448 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1227 : CodeAt image (pcOf 1227) seg_1227 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1432 : CodeAt image (pcOf 1432) seg_1432 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1433 : CodeAt image (pcOf 1433) seg_1433 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1438 : CodeAt image (pcOf 1438) seg_1438 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1456 : CodeAt image (pcOf 1456) seg_1456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1457 : CodeAt image (pcOf 1457) seg_1457 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1482 : CodeAt image (pcOf 1482) seg_1482 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_maxDigit : CodeAt image (pcOf 2013) Keygen.maxDigitCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2017 : CodeAt image (pcOf 2017) Keygen.revCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_225 : CodeAt image (pcOf 225) seg_225 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2045 : CodeAt image (pcOf 2045) seg_2045 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2074 : CodeAt image (pcOf 10947) seg_2074 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem subAt_sign : Keygen.SubAt image 1013 :=
  ⟨codeAt_subCode, Or.inr rfl, codeAt_maxDigit, codeAt_2017, Or.inr ⟨rfl, rfl⟩⟩
def signK : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, kerCode), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, Keygen.maxDigitCode), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signK_ok : layoutOk 0 signK = true := by decide +kernel
theorem codeAt_ker : CodeAt image (pcOf 543) kerCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 100
sym_block blk_47 := symRun { noAlias := true } seg_47 (pcOf 47) 100
sym_block blk_54 := symRun { noAlias := true } seg_54 (pcOf 54) 100
sym_block blk_57 := symRun { noAlias := true } seg_57 (pcOf 57) 100
sym_block blk_60 := symRun { noAlias := true } seg_60 (pcOf 60) 100
sym_block blk_63 := symRun { noAlias := true } seg_63 (pcOf 63) 100
sym_block blk_123 := symRun { noAlias := true } seg_123 (pcOf 123) 100
sym_block blk_153 := symRun { noAlias := true } seg_153 (pcOf 153) 100
sym_block blk_155 := symRun { noAlias := true } seg_155 (pcOf 155) 100
sym_block blk_168 := symRun { noAlias := true } seg_168 (pcOf 168) 100
sym_block blk_169 := symRun { noAlias := true } seg_169 (pcOf 169) 100
sym_block blk_170 := symRun { noAlias := true } seg_170 (pcOf 170) 100
sym_block blk_172 := symRun { noAlias := true } seg_172 (pcOf 172) 100
sym_block blk_186 := symRun { noAlias := true } seg_186 (pcOf 186) 100
sym_block blk_188 := symRun { noAlias := true } seg_188 (pcOf 188) 100
sym_block blk_189 := symRun { noAlias := true } seg_189 (pcOf 189) 100
sym_block blk_192 := symRun { noAlias := true } seg_192 (pcOf 192) 100
sym_block blk_194 := symRun { noAlias := true } seg_194 (pcOf 194) 100
sym_block blk_211 := symRun { noAlias := true } seg_211 (pcOf 211) 100
sym_block blk_225 := symRun { noAlias := true } seg_225 (pcOf 225) 100
sym_block blk_2045 := symRun { noAlias := true } seg_2045 (pcOf 2045) 100
sym_block blk_237 := symRun { noAlias := true } seg_237 (pcOf 237) 100
sym_block blk_250 := symRun { noAlias := true } seg_250 (pcOf 250) 100
sym_block blk_256 := symRun { noAlias := true } seg_256 (pcOf 256) 100
sym_block blk_263 := symRun { noAlias := true } seg_263 (pcOf 263) 100
sym_block blk_265 := symRun { noAlias := true } seg_265 (pcOf 265) 100
sym_block blk_278 := symRun { noAlias := true } seg_278 (pcOf 278) 100
sym_block blk_280 := symRun { noAlias := true } seg_280 (pcOf 280) 100
sym_block blk_282 := symRun { noAlias := true } seg_282 (pcOf 282) 100
sym_block blk_291 := symRun { noAlias := true } seg_291 (pcOf 291) 100
sym_block blk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 100
sym_block blk_296 := symRun { noAlias := true } seg_296 (pcOf 296) 100
sym_block blk_297 := symRun { noAlias := true } seg_297 (pcOf 297) 100
sym_block blk_301 := symRun { noAlias := true } seg_301 (pcOf 301) 100
sym_block blk_310 := symRun { noAlias := true } seg_310 (pcOf 310) 100
sym_block blk_311 := symRun { noAlias := true } seg_311 (pcOf 311) 100
sym_block blk_313 := symRun { noAlias := true } seg_313 (pcOf 313) 100
sym_block blk_316 := symRun { noAlias := true } seg_316 (pcOf 316) 100
sym_block blk_319 := symRun { noAlias := true } seg_319 (pcOf 319) 100
sym_block blk_326 := symRun { noAlias := true } seg_326 (pcOf 326) 100
sym_block blk_328 := symRun { noAlias := true } seg_328 (pcOf 328) 100
sym_block blk_331 := symRun { noAlias := true } seg_331 (pcOf 331) 100
sym_block blk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 100
sym_block blk_334 := symRun { noAlias := true } seg_334 (pcOf 334) 100
sym_block blk_345 := symRun { noAlias := true } seg_345 (pcOf 345) 100
sym_block blk_347 := symRun { noAlias := true } seg_347 (pcOf 347) 100
sym_block blk_348 := symRun { noAlias := true } seg_348 (pcOf 348) 100
sym_block blk_357 := symRun { noAlias := true } seg_357 (pcOf 357) 100
sym_block blk_370 := symRun { noAlias := true } seg_370 (pcOf 370) 100
sym_block blk_396 := symRun { noAlias := true } seg_396 (pcOf 396) 100
sym_block blk_397 := symRun { noAlias := true } seg_397 (pcOf 397) 100
sym_block blk_411 := symRun { noAlias := true } seg_411 (pcOf 411) 100
sym_block blk_412 := symRun { noAlias := true } seg_412 (pcOf 412) 100
sym_block blk_426 := symRun { noAlias := true } seg_426 (pcOf 426) 100
sym_block blk_427 := symRun { noAlias := true } seg_427 (pcOf 427) 100
sym_block blk_441 := symRun { noAlias := true } seg_441 (pcOf 441) 100
sym_block blk_447 := symRun { noAlias := true } seg_447 (pcOf 447) 100
sym_block blk_456 := symRun { noAlias := true } seg_456 (pcOf 456) 100
sym_block blk_464 := symRun { noAlias := true } seg_464 (pcOf 464) 100
sym_block blk_470 := symRun { noAlias := true } seg_470 (pcOf 470) 100
sym_block blk_486 := symRun { noAlias := true } seg_486 (pcOf 486) 100
sym_block blk_498 := symRun { noAlias := true } seg_498 (pcOf 498) 100
sym_block blk_500 := symRun { noAlias := true } seg_500 (pcOf 500) 100
sym_block blk_515 := symRun { noAlias := true } seg_515 (pcOf 515) 100
sym_block blk_540 := symRun { noAlias := true } seg_540 (pcOf 540) 100
sym_block blk_1173 := symRun { noAlias := true } seg_1173 (pcOf 1173) 100
sym_block blk_1175 := symRun { noAlias := true } seg_1175 (pcOf 1175) 100
sym_block blk_1178 := symRun { noAlias := true } seg_1178 (pcOf 1178) 100
sym_block blk_1184 := symRun { noAlias := true } seg_1184 (pcOf 1184) 100
sym_block blk_1187 := symRun { noAlias := true } seg_1187 (pcOf 1187) 100
sym_block blk_1191 := symRun { noAlias := true } seg_1191 (pcOf 1191) 100
sym_block blk_1193 := symRun { noAlias := true } seg_1193 (pcOf 1193) 100
sym_block blk_1196 := symRun { noAlias := true } seg_1196 (pcOf 1196) 100
sym_block blk_1202 := symRun { noAlias := true } seg_1202 (pcOf 1202) 100
sym_block blk_1203 := symRun { noAlias := true } seg_1203 (pcOf 1203) 100
sym_block blk_1214 := symRun { noAlias := true } seg_1214 (pcOf 1214) 100
sym_block blk_2074 := symRun { noAlias := true } seg_2074 (pcOf 10947) 100
sym_block blk_543 := symRun { noAlias := true } seg_543 (pcOf 543) 100
sym_block blk_1432 := symRun { noAlias := true } seg_1432 (pcOf 1432) 100
sym_block blk_1433 := symRun { noAlias := true } seg_1433 (pcOf 1433) 100
sym_block blk_1438 := symRun { noAlias := true } seg_1438 (pcOf 1438) 100
sym_block blk_1457 := symRun { noAlias := true } seg_1457 (pcOf 1457) 100
sym_block blk_1482 := symRun { noAlias := true } seg_1482 (pcOf 1482) 100
end SigGolfCandidate.T3M.Sign
end
section
abbrev SigGolfCandidate.T3M.Keygen.MACBLK : Nat := 0x8FE0
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateMac privateNonce mask
  privateInput header pad64 Coordinate HashOutput Digest Region)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
abbrev MSG : Nat := 0x40
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev CACHE : Nat := 0x80000
abbrev NONCE : Nat := 0x20080
abbrev RHOOUT : Nat := 0x20100
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev ENC : Nat := 0x20260
abbrev EOUT : Nat := 0x202A0
abbrev FLEAF : Nat := 0x202C0
abbrev LFOUT : Nat := 0x20300
abbrev FOREST : Nat := 0x20320
abbrev FOUT : Nat := 0x203A0
abbrev MACOUT : Nat := 0x203E0
abbrev TAG : Nat := 0x20400
abbrev DIGITS : Nat := 0x20420
abbrev SEL : Nat := 0x204A0
abbrev IDXV : Nat := 0x20550
abbrev LOW : Nat := 0x21000
abbrev FTS : Nat := 0x30000
abbrev SEC : Nat := 0x40000
macro "sg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC] at *); omega))
section tb
variable {α β : Type} {image : Image} {sk : BitVec 256}
theorem TBSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) (hW : W = W') : TBSim image sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.post_steps {s : MachineState} {W k c : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (hs : ∀ a t, Q a t → ∃ u, Steps image t k c u ∧ Q' a u) :
    TBSim image sk s (W + c) p Q' :=
  TBSim.of_eq (TBSim.bind (f := fun a => (Pure.pure a : M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TBSim.pure_steps hu hq)) (bind_pure p) rfl
theorem TBSim.publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privateNonce_bind {s : MachineState} {m : T3.Message} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inl m))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * 2 + W) (privateNonce m >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inl m)))).blocks = 2 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_nonce_eq]
    simp [bytesLE_length, SigGolfCandidate.T3.zero16]
  have : privateNonce m >>= f = privateHash (.inr (.inl m)) >>= fun a => f (a.extractLsb' 0 128) := by
    unfold privateNonce; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.privatePair_bind {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.mask_bind {s : MachineState} {level index : Nat} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header 13 0 0 level (index/2)))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (if index % 2 = 0 then a.extractLsb' 0 128 else a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (mask level index >>= f) Q := by
  have : mask level index >>= f = privatePair 13 0 0 level (index/2) >>=
      fun x => f (if index % 2 = 0 then x.1 else x.2) := by
    unfold mask T3.pairedMask; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.privatePair_bind hf ht0 hv hq h
end tb
structure Failed (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
theorem fetch_545 (s : MachineState) (hpc : s.pc = pcOf 545) : fetch image s = some (.base .ECALL) :=
  (codeAt_545.fetch s hpc).trans rfl
theorem fail_spec (s : MachineState) (hpc : s.pc = pcOf 543) :
    ∃ t, Steps image s 2 2 t ∧ Failed t ∧ RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_543 codeAt_543 s hpc (by simp [blk_543.res, rv_simp]), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [blk_543.res, E.eval]
  · simp [blk_543.res, rv_simp]
  · simp [blk_543.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_543.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_543.res, rv_simp]
theorem bv256_eq_iff (x y : BitVec 256) :
    x = y ↔ (x.extractLsb' 0 64 = y.extractLsb' 0 64 ∧ x.extractLsb' 64 64 = y.extractLsb' 64 64 ∧
      x.extractLsb' 128 64 = y.extractLsb' 128 64 ∧ x.extractLsb' 192 64 = y.extractLsb' 192 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    apply BitVec.eq_of_toNat_eq
    have e0 := congrArg BitVec.toNat h0; have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2; have e3 := congrArg BitVec.toNat h3
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at e0 e1 e2 e3
    have hx := x.isLt; have hy := y.isLt
    simp only [Nat.reducePow] at e0 e1 e2 e3 hx hy
    omega
theorem bytesToWordLE_bytes {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply Keygen.word_ext_bytes
  intro i hi
  rw [Keygen.extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [Keygen.extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
end SigGolfCandidate.T3M.Sign
end
