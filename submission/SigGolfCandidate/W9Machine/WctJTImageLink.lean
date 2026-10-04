import SigGolfCandidate.W9Machine.WctJTCheck14
import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def jtWords60 : List (BitVec 32) :=
  [0xea81d06f,0xee41d06f,0xf201d06f,0xf5c1d06f,0xf981d06f,0xfd41d06f,0x8111d06f,0x8611d06f,0x8b11d06f,0x9011d06f,0x96d1d06f,0x9c91d06f,0xa3d1d06f,0xa6d1d06f,0xa9d1d06f,0xacd1d06f,0xafd1d06f,0xb2d1d06f,0xb5d1d06f,0xb8d1d06f,0xbbd1d06f,0xbed1d06f,0xc1d1d06f,0xc4d1d06f,0xc7d1d06f,0xcc91d06f,0xd151d06f,0xd611d06f,0xdad1d06f,0xde91d06f,0xe251d06f,0xe611d06f,0xe9d1d06f,0xed91d06f,0xf151d06f,0xf691d06f,0xfbd1d06f,0x8101e06f,0x8581e06f,0x8a01e06f,0x8e81e06f,0x9441e06f,0x9a01e06f,0xa181e06f,0xa501e06f,0xa881e06f,0xac01e06f,0xaf81e06f,0xb301e06f,0xb681e06f,0xba01e06f,0xbd81e06f,0xc101e06f,0xc481e06f,0xc9c1e06f,0xcf01e06f,0xd441e06f,0xd881e06f,0xdcc1e06f,0xe101e06f,0xe6c1e06f,0xec81e06f,0xf181e06f,0xf7c1e06f,0xfa41e06f,0xfcc1e06f,0xff41e06f,0x81d1e06f,0x8451e06f,0x86d1e06f,0x8951e06f,0x8bd1e06f,0x8e51e06f,0x90d1e06f,0x9351e06f,0x95d1e06f,0x9851e06f,0x9d51e06f,0x9fd1e06f,0xa251e06f,0xa4d1e06f,0xa751e06f,0xa9d1e06f,0xac51e06f,0xaed1e06f,0xb151e06f,0xb3d1e06f,0xb651e06f,0xb8d1e06f,0xbb51e06f,0xbdd1e06f,0xc051e06f,0xc511e06f,0xc791e06f,0xca11e06f,0xcc91e06f,0xd151e06f,0xd3d1e06f,0xd651e06f,0xd8d1e06f,0xdb51e06f,0xddd1e06f,0xe051e06f,0xe2d1e06f,0xe6d1e06f,0xead1e06f,0xeed1e06f,0xf2d1e06f,0xf6d1e06f,0xfad1e06f,0xfed1e06f,0x82c1f06f,0x86c1f06f,0x8ac1f06f,0x8ec1f06f,0x92c1f06f,0x95c1f06f,0x98c1f06f,0x9bc1f06f,0x9ec1f06f,0xa1c1f06f,0xa4c1f06f,0xa7c1f06f,0xaac1f06f,0xadc1f06f,0xb0c1f06f,0xb3c1f06f,0xb6c1f06f,0xb9c1f06f,0xbcc1f06f,0xbfc1f06f,0xc2c1f06f,0xc5c1f06f,0xc8c1f06f,0xcbc1f06f,0xd041f06f,0xd4c1f06f,0xd941f06f,0xddc1f06f,0xe241f06f,0xe6c1f06f,0xeb41f06f,0xefc1f06f,0xf441f06f,0xf8c1f06f,0xfc81f06f,0x8051f06f,0x8411f06f,0x87d1f06f,0x8b91f06f,0x8f51f06f,0x9311f06f,0x96d1f06f,0x9a91f06f,0x9e51f06f,0xa351f06f,0xa851f06f,0xad51f06f,0xb251f06f,0xb751f06f,0xbc51f06f,0xc311f06f,0xc9d1f06f,0xcf91f06f,0xd6d1f06f,0xd9d1f06f,0xdcd1f06f,0xdfd1f06f,0xe2d1f06f,0xe5d1f06f,0xe8d1f06f,0xebd1f06f,0xeed1f06f,0xf1d1f06f,0xf4d1f06f,0x5450006f,0x5750006f,0x5a50006f,0x5d50006f,0x6050006f,0x6350006f,0x6650006f,0x6950006f,0x6c50006f,0x6f50006f,0x7250006f,0x7550006f,0x7850006f,0x7b50006f,0x7e50006f,20975727,71307375,0x740106f,0xa40106f,0xd40106f,272633967,352325743,432017519,511709295,591401071,671092847,750784623,830476399,910168175,989859951,0x3fc0106f,0x4380106f,0x4740106f,0x4b00106f,0x4ec0106f,0x5280106f,0x5640106f,0x5a00106f,0x5dc0106f,0x6180106f,0x6540106f,0x6a80106f,0x6fc0106f,0x7500106f,0x7a40106f,0x7f80106f,80744559,0x950106f,273682543,349180015,424677487,521146479,617615471,714084463,839913583,898633839,957354095,0x3c90106f,0x4010106f,0x4390106f,0x4710106f,0x4a90106f,0x4e10106f,0x5190106f,0x5510106f,0x5890106f,0x5c10106f,0x5f90106f,0x6310106f,0x6690106f,0x6a10106f,0x6d90106f,0x7110106f,0x7490106f,0x7810106f,0x7d50106f,41951343,0x7c0206f,0xd00206f,306192495,394272879]
theorem jtCheck60 : jtCheck 15360 jtWords60 = true := by
  decide +kernel
def jtWords61 : List (BitVec 32) :=
  [465576047,536879215,608182383,679485551,775954543,872423535,968892527,0x3ec0206f,0x4500206f,0x4680206f,0x4800206f,0x4980206f,0x4b00206f,0x4c80206f,0x4e00206f,0x4f80206f,0x5100206f,0x5280206f,0x5400206f,0x5580206f,0x5700206f,0x5880206f,0x5a00206f,0x5b80206f,0x5d00206f,0x5e80206f,0x6000206f,0x6180206f,0x6300206f,0x6480206f,0x6600206f,0x6780206f,0x6900206f,0x6a80206f,0x6c00206f,0x6d80206f,0x6f00206f,0x7080206f,0x7200206f,0x7380206f,0x7500206f,0x7680206f,0x7800206f,0x7980206f,0x7b00206f,0x7c80206f,0x7e00206f,0x7f80206f,17834095,42999919,68165743,93331567,0x990206f,0xd90206f,294658159,319823983,386932847,454041711,521150575,546316399,571482223,596648047,646979695,697311343,722477167,772808815,797974639,823140463,848306287,898637935,923803759,948969583,974135407,999301231,0x3e90206f,0x4190206f,0x4310206f,0x4490206f,0x4610206f,0x4790206f,0x4910206f,0x4a90206f,0x4c10206f,0x4d90206f,0x5210206f,0x5390206f,0x5510206f,0x5690206f,0x5b10206f,0x5c90206f,0x5e10206f,0x61d0206f,0x6590206f,0x6950206f,0x6d10206f,0x6e90206f,0x7010206f,0x73d0206f,0x7550206f,0x76d0206f,0x7850206f,0x79d0206f,0x7b50206f,0x7cd0206f,0x7e50206f,0x7fd0206f,20983919,46149743,71315567,96481391,0x9c0306f,0xdc0306f,297807983,364916847,432025711,499134575,566243439,633352303,700461167,767570031,834678895,901787759,968896623,0x4540306f,0x50c0306f,0x5740306f,0x62c0306f,0x6b40306f,0x7540306f,0x7dc0306f,0x950306f,0xd50306f,290467951,433074287,600846447,793784431,986722415,0x3ed0306f,0x42d0306f,0x4cd0306f,0x50d0306f,0x53d0306f,0x5950306f,0x5ed0306f,0x61d0306f,0x6d50306f,0x75d0306f,0x7fd0306f,0x840406f,331366511,381698159,457195631,599801967,767574127,910180463,0x4040406f,0x4340406f,0x4640406f,0x5040406f,0x54c0406f,0x57c0406f,0x5ac0406f,0x5dc0406f,0x60c0406f,0x6940406f,0x7340406f,0x7640406f,0x7b80406f,0x710406f,0xc50406f,0xf50406f,307249263,357580911,407912559,458244207,533741679,609239151,684736623,760234095,835731567,911229039,986726511,0x3f50406f,0x43d0406f,0x4850406f,0x4cd0406f,0x5550406f,0x5f50406f,0x67d0406f,0x71d0406f,0x7650406f,0x7ad0406f,79712367,0x940506f,0xdc0506f,293621871,398479471,503337071,696275055,889213039,994070639,0x4080506f,0x4c00506f,0x5140506f,0x5500506f,0x58c0506f,0x5f80506f,0x6640506f,0x6a00506f,0x6dc0506f,0x72c0506f,0x77c0506f,0x7cc0506f,30429295,0x6d0506f,0xbd0506f,282087535,449859695,533745775,617631855,730878063,844124271,957370479,0x3ed0506f,0x4610506f,0x4810506f,0x4a10506f,0x4c10506f,0x4e10506f,0x5010506f,0x5210506f,0x5410506f,0x5610506f,0x5810506f,0x5a10506f,0x5c10506f,0x5e10506f,0x6010506f,0x6210506f,0x6410506f,0x6610506f,0x6810506f,0x6a10506f,0x6c10506f,0x6e10506f,0x7010506f,0x7210506f,0x7410506f,0x7610506f,0x7810506f,0x7a10506f,0x7c10506f,0x7e10506f,24687,33579119,67133551]
theorem jtCheck61 : jtCheck 15616 jtWords61 = true := by
  decide +kernel
def jtWords62 : List (BitVec 32) :=
  [0x600606f,0x800606f,0xa00606f,0xc00606f,0xe00606f,268460143,302014575,335569007,369123439,402677871,436232303,469786735,503341167,536895599,570450031,604004463,637558895,671113327,704667759,738222191,771776623,805331055,838885487,872439919,905994351,939548783,973103215,0x3c00606f,0x3e00606f,0x4000606f,0x4200606f,0x4400606f,0x4600606f,0x4800606f,0x4c80606f,0x5100606f,0x5580606f,0x5a00606f,0x5e80606f,0x6300606f,0x6780606f,0x6c00606f,0x7080606f,0x7500606f,0x7980606f,34627695,0xc10606f,345006191,512778351,588275823,663773295,831545455,907042927,982540399,0x3e10606f,0x4190606f,0x4510606f,0x4d90606f,0x5790606f,0x5b10606f,0x5e90606f,0x6890606f,0x6c10606f,0x6f90606f,0x7310606f,0x7690606f,0x7a10606f,0x7d90606f,16805999,0x600706f,0xb00706f,268464239,352350319,436236399,520122479,604008559,771780719,855666799,939552879,0x3c40706f,0x4300706f,0x49c0706f,0x4e00706f,0x5240706f,0x57c0706f,0x5d40706f,0x62c0706f,0x6840706f,0x6f80706f,0x7200706f,0x7480706f,0x7700706f,0x7980706f,0x7c00706f,0x7e80706f,17854575,59797615,0x610706f,0x890706f,0xb10706f,0xd90706f,269512815,311455855,353398895,395341935,437284975,479228015,521171055,563114095,605057135,647000175,688943215,730886255,772829295,814772335,856715375,898658415,940601455,982544495,0x3d10706f,0x3f90706f,0x4210706f,0x4490706f,0x4710706f,0x4c10706f,0x5110706f,0x5610706f,0x5b10706f,0x6010706f,0x6510706f,0x6a10706f,0x7410706f,0x7910706f,0x7e10706f,33587311,0x600806f,0xa00806f,0xe00806f,302022767,394297455,486572143,578846831,671121519,750813295,0xe211a06f,0xe1d1a06f,0xe191a06f,0xe151a06f,0xe111a06f,0xe0d1a06f,0xe091a06f,0xe051a06f,0xe011a06f,0xdfd1a06f,0xdf91a06f,0xdf51a06f,0xdf11a06f,0xded1a06f,0xde91a06f,0xde51a06f,0xde11a06f,0xddd1a06f,0xdd91a06f,0xdd51a06f,0xdd11a06f,0xdcd1a06f,0xdc91a06f,0xdc51a06f,0xdc11a06f,0xdbd1a06f,0xdb91a06f,0xdb51a06f,0xdb11a06f,0xdad1a06f,0xda91a06f,0xda51a06f,0xda11a06f,0xd9d1a06f,0xd991a06f,0xd951a06f,0xd911a06f,0xd8d1a06f,0xd891a06f,0xd851a06f,0xd811a06f,0xd7d1a06f,0xd791a06f,0xd751a06f,0xd711a06f,0xd6d1a06f,0xd691a06f,0xd651a06f,0xd611a06f,0xd5d1a06f,0xd591a06f,0xd551a06f,0xd511a06f,0xd4d1a06f,0xd491a06f,0xd451a06f,0xd411a06f,0xd3d1a06f,0xd391a06f,0xd351a06f,0xd311a06f,0xd2d1a06f,0xd291a06f,0xd251a06f,0xd211a06f,0xd1d1a06f,0xd191a06f,0xd151a06f,0xd111a06f,0xd0d1a06f,0xd091a06f,0xd051a06f,0xd011a06f,0xcfd1a06f,0xcf91a06f,0xcf51a06f,0xcf11a06f,0xced1a06f,0xce91a06f,0xce51a06f,0xce11a06f,0xcdd1a06f,0xcd91a06f,0xcd51a06f,0xcd11a06f,0xccd1a06f,0xcc91a06f,0xcc51a06f,0xcc11a06f,0xcbd1a06f,0xcb91a06f,0xcb51a06f,0xcb11a06f,0xcad1a06f,0xca91a06f,0xca51a06f,0xca11a06f,0xc9d1a06f,0xc991a06f,0xc951a06f,0xc911a06f,0xc8d1a06f,0xc891a06f,0xc851a06f,0xc811a06f,0xc7d1a06f,0xc791a06f,0xc751a06f,0xc711a06f,0xc6d1a06f,0xc691a06f,0xc651a06f]
theorem jtCheck62 : jtCheck 15872 jtWords62 = true := by
  decide +kernel
def jtWords63 : List (BitVec 32) :=
  [0xc611a06f,0xc5d1a06f,0xc591a06f,0xc551a06f,0xc511a06f,0xc4d1a06f,0xc491a06f,0xc451a06f,0xc411a06f,0xc3d1a06f,0xc391a06f,0xc351a06f,0xc311a06f,0xc2d1a06f,0xc291a06f,0xc251a06f,0xc211a06f,0xc1d1a06f,0xc191a06f,0xc151a06f,0xc111a06f,0xc0d1a06f,0xc091a06f,0xc051a06f,0xc011a06f,0xbfd1a06f,0xbf91a06f,0xbf51a06f,0xbf11a06f,0xbed1a06f,0xbe91a06f,0xbe51a06f,0xbe11a06f,0xbdd1a06f,0xbd91a06f,0xbd51a06f,0xbd11a06f,0xbcd1a06f,0xbc91a06f,0xbc51a06f,0xbc11a06f,0xbbd1a06f,0xbb91a06f,0xbb51a06f,0xbb11a06f,0xbad1a06f,0xba91a06f,0xba51a06f,0xba11a06f,0xb9d1a06f,0xb991a06f,0xb951a06f,0xb911a06f,0xb8d1a06f,0xb891a06f,0xb851a06f,0xb811a06f,0xb7d1a06f,0xb791a06f,0xb751a06f,0xb711a06f,0xb6d1a06f,0xb691a06f,0xb651a06f,0xb611a06f,0xb5d1a06f,0xb591a06f,0xb551a06f,0xb511a06f,0xb4d1a06f,0xb491a06f,0xb451a06f,0xb411a06f,0xb3d1a06f,0xb391a06f,0xb351a06f,0xb311a06f,0xb2d1a06f,0xb291a06f,0xb251a06f,0xb211a06f,0xb1d1a06f,0xb191a06f,0xb151a06f,0xb111a06f,0xb0d1a06f,0xb091a06f,0xb051a06f,0xb011a06f,0xafd1a06f,0xaf91a06f,0xaf51a06f,0xaf11a06f,0xaed1a06f,0xae91a06f,0xae51a06f,0xae11a06f,0xadd1a06f,0xad91a06f,0xad51a06f,0xad11a06f,0xacd1a06f,0xac91a06f,0xac51a06f,0xac11a06f,0xabd1a06f,0xab91a06f,0xab51a06f,0xab11a06f,0xaad1a06f,0xaa91a06f,0xaa51a06f,0xaa11a06f,0xa9d1a06f,0xa991a06f,0xa951a06f,0xa911a06f,0xa8d1a06f,0xa891a06f,0xa851a06f,0xa811a06f,0xa7d1a06f,0xa791a06f,0xa751a06f,0xa711a06f,0xa6d1a06f,0xa691a06f,0xa651a06f,0xa611a06f,0xa5d1a06f,0xa591a06f,0xa551a06f,0xa511a06f,0xa4d1a06f,0xa491a06f,0xa451a06f,0xa411a06f,0xa3d1a06f,0xa391a06f,0xa351a06f,0xa311a06f,0xa2d1a06f,0xa291a06f,0xa251a06f,0xa211a06f,0xa1d1a06f,0xa191a06f,0xa151a06f,0xa111a06f,0xa0d1a06f,0xa091a06f,0xa051a06f,0xa011a06f,0x9fd1a06f,0x9f91a06f,0x9f51a06f,0x9f11a06f,0x9ed1a06f,0x9e91a06f,0x9e51a06f,0x9e11a06f,0x9dd1a06f,0x9d91a06f,0x9d51a06f,0x9d11a06f,0x9cd1a06f,0x9c91a06f,0x9c51a06f,0x9c11a06f,0x9bd1a06f,0x9b91a06f,0x9b51a06f,0x9b11a06f,0x9ad1a06f,0x9a91a06f,0x9a51a06f,0x9a11a06f,0x99d1a06f,0x9991a06f,0x9951a06f,0x9911a06f,0x98d1a06f,0x9891a06f,0x9851a06f,0x9811a06f,0x97d1a06f,0x9791a06f,0x9751a06f,0x9711a06f,0x96d1a06f,0x9691a06f,0x9651a06f,0x9611a06f,0x95d1a06f,0x9591a06f,0x9551a06f,0x9511a06f,0x94d1a06f,0x9491a06f,0x9451a06f,0x9411a06f,0x93d1a06f,0x9391a06f,0x9351a06f,0x9311a06f,0x92d1a06f,0x9291a06f,0x9251a06f,0x9211a06f,0x91d1a06f,0x9191a06f,0x9151a06f,0x9111a06f,0x90d1a06f,0x9091a06f,0x9051a06f,0x9011a06f,0x8fd1a06f,0x8f91a06f,0x8f51a06f,0x8f11a06f,0x8ed1a06f,0x8e91a06f,0x8e51a06f,0x8e11a06f,0x8dd1a06f,0x8d91a06f,0x8d51a06f,0x8d11a06f,0x8cd1a06f,0x8c91a06f,0x8c51a06f,0x8c11a06f,0x8bd1a06f,0x8b91a06f,0x8b51a06f,0x8b11a06f,0x8ad1a06f,0x8a91a06f,0x8a51a06f,0x8a11a06f,0x89d1a06f,0x8991a06f,0x8951a06f,0x8911a06f,0x88d1a06f,0x8891a06f,0x8851a06f,0x8811a06f,0x87d1a06f,0x8791a06f,0x8751a06f,0x8711a06f,0x86d1a06f,0x8691a06f,0x8651a06f]
theorem jtCheck63 : jtCheck 16128 jtWords63 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
def AllJTChecked : Prop :=
  jtCheck 0 jtWords00 = true ∧
  jtCheck 256 jtWords01 = true ∧
  jtCheck 512 jtWords02 = true ∧
  jtCheck 768 jtWords03 = true ∧
  jtCheck 1024 jtWords04 = true ∧
  jtCheck 1280 jtWords05 = true ∧
  jtCheck 1536 jtWords06 = true ∧
  jtCheck 1792 jtWords07 = true ∧
  jtCheck 2048 jtWords08 = true ∧
  jtCheck 2304 jtWords09 = true ∧
  jtCheck 2560 jtWords10 = true ∧
  jtCheck 2816 jtWords11 = true ∧
  jtCheck 3072 jtWords12 = true ∧
  jtCheck 3328 jtWords13 = true ∧
  jtCheck 3584 jtWords14 = true ∧
  jtCheck 3840 jtWords15 = true ∧
  jtCheck 4096 jtWords16 = true ∧
  jtCheck 4352 jtWords17 = true ∧
  jtCheck 4608 jtWords18 = true ∧
  jtCheck 4864 jtWords19 = true ∧
  jtCheck 5120 jtWords20 = true ∧
  jtCheck 5376 jtWords21 = true ∧
  jtCheck 5632 jtWords22 = true ∧
  jtCheck 5888 jtWords23 = true ∧
  jtCheck 6144 jtWords24 = true ∧
  jtCheck 6400 jtWords25 = true ∧
  jtCheck 6656 jtWords26 = true ∧
  jtCheck 6912 jtWords27 = true ∧
  jtCheck 7168 jtWords28 = true ∧
  jtCheck 7424 jtWords29 = true ∧
  jtCheck 7680 jtWords30 = true ∧
  jtCheck 7936 jtWords31 = true ∧
  jtCheck 8192 jtWords32 = true ∧
  jtCheck 8448 jtWords33 = true ∧
  jtCheck 8704 jtWords34 = true ∧
  jtCheck 8960 jtWords35 = true ∧
  jtCheck 9216 jtWords36 = true ∧
  jtCheck 9472 jtWords37 = true ∧
  jtCheck 9728 jtWords38 = true ∧
  jtCheck 9984 jtWords39 = true ∧
  jtCheck 10240 jtWords40 = true ∧
  jtCheck 10496 jtWords41 = true ∧
  jtCheck 10752 jtWords42 = true ∧
  jtCheck 11008 jtWords43 = true ∧
  jtCheck 11264 jtWords44 = true ∧
  jtCheck 11520 jtWords45 = true ∧
  jtCheck 11776 jtWords46 = true ∧
  jtCheck 12032 jtWords47 = true ∧
  jtCheck 12288 jtWords48 = true ∧
  jtCheck 12544 jtWords49 = true ∧
  jtCheck 12800 jtWords50 = true ∧
  jtCheck 13056 jtWords51 = true ∧
  jtCheck 13312 jtWords52 = true ∧
  jtCheck 13568 jtWords53 = true ∧
  jtCheck 13824 jtWords54 = true ∧
  jtCheck 14080 jtWords55 = true ∧
  jtCheck 14336 jtWords56 = true ∧
  jtCheck 14592 jtWords57 = true ∧
  jtCheck 14848 jtWords58 = true ∧
  jtCheck 15104 jtWords59 = true ∧
  jtCheck 15360 jtWords60 = true ∧
  jtCheck 15616 jtWords61 = true ∧
  jtCheck 15872 jtWords62 = true ∧
  jtCheck 16128 jtWords63 = true
theorem allJTChecked : AllJTChecked := by
  exact ⟨jtCheck00, jtCheck01, jtCheck02, jtCheck03, jtCheck04, jtCheck05, jtCheck06, jtCheck07, jtCheck08, jtCheck09, jtCheck10, jtCheck11, jtCheck12, jtCheck13, jtCheck14, jtCheck15, jtCheck16, jtCheck17, jtCheck18, jtCheck19, jtCheck20, jtCheck21, jtCheck22, jtCheck23, jtCheck24, jtCheck25, jtCheck26, jtCheck27, jtCheck28, jtCheck29, jtCheck30, jtCheck31, jtCheck32, jtCheck33, jtCheck34, jtCheck35, jtCheck36, jtCheck37, jtCheck38, jtCheck39, jtCheck40, jtCheck41, jtCheck42, jtCheck43, jtCheck44, jtCheck45, jtCheck46, jtCheck47, jtCheck48, jtCheck49, jtCheck50, jtCheck51, jtCheck52, jtCheck53, jtCheck54, jtCheck55, jtCheck56, jtCheck57, jtCheck58, jtCheck59, jtCheck60, jtCheck61, jtCheck62, jtCheck63⟩
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt60_linked : sliceChecked 233984 jtWords60 = true := by
  decide +kernel
theorem jt60_at : CodeAt Frozen.image (pcOf 233984) jtWords60 :=
  slice_at _ _ jt60_linked
theorem jt61_linked : sliceChecked 234240 jtWords61 = true := by
  decide +kernel
theorem jt61_at : CodeAt Frozen.image (pcOf 234240) jtWords61 :=
  slice_at _ _ jt61_linked
theorem jt62_linked : sliceChecked 234496 jtWords62 = true := by
  decide +kernel
theorem jt62_at : CodeAt Frozen.image (pcOf 234496) jtWords62 :=
  slice_at _ _ jt62_linked
theorem jt63_linked : sliceChecked 234752 jtWords63 = true := by
  decide +kernel
theorem jt63_at : CodeAt Frozen.image (pcOf 234752) jtWords63 :=
  slice_at _ _ jt63_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt56_linked : sliceChecked 232960 jtWords56 = true := by
  decide +kernel
theorem jt56_at : CodeAt Frozen.image (pcOf 232960) jtWords56 :=
  slice_at _ _ jt56_linked
theorem jt57_linked : sliceChecked 233216 jtWords57 = true := by
  decide +kernel
theorem jt57_at : CodeAt Frozen.image (pcOf 233216) jtWords57 :=
  slice_at _ _ jt57_linked
theorem jt58_linked : sliceChecked 233472 jtWords58 = true := by
  decide +kernel
theorem jt58_at : CodeAt Frozen.image (pcOf 233472) jtWords58 :=
  slice_at _ _ jt58_linked
theorem jt59_linked : sliceChecked 233728 jtWords59 = true := by
  decide +kernel
theorem jt59_at : CodeAt Frozen.image (pcOf 233728) jtWords59 :=
  slice_at _ _ jt59_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt52_linked : sliceChecked 231936 jtWords52 = true := by
  decide +kernel
theorem jt52_at : CodeAt Frozen.image (pcOf 231936) jtWords52 :=
  slice_at _ _ jt52_linked
theorem jt53_linked : sliceChecked 232192 jtWords53 = true := by
  decide +kernel
theorem jt53_at : CodeAt Frozen.image (pcOf 232192) jtWords53 :=
  slice_at _ _ jt53_linked
theorem jt54_linked : sliceChecked 232448 jtWords54 = true := by
  decide +kernel
theorem jt54_at : CodeAt Frozen.image (pcOf 232448) jtWords54 :=
  slice_at _ _ jt54_linked
theorem jt55_linked : sliceChecked 232704 jtWords55 = true := by
  decide +kernel
theorem jt55_at : CodeAt Frozen.image (pcOf 232704) jtWords55 :=
  slice_at _ _ jt55_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt48_linked : sliceChecked 230912 jtWords48 = true := by
  decide +kernel
theorem jt48_at : CodeAt Frozen.image (pcOf 230912) jtWords48 :=
  slice_at _ _ jt48_linked
theorem jt49_linked : sliceChecked 231168 jtWords49 = true := by
  decide +kernel
theorem jt49_at : CodeAt Frozen.image (pcOf 231168) jtWords49 :=
  slice_at _ _ jt49_linked
theorem jt50_linked : sliceChecked 231424 jtWords50 = true := by
  decide +kernel
theorem jt50_at : CodeAt Frozen.image (pcOf 231424) jtWords50 :=
  slice_at _ _ jt50_linked
theorem jt51_linked : sliceChecked 231680 jtWords51 = true := by
  decide +kernel
theorem jt51_at : CodeAt Frozen.image (pcOf 231680) jtWords51 :=
  slice_at _ _ jt51_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt44_linked : sliceChecked 229888 jtWords44 = true := by
  decide +kernel
theorem jt44_at : CodeAt Frozen.image (pcOf 229888) jtWords44 :=
  slice_at _ _ jt44_linked
theorem jt45_linked : sliceChecked 230144 jtWords45 = true := by
  decide +kernel
theorem jt45_at : CodeAt Frozen.image (pcOf 230144) jtWords45 :=
  slice_at _ _ jt45_linked
theorem jt46_linked : sliceChecked 230400 jtWords46 = true := by
  decide +kernel
theorem jt46_at : CodeAt Frozen.image (pcOf 230400) jtWords46 :=
  slice_at _ _ jt46_linked
theorem jt47_linked : sliceChecked 230656 jtWords47 = true := by
  decide +kernel
theorem jt47_at : CodeAt Frozen.image (pcOf 230656) jtWords47 :=
  slice_at _ _ jt47_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt40_linked : sliceChecked 228864 jtWords40 = true := by
  decide +kernel
theorem jt40_at : CodeAt Frozen.image (pcOf 228864) jtWords40 :=
  slice_at _ _ jt40_linked
theorem jt41_linked : sliceChecked 229120 jtWords41 = true := by
  decide +kernel
theorem jt41_at : CodeAt Frozen.image (pcOf 229120) jtWords41 :=
  slice_at _ _ jt41_linked
theorem jt42_linked : sliceChecked 229376 jtWords42 = true := by
  decide +kernel
theorem jt42_at : CodeAt Frozen.image (pcOf 229376) jtWords42 :=
  slice_at _ _ jt42_linked
theorem jt43_linked : sliceChecked 229632 jtWords43 = true := by
  decide +kernel
theorem jt43_at : CodeAt Frozen.image (pcOf 229632) jtWords43 :=
  slice_at _ _ jt43_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt36_linked : sliceChecked 227840 jtWords36 = true := by
  decide +kernel
theorem jt36_at : CodeAt Frozen.image (pcOf 227840) jtWords36 :=
  slice_at _ _ jt36_linked
theorem jt37_linked : sliceChecked 228096 jtWords37 = true := by
  decide +kernel
theorem jt37_at : CodeAt Frozen.image (pcOf 228096) jtWords37 :=
  slice_at _ _ jt37_linked
theorem jt38_linked : sliceChecked 228352 jtWords38 = true := by
  decide +kernel
theorem jt38_at : CodeAt Frozen.image (pcOf 228352) jtWords38 :=
  slice_at _ _ jt38_linked
theorem jt39_linked : sliceChecked 228608 jtWords39 = true := by
  decide +kernel
theorem jt39_at : CodeAt Frozen.image (pcOf 228608) jtWords39 :=
  slice_at _ _ jt39_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt32_linked : sliceChecked 226816 jtWords32 = true := by
  decide +kernel
theorem jt32_at : CodeAt Frozen.image (pcOf 226816) jtWords32 :=
  slice_at _ _ jt32_linked
theorem jt33_linked : sliceChecked 227072 jtWords33 = true := by
  decide +kernel
theorem jt33_at : CodeAt Frozen.image (pcOf 227072) jtWords33 :=
  slice_at _ _ jt33_linked
theorem jt34_linked : sliceChecked 227328 jtWords34 = true := by
  decide +kernel
theorem jt34_at : CodeAt Frozen.image (pcOf 227328) jtWords34 :=
  slice_at _ _ jt34_linked
theorem jt35_linked : sliceChecked 227584 jtWords35 = true := by
  decide +kernel
theorem jt35_at : CodeAt Frozen.image (pcOf 227584) jtWords35 :=
  slice_at _ _ jt35_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt28_linked : sliceChecked 225792 jtWords28 = true := by
  decide +kernel
theorem jt28_at : CodeAt Frozen.image (pcOf 225792) jtWords28 :=
  slice_at _ _ jt28_linked
theorem jt29_linked : sliceChecked 226048 jtWords29 = true := by
  decide +kernel
theorem jt29_at : CodeAt Frozen.image (pcOf 226048) jtWords29 :=
  slice_at _ _ jt29_linked
theorem jt30_linked : sliceChecked 226304 jtWords30 = true := by
  decide +kernel
theorem jt30_at : CodeAt Frozen.image (pcOf 226304) jtWords30 :=
  slice_at _ _ jt30_linked
theorem jt31_linked : sliceChecked 226560 jtWords31 = true := by
  decide +kernel
theorem jt31_at : CodeAt Frozen.image (pcOf 226560) jtWords31 :=
  slice_at _ _ jt31_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt24_linked : sliceChecked 224768 jtWords24 = true := by
  decide +kernel
theorem jt24_at : CodeAt Frozen.image (pcOf 224768) jtWords24 :=
  slice_at _ _ jt24_linked
theorem jt25_linked : sliceChecked 225024 jtWords25 = true := by
  decide +kernel
theorem jt25_at : CodeAt Frozen.image (pcOf 225024) jtWords25 :=
  slice_at _ _ jt25_linked
theorem jt26_linked : sliceChecked 225280 jtWords26 = true := by
  decide +kernel
theorem jt26_at : CodeAt Frozen.image (pcOf 225280) jtWords26 :=
  slice_at _ _ jt26_linked
theorem jt27_linked : sliceChecked 225536 jtWords27 = true := by
  decide +kernel
theorem jt27_at : CodeAt Frozen.image (pcOf 225536) jtWords27 :=
  slice_at _ _ jt27_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt20_linked : sliceChecked 223744 jtWords20 = true := by
  decide +kernel
theorem jt20_at : CodeAt Frozen.image (pcOf 223744) jtWords20 :=
  slice_at _ _ jt20_linked
theorem jt21_linked : sliceChecked 224000 jtWords21 = true := by
  decide +kernel
theorem jt21_at : CodeAt Frozen.image (pcOf 224000) jtWords21 :=
  slice_at _ _ jt21_linked
theorem jt22_linked : sliceChecked 224256 jtWords22 = true := by
  decide +kernel
theorem jt22_at : CodeAt Frozen.image (pcOf 224256) jtWords22 :=
  slice_at _ _ jt22_linked
theorem jt23_linked : sliceChecked 224512 jtWords23 = true := by
  decide +kernel
theorem jt23_at : CodeAt Frozen.image (pcOf 224512) jtWords23 :=
  slice_at _ _ jt23_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt16_linked : sliceChecked 222720 jtWords16 = true := by
  decide +kernel
theorem jt16_at : CodeAt Frozen.image (pcOf 222720) jtWords16 :=
  slice_at _ _ jt16_linked
theorem jt17_linked : sliceChecked 222976 jtWords17 = true := by
  decide +kernel
theorem jt17_at : CodeAt Frozen.image (pcOf 222976) jtWords17 :=
  slice_at _ _ jt17_linked
theorem jt18_linked : sliceChecked 223232 jtWords18 = true := by
  decide +kernel
theorem jt18_at : CodeAt Frozen.image (pcOf 223232) jtWords18 :=
  slice_at _ _ jt18_linked
theorem jt19_linked : sliceChecked 223488 jtWords19 = true := by
  decide +kernel
theorem jt19_at : CodeAt Frozen.image (pcOf 223488) jtWords19 :=
  slice_at _ _ jt19_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt12_linked : sliceChecked 221696 jtWords12 = true := by
  decide +kernel
theorem jt12_at : CodeAt Frozen.image (pcOf 221696) jtWords12 :=
  slice_at _ _ jt12_linked
theorem jt13_linked : sliceChecked 221952 jtWords13 = true := by
  decide +kernel
theorem jt13_at : CodeAt Frozen.image (pcOf 221952) jtWords13 :=
  slice_at _ _ jt13_linked
theorem jt14_linked : sliceChecked 222208 jtWords14 = true := by
  decide +kernel
theorem jt14_at : CodeAt Frozen.image (pcOf 222208) jtWords14 :=
  slice_at _ _ jt14_linked
theorem jt15_linked : sliceChecked 222464 jtWords15 = true := by
  decide +kernel
theorem jt15_at : CodeAt Frozen.image (pcOf 222464) jtWords15 :=
  slice_at _ _ jt15_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt08_linked : sliceChecked 220672 jtWords08 = true := by
  decide +kernel
theorem jt08_at : CodeAt Frozen.image (pcOf 220672) jtWords08 :=
  slice_at _ _ jt08_linked
theorem jt09_linked : sliceChecked 220928 jtWords09 = true := by
  decide +kernel
theorem jt09_at : CodeAt Frozen.image (pcOf 220928) jtWords09 :=
  slice_at _ _ jt09_linked
theorem jt10_linked : sliceChecked 221184 jtWords10 = true := by
  decide +kernel
theorem jt10_at : CodeAt Frozen.image (pcOf 221184) jtWords10 :=
  slice_at _ _ jt10_linked
theorem jt11_linked : sliceChecked 221440 jtWords11 = true := by
  decide +kernel
theorem jt11_at : CodeAt Frozen.image (pcOf 221440) jtWords11 :=
  slice_at _ _ jt11_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt04_linked : sliceChecked 219648 jtWords04 = true := by
  decide +kernel
theorem jt04_at : CodeAt Frozen.image (pcOf 219648) jtWords04 :=
  slice_at _ _ jt04_linked
theorem jt05_linked : sliceChecked 219904 jtWords05 = true := by
  decide +kernel
theorem jt05_at : CodeAt Frozen.image (pcOf 219904) jtWords05 :=
  slice_at _ _ jt05_linked
theorem jt06_linked : sliceChecked 220160 jtWords06 = true := by
  decide +kernel
theorem jt06_at : CodeAt Frozen.image (pcOf 220160) jtWords06 :=
  slice_at _ _ jt06_linked
theorem jt07_linked : sliceChecked 220416 jtWords07 = true := by
  decide +kernel
theorem jt07_at : CodeAt Frozen.image (pcOf 220416) jtWords07 :=
  slice_at _ _ jt07_linked
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem jt00_linked : sliceChecked 218624 jtWords00 = true := by
  decide +kernel
theorem jt00_at : CodeAt Frozen.image (pcOf 218624) jtWords00 :=
  slice_at _ _ jt00_linked
theorem jt01_linked : sliceChecked 218880 jtWords01 = true := by
  decide +kernel
theorem jt01_at : CodeAt Frozen.image (pcOf 218880) jtWords01 :=
  slice_at _ _ jt01_linked
theorem jt02_linked : sliceChecked 219136 jtWords02 = true := by
  decide +kernel
theorem jt02_at : CodeAt Frozen.image (pcOf 219136) jtWords02 :=
  slice_at _ _ jt02_linked
theorem jt03_linked : sliceChecked 219392 jtWords03 = true := by
  decide +kernel
theorem jt03_at : CodeAt Frozen.image (pcOf 219392) jtWords03 :=
  slice_at _ _ jt03_linked
end W9Machine
end

section

end
