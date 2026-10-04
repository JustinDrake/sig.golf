import SigGolfCandidate.W9Machine.WctJTCheck14
import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def jtWords60 : List (BitVec 32) :=
  [0xcac1d06f,0xce01d06f,0xd141d06f,0xd481d06f,0xd7c1d06f,0xdb01d06f,0xde41d06f,0xe2c1d06f,0xe741d06f,0xebc1d06f,0xf1c1d06f,0xf6c1d06f,0xfd41d06f,0x8011d06f,0x82d1d06f,0x8591d06f,0x8851d06f,0x8b11d06f,0x8dd1d06f,0x9091d06f,0x9351d06f,0x9611d06f,0x98d1d06f,0x9b91d06f,0x9e51d06f,0xa291d06f,0xa6d1d06f,0xab11d06f,0xaf51d06f,0xb291d06f,0xb5d1d06f,0xb911d06f,0xbc51d06f,0xbf91d06f,0xc2d1d06f,0xc791d06f,0xcc51d06f,0xd111d06f,0xd511d06f,0xd911d06f,0xdd11d06f,0xe251d06f,0xe791d06f,0xee51d06f,0xf191d06f,0xf4d1d06f,0xf811d06f,0xfb51d06f,0xfe91d06f,0x81c1e06f,0x8501e06f,0x8841e06f,0x8b81e06f,0x8ec1e06f,0x9381e06f,0x9841e06f,0x9d01e06f,0xa0c1e06f,0xa481e06f,0xa841e06f,0xad81e06f,0xb2c1e06f,0xb741e06f,0xbd01e06f,0xbf41e06f,0xc181e06f,0xc3c1e06f,0xc601e06f,0xc841e06f,0xca81e06f,0xccc1e06f,0xcf01e06f,0xd141e06f,0xd381e06f,0xd5c1e06f,0xd801e06f,0xdc81e06f,0xe101e06f,0xe341e06f,0xe6c1e06f,0xe901e06f,0xeb41e06f,0xed81e06f,0xf101e06f,0xf341e06f,0xf6c1e06f,0xf901e06f,0xfb41e06f,0xfd81e06f,0x8291e06f,0x8791e06f,0x89d1e06f,0x9051e06f,0x9291e06f,0x96d1e06f,0x9b11e06f,0xa151e06f,0xa391e06f,0xa5d1e06f,0xa811e06f,0xaa51e06f,0xac91e06f,0xaed1e06f,0xb111e06f,0xb491e06f,0xb811e06f,0xbb91e06f,0xbf11e06f,0xc291e06f,0xc611e06f,0xc991e06f,0xcd11e06f,0xd091e06f,0xd411e06f,0xd791e06f,0xdb11e06f,0xdd91e06f,0xe011e06f,0xe291e06f,0xe511e06f,0xe791e06f,0xea11e06f,0xec91e06f,0xef11e06f,0xf191e06f,0xf411e06f,0xf691e06f,0xf911e06f,0xfb91e06f,0xfe11e06f,0x8081f06f,0x8301f06f,0x8581f06f,0x8801f06f,0x8a81f06f,0x8e81f06f,0x9281f06f,0x9681f06f,0x9a81f06f,0x9e81f06f,0xa281f06f,0xa681f06f,0xaa81f06f,0xae81f06f,0xb281f06f,0xb5c1f06f,0xb901f06f,0xbe81f06f,0xc1c1f06f,0xc501f06f,0xc841f06f,0xcb81f06f,0xd181f06f,0xd4c1f06f,0xd801f06f,0xdc81f06f,0xe101f06f,0xe581f06f,0xea01f06f,0xee81f06f,0xf301f06f,0xf901f06f,0xff01f06f,0x8411f06f,0x8a91f06f,0x8d51f06f,0x9011f06f,0x92d1f06f,0x9591f06f,0x9851f06f,0x9b11f06f,0x9dd1f06f,0xa091f06f,0xa351f06f,0xa611f06f,0xa8d1f06f,0xab91f06f,0xae51f06f,0xb351f06f,0xb851f06f,0xbb11f06f,0xbf11f06f,0xc1d1f06f,0xc491f06f,0xc751f06f,0xcb51f06f,0xce11f06f,0xd0d1f06f,0xd391f06f,0xd911f06f,0xddd1f06f,0xe291f06f,0xe551f06f,0xe811f06f,0xead1f06f,0xed91f06f,0x4f10006f,0x5350006f,0x5790006f,0x5bd0006f,0x6250006f,0x6690006f,0x6ad0006f,0x6f10006f,0x7550006f,0x7990006f,0x7cd0006f,4207,92278895,0x8c0106f,0xc00106f,0xf40106f,310382703,411045999,465571951,520097903,599789679,679481455,759173231,838865007,918556783,998248559,0x3f80106f,0x45c0106f,0x49c0106f,0x4dc0106f,0x5300106f,0x5840106f,0x5d80106f,0x6440106f,0x6780106f,0x6ac0106f,0x6e00106f,0x7140106f,0x7480106f,0x77c0106f,0x7b00106f,0x7e40106f,26218607,80744559,0x810106f,0xb50106f,282071151,336597103,391123055,445649007,500174959,600838255,655364207,709890159,789581935,869273711,948965487,0x3d50106f,0x4210106f,0x46d0106f]
theorem jtCheck60 : jtCheck 15360 jtWords60 = true := by
  decide +kernel
def jtWords61 : List (BitVec 32) :=
  [0x4a90106f,0x5090106f,0x5450106f,0x5810106f,0x5d50106f,0x6290106f,0x67d0106f,0x6c50106f,0x7210106f,0x7350106f,0x7490106f,0x75d0106f,0x7710106f,0x7850106f,0x7990106f,0x7ad0106f,0x7c10106f,0x7d50106f,0x7e90106f,0x7fd0106f,16785519,37757039,58728559,79700079,0x600206f,0x740206f,0x880206f,0x9c0206f,0xb00206f,0xc40206f,0xd80206f,0xec0206f,268443759,289415279,310386799,331358319,352329839,373301359,394272879,415244399,436215919,457187439,478158959,499130479,520101999,541073519,562045039,583016559,603988079,624959599,645931119,666902639,725622895,784343151,843063407,864034927,922755183,981475439,0x3e00206f,0x3f40206f,0x42c0206f,0x4400206f,0x4680206f,0x4900206f,0x4a40206f,0x4cc0206f,0x4e00206f,0x4f40206f,0x5080206f,0x5300206f,0x5440206f,0x5580206f,0x56c0206f,0x5940206f,0x5bc0206f,0x5e40206f,0x5f80206f,0x60c0206f,0x6200206f,0x6340206f,0x6480206f,0x65c0206f,0x6700206f,0x6840206f,0x6c40206f,0x6d80206f,0x7180206f,0x7580206f,0x7980206f,0x7ac0206f,0x7c00206f,0x7f40206f,80748655,0x810206f,0xb50206f,0xc90206f,0xdd0206f,332406895,353378415,374349935,395321455,416292975,437264495,458236015,479207535,500179055,521150575,621813871,642785391,663756911,722477167,781197423,839917679,898637935,957358191,0x3c90206f,0x4010206f,0x4390206f,0x4710206f,0x4a90206f,0x4e10206f,0x5190206f,0x5750206f,0x6190206f,0x6bd0206f,0x7610206f,4206703,0x640306f,0xf00306f,377499759,549466223,608186479,713044079,838873199,0x3c40306f,0x4680306f,0x50c0306f,0x5640306f,0x59c0306f,0x6400306f,0x6780306f,0x6a00306f,0x6ec0306f,0x7380306f,0x7600306f,5255279,0x650306f,0xf10306f,378548335,550514799,592457839,655372399,756035695,902836335,0x3d10306f,0x4350306f,0x45d0306f,0x4850306f,0x5110306f,0x54d0306f,0x5750306f,0x59d0306f,0x5c50306f,0x6190306f,0x6910306f,0x71d0306f,0x7710306f,0x7b90306f,96485487,0xa40406f,0xcc0406f,0xf40406f,297812079,339755119,381698159,448807023,515915887,583024751,650133615,717242479,784351343,851460207,918569071,985677935,0x3ec0406f,0x4500406f,0x4c80406f,0x56c0406f,0x5e40406f,0x6700406f,0x6b00406f,0x6f00406f,0x7940406f,0x7f40406f,55591023,0x690406f,0xc10406f,294666351,466632815,638599279,730873967,806371439,978337903,0x3ed0406f,0x4210406f,0x4550406f,0x4b50406f,0x5150406f,0x5490406f,0x57d0406f,0x5c50406f,0x60d0406f,0x6550406f,0x69d0406f,0x6e50406f,0x72d0406f,0x7750406f,25186415,0x600506f,0xa80506f,276844655,377507951,478171247,562057327,671109231,700469359,729829487,759189615,788549743,817909871,847269999,876630127,905990255,935350383,964710511,994070639,0x3d00506f,0x3ec0506f,0x4080506f,0x4240506f,0x4400506f,0x45c0506f,0x4780506f,0x4940506f,0x4b00506f,0x4cc0506f,0x4e80506f,0x5040506f,0x5200506f,0x53c0506f,0x5580506f,0x5740506f,0x5900506f,0x5ac0506f,0x5c80506f,0x5e40506f]
theorem jtCheck61 : jtCheck 15616 jtWords61 = true := by
  decide +kernel
def jtWords62 : List (BitVec 32) :=
  [0x6000506f,0x61c0506f,0x6380506f,0x6540506f,0x6700506f,0x68c0506f,0x6a80506f,0x6c40506f,0x6e00506f,0x6fc0506f,0x7180506f,0x7340506f,0x7500506f,0x76c0506f,0x7880506f,0x7a40506f,0x7c00506f,0x7dc0506f,0x7f80506f,22040687,51400815,80760943,0x690506f,0x850506f,0xa10506f,0xbd0506f,0xd90506f,0xf50506f,286281839,315641967,345002095,374362223,403722351,433082479,500191343,567300207,634409071,701517935,768626799,835735663,902844527,969953391,0x3dd0506f,0x41d0506f,0x4810506f,0x4f90506f,0x59d0506f,0x6150506f,0x6a10506f,0x6e10506f,0x7210506f,0x7c50506f,37773423,0x640606f,0x940606f,0xc40606f,293625967,419455087,566255727,654336111,704667759,851468399,901800047,952131695,0x3bc0606f,0x4180606f,0x4740606f,0x4a40606f,0x4d40606f,0x51c0606f,0x5640606f,0x5ac0606f,0x5f40606f,0x63c0606f,0x6840606f,0x6cc0606f,0x7700606f,0x7b80606f,1073263,63987823,0x9d0606f,0xfd0606f,328228975,391143535,475029615,558915695,642801775,726687855,835739759,873488495,911237231,948985967,986734703,0x3d10606f,0x3f50606f,0x4190606f,0x43d0606f,0x4610606f,0x4850606f,0x4a90606f,0x4cd0606f,0x4f10606f,0x5150606f,0x5390606f,0x55d0606f,0x5810606f,0x5a50606f,0x5c90606f,0x5ed0606f,0x6110606f,0x6350606f,0x6590606f,0x67d0606f,0x6a10606f,0x6c50606f,0x6e90606f,0x70d0606f,0x7310606f,0x7550606f,0x7790606f,0x79d0606f,0x7c10606f,0x7e50606f,8417391,83914863,0x980706f,0xe00706f,310407279,385904751,461402223,536899695,708866159,784363631,859861103,918581359,977301615,0x3dc0706f,0x4140706f,0x44c0706f,0x49c0706f,0x4ec0706f,0x53c0706f,0x58c0706f,0x5d00706f,0xe211a06f,0xe1d1a06f,0xe191a06f,0xe151a06f,0xe111a06f,0xe0d1a06f,0xe091a06f,0xe051a06f,0xe011a06f,0xdfd1a06f,0xdf91a06f,0xdf51a06f,0xdf11a06f,0xded1a06f,0xde91a06f,0xde51a06f,0xde11a06f,0xddd1a06f,0xdd91a06f,0xdd51a06f,0xdd11a06f,0xdcd1a06f,0xdc91a06f,0xdc51a06f,0xdc11a06f,0xdbd1a06f,0xdb91a06f,0xdb51a06f,0xdb11a06f,0xdad1a06f,0xda91a06f,0xda51a06f,0xda11a06f,0xd9d1a06f,0xd991a06f,0xd951a06f,0xd911a06f,0xd8d1a06f,0xd891a06f,0xd851a06f,0xd811a06f,0xd7d1a06f,0xd791a06f,0xd751a06f,0xd711a06f,0xd6d1a06f,0xd691a06f,0xd651a06f,0xd611a06f,0xd5d1a06f,0xd591a06f,0xd551a06f,0xd511a06f,0xd4d1a06f,0xd491a06f,0xd451a06f,0xd411a06f,0xd3d1a06f,0xd391a06f,0xd351a06f,0xd311a06f,0xd2d1a06f,0xd291a06f,0xd251a06f,0xd211a06f,0xd1d1a06f,0xd191a06f,0xd151a06f,0xd111a06f,0xd0d1a06f,0xd091a06f,0xd051a06f,0xd011a06f,0xcfd1a06f,0xcf91a06f,0xcf51a06f,0xcf11a06f,0xced1a06f,0xce91a06f,0xce51a06f,0xce11a06f,0xcdd1a06f,0xcd91a06f,0xcd51a06f,0xcd11a06f,0xccd1a06f,0xcc91a06f,0xcc51a06f,0xcc11a06f,0xcbd1a06f,0xcb91a06f,0xcb51a06f,0xcb11a06f,0xcad1a06f,0xca91a06f,0xca51a06f,0xca11a06f,0xc9d1a06f,0xc991a06f,0xc951a06f,0xc911a06f,0xc8d1a06f,0xc891a06f,0xc851a06f,0xc811a06f,0xc7d1a06f,0xc791a06f,0xc751a06f,0xc711a06f,0xc6d1a06f,0xc691a06f,0xc651a06f]
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
