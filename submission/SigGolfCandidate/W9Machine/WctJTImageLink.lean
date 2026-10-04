import SigGolfCandidate.W9Machine.WctJTCheck14
import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def jtWords60 : List (BitVec 32) :=
  [0xea81d06f,0xee41d06f,0xf201d06f,0xf5c1d06f,0xf981d06f,0xfd41d06f,0x8111d06f,0x8611d06f,0x8b11d06f,0x9011d06f,0x96d1d06f,0x9c91d06f,0xa3d1d06f,0xa6d1d06f,0xa9d1d06f,0xacd1d06f,0xafd1d06f,0xb2d1d06f,0xb5d1d06f,0xb8d1d06f,0xbbd1d06f,0xbed1d06f,0xc1d1d06f,0xc4d1d06f,0xc7d1d06f,0xcc91d06f,0xd151d06f,0xd611d06f,0xdad1d06f,0xde91d06f,0xe251d06f,0xe611d06f,0xe9d1d06f,0xed91d06f,0xf151d06f,0xf691d06f,0xfbd1d06f,0x8101e06f,0x8581e06f,0x8a01e06f,0x8e81e06f,0x9441e06f,0x9a01e06f,0xa181e06f,0xa501e06f,0xa881e06f,0xac01e06f,0xaf81e06f,0xb301e06f,0xb681e06f,0xba01e06f,0xbd81e06f,0xc101e06f,0xc481e06f,0xc9c1e06f,0xcf01e06f,0xd441e06f,0xd881e06f,0xdcc1e06f,0xe101e06f,0xe6c1e06f,0xec81e06f,0xf181e06f,0xf7c1e06f,0xfa41e06f,0xfcc1e06f,0xff41e06f,0x81d1e06f,0x8451e06f,0x86d1e06f,0x8951e06f,0x8bd1e06f,0x8e51e06f,0x90d1e06f,0x9351e06f,0x95d1e06f,0x9851e06f,0x9d51e06f,0x9fd1e06f,0xa251e06f,0xa4d1e06f,0xa751e06f,0xa9d1e06f,0xac51e06f,0xaed1e06f,0xb151e06f,0xb3d1e06f,0xb651e06f,0xb8d1e06f,0xbb51e06f,0xbdd1e06f,0xc051e06f,0xc511e06f,0xc791e06f,0xca11e06f,0xcc91e06f,0xd151e06f,0xd3d1e06f,0xd651e06f,0xd8d1e06f,0xdb51e06f,0xddd1e06f,0xe051e06f,0xe2d1e06f,0xe6d1e06f,0xead1e06f,0xeed1e06f,0xf2d1e06f,0xf6d1e06f,0xfad1e06f,0xfed1e06f,0x82c1f06f,0x86c1f06f,0x8ac1f06f,0x8ec1f06f,0x92c1f06f,0x95c1f06f,0x98c1f06f,0x9bc1f06f,0x9ec1f06f,0xa1c1f06f,0xa4c1f06f,0xa7c1f06f,0xaac1f06f,0xadc1f06f,0xb0c1f06f,0xb3c1f06f,0xb6c1f06f,0xb9c1f06f,0xbcc1f06f,0xbfc1f06f,0xc2c1f06f,0xc5c1f06f,0xc8c1f06f,0xcbc1f06f,0xd041f06f,0xd4c1f06f,0xd941f06f,0xddc1f06f,0xe241f06f,0xe6c1f06f,0xeb41f06f,0xefc1f06f,0xf441f06f,0xf8c1f06f,0xfc81f06f,0x8051f06f,0x8411f06f,0x87d1f06f,0x8b91f06f,0x8f51f06f,0x9311f06f,0x96d1f06f,0x9a91f06f,0x9e51f06f,0xa351f06f,0xa851f06f,0xad51f06f,0xb251f06f,0xb751f06f,0xbc51f06f,0xc311f06f,0xc9d1f06f,0xcf91f06f,0xd6d1f06f,0xd9d1f06f,0xdcd1f06f,0xdfd1f06f,0xe2d1f06f,0xe5d1f06f,0xe8d1f06f,0xebd1f06f,0xeed1f06f,0xf1d1f06f,0xf4d1f06f,0xf7d1f06f,0xfad1f06f,0xfdd1f06f,0x80c2006f,0x83c2006f,0x86c2006f,0x89c2006f,0x8cc2006f,0x8fc2006f,0x92c2006f,0x95c2006f,0x98c2006f,0x9bc2006f,0x9ec2006f,0xa1c2006f,0xa4c2006f,0xa7c2006f,0xaac2006f,0xadc2006f,0xb0c2006f,0xb3c2006f,0xb882006f,0xbd42006f,0xc202006f,0xc6c2006f,0xcb82006f,0xd042006f,0xd502006f,0xd9c2006f,0xde82006f,0xe342006f,0xe702006f,0xeac2006f,0xee82006f,0xf242006f,0xf602006f,0xf9c2006f,0xfd82006f,0x8152006f,0x8512006f,0x88d2006f,0x4a10006f,0x4f50006f,0x5490006f,0x59d0006f,0x5f10006f,0x6450006f,0x68d0006f,0x6fd0006f,0x7450006f,0x78d0006f,0x7e90006f,71307375,0xa00106f,293605487,352325743,411045999,469766255,528486511,587206767,645927023,704647279,763367535,822087791,880808047,939528303,998248559,0x3f00106f,0x4280106f,0x4600106f,0x4980106f,0x4d00106f,0x5080106f,0x5400106f,0x5780106f,0x5cc0106f,0x6200106f,0x6740106f,0x6c80106f,0x71c0106f,0x7700106f]
theorem jtCheck60 : jtCheck 15360 jtWords60 = true := by
  decide +kernel
def jtWords61 : List (BitVec 32) :=
  [0x7b40106f,0x7f80106f,63967343,0x810106f,0xdd0106f,328208495,424677487,508563567,613421167,638586991,663752815,688918639,714084463,739250287,764416111,789581935,814747759,839913583,865079407,890245231,915411055,940576879,965742703,990908527,0x3c90106f,0x3e10106f,0x3f90106f,0x4110106f,0x4290106f,0x4410106f,0x4590106f,0x4710106f,0x4890106f,0x4a10106f,0x4b90106f,0x4d10106f,0x4e90106f,0x5010106f,0x5190106f,0x5310106f,0x5490106f,0x5610106f,0x5790106f,0x5910106f,0x5a90106f,0x5c10106f,0x5d90106f,0x5f10106f,0x6090106f,0x6210106f,0x6390106f,0x6510106f,0x6910106f,0x6d10106f,0x7110106f,0x7290106f,0x7690106f,0x7a90106f,0x7e90106f,8303,25174127,50339951,0x600206f,0x900206f,0xa80206f,0xd80206f,0xf00206f,276832367,301998191,352329839,377495663,402661487,427827311,452993135,503324783,553656431,578822255,603988079,629153903,654319727,679485551,704651375,729817199,754983023,830480495,855646319,880812143,905977967,981475439,0x3c00206f,0x3d80206f,0x4140206f,0x4500206f,0x48c0206f,0x4c80206f,0x4e00206f,0x4f80206f,0x5340206f,0x54c0206f,0x5640206f,0x57c0206f,0x5940206f,0x5ac0206f,0x5c40206f,0x5dc0206f,0x5f40206f,0x60c0206f,0x6240206f,0x63c0206f,0x6540206f,0x6940206f,0x6d40206f,0x7140206f,0x7540206f,0x7940206f,0x7d40206f,22028399,89137263,0x950206f,0xd50206f,290463855,357572719,424681583,617619567,810557551,919609455,0x4250206f,0x4ad0206f,0x54d0206f,0x5d50206f,0x68d0206f,0x6cd0206f,0x70d0206f,0x7950206f,54538351,0xec0306f,440414319,507523183,574632047,742404207,809513071,859844719,952119407,0x3e40306f,0x4140306f,0x4cc0306f,0x5540306f,0x5f40306f,0x67c0306f,0x7340306f,0x7640306f,0x7ac0306f,55586927,0xd50306f,365965423,533737583,584069231,634400879,802173039,877670511,928002159,978333807,0x3d50306f,0x4050306f,0x48d0306f,0x52d0306f,0x55d0306f,0x5b10306f,0x6690306f,0x6bd0306f,0x6ed0306f,0x71d0306f,0x74d0306f,0x77d0306f,0x7ad0306f,0x7f50306f,62931055,0x840406f,0xcc0406f,289423471,364920943,440418415,515915887,591413359,666910831,742408303,885014639,0x3ec0406f,0x4740406f,0x5140406f,0x55c0406f,0x5a40406f,0x6440406f,0x68c0406f,0x6d40406f,0x7100406f,0x7740406f,0x7d80406f,0x910406f,344997999,449855599,537935983,730873967,818954351,881868911,944783471,0x3f10406f,0x45d0406f,0x4990406f,0x4d50406f,0x5250406f,0x5750406f,0x5c50406f,0x6150406f,0x6650406f,0x6b50406f,0x7050406f,0x7a50406f,0x7f50406f,71323759,0xb00506f,297816175,411062383,507531375,629166191,662720623,696275055,729829487,763383919,796938351,830492783,864047215,897601647,931156079,964710511,998264943,0x3d80506f,0x3f80506f,0x4180506f,0x4380506f,0x4580506f,0x4780506f,0x4980506f,0x4b80506f,0x4d80506f,0x4f80506f,0x5180506f,0x5380506f,0x5580506f,0x5780506f,0x5980506f,0x5b80506f,0x5d80506f,0x5f80506f,0x6180506f,0x6380506f]
theorem jtCheck61 : jtCheck 15616 jtWords61 = true := by
  decide +kernel
def jtWords62 : List (BitVec 32) :=
  [0x6580506f,0x6780506f,0x6980506f,0x6b80506f,0x6d80506f,0x6f80506f,0x7180506f,0x7380506f,0x7580506f,0x7780506f,0x7980506f,0x7b80506f,0x7d80506f,0x7f80506f,26234991,59789423,93343855,0x790506f,0x990506f,0xb90506f,0xd90506f,0xf90506f,294670447,328224879,361779311,395333743,428888175,462442607,495997039,529551471,563105903,596660335,630214767,663769199,739266671,814764143,890261615,965759087,0x3e10506f,0x4290506f,0x4710506f,0x4b90506f,0x5010506f,0x5490506f,0x5910506f,0x6190506f,0x6b90506f,0x7410506f,0x7e10506f,41967727,0x700606f,285237359,360734831,436232303,494952559,553672815,612393071,754999407,922771567,981491823,0x3e00606f,0x4800606f,0x4b80606f,0x4f00606f,0x5280606f,0x5600606f,0x5980606f,0x5d00606f,0x6080606f,0x6580606f,0x6a80606f,0x6f80606f,0x7480606f,0x7980606f,0x7e80606f,59793519,0xd90606f,311451759,395337839,466641007,579887215,693133423,764436591,835739759,928014447,0x3cd0606f,0x4250606f,0x47d0606f,0x4f10606f,0x5190606f,0x5410606f,0x5690606f,0x5910606f,0x5b90606f,0x5e10606f,0x6090606f,0x6310606f,0x6590606f,0x6810606f,0x6a90606f,0x6d10606f,0x6f90606f,0x7210606f,0x7490606f,0x7710606f,0x7990606f,0x7c10606f,0x7e90606f,16805999,58749039,0x600706f,0x880706f,0xb00706f,0xd80706f,268464239,310407279,352350319,394293359,436236399,478179439,520122479,562065519,604008559,645951599,729837679,813723759,897609839,981495919,0x3f80706f,0x4480706f,0x4980706f,0x5380706f,0x5880706f,0x5d80706f,0x6180706f,0x6580706f,0x6980706f,0x6d80706f,0x7180706f,0x7700706f,0x7c80706f,34631791,0x790706f,0xc50706f,0xe211a06f,0xe1d1a06f,0xe191a06f,0xe151a06f,0xe111a06f,0xe0d1a06f,0xe091a06f,0xe051a06f,0xe011a06f,0xdfd1a06f,0xdf91a06f,0xdf51a06f,0xdf11a06f,0xded1a06f,0xde91a06f,0xde51a06f,0xde11a06f,0xddd1a06f,0xdd91a06f,0xdd51a06f,0xdd11a06f,0xdcd1a06f,0xdc91a06f,0xdc51a06f,0xdc11a06f,0xdbd1a06f,0xdb91a06f,0xdb51a06f,0xdb11a06f,0xdad1a06f,0xda91a06f,0xda51a06f,0xda11a06f,0xd9d1a06f,0xd991a06f,0xd951a06f,0xd911a06f,0xd8d1a06f,0xd891a06f,0xd851a06f,0xd811a06f,0xd7d1a06f,0xd791a06f,0xd751a06f,0xd711a06f,0xd6d1a06f,0xd691a06f,0xd651a06f,0xd611a06f,0xd5d1a06f,0xd591a06f,0xd551a06f,0xd511a06f,0xd4d1a06f,0xd491a06f,0xd451a06f,0xd411a06f,0xd3d1a06f,0xd391a06f,0xd351a06f,0xd311a06f,0xd2d1a06f,0xd291a06f,0xd251a06f,0xd211a06f,0xd1d1a06f,0xd191a06f,0xd151a06f,0xd111a06f,0xd0d1a06f,0xd091a06f,0xd051a06f,0xd011a06f,0xcfd1a06f,0xcf91a06f,0xcf51a06f,0xcf11a06f,0xced1a06f,0xce91a06f,0xce51a06f,0xce11a06f,0xcdd1a06f,0xcd91a06f,0xcd51a06f,0xcd11a06f,0xccd1a06f,0xcc91a06f,0xcc51a06f,0xcc11a06f,0xcbd1a06f,0xcb91a06f,0xcb51a06f,0xcb11a06f,0xcad1a06f,0xca91a06f,0xca51a06f,0xca11a06f,0xc9d1a06f,0xc991a06f,0xc951a06f,0xc911a06f,0xc8d1a06f,0xc891a06f,0xc851a06f,0xc811a06f,0xc7d1a06f,0xc791a06f,0xc751a06f,0xc711a06f,0xc6d1a06f,0xc691a06f,0xc651a06f]
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
