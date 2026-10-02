import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.FullCache.MacBytes

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 20000

abbrev PRIV : Nat := 0x20000
abbrev KEYS : Nat := 0x70000
abbrev REGION : Nat := 0x80020
abbrev REGIONEND : Nat := 0xA0000

def macImage (sg : Bool) : Image := if sg then Images.signImage else Images.keygenImage
def macBase (sg : Bool) : Nat := if sg then 1227 else 334
def macOut (sg : Bool) : Nat := if sg then 0x203E0 else 0x80000

def macSeg_0 : List (BitVec 32) := [0x00020e37, 0x000e0e13, 0x00000eb7, 0x080e8e93, 0x000eb303, 0x006e3023, 0x008eb303, 0x006e3423, 0x010eb303, 0x026e3023, 0x018eb303, 0x026e3423, 0x020e3823, 0x020e3c23, 0x00001337, 0xe0130313, 0x006e3823, 0x000e3c23, 0x00020537, 0x00050513, 0x04000593, 0x00070637, 0x00060613]
theorem macAt_0 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 0)) (macSeg_0) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 334)
      (post := Images.keygenCode.drop 357) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1227)
      (post := Images.signCode.drop 1250) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_0 := symRun { noAlias := true } (macSeg_0) (pcOf 334) 100
sym_block macBlkS_0 := symRun { noAlias := true } (macSeg_0) (pcOf 1227) 100

def macSeg_23 : List (BitVec 32) := [0x00000073]
theorem macAt_23 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 23)) (macSeg_23) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 357)
      (post := Images.keygenCode.drop 358) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1250)
      (post := Images.signCode.drop 1251) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_24 : List (BitVec 32) := [0x00100313, 0x02031313, 0x006e3c23, 0x00070637, 0x02060613]
theorem macAt_24 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 24)) (macSeg_24) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 358)
      (post := Images.keygenCode.drop 363) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1251)
      (post := Images.signCode.drop 1256) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_24 := symRun { noAlias := true } (macSeg_24) (pcOf 358) 100
sym_block macBlkS_24 := symRun { noAlias := true } (macSeg_24) (pcOf 1251) 100

def macSeg_29 : List (BitVec 32) := [0x00000073]
theorem macAt_29 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 29)) (macSeg_29) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 363)
      (post := Images.keygenCode.drop 364) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1256)
      (post := Images.signCode.drop 1257) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_30 (sg : Bool) : List (BitVec 32) := if sg then [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00020cb7, 0x3e0c8c93] else [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00080cb7, 0x000c8c93]
theorem macAt_30 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 30)) (macSeg_30 sg) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 364)
      (post := Images.keygenCode.drop 372) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1257)
      (post := Images.signCode.drop 1265) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_30 := symRun { noAlias := true } (macSeg_30 false) (pcOf 364) 100
sym_block macBlkS_30 := symRun { noAlias := true } (macSeg_30 true) (pcOf 1257) 100

def macSeg_38 : List (BitVec 32) := [0x000b3b83, 0x012bfbb3, 0x008b3c03, 0x000806b7, 0x02068693, 0x00000713, 0x0006e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x0046e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x00868693, 0xf9369ee3, 0x03d75793, 0x01277733, 0x00f70733, 0x012747b3, 0x0017b793, 0xfff78793, 0x00f77733, 0x01870733]
theorem macSeg_38_pass : macSeg_38 = MacPass.macPassCode := by decide +kernel
theorem macAt_38 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 38)) (macSeg_38) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 372)
      (post := Images.keygenCode.drop 412) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1265)
      (post := Images.signCode.drop 1305) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_78 : List (BitVec 32) := [0x00ecb023, 0x010b0b13]
theorem macAt_78 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 78)) (macSeg_78) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 412)
      (post := Images.keygenCode.drop 414) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1305)
      (post := Images.signCode.drop 1307) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_78 := symRun { noAlias := true } (macSeg_78) (pcOf 412) 100
sym_block macBlkS_78 := symRun { noAlias := true } (macSeg_78) (pcOf 1305) 100

def macSeg_80 : List (BitVec 32) := [0x000b3b83, 0x012bfbb3, 0x008b3c03, 0x000806b7, 0x02068693, 0x00000713, 0x0006e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x0046e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x00868693, 0xf9369ee3, 0x03d75793, 0x01277733, 0x00f70733, 0x012747b3, 0x0017b793, 0xfff78793, 0x00f77733, 0x01870733]
theorem macSeg_80_pass : macSeg_80 = MacPass.macPassCode := by decide +kernel
theorem macAt_80 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 80)) (macSeg_80) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 414)
      (post := Images.keygenCode.drop 454) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1307)
      (post := Images.signCode.drop 1347) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_120 : List (BitVec 32) := [0x00ecb423, 0x010b0b13]
theorem macAt_120 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 120)) (macSeg_120) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 454)
      (post := Images.keygenCode.drop 456) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1347)
      (post := Images.signCode.drop 1349) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_120 := symRun { noAlias := true } (macSeg_120) (pcOf 454) 100
sym_block macBlkS_120 := symRun { noAlias := true } (macSeg_120) (pcOf 1347) 100

def macSeg_122 : List (BitVec 32) := [0x000b3b83, 0x012bfbb3, 0x008b3c03, 0x000806b7, 0x02068693, 0x00000713, 0x0006e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x0046e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x00868693, 0xf9369ee3, 0x03d75793, 0x01277733, 0x00f70733, 0x012747b3, 0x0017b793, 0xfff78793, 0x00f77733, 0x01870733]
theorem macSeg_122_pass : macSeg_122 = MacPass.macPassCode := by decide +kernel
theorem macAt_122 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 122)) (macSeg_122) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 456)
      (post := Images.keygenCode.drop 496) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1349)
      (post := Images.signCode.drop 1389) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_162 : List (BitVec 32) := [0x00ecb823, 0x010b0b13]
theorem macAt_162 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 162)) (macSeg_162) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 496)
      (post := Images.keygenCode.drop 498) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1389)
      (post := Images.signCode.drop 1391) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_162 := symRun { noAlias := true } (macSeg_162) (pcOf 496) 100
sym_block macBlkS_162 := symRun { noAlias := true } (macSeg_162) (pcOf 1389) 100

def macSeg_164 : List (BitVec 32) := [0x000b3b83, 0x012bfbb3, 0x008b3c03, 0x000806b7, 0x02068693, 0x00000713, 0x0006e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x0046e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733, 0x00868693, 0xf9369ee3, 0x03d75793, 0x01277733, 0x00f70733, 0x012747b3, 0x0017b793, 0xfff78793, 0x00f77733, 0x01870733]
theorem macSeg_164_pass : macSeg_164 = MacPass.macPassCode := by decide +kernel
theorem macAt_164 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 164)) (macSeg_164) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 498)
      (post := Images.keygenCode.drop 538) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1391)
      (post := Images.signCode.drop 1431) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def macSeg_204 : List (BitVec 32) := [0x00ecbc23]
theorem macAt_204 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 204)) (macSeg_204) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 538)
      (post := Images.keygenCode.drop 539) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact CodeAt.of_append (pre := Images.signCode.take 1431)
      (post := Images.signCode.drop 1432) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block macBlkK_204 := symRun { noAlias := true } (macSeg_204) (pcOf 538) 100
sym_block macBlkS_204 := symRun { noAlias := true } (macSeg_204) (pcOf 1431) 100

end SigGolfCandidate.T3M.FullCache
