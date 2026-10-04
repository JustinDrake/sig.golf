import SigGolfCandidate.T3M.Verify.Spec
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def xtrTab : List (List Nat) :=
  [[18455, 18589, 18723, 18857, 18991, 19125, 19259, 19393, 19527, 19661, 19795, 19929, 20063, 20197, 20331, 20465,
    20599, 20733, 20867, 21001, 21135, 21269, 21403, 21537, 21671, 21805, 21939, 22073, 22207, 22341, 22475, 22609,
    22743, 22877, 23011, 23145, 23279, 23413, 23547, 23681, 23815, 23949, 24083, 24217, 24351, 24485, 24619, 24753,
    24887, 25021, 25155, 25289, 25423, 25557, 25691, 25825, 25959, 26093, 26227, 26361, 26495, 26629, 26763, 26897,
    27031, 27165, 27299, 27433, 27567, 27701, 27835, 27969, 28103, 28237, 28371, 28505, 28639, 28773, 28907, 29041,
    29175, 29309, 29443, 29577, 29711, 29845, 29979, 30113, 30247, 30381, 30515, 30649, 30783, 30917, 31051, 31185,
    31319, 31453, 31587, 31721, 31855, 31989, 32123, 32257, 32391, 32525, 32659, 32793, 32927, 33061, 33195, 33329,
    33463, 33597, 33731, 33865, 33999, 34133, 34267, 34401, 34535, 34669, 34803, 34937, 35071, 35205, 35339, 35473],
   [11984, 12085, 12186, 12287, 12388, 12489, 12590, 12691, 12792, 12893, 12994, 13095, 13196, 13297, 13398, 13499,
    13600, 13701, 13802, 13903, 14004, 14105, 14206, 14307, 14408, 14509, 14610, 14711, 14812, 14913, 15014, 15115,
    15216, 15317, 15418, 15519, 15620, 15721, 15822, 15923, 16024, 16125, 16226, 16327, 16428, 16529, 16630, 16731,
    16832, 16933, 17034, 17135, 17236, 17337, 17438, 17539, 17640, 17741, 17842, 17943, 18044, 18145, 18246, 18347],
   [5520, 5621, 5722, 5823, 5924, 6025, 6126, 6227, 6328, 6429, 6530, 6631, 6732, 6833, 6934, 7035,
    7136, 7237, 7338, 7439, 7540, 7641, 7742, 7843, 7944, 8045, 8146, 8247, 8348, 8449, 8550, 8651,
    8752, 8853, 8954, 9055, 9156, 9257, 9358, 9459, 9560, 9661, 9762, 9863, 9964, 10065, 10166, 10267,
    10368, 10469, 10570, 10671, 10772, 10873, 10974, 11075, 11176, 11277, 11378, 11479, 11580, 11681, 11782, 11883],
   [664]]
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def hL (lay : Nat) : Nat := [12,7,6,6].getD lay 0
def stepsA (lay : Nat) : Nat := if lay = 3 then 21 else if lay = 0 then 15 else 14
def retOff (lay : Nat) : Nat := if lay = 0 then 19 else if lay = 3 then 50 else 43
def s6v (lay : Nat) : Nat := [15064,19288,22424,25560].getD lay 0
def s3v : Nat := 15768
def tgtL (lay : Nat) : Nat := [126,196,196,196].getD lay 0
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
def encB (lay : Nat) : Nat := [17816, 21016, 24152, 256].getD lay 0
def copyAllow (lay : Nat) : List Nat := [encB lay + 16, encB lay + 24, encB lay + 32]
def rejEcall : Nat := 743
def stabIdx (lay : Nat) : Nat := [209768,209640,209576,209512].getD lay 0
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x28, BitVec.ofNat 64 (2 ^ 40)), (.x21, BitVec.ofNat 64 M2c), (.x20, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00), (.x6, 1), (.x7, 2)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 (lay + 1))), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x22, BitVec.ofNat 64 (s6v (lay + 1)))]
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x28, BitVec.ofNat 64 (if lay = 3 then 2 ^ 40 else headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]
def chainK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]
def ld3Spec : Spec :=
  ⟨[(.x28, .ld (kw DATA)), (.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))),
      (.x27, .ld (kw (DATA + 24))), (.x2, .ld (kw (DATA + 32)))],
    [], 664, false, 6, [], none, 6⟩
def ld3Check : Bool := specB [] [] baseK (runAt (baseK ++ [(.x6, 1), (.x7, 2)]) [664] 658 []) ld3Spec [] (baseK ++ [(.x6, 1), (.x7, 2)]) [.x22]
def bKB (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, BitVec.ofNat 64 (encB lay))]
def bK (lay : Nat) : List (Reg × Word) := bKB lay ++ (if lay = 3 then [(.x12, 320)] else [])
def dstSet (lay : Nat) : List Nat := if lay = 3 then [320] else [encB lay, encB lay + 48]
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x30
def leafE (lay : Nat) : E := if lay = 0 then .reg .x30 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def s7E (lay : Nat) : E := .bin .or (leafE lay) (kw (2 ^ hL lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl (ctrE lay) (kw 22), kw 0, d⟩
def specA (lay p : Nat) : Spec :=
  ⟨[(.x4, tpE lay), (.x23, s7E lay), (.x30, treeE lay), (.x3, ctrE lay)],
   [(⟨none, BitVec.ofNat 64 (encB lay + 32)⟩, .bin (.st .w 0) (.ld (kw (encB lay + 32))) (ctrE lay)),
    (⟨none, BitVec.ofNat 64 (encB lay + 24)⟩, tpE lay), (⟨none, BitVec.ofNat 64 (encB lay + 16)⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay false], none, stepsA lay⟩
def rejSt (lay : Nat) : Nat := stepsA lay + (if lay = 3 then 0 else 2)
def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 (encB lay + 24)⟩, tpE lay), (⟨none, BitVec.ofNat 64 (encB lay + 16)⟩, kw (hw 4 lay))],
   rejEcall, true, rejSt lay, [ctrBr lay true], none, rejSt lay⟩
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
def ansObl : List Oblig := [.valid ⟨some (.reg .x12), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x12), BitVec.ofNat 64 0⟩ 8]
def b1E : E := .bin .sll a7E (kw 1)
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl b1E (kw 3)) (kw M1c))) (.bin .and b1E (kw M1c))
def swLowE : E := .bin .add (.bin .and a6E (kw M1c)) (.bin .and b1E (kw M1c))
def sw1E : E := .bin .add swLowE (.bin .srl (.bin .sub (.bin .add a6E b1E) swLowE) (kw 3))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
def t4E (lay : Nat) : E := .bin .add sumE (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.eq, .bin .sltu (t4E lay) (kw 8), kw 0, d⟩
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))
def bSt (_lay : Nat) : Nat := 38
def bCy (_lay : Nat) : Nat := 41
def packedRouteE (lay : Nat) : E :=
  .bin .or (.bin .or (.ld (kw (HDATA + 8 * lay)))
    (.bin .sll (.bin .srl (.reg .x4) (kw 32)) (kw 16)))
    (.bin .sll (.reg .x30) (kw (hL lay + 16)))
def prefixReturn (lay _p : Nat) : Nat := 111289 + 3 * lay
def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE), (.x25, kw (0x1000 + 4 * prefixReturn lay p)), (.x29, t4E lay),
    (.x3, .bin .sll (.reg .x30) (kw (hL lay + 16))), (.x14, x14l), (.x28, packedRouteE lay)],
   [], 0, false, 38, [ckBr lay false, rngBr 62 false], some tgtl, 41⟩
def postBl (lay p : Nat) : List (Reg × Word) :=
  chainK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay))]
def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [rngBr k true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 22, [ckBr lay true, rngBr 62 false], none, 25⟩
def gE : E := .bin .srl a7E (kw 34)
def p3E : E := .bin .add (.bin .and (.bin .srl gE (kw 3)) (kw M1c)) (.bin .and gE (kw M1c))
def s3E : E := .bin .remu (.bin .and (.bin .add p3E (.bin .srl p3E (kw 6))) (kw M2c)) (kw 4095)
def c34E : E := .bin .srl (.bin .sll a7E (kw 30)) (kw 30)
def l1E : E := .bin .add (.bin .and (.bin .srl a6E (kw 2)) (kw M4c)) (.bin .and a6E (kw M4c))
def l2E : E := .bin .add (.bin .and (.bin .srl c34E (kw 2)) (kw M4c)) (.bin .and c34E (kw M4c))
def lRefE : E := .bin .add l1E l2E
def lLowE : E := .bin .add (.bin .and a6E (kw M4c)) (.bin .and c34E (kw M4c))
def lE : E := .bin .add lLowE (.bin .srl (.bin .sub (.bin .add a6E c34E) lLowE) (kw 2))
def pE : E := .bin .add (.bin .and (.bin .srl lE (kw 4)) (kw M8c)) (.bin .and lE (kw M8c))
def totE : E := .bin .add (.bin .remu pE (kw 255)) s3E
def totBr (d : Bool) : Br := ⟨.ne, totE, kw 126, d⟩
def x14t : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 0xae000)
def tgtt : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 711072)) (.c (~~~1#64))
def specBt (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, .bin .sll a7E (kw 2)), (.x3, totE), (.x14, x14t), (.x25, .bin .and c34E (kw M4c))],
   [], 0, false, 52, [totBr false, rngBr 61 false], some tgtt, 58⟩
def postBt (p : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 0)), (.x2, 0x3fe00), (.x20, BitVec.ofNat 64 M4c), (.x21, BitVec.ofNat 64 M8c),
    (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
    (.x31, 7), (.x22, BitVec.ofNat 64 (s6v 0)), (.x19, BitVec.ofNat 64 s3v), (.x24, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]
def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))] ++ (if lay = 0 then [] else [(.x6, 1)])
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay))) (kw 0xce000)
  else .bin .add (.bin .sll (.reg .x23) (kw 2)) (kw 0xce000)
def tgtLfOld (lay : Nat) : E :=
  .bin .and (.bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay)))
    (kw (0x1000 + 4 * stabIdx lay))) (.c (~~~1#64))
def tgtLf (lay : Nat) : E :=
  if lay = 0 then tgtLfOld lay
  else .bin .and (.bin .add (.bin .sll (.reg .x23) (kw 2))
    (kw (0x1000 + 4 * stabIdx lay - 4 * 2 ^ hL lay))) (.c (~~~1#64))
def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 13, [], some (tgtLf lay), 13⟩
  else
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false, 12, [],
     some (tgtLf lay), 12⟩
def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ (if lay = 0 then [] else [(.x28, BitVec.ofNat 64 (headerBank 0 0))]) ++
   [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, 0xce000)]
def keepA (lay : Nat) : List Reg := if lay = 3 then [] else [.x12]
def keepB : List Reg := [.x4, .x23, .x30]
def keepLf : List Reg := [.x23, .x30, .x22]
def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x1, kw (0x1000 + 4 * (p + 19)))], [], 724, false, 3, [], none, 3⟩
def copyCheck (lay p : Nat) : Bool :=
  specB (copyAllow lay) [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) (keepA lay) &&
  specB (copyAllow lay) [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [724] (p + stepsA lay + 1) []) (specTopCall p) ansObl [] keepTopCall
  else
    specB [] [] baseK (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) ansObl
      (postBl lay p) keepB &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) ansObl [] [] &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) ansObl [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)
end SigGolfCandidate.T3M
