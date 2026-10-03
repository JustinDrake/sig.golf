
namespace ClaudeWCT.Numerics.Kernel
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
def PB : Nat := 2 ^ 64
def HB : Nat := 2 ^ 128
def monos (js : List Nat) : Nat := js.foldr (fun j s => PB ^ j + s) 0
def box (m : Nat) : Nat := monos (List.range (m + 1))
def chainFac (inS : Bool) (x : Nat) : Nat :=
  if inS then (match x with | 0 => 0 | x' + 1 => box x') else box 3
def pairFac (x : Nat) : Nat :=
  monos ((List.range (x + 1)).map (fun b => x + 32 * b) ++ (List.range x).map (fun a => a + 32 * x))
def coeffAt (p j : Nat) : Nat := p / PB ^ j % PB
abbrev Opt := Nat × Nat × Nat × Bool
def loopK (child : Nat → Nat → Nat → Nat → Nat → Bool → Nat × Nat) (n rem u fu fb fden : Nat)
    (inS : Bool) : (j k : Nat) → (q p fk : Nat) → (sg : Bool) → Nat × Nat
  | 0, _, _, _, _, _ => (0, 0)
  | j + 1, k, q, p, fk, sg =>
    if k * u ≤ rem then
      let a := child (n - k) (rem - k * u) q p (fden * fk) sg
      let b := loopK child n rem u fu fb fden inS j (k + 1) (q * fb) (p * fu) (fk * (k + 1)) (sg ^^ inS)
      (a.1 + b.1, a.2 + b.2)
    else (0, 0)
def enumK (hb total qIdx : Nat) : (opts : List Opt) → (n rem : Nat) → (q p fden : Nat) → (neg : Bool) →
    Nat × Nat
  | [], n, rem, q, p, fden, neg =>
    if n == 0 && rem == 0 then
      let h := (fact total / fden) * coeffAt q qIdx * hb ^ coeffAt p 6
      if neg then (0, h) else (h, 0)
    else (0, 0)
  | (u, fu, fb, inS) :: os, n, rem, q, p, fden, neg =>
    loopK (fun n' rem' q' p' fden' sg => enumK hb total qIdx os n' rem' q' p' fden' sg)
      n rem u fu fb fden inS (n + 1) 0 q p 1 neg
def optsU : List Opt :=
  [(0, chainFac false 0, 1, false), (0, chainFac true 0, 1, true),
   (1, chainFac false 1, 1, false), (1, chainFac true 1, 1, true),
   (2, chainFac false 2, 1, false), (2, chainFac true 2, 1, true),
   (3, chainFac false 3, 1, false), (3, chainFac true 3, 1, true)]
def optsP : List Opt :=
  [(0, chainFac false 0, pairFac 0, false), (0, chainFac true 0, pairFac 0, true),
   (0, chainFac false 1, pairFac 1, false), (0, chainFac true 1, pairFac 1, true),
   (0, chainFac false 2, pairFac 2, false), (0, chainFac true 2, pairFac 2, true),
   (0, chainFac false 3, pairFac 3, false), (0, chainFac true 3, pairFac 3, true)]
def w1Hist (hb : Nat) : Nat × Nat := enumK hb 7 0 optsU 7 6 1 1 1 false
def wfHist (hb : Nat) : Nat × Nat :=
  (List.range 4).foldr (fun x acc =>
    let h := enumK hb 6 0 optsU 6 (6 - x) 1 (box 3) 1 false
    (h.1 + acc.1, h.2 + acc.2)) (0, 0)
def w2Hist (hb : Nat) : Nat × Nat := enumK hb 7 (6 + 32 * 6) optsP 7 0 1 1 1 false
def packPos (d : List (Nat × Int)) : Nat := d.foldr (fun e s => e.2.toNat * HB ^ e.1 + s) 0
def packNeg (d : List (Nat × Int)) : Nat := d.foldr (fun e s => (-e.2).toNat * HB ^ e.1 + s) 0
def histEq (h : Nat × Nat) (d : List (Nat × Int)) : Bool := h.1 + packNeg d == h.2 + packPos d
def massOk (m : Nat × Nat) (d : List (Nat × Int)) : Bool :=
  m.1 < 2 ^ 120 && m.2 < 2 ^ 120 && packPos' d < 2 ^ 120 && packNeg' d < 2 ^ 120
where
  packPos' (d : List (Nat × Int)) : Nat := d.foldr (fun e s => e.2.toNat + s) 0
  packNeg' (d : List (Nat × Int)) : Nat := d.foldr (fun e s => (-e.2).toNat + s) 0
def w1Data : List (Nat × Int) := [(0, 7), (1, -42), (3, -105), (10, 210), (22, 420), (34, 140), (44, -700), (46, 210), (84, -1050), (115, -420), (135, 1365), (155, -420), (206, -210), (236, 1470), (277, -35), (301, 630), (336, -1512), (402, 315), (502, 210), (552, -840), (617, 21), (672, -392), (728, 728)]
def wfData : List (Nat × Int) := [(0, 1), (1, -12), (3, -30), (10, 90), (22, 180), (34, 60), (44, -400), (46, 90), (84, -600), (115, -240), (135, 975), (155, -240), (206, -120), (236, 1050), (277, -20), (301, 450), (336, -1296), (402, 225), (502, 150), (552, -720), (617, 15), (672, -336), (728, 728)]
def w2Data : List (Nat × Int) := [(0, 122073), (1, 157892), (3, -267855), (4, 105840), (5, 32970), (6, -200340), (8, -511560), (9, 26040), (10, 279300), (12, 31080), (15, -511560), (16, 3360), (17, 840), (20, -333480), (22, 1076460), (23, 6300), (25, -107100), (31, 1680), (34, 284340), (42, 140), (44, -836010), (46, 1194690), (53, -110880), (68, 1236480), (72, -85680), (78, -5040), (84, -2182110), (92, 522480), (96, 249060), (98, -5670), (106, -27720), (115, -1251600), (130, 617400), (135, 1437177), (144, -4200), (149, -2520), (155, -1592640), (176, 64470), (177, 203280), (202, -420), (206, -1533630), (234, 12600), (236, 2330790), (239, 73640), (267, -306810), (277, -318675), (301, 1277010), (315, 27300), (336, -1342656), (358, -374850), (402, 803985), (405, 4200), (453, -133350), (502, 764190), (510, 210), (552, -1028160), (563, -11550), (617, 157605), (672, -548800), (728, 529984)]
def wpos (d : List (Nat × Int)) (base r : Nat) : Nat := d.foldr (fun e s => e.2.toNat * (base + e.1) ^ r + s) 0
def wneg (d : List (Nat × Int)) (base r : Nat) : Nat := d.foldr (fun e s => (-e.2).toNat * (base + e.1) ^ r + s) 0
def wwpos (d : List (Nat × Int)) (base r : Nat) : Nat :=
  d.foldr (fun e s => e.2.toNat * wpos d (base + e.1) r + (-e.2).toNat * wneg d (base + e.1) r + s) 0
def wwneg (d : List (Nat × Int)) (base r : Nat) : Nat :=
  d.foldr (fun e s => e.2.toNat * wneg d (base + e.1) r + (-e.2).toNat * wpos d (base + e.1) r + s) 0
def Nn : Nat := 728
def Kc : Nat := 128
def Q : Nat := 93184
def B1 : Nat := 92456
def B2 : Nat := 91728
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xOk (r : Nat) : Bool := wneg w1Data B1 r ≤ wpos w1Data B1 r
def xfNum (r : Nat) : Nat := wpos wfData B1 r - wneg wfData B1 r
def xfOk (r : Nat) : Bool := wneg wfData B1 r ≤ wpos wfData B1 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wwpos w1Data B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wwneg w1Data B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def yOk (r : Nat) : Bool := yNeg r ≤ yPos r
def poissonCheck (f : Nat → Nat) (ok : Nat → Bool) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    27 * 513 ^ r * 256 ^ (R - r) * (fact R / fact r) * f r * Q ^ (9 * (R - r)) + s) 0
  (List.range (R + 1)).all ok &&
  Md * sn * (S * 256 * (R + 1) + 513 ^ (R + 1) * 200 * dbase * Q ^ (9 * R)) ≤
    Mn * sd * 200 * dbase * 256 ^ (R + 1) * fact (R + 1) * Q ^ (9 * R)
def A : Nat := 2 ^ 26 * 1001 ^ 9
def meanCheck : Bool := poissonCheck (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 37 64 80
def meanTightCheck : Bool := poissonCheck (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 1 10 80
def nearCheck : Bool :=
  poissonCheck (fun r => xNum r ^ 8 * xfNum r) (fun r => xOk r && xfOk r) (Nn ^ 9) (63 * A) 1 404 1 80
def diagCheck : Bool :=
  poissonCheck (fun r => yNum r ^ 9) yOk ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) 18400 100000000 80
end ClaudeWCT.Numerics.Kernel
