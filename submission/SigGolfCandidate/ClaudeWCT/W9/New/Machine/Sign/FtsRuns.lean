import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Common

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runA (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux { noAlias := true } look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
def cE (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldc (a : Nat) : E := .ld (cE a)
def mwc (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def regsOf (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def pres (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, k, brs, none⟩
def pI (c p : Nat) : Nat := pIdx.getD (4 * c + p) 0
def preI (c i : Nat) : Nat := preIdx.getD (7 * c + i) 0
def chkI (c i s : Nat) : Nat := chkIdx.getD (28 * c + 4 * i + s) 0
def skipI (c i s : Nat) : Nat := skipIdx.getD (28 * c + 4 * i + s) 0
def leafI (c : Nat) : Nat := leafIdx.getD c 0
def lI (c : Nat) : Nat := lIdx.getD c 0
def tI (c : Nat) : Nat := tIdx.getD c 0
def nodeI (c : Nat) : Nat := nodeIdx.getD c 0
def ntI (c : Nat) : Nat := ntIdx.getD c 0
def rI (c : Nat) : Nat := rIdx.getD c 0
def lwuI (c : Nat) : Nat := lwuIdx.getD c 0
def pcI (c l : Nat) : Nat := rI c + 8 + 13 * l
def lcEnd (c i : Nat) : Nat := if i = 6 then lI c else if i % 2 = 0 then preI c (i + 1) else pI c ((i + 1) / 2)
def hdr8 (c : Nat) : Nat := 2049 + 65536 * c
def hdr5 (c : Nat) : Nat := 1281 + 65536 * c
def hdr6 (c : Nat) : Nat := 1537 + 65536 * c
def hdr11 (c : Nat) : Nat := 2817 + 65536 * c
def slotV (c i : Nat) : Nat := SIG + 16 + 224 * c + 16 * i
def slotP (c l : Nat) : Nat := SIG + 128 + 224 * c + 16 * l
def leafOff (i : Nat) : Nat := if i = 0 then 0 else 16 * (i + 1)
def forOff (c : Nat) : Nat := if c = 0 then 0 else 16 * (c + 1)
def x18x4 : E := .bin .add (.bin .add (.bin .add (.reg .x18) (.reg .x18)) (.reg .x18)) (.reg .x18)
def privW1E (p : Nat) : E := .bin .or (.bin .sll (if p = 0 then x18x4 else .bin .add x18x4 (cE p)) (cE 32)) (.reg .x22)
def w1E : E := .bin .or (.bin .sll (.reg .x18) (cE 32)) (.reg .x22)
def dE (i : Nat) : E := .bin .sub (cE 3) (.bin .and (.bin .srl (.reg .x25) (cE (2 * i))) (cE 3))
def x18p1 : E := .bin .add (.reg .x18) (cE 1)
def x18m1 : E := .bin .add (.reg .x18) (cE (2 ^ 64 - 1))
def heapLeafE : E := .bin .sll (.bin .add (.reg .x18) (cE 128)) (cE 4)
def sh5 : E := .bin .sll (.reg .x18) (cE 5)
def sh4 : E := .bin .sll (.reg .x18) (cE 4)
def pathE (l : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.bin .add (.reg .x24) (cE 128)) (cE l)) (cE 1)) (cE 4)
def fsrcE (c : Nat) : E :=
  if WCT9.coordBase c % 64 = 0 then ldc (NBUF + 8 * (WCT9.coordBase c / 64))
  else .bin .srl (ldc (NBUF + 8 * (WCT9.coordBase c / 64))) (cE (WCT9.coordBase c % 64))
def fieldE (c : Nat) : E := .bin .and (.bin .srl (fsrcE c) (cE 7)) (cE 16383)
def expF (c : Nat) : PRes :=
  pres [(.x6, .bin .sll (fieldE c) (cE 2)), (.x24, .bin .and (fsrcE c) (cE 127)), (.x25, fieldE c),
    (.x28, .bin .add (.bin .sll (fieldE c) (cE 2)) (cE TBL))] [] [] (lwuI c) false
    (if WCT9.coordBase c % 64 = 0 then 12 else 13) []
def expZ (c : Nat) : PRes := pres [(.x18, cE 0)] [] [] (leafI c) false 1 []
def expP (c p : Nat) : PRes :=
  pres [(.x6, privW1E p), (.x10, cE PRIVW), (.x11, cE 64), (.x12, cE PAIRW), (.x28, cE PRIVW)]
    [mwc (PRIVW + 24) (privW1E p), mwc (PRIVW + 16) (cE (hdr8 c))] [] (pI c p + 19) true 19 []
def expPre (c i : Nat) : PRes :=
  pres [(.x6, cE 3), (.x7, ldc (PAIRW + 16 * (i % 2) + 8)), (.x26, dE i), (.x28, cE PAIRW), (.x29, cE CHAINW)]
    [mwc (CHAINW + 16) (cE (hdr5 c + 2 ^ 40 * i)), mwc (CHAINW + 24) w1E,
      mwc (CHAINW + 56) (ldc (PAIRW + 16 * (i % 2) + 8)), mwc (CHAINW + 48) (ldc (PAIRW + 16 * (i % 2)))] []
    (chkI c i 0) false (if c = 0 then 19 else 20) []
def expChk (c i s v : Nat) : PRes :=
  if v = 0 then pres [] [] [] (skipI c i s) false 1 [⟨.ne, .reg .x18, .reg .x24, true⟩]
  else if v = 1 then
    pres [(.x6, cE s)] [] [] (skipI c i s) false 3 [⟨.ne, .reg .x26, cE s, true⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
  else
    pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE (slotV c i))]
      [mwc (slotV c i + 8) (ldc (CHAINW + 56)), mwc (slotV c i) (ldc (CHAINW + 48))] [] (skipI c i s) false 11
      [⟨.ne, .reg .x26, cE s, false⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
def expStp (c i s : Nat) : PRes :=
  pres [(.x6, cE (s - 1)), (.x10, cE CHAINW), (.x11, cE 64), (.x12, cE (CHAINW + 48)), (.x29, cE CHAINW)]
    [mwc (CHAINW + 16) (.bin (.st .b 4) (ldc (CHAINW + 16)) (cE (s - 1)))] [] (chkI c i s - 1) true 9 []
def expLc (c i : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE LEAFW)]
    [mwc (LEAFW + leafOff i + 8) (ldc (CHAINW + 56)), mwc (LEAFW + leafOff i) (ldc (CHAINW + 48))] []
    (lcEnd c i) false 8 []
def expL (c : Nat) : PRes :=
  pres [(.x6, heapLeafE), (.x10, cE LEAFW), (.x11, cE 128), (.x12, .bin .add heapLeafE (cE HEAPW)),
    (.x29, cE LEAFW)] [mwc (LEAFW + 24) w1E, mwc (LEAFW + 16) (cE (hdr6 c))] [] (tI c - 1) true
    (if c = 0 then 15 else 16) []
def expT (c : Nat) (back : Bool) : PRes :=
  if back then pres [(.x6, cE 128), (.x18, x18p1)] [] [] (leafI c) false 3 [⟨.ltu, x18p1, cE 128, true⟩]
  else pres [(.x6, cE 128), (.x18, cE 127)] [] [] (nodeI c) false 4 [⟨.ltu, x18p1, cE 128, false⟩]
def nodeLd (off : Nat) : E := .ld (.bin .add sh5 (cE (HEAPW + off)))
def nodeAddr (off : Nat) : Addr := ⟨some sh5, BitVec.ofNat 64 (HEAPW + off)⟩
def expN (c : Nat) : PRes :=
  pres [(.x6, w1E), (.x7, nodeLd 24), (.x10, cE NODEW), (.x11, cE 64), (.x12, cE NOUTW),
    (.x28, .bin .add sh5 (cE HEAPW)), (.x29, cE NODEW)]
    [mwc (NODEW + 24) w1E, mwc (NODEW + 16) (cE (hdr11 c)), mwc (NODEW + 56) (nodeLd 24),
      mwc (NODEW + 48) (nodeLd 16), mwc (NODEW + 8) (nodeLd 8), mwc NODEW (nodeLd 0)]
    [.ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 NODEW⟩, .ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩,
      .valid (nodeAddr 24) 8, .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 NODEW⟩,
      .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩, .valid (nodeAddr 16) 8, .valid (nodeAddr 8) 8,
      .valid (nodeAddr 0) 8]
    (ntI c - 1) true 25 []
def heapAddr (off : Nat) : Addr := ⟨some sh4, BitVec.ofNat 64 (HEAPW + off)⟩
def expNT (c : Nat) (back : Bool) : PRes :=
  pres [(.x6, ldc NOUTW), (.x7, ldc (NOUTW + 8)), (.x18, x18m1), (.x28, cE NOUTW),
    (.x29, .bin .add sh4 (cE HEAPW))]
    [(heapAddr 8, ldc (NOUTW + 8)), (heapAddr 0, ldc NOUTW)] [.valid (heapAddr 8) 8, .valid (heapAddr 0) 8]
    (if back then nodeI c else rI c) false 12 [⟨.ne, x18m1, cE 0, back⟩]
def expR0 (c : Nat) : PRes :=
  pres [(.x6, ldc (HEAPW + 16)), (.x7, ldc (HEAPW + 24)), (.x28, cE (HEAPW + 16)), (.x29, cE (FORW + forOff c))]
    [mwc (FORW + forOff c + 8) (ldc (HEAPW + 24)), mwc (FORW + forOff c) (ldc (HEAPW + 16))] [] (pcI c 0) false 8 []
def pathAddr (l off : Nat) : Addr := ⟨some (pathE l), BitVec.ofNat 64 (HEAPW + off)⟩
def pathLd (l off : Nat) : E := .ld (.bin .add (pathE l) (cE (HEAPW + off)))
def expPC (c l : Nat) : PRes :=
  pres [(.x6, pathLd l 0), (.x7, pathLd l 8), (.x28, .bin .add (pathE l) (cE HEAPW)), (.x29, cE (slotP c l))]
    [mwc (slotP c l + 8) (pathLd l 8), mwc (slotP c l) (pathLd l 0)] [.valid (pathAddr l 8) 8, .valid (pathAddr l 0) 8]
    (pcI c (l + 1)) false 13 []
def expSK : PRes :=
  pres [(.x6, ldc 0x90), (.x7, ldc 0x98), (.x28, cE 0x80), (.x29, cE PRIVW)]
    [mwc (PRIVW + 40) (ldc 0x98), mwc (PRIVW + 32) (ldc 0x90), mwc (PRIVW + 8) (ldc 0x88), mwc PRIVW (ldc 0x80)] []
    (fieldIdx.getD 0 0) false 11 []
def expFor : PRes :=
  pres [(.x6, cE 3841), (.x10, cE FORW), (.x11, cE 192), (.x12, cE FOUT), (.x28, cE FORW)]
    [mwc (FORW + 24) (.reg .x22), mwc (FORW + 16) (cE 3841)] [] 10929 true 11 []
def expJ : PRes := pres [] [] [] 370 false 1 []
def runF (c : Nat) : Option PRes := run (coordLook c) [lwuI c] (cbase c) []
def runZ (c : Nat) : Option PRes := run (coordLook c) [leafI c] (lwuI c + 1) []
def runP (c p : Nat) : Option PRes := run (coordLook c) [] (pI c p) []
def runPre (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (preI c i) []
def chkDirs (v : Nat) : List Dir := if v = 0 then [.br true] else if v = 1 then [.br false, .br true] else [.br false, .br false]
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 3) []
def runL (c : Nat) : Option PRes := run (coordLook c) [] (lI c) []
def runT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [leafI c, nodeI c] (tI c) [.br back]
def runN (c : Nat) : Option PRes := runA (coordLook c) [] (nodeI c) []
def runNT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [nodeI c, rI c] (ntI c) [.br back]
def runR0 (c : Nat) : Option PRes := run (coordLook c) [pcI c 0] (rI c) []
def runPC (c l : Nat) : Option PRes := run (coordLook c) [pcI c (l + 1)] (pcI c l) []
def runSK : Option PRes := run headLook [fieldIdx.getD 0 0] 2215 []
def runFor : Option PRes := run tailLook [370] 10918 []
def runJ : Option PRes := run tailLook [370] 10930 []
def okF (c : Nat) : Bool := optBeq (runF c) (expF c) && optBeq (runZ c) (expZ c)
def okP (c : Nat) : Bool := (List.range 4).all fun p => optBeq (runP c p) (expP c p)
def okPre (c : Nat) : Bool := (List.range 7).all fun i => optBeq (runPre c i) (expPre c i)
def okChk (c : Nat) : Bool :=
  (List.range 7).all fun i => (List.range 4).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
def okStp (c : Nat) : Bool :=
  (List.range 7).all fun i => (List.range' 1 3).all fun s => optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 7).all fun i => optBeq (runLc c i) (expLc c i)
def okTail (c : Nat) : Bool :=
  optBeq (runL c) (expL c) && optBeq (runT c true) (expT c true) && optBeq (runT c false) (expT c false) &&
    optBeq (runN c) (expN c) && optBeq (runNT c true) (expNT c true) && optBeq (runNT c false) (expNT c false) &&
    optBeq (runR0 c) (expR0 c) && (List.range 7).all fun l => optBeq (runPC c l) (expPC c l)
def okCoord (c : Nat) : Bool := okF c && okP c && okPre c && okChk c && okStp c && okLc c && okTail c
def okGlobal : Bool := optBeq runSK expSK && optBeq runFor expFor && optBeq runJ expJ
end ClaudeWCT.W9.Machine.Sign
