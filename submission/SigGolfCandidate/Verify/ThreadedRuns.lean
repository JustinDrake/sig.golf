import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ThreadedImages

/-! Symbolic checks for the submitted threaded verifier. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify.Threaded
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def pairStarts : List Nat := [0,2,4,6,8,10,12,14,16,18,21,23,25,27,29,31,33,35,37,39]
def variantOffset (d2 : Nat) : Nat := [0,37,72,105,136,165,192,217].getD d2 0
def firstBody (lay i d2 : Nat) : Nat := (tabAddr lay (i+1) - 0x1000) / 4 + variantOffset d2
def secondHead (lay i d2 : Nat) : Nat := firstBody lay i d2 + 15
def secondBody (lay i d2 : Nat) : Nat := secondHead lay i d2 + 6
def tailPc (lay i d2 : Nat) : Nat :=
  if d2 < 7 then secondBody lay i d2 + 2 * (7-d2) + 1 else secondHead lay i d2 + 5

def chainS1 (lay i d2 : Nat) : Nat :=
  if isSingle i then s1Pc lay i else if isFirst i then firstBody lay i d2
  else secondBody lay (i-1) d2 - 2*d2

def chainEnd (lay i d2 : Nat) : Nat :=
  if isSingle i then nextPc' lay i else if isFirst i then secondHead lay i d2
  else tailPc lay (i-1) d2

def run (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Dir := []) : Option PRes :=
  pathAux cfg0 look (stops.map pcOf) 400 (pcOf n) dirs (σK known) []

def threadedStepExp (lay i d2 mu : Nat) : PRes :=
  let st := chainS1 lay i d2 + 2 * (mu - 1)
  if mu = 7 then
    ⟨⟨(RegFile.withKnown (chKa lay)).set .x12 (cw (0x360+16*i)),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 6 (cw (mu-1)))], []⟩,
      pcOf (st+2), true, 2, 2, [], none⟩
  else
    ⟨⟨RegFile.withKnown (chKa lay),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 6 (cw (mu-1)))], []⟩,
      pcOf (st+1), true, 1, 1, [], none⟩

def secondK (lay i : Nat) : List (Reg × Word) :=
  chK lay ++ [(.x12, BitVec.ofNat 64 (0x360+16*i))]

def secondExp (lay i d2 : Nat) : PRes :=
  let wa := chainAddr lay (i+1)
  let rf := ((RegFile.withKnown (secondK lay i)).set .x1 (ldE wa)).set .x2 (ldE (wa+8))
  let dst := if d2 < 7 then 0xF0 else 0x360+16*(i+1)
  let mem := [(⟨none, BitVec.ofNat 64 (dst+8)⟩, ldE (wa+8)),
    (⟨none, BitVec.ofNat 64 dst⟩, ldE wa)] ++
    (if d2 < 7 then [(⟨none, BitVec.ofNat 64 0xC0⟩, stH 4 (cw (0x360+16*i)))] else [])
  let n := if d2 < 7 then 6 else 5
  ⟨⟨rf.set .x12 (cw dst), mem, []⟩,
    pcOf (if d2 < 7 then secondBody lay i d2 else tailPc lay i d2), false, n, n, [], none⟩

def tailK (lay i : Nat) : List (Reg × Word) :=
  chK lay ++ [(.x12, BitVec.ofNat 64 (0x360+16*(i+1)))]

def tailExp (lay i : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (tailK lay i), [], []⟩, pcOf (nextPc' lay (i+1)), false, 1, 1, [], none⟩

def firstEntryExp (lay i d1 d2 : Nat) : PRes :=
  let dst := if d1<7 then 0xF0 else 0x360+16*i
  let rf := if d1<7 then RegFile.init else RegFile.init.set .x12 (cw dst)
  let tgt := if d1<7 then firstBody lay i d2 + 2*d1 else secondHead lay i d2
  let n := if d1<7 then 3 else 4
  ⟨⟨rf, [(⟨none, BitVec.ofNat 64 (dst+8)⟩, .reg .x2),
    (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)], []⟩, pcOf tgt, false, n, n, [], none⟩

def pairStepCheck (lay i d2 : Nat) : Bool :=
  ((List.range 7).all fun m => optBeq (run (chKa lay) [] (chainS1 lay i d2 + 2*m))
    (threadedStepExp lay i d2 (m+1))) &&
  ((List.range (7-d2)).all fun m =>
    optBeq (run (chKa lay) [] (chainS1 lay (i+1) d2 + 2*(m+d2)))
      (threadedStepExp lay (i+1) d2 (m+d2+1)))

def secondCheck (lay i d2 : Nat) : Bool :=
  optBeq (run (secondK lay i) [secondBody lay i d2, tailPc lay i d2] (secondHead lay i d2))
    (secondExp lay i d2)

def tailCheck (lay i d2 : Nat) : Bool :=
  optBeq (run (tailK lay i) [nextPc' lay (i+1)] (tailPc lay i d2)) (tailExp lay i)

def entryCheck (lay i d1 d2 : Nat) : Bool :=
  let tgt := if d1<7 then firstBody lay i d2 + 2*d1 else secondHead lay i d2
  optBeq (run [] [tgt] (entryIdx lay i (d1+8*d2))) (firstEntryExp lay i d1 d2)

def variantCheck (lay i d2 : Nat) : Bool :=
  pairStepCheck lay i d2 && secondCheck lay i d2 && tailCheck lay i d2 &&
    ((List.range 8).all fun d1 => entryCheck lay i d1 d2)
def pairCheck (lay i : Nat) : Bool := (List.range 8).all (variantCheck lay i)

theorem chunks_ok : (chunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel

def image : Image := ⟨chunks.flatten, []⟩
theorem look_ok : LookOK image look := by
  intro n w h
  exact lookup_chunks chunks n w chunks_ok h

end SigGolfCandidate.Verify.Threaded
