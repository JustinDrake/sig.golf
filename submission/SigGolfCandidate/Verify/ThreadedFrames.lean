import SigGolfCandidate.Verify.ThreadedFormatRuns
import SigGolfCandidate.Verify.ThreadedBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify.Threaded
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def frames (post : List (Reg × Word)) (keep : List Reg) (e : PRes) : Bool :=
  resOK gkL e && knownB post e && keepB keep e

def stepPost (lay i mu : Nat) : List (Reg × Word) :=
  chK lay ++ [(.x12, BitVec.ofNat 64 (if mu=7 then 0x360+16*i else 0xF0))]
def stepFrames (lay i d2 mu : Nat) : Bool :=
  frames (stepPost lay i mu) ckeep (threadedStepExp lay i d2 mu)

def secondPost (lay i d2 : Nat) : List (Reg × Word) :=
  chK lay ++ [(.x12, BitVec.ofNat 64 (if d2<7 then 0xF0 else 0x360+16*(i+1)))]
def secondFrames (lay i d2 : Nat) : Bool := frames (secondPost lay i d2) ckeep (secondExp lay i d2)
def tailFrames (lay i : Nat) : Bool := frames (tailK lay i) ckeep (tailExp lay i)
def firstHeadFrames (lay i : Nat) : Bool :=
  frames (chKa lay ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i) (firstHeadExp lay i)
def entryPost (i d : Nat) : List (Reg × Word) :=
  if d<7 then [] else [(.x12, BitVec.ofNat 64 (0x360+16*i))]
def firstEntryFrames (lay i d1 d2 : Nat) : Bool :=
  resOK [] (firstEntryExp lay i d1 d2) && knownB (entryPost i d1) (firstEntryExp lay i d1 d2) &&
    keepB (ckeep ++ gkL.map Prod.fst) (firstEntryExp lay i d1 d2)
def singleEntryFrames (lay i d : Nat) : Bool :=
  resOK [] (singleEntryExp lay i d) && knownB (entryPost i d) (singleEntryExp lay i d) &&
    keepB (ckeep ++ gkL.map Prod.fst) (singleEntryExp lay i d)

def stepOK (lay i d2 mu : Nat) : Bool :=
  okC (run (chKa lay) [] (chainS1 lay i d2+2*(mu-1)))
    (threadedStepExp lay i d2 mu) (stepPost lay i mu) ckeep

def secondOK (lay i d2 : Nat) : Bool :=
  okC (run (secondK lay i) [secondBody lay i d2,tailPc lay i d2] (secondHead lay i d2))
    (secondExp lay i d2) (secondPost lay i d2) ckeep

def tailOK (lay i d2 : Nat) : Bool :=
  okC (run (tailK lay i) [nextPc' lay (i+1)] (tailPc lay i d2))
    (tailExp lay i) (tailK lay i) ckeep

def firstHeadOK (lay i : Nat) : Bool :=
  okC (run (firstHeadK lay i) [] (nextPc' lay (i-1)) [.jmp])
    (firstHeadExp lay i) (chKa lay ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i)

theorem okC_of_opt_frames {o : Option PRes} {e : PRes} {post : List (Reg × Word)} {keep : List Reg}
    (ho : optBeq o e = true) (hf : frames post keep e = true) : okC o e post keep = true := by
  simp only [okC, frames, Bool.and_eq_true] at *
  exact ⟨⟨⟨ho,hf.1.1⟩,hf.1.2⟩,hf.2⟩

def layerFrames (lay : Nat) : Bool :=
  (((pairStarts.drop 1) ++ [20,41]).all (firstHeadFrames lay)) &&
  (pairStarts.all fun i =>
    tailFrames lay i && ((List.range 8).all fun d2 =>
      secondFrames lay i d2 &&
      ((List.range 8).all fun d1 => firstEntryFrames lay i d1 d2) &&
      ((List.range 7).all fun m => stepFrames lay i d2 (m+1)) &&
      ((List.range (7-d2)).all fun m => stepFrames lay (i+1) d2 (m+d2+1)))) &&
  ([20,41].all fun i =>
    ((List.range 8).all fun d => singleEntryFrames lay i d) &&
    ((List.range 7).all fun m => stepFrames lay i 0 (m+1)))

theorem layerFrames_0 : layerFrames 0 = true := by decide +kernel
theorem layerFrames_1 : layerFrames 1 = true := by decide +kernel
theorem layerFrames_2 : layerFrames 2 = true := by decide +kernel
theorem layerFrames_3 : layerFrames 3 = true := by decide +kernel
theorem layerFrames_4 : layerFrames 4 = true := by decide +kernel
end SigGolfCandidate.Verify.Threaded
