import SigGolfCandidate.Verify.ThreadedRuns

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify.Threaded
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def firstHeadK (lay i : Nat) : List (Reg × Word) :=
  chK lay ++ [(.x15, BitVec.ofNat 64 (bIn lay i)),
    (.x12, BitVec.ofNat 64 (0x350+16*i))]

def firstHeadExp (lay i : Nat) : PRes :=
  let wa := chainAddr lay i
  let rf0 := RegFile.withKnown (firstHeadK lay i)
  let rf1 := if hasPrep i && hasLui lay i then rf0.set .x15 (cw (bVal lay i)) else rf0
  let rf2 := if hasPrep i then rf1.set .x14 (rE lay i) else rf1
  let rcur : E := if hasPrep i then rE lay i else .reg .x14
  let rf3 := (rf2.set .x1 (ldE wa)).set .x2 (ldE (wa+8))
  let rf4 := if 1 ≤ i && i < 41 then rf3.set .x4 (.c (linkPc lay i))
    else if i < 2 then rf3.set .x4 (cw i) else rf3
  let n := headLen lay i
  ⟨⟨rf4.set .x12 (cw 0xF0),
    [(⟨none, BitVec.ofNat 64 0xC0⟩, stH 4 (cw (0x350+16*i)))], []⟩,
    0, false, n, n, [],
    some (mkBin .and (mkAdd rcur (.c (BitVec.ofNat 64 (tabAddr lay i)-BitVec.ofNat 64 (bVal lay i))))
      (.c (~~~1#64)))⟩

def firstHeadCheck (lay i : Nat) : Bool :=
  optBeq (run (firstHeadK lay i) [] (nextPc' lay (i-1)) [.jmp]) (firstHeadExp lay i)

def singleEntryExp (lay i d : Nat) : PRes :=
  let dst := if d<7 then 0xF0 else 0x360+16*i
  let rf := if d<7 then RegFile.init else RegFile.init.set .x12 (cw dst)
  let tgt := if d<7 then s1Pc lay i+2*d else nextPc' lay i
  let n := if d<7 then 3 else 4
  ⟨⟨rf, [(⟨none, BitVec.ofNat 64 (dst+8)⟩, .reg .x2),
    (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)], []⟩, pcOf tgt, false, n, n, [], none⟩

def singleCheck (lay i : Nat) : Bool :=
  ((List.range 8).all fun d =>
    optBeq (run [] [if d<7 then s1Pc lay i+2*d else nextPc' lay i] (entryIdx lay i d))
      (singleEntryExp lay i d)) &&
  ((List.range 7).all fun m =>
    optBeq (run (chKa lay) [] (s1Pc lay i+2*m)) (threadedStepExp lay i 0 (m+1)))

def unchangedTopologyCheck (lay : Nat) : Bool :=
  (((pairStarts.drop 1) ++ [20,41]).all (firstHeadCheck lay)) &&
  singleCheck lay 20 && singleCheck lay 41

theorem unchangedTopologyCheck_0 : unchangedTopologyCheck 0 = true := by decide +kernel
theorem unchangedTopologyCheck_1 : unchangedTopologyCheck 1 = true := by decide +kernel
theorem unchangedTopologyCheck_2 : unchangedTopologyCheck 2 = true := by decide +kernel
theorem unchangedTopologyCheck_3 : unchangedTopologyCheck 3 = true := by decide +kernel
theorem unchangedTopologyCheck_4 : unchangedTopologyCheck 4 = true := by decide +kernel
end SigGolfCandidate.Verify.Threaded
