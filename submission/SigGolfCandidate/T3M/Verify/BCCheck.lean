import SigGolfCandidate.T3M.Verify.LayerRuns

section

namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.preK lay else
  (T3M.preK lay).filter (fun p => p.1 != .x10 && p.1 != .x12) ++
    [(.x22, BitVec.ofNat 64 (s6v (lay + 1)))]
def bK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.bK lay else
  (T3M.bK lay).filter (fun p => p.1 != .x10) ++
    [(.x10, BitVec.ofNat 64 (x10In lay))]
def ctrE (lay : Nat) : E :=
  if lay = 3 then T3M.ctrE lay else .un (.ld .wu 0) (.ld (kw (x10In lay + 32)))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨.geu, ctrE lay, kw 0x400000, d⟩
def headerWrites (lay : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (x10In lay + 24)⟩, tpE lay),
   (⟨none, BitVec.ofNat 64 (x10In lay + 16)⟩, kw (hw 4 lay))]
def specA (lay p : Nat) : Spec :=
  if lay = 3 then T3M.specA lay p else
  ⟨if lay = 0 then [(.x4, tpE lay), (.x23, s7E lay), (.x3, ctrE lay)]
   else [(.x4, tpE lay), (.x23, s7E lay), (.x30, treeE lay), (.x3, ctrE lay)],
   headerWrites lay, p + stepsA lay, true, stepsA lay,
   [ctrBr lay false], none, stepsA lay⟩
def rejA (lay p : Nat) : Spec :=
  if lay = 3 then T3M.rejA lay p else
  ⟨[(.x5, kw 1), (.x10, kw 1)], headerWrites lay,
   rejEcall, true, stepsA lay + 2, [ctrBr lay true], none, stepsA lay + 2⟩
def allowed (lay : Nat) : List Nat :=
  if lay = 3 then [] else [x10In lay + 16, x10In lay + 24]
def setupCheck (lay p : Nat) : Bool :=
  specB (allowed lay) [] baseK (runAt (preK lay) [] p [.br false])
    (specA lay p) [] (bK lay) keepA &&
  specB (allowed lay) [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] []
def copyCheck (lay p : Nat) : Bool :=
  setupCheck lay p &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [724] (p + stepsA lay + 1) [])
      (specTopCall p) [] [] keepTopCall
  else
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1)
      [.br false, .br false, .jmp]) (specBl lay p) [] (postBl lay p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1)
      [.br false, .br true]) (rejCk lay) [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1)
      [.br true]) (rejRng 62) [] [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) (lfDirs lay))
    (specLf lay) [] (postLf lay) keepLf
def layerCheck (lay lo n : Nat) : Bool :=
  (List.range' lo n).all fun c => copyCheck lay (trPc lay c)
end SigGolfCandidate.T3M.BC
end

section

namespace SigGolfCandidate.T3M.BC
set_option maxRecDepth 100000
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by decide +kernel
end SigGolfCandidate.T3M.BC
end
