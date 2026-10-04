import SigGolfCandidate.W9Machine.WctDriverCheck

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def rootPc (k : Fin 9) : Nat := [79,94,109,124,139,154,169,184,199].getD k.val 0
def rootCode (k : Fin 9) : List (BitVec 32) :=
  [rootWords0, rootWords1, rootWords2, rootWords3, rootWords4,
    rootWords5, rootWords6, rootWords7, rootWords8].getD k.val []
def forestSlot (k : Nat) : Nat := 1792 + if k = 0 then 0 else 16 * (k + 1)
theorem rootCode_checked (k : Fin 9) :
    rOK (symRun {} (rootCode k) (pcOf (rootPc k)) 2) (coordRoot (rootPc k) k.val) = true := by
  fin_cases k
  · exact root0_checked
  · exact root1_checked
  · exact root2_checked
  · exact root3_checked
  · exact root4_checked
  · exact root5_checked
  · exact root6_checked
  · exact root7_checked
  · exact root8_checked
theorem rootCode_linked (k : Fin 9) : sliceChecked (rootPc k) (rootCode k) = true := by
  fin_cases k
  · exact root0_linked
  · exact root1_linked
  · exact root2_linked
  · exact root3_linked
  · exact root4_linked
  · exact root5_linked
  · exact root6_linked
  · exact root7_linked
  · exact root8_linked
theorem coordRoot_keeps (p k : Nat) : Keeps (coordRoot p k) [.x12] := by
  intro r hr
  exact RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp))
theorem coordRoot_mem (p k : Nat) (s : MachineState) (a : Word) :
    ((coordRoot p k).toState s).getMem a = s.getMem a := by
  rfl
theorem coordRoot_dest (p k : Nat) (s : MachineState) :
    ((coordRoot p k).toState s).getReg .x12 = BitVec.ofNat 64 (forestSlot k) := by
  rfl
end W9Machine
