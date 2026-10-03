import SigGolfCandidate.T3M.Verify.CanonicalChecked

/-! The branch-free joins between scheduled segments and bank returns. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def returns : Array Nat := #[222283, 222479, 222689, 222913, 223151, 223403, 223583, 223795, 224023, 224265, 224521, 224791, 224987, 225199, 225439, 225695, 225965, 226249, 226459, 226687, 226927, 227195, 227479, 227777, 228001, 228243, 228499, 228767, 229063, 229375, 229613, 229869, 230139, 230423, 230719, 231043, 231295, 231565, 231849, 232147, 232459, 232783]
def allKeep : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

def nextSegment (g j : Nat) : Nat := if j=4 then returns[g]! else (plan g (j+1)).start
def tailSpec (g j side : Nat) : Spec :=
  ⟨[],[],nextSegment g j,false,
    (if (plan g j).folds>0 ∧ side=0 then 1 else 0),[],none,
    (if (plan g j).folds>0 ∧ side=0 then 1 else 0)⟩
def tailCheck (g j side : Nat) : Bool :=
  let p := plan g j
  if p.folds>0 ∧ side=0 then
    rawB (runAtC {} [] [nextSegment g j] (atHash p side p.folds+1) [])
      (tailSpec g j side) [] allKeep
  else atHash p side p.folds+1==nextSegment g j

theorem tails_checked : ∀ (g : Fin 42) (j : Fin 5) (side : Fin 2),
    tailCheck g.val j.val side.val=true := by decide +kernel

def returnSpec : Spec :=
  ⟨[],[],0,false,1,[],some (.bin .and (.reg .x1) (cE (~~~1#64))),1⟩
def returnCheck (g : Nat) : Bool :=
  rawB (runAtC {} [] [] returns[g]! [.jmp]) returnSpec [] allKeep

theorem returns_checked : ∀ g : Fin 42, returnCheck g.val=true := by decide +kernel

theorem tail_run (g j side : Nat) (hg : g<42) (hj : j<5) (hs : side<2)
    (s : MachineState) (hpc : s.pc=pcOf (atHash (plan g j) side (plan g j).folds+1)) :
    ∃ t, RawRes (tailSpec g j side) allKeep s t := by
  have hh := tails_checked ⟨g,hg⟩ ⟨j,hj⟩ ⟨side,hs⟩
  unfold tailCheck at hh
  by_cases he : (plan g j).folds>0 ∧ side=0
  · rw [if_pos he] at hh
    exact raw_run hh s hpc (by simp [KnownOK]) (by simp [tailSpec]) (by simp)
  · rw [if_neg he] at hh
    have hp : atHash (plan g j) side (plan g j).folds+1=nextSegment g j := beq_iff_eq.mp hh
    refine ⟨s,⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
    · simpa [tailSpec,he] using (Steps.refl (image:=fixture) s)
    · simp [tailSpec]
    · intro r hr; rfl
    · simp [tailSpec]
    · intro A; rfl
    · intro hn; simpa [tailSpec,hp] using hpc
    · simp [tailSpec]

theorem return_run (g : Nat) (hg : g<42) (s : MachineState) (hpc : s.pc=pcOf returns[g]!) :
    ∃ t, RawRes returnSpec allKeep s t := by
  exact raw_run (returns_checked ⟨g,hg⟩) s hpc
    (by simp [KnownOK]) (by simp [returnSpec]) (by simp)

#print axioms tail_run
#print axioms return_run
end SigGolfCandidate.T3M.CanonicalNative
