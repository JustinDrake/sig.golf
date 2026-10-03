import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck0
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck1
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck2
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck3
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck4
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck5
import SigGolfCandidate.T3M.Verify.CanonicalBlockCheck6

namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

theorem blocks_checked : ∀ g : Fin 42, checkGeom g.val=true := by
  have hgroup : ∀ group : Fin 7, ∀ offset : Fin 6,
      checkGeom (6*group.val+offset.val)=true := by
    intro group offset
    fin_cases group
    · simpa using blocks_checked_0 offset
    · simpa using blocks_checked_1 offset
    · simpa using blocks_checked_2 offset
    · simpa using blocks_checked_3 offset
    · simpa using blocks_checked_4 offset
    · simpa using blocks_checked_5 offset
    · simpa using blocks_checked_6 offset
  intro g
  have hdiv : g.val/6<7 := by omega
  have hmod : g.val%6<6 := Nat.mod_lt _ (by decide)
  have he : 6*(g.val/6)+g.val%6=g.val := by omega
  rw [← he]
  exact hgroup ⟨g.val/6,hdiv⟩ ⟨g.val%6,hmod⟩

theorem pending_checked (g j side : Nat) (hg : g<42) (hj : j<5) (hs : side<2) :
    pendingCheck g j side=true := by
  have hh := blocks_checked ⟨g,hg⟩
  have hj' := List.all_eq_true.mp hh j (List.mem_range.mpr hj)
  have hs' := List.all_eq_true.mp hj' side (List.mem_range.mpr hs)
  simp only [Bool.and_eq_true] at hs'
  exact hs'.1

theorem rung_checked (g j i side out : Nat) (hg : g<42) (hj : j<5)
    (hi : i<10) (hs : side<2) (ho : out<2) : rungCheck g j i side out=true := by
  have hh := blocks_checked ⟨g,hg⟩
  have hj' := List.all_eq_true.mp hh j (List.mem_range.mpr hj)
  have hs' := List.all_eq_true.mp hj' side (List.mem_range.mpr hs)
  simp only [Bool.and_eq_true] at hs'
  have hi' := List.all_eq_true.mp hs'.2 i (List.mem_range.mpr hi)
  exact List.all_eq_true.mp hi' out (List.mem_range.mpr ho)

theorem pending_run (g j side : Nat) (hg : g<42) (hj : j<5) (hs : side<2)
    (s : MachineState) (hpc : s.pc=pcOf (plan g j).start)
    (hbr : ∀ b∈(pendingSpec (plan g j) side).brs, b.holds s)
    (hob : ∀ o∈pendingObl (plan g j), o.holds s) :
    ∃ t, RawRes (pendingSpec (plan g j) side) pendingKeep s t := by
  exact raw_run (pending_checked g j side hg hj hs) s hpc (by simp [KnownOK]) hbr hob

theorem rung_run (g j i side out : Nat) (hg : g<42) (hj : j<5)
    (hi : i<10) (hs : side<2) (ho : out<2) (ha : i<(plan g j).folds)
    (s : MachineState) (hpc : s.pc=pcOf (atRung (plan g j) side i))
    (hbr : ∀ b∈(rungSpec (plan g j) i side out).brs, b.holds s)
    (hob : ∀ o∈rungObl (plan g j) i, o.holds s) :
    ∃ t, RawRes (rungSpec (plan g j) i side out) rungKeep s t := by
  have hh := rung_checked g j i side out hg hj hi hs ho
  unfold rungCheck at hh
  rw [if_neg (by omega)] at hh
  exact raw_run hh s hpc (by simp [KnownOK]) hbr hob

#print axioms pending_run
#print axioms rung_run
end SigGolfCandidate.T3M.CanonicalNative
