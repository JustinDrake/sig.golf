import SigGolfCandidate.Verify.ThreadedRuns

namespace SigGolfCandidate.Verify.Threaded
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem run_post {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {r : PRes} {gk : List (Reg × Word)} (hlook : LookOK Verify.image look)
    (hrun : run known stops n dirs = some r) (hok : resOK gk r = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps Verify.image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch Verify.image (r.toState s) = some (.base .ECALL)) ∧
      (∀ wl pk, Glob gk wl pk s → Glob gk wl pk (r.toState s)) := by
  simp only [resOK, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨hm, hr⟩, ho⟩ := hok
  obtain ⟨h1,h2⟩ := pathRun_sound hrun hlook s hpc hk (by rw [ho]; simp) hbr
  exact ⟨h1,h2,fun wl pk hG => Glob_toState hG r.st _ hm hr⟩

theorem run_post' {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {r : PRes} (hlook : LookOK Verify.image look)
    (hrun : run known stops n dirs = some r) (hobl : r.st.obl = [])
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps Verify.image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch Verify.image (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound hrun hlook s hpc hk (by rw [hobl]; simp) hbr

end SigGolfCandidate.Verify.Threaded
