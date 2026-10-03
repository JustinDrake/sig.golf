import SigGolfCandidate.T3M.Verify.CanonicalNative
import SigGolfCandidate.T3M.Verify.Spec

/-! Checked symbolic paths for the research fixture. No full refinement or
security certificate is asserted here. -/
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def runAtC (cfg : Config) (known : List (Reg × Word)) (stops : List Nat)
    (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg look (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

structure SpecResC (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (sp : Spec)
    (post : List (Reg × Word)) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps fixture s sp.steps sp.cycles t
  ecall : sp.ecall = true → fetch fixture t = some (.base .ECALL)
  glob : ∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKA allow rel sp.mem = true
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem spec_runC {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)} {stops : List Nat}
    {cfg : Config} {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (runAtC cfg known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecResC allow rel gk sp post keep s t := by
  unfold specB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  obtain ⟨hst', hec'⟩ := pathRun_sound hr look_ok s hpc hk (by rw [hobl']; exact hob)
    (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro gk0 w pk hG hrel; exact Glob_toState_allow hG r.st _ hmok hrel hrok
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]


end SigGolfCandidate.T3M.CanonicalNative
