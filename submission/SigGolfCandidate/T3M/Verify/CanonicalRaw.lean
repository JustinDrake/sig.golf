import SigGolfCandidate.T3M.Verify.CanonicalSpec

/-! Checked paths without a phase-independent memory permission predicate.
The caller proves the exact memory frame from the listed writes. This covers
FTS stores behind the already advanced stream pointer. -/
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def rawB (o : Option PRes) (sp : Spec) (obl : List Oblig) (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem &&
      (sp.spc.isSome || r.pc.toNat == (pcOf sp.pc).toNat) &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.cycles &&
      listBeq Br.beq r.brs sp.brs && optEBeq r.spc sp.spc &&
      listBeq Oblig.beq r.st.obl obl && keepB keep r

structure RawRes (sp : Spec) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps fixture s sp.steps sp.cycles t
  ecall : sp.ecall=true → fetch fixture t=some (.base .ECALL)
  keep : ∀ x∈keep, t.getReg x=s.getReg x
  regs : ∀ p∈sp.regs, t.getReg p.1=p.2.eval s
  mem : ∀ A, t.getMem A=memEval s sp.mem A
  pc : sp.spc=none → t.pc=pcOf sp.pc
  spc : ∀ e, sp.spc=some e → t.pc=e.eval s

theorem raw_run {known : List (Reg × Word)} {stops : List Nat}
    {cfg : Config} {n : Nat} {dirs : List Dir} {sp : Spec}
    {obl : List Oblig} {keep : List Reg}
    (h : rawB (runAtC cfg known stops n dirs) sp obl keep=true)
    (s : MachineState) (hpc : s.pc=pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b∈sp.brs, b.holds s) (hob : ∀ o∈obl, o.holds s) :
    ∃ t, RawRes sp keep s t := by
  unfold rawB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs,hmem⟩,hpc'⟩,hec⟩,hst⟩,hcy⟩,hbrs⟩,hspc⟩,hobl⟩,hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  obtain ⟨hst',hec'⟩ := pathRun_sound hr look_ok s hpc hk
    (by rw [hobl']; exact hob) (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s,⟨?_,?_,keepB_ok hkeep s,?_,?_,?_,?_⟩⟩
  · rw [hcy,hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro p hp
    rw [PRes.toState_getReg,E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem,hmem']
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none,Bool.false_or,beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn),BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState,PRes.finalPc,hspc'.trans he]

theorem RawRes.frame {sp : Spec} {keep : List Reg} {s t : MachineState}
    (h : RawRes sp keep s t) (A : Word)
    (hn : ∀ p∈sp.mem, A≠p.1.eval s) : t.getMem A=s.getMem A := by
  rw [h.mem]
  exact memEval_frame s _ _ hn

end SigGolfCandidate.T3M.CanonicalNative
