import SigGolfCandidate.T3M.Verify.Post

/-!
# Checked path runs (T3M)

`specB allow rel gk (runAt known stops n dirs) sp obl post keep = true` (checked by `decide +kernel`) says: the path
run from instruction `n` has exactly the register values `sp.regs` (symbolic over the initial state), the memory
writes `sp.mem`, the final pc (`sp.pc`, or the symbolic target `sp.spc`), stops at an `ECALL` iff `sp.ecall`, takes
`sp.steps` steps and `sp.cycles` cycles, assumes exactly the branch outcomes `sp.brs` and emits exactly the side
conditions `obl` (accesses at symbolic addresses); its writes pass `memOKA allow rel` (constant safe/allowed
addresses, `rel`-relative pointer writes), it sets the constant registers `gk`, the registers of `post` to the given
constants and keeps the registers of `keep`.

`spec_run` turns a checked run into a `SpecRes` on every concrete state satisfying the known registers, the branch
outcomes and the side conditions. Witness frames: `SpecRes.orig` (general), `SpecRes.orig_const` (no relative
writes), `SpecRes.witAll` (no witness writes).
-/

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

structure Spec where
  regs : List (Reg × E)
  mem : List (Addr × E)
  pc : Nat
  ecall : Bool
  steps : Nat
  brs : List Br
  spc : Option E := none
  /-- RV64M instructions can cost more than one cycle per step. -/
  cycles : Nat := steps

def regsB (r : PRes) (l : List (Reg × E)) : Bool := l.all fun p => E.beq (r.st.regs.get p.1) p.2

def specB (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (o : Option PRes) (sp : Spec)
    (obl : List Oblig) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem &&
      (sp.spc.isSome || r.pc.toNat == (pcOf sp.pc).toNat) &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.cycles &&
      listBeq Br.beq r.brs sp.brs && optEBeq r.spc sp.spc && listBeq Oblig.beq r.st.obl obl &&
      memOKA allow rel r.st.mem && regsOK gk r.st.regs && knownB post r && keepB keep r

/-- What a checked run gives on a concrete state. -/
structure SpecRes (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (sp : Spec)
    (post : List (Reg × Word)) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.cycles t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  glob : ∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKA allow rel sp.mem = true
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem spec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (runAt known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
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
  obtain ⟨hst', hec'⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl']; exact hob)
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

section specres
variable {allow : List Nat} {rel : List Reg} {gk post : List (Reg × Word)} {sp : Spec} {keep : List Reg}
  {s t : MachineState}

/-- The witness words a checked run does not write stay original. -/
theorem SpecRes.orig (hr : SpecRes allow rel gk sp post keep s t) {w : WBytes} {P P' : Nat → Prop}
    (hO : Orig w P s)
    (hfr : ∀ o, o < WX → P' o → P o ∧ ∀ p ∈ sp.mem, BitVec.ofNat 64 (WIT + o) ≠ p.1.eval s) :
    Orig w P' t := by
  intro j h1 h2
  obtain ⟨hp, hne⟩ := hfr (8 * j) h1 h2
  rw [hr.mem, memEval_frame s _ _ hne]
  exact hO j h1 hp

/-- Without relative writes, the witness words outside `allow` stay original. -/
theorem SpecRes.orig_const (hr : SpecRes allow [] gk sp post keep s t) {w : WBytes} {P : Nat → Prop}
    (hO : Orig w P s) : Orig w (fun o => P o ∧ WIT + o ∉ allow) t := by
  have h := Orig_toState_const (σ := ⟨RegFile.init, sp.mem, []⟩) (pc := 0) hO hr.memc
  intro j h1 h2
  have := h j h1 h2
  rw [hr.mem]
  exact this

/-- Without witness writes, the whole witness (and the zero memory after it) stays original. -/
theorem SpecRes.witAll (hr : SpecRes [] [] gk sp post keep s t) {w : WBytes} (hW : WitAll w s) :
    WitAll w t := by
  intro j hj
  have := hr.orig_const (hW.orig (fun _ => True)) j hj ⟨trivial, by simp⟩
  exact this

theorem SpecRes.reg (hr : SpecRes allow rel gk sp post keep s t) {x : Reg} {v : Word} (h : (x, v) ∈ post) :
    t.getReg x = v := hr.known _ h

end specres

end SigGolfCandidate.T3M.Verify
