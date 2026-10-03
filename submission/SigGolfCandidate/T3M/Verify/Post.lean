import SigGolfCandidate.T3M.Verify.Mem

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
def cfg0 : Config := {}
def runAt (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 vlook (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []
def KnownOK (known : List (Reg × Word)) (s : MachineState) : Prop := ∀ p ∈ known, s.getReg p.1 = p.2
def resOK (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (r : PRes) : Bool :=
  memOKA allow rel r.st.mem && regsOK gk r.st.regs && r.st.obl.isEmpty
def knownB (known : List (Reg × Word)) (r : PRes) : Bool :=
  known.all fun p => E.beq (r.st.regs.get p.1) (.c p.2)
def keepB (rs : List Reg) (r : PRes) : Bool := rs.all fun x => E.beq (r.st.regs.get x) (.reg x)
theorem PRes.toState_getReg (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc (r : PRes) (s : MachineState) (h : r.spc = none := by rfl) :
    (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
theorem knownB_ok {known : List (Reg × Word)} {r : PRes} (h : knownB known r = true)
    (s : MachineState) : KnownOK known (r.toState s) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rw [PRes.toState_getReg, E.beq_eq this]; rfl
theorem keepB_ok {rs : List Reg} {r : PRes} (h : keepB rs r = true) (s : MachineState) :
    ∀ x ∈ rs, (r.toState s).getReg x = s.getReg x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [PRes.toState_getReg, E.beq_eq this]; rfl
theorem run_post {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {r : PRes} {allow : List Nat} {rel : List Reg} {gk : List (Reg × Word)}
    (hrun : runAt known stops n dirs = some r) (hok : resOK allow rel gk r = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) ∧
      (∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk (r.toState s)) := by
  simp only [resOK, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨hm, hr⟩, ho⟩ := hok
  obtain ⟨h1, h2⟩ := pathRun_sound hrun vlook_ok s hpc hk (by rw [ho]; simp) hbr
  exact ⟨h1, h2, fun gk0 w pk hG hrel => Glob_toState_allow hG r.st _ hm hrel hr⟩
theorem br_ne_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, x, .c 0, d⟩ ↔ (decide (x.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]
theorem br_eq_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.eq, x, .c 0, d⟩ ↔ (decide (x.eval s = 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp
def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)
theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega
theorem hashArgs_of (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha8 : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd8 : d % 8 = 0)
    (hd : d + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true :=
  hashArgs_ofNat t a n d h10 h11 h12 (by omega) (by omega) (by omega) (by
    unfold hashArgsB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨decide_eq_true ha8, decide_eq_true hn⟩, decide_eq_true ?_⟩, decide_eq_true ⟨?_, hd8⟩⟩,
      decide_eq_true ?_⟩ <;> unfold MEMORY_BYTES <;> omega)
theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; exact ofNat_ne hA hk h
    rw [if_neg hne, if_neg h]
theorem memEval_cons_ne (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A ≠ k) : memEval s ((⟨none, k⟩, v) :: ws) A = memEval s ws A := by
  rw [memEval_cons, if_neg (by simpa [Addr.eval] using h)]
theorem memEval_cons_eq (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A = k) : memEval s ((⟨none, k⟩, v) :: ws) A = v.eval s := by
  rw [memEval_cons, if_pos (by simpa [Addr.eval] using h)]
end SigGolfCandidate.T3M.Verify
