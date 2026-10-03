import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base
import SigGolfCandidate.T3M.Verify.Post

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def cMem : List (Nat × Option Nat) → SymMem
  | [] => []
  | (d, some a) :: L => (⟨none, BitVec.ofNat 64 d⟩, .ld (.c (BitVec.ofNat 64 a))) :: cMem L
  | (d, none) :: L => (⟨none, BitVec.ofNat 64 d⟩, .c 0) :: cMem L
def lookW : List (Nat × Option Nat) → Nat → Option (Option Nat)
  | [], _ => none
  | (d, a) :: L, A => if d = A then some a else lookW L A
def effMem (s : MachineState) (L : List (Nat × Option Nat)) (A : Nat) : Word :=
  match lookW L A with
  | none => s.getMem (BitVec.ofNat 64 A)
  | some none => 0
  | some (some a) => s.getMem (BitVec.ofNat 64 a)
theorem lookW_cons (d : Nat) (a : Option Nat) (L : List (Nat × Option Nat)) (A : Nat) :
    lookW ((d, a) :: L) A = if d = A then some a else lookW L A := rfl
theorem memEval_cMem (s : MachineState) :
    ∀ (L : List (Nat × Option Nat)), (L.all fun p => decide (p.1 < 2 ^ 64)) = true →
      ∀ A, A < 2 ^ 64 → memEval s (cMem L) (BitVec.ofNat 64 A) = effMem s L A
  | [], _, A, _ => rfl
  | (d, a) :: L, hL, A, hA => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hL
    have ih := memEval_cMem s L hL.2 A hA
    rcases a with _ | a
    · simp only [cMem]
      rw [memEval_cons_ofNat s d A _ _ hA hL.1, ih]
      by_cases h : A = d
      · subst h; simp [effMem, lookW_cons, E.eval]
      · rw [if_neg h]; unfold effMem; rw [lookW_cons, if_neg (Ne.symm h)]
    · simp only [cMem]
      rw [memEval_cons_ofNat s d A _ _ hA hL.1, ih]
      by_cases h : A = d
      · subst h; simp [effMem, lookW_cons, E.eval]
      · rw [if_neg h]; unfold effMem; rw [lookW_cons, if_neg (Ne.symm h)]
theorem effMem_none {s : MachineState} {L : List (Nat × Option Nat)} {A : Nat} (h : lookW L A = none) :
    effMem s L A = s.getMem (BitVec.ofNat 64 A) := by
  unfold effMem; rw [h]
theorem effMem_some {s : MachineState} {L : List (Nat × Option Nat)} {A a : Nat} (h : lookW L A = some (some a)) :
    effMem s L A = s.getMem (BitVec.ofNat 64 a) := by
  unfold effMem; rw [h]
theorem effMem_zero {s : MachineState} {L : List (Nat × Option Nat)} {A : Nat} (h : lookW L A = some none) :
    effMem s L A = 0 := by
  unfold effMem; rw [h]
theorem lookW_none_of {L : List (Nat × Option Nat)} {A : Nat} (h : ∀ p ∈ L, p.1 ≠ A) : lookW L A = none := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨d, a⟩ := p
    simp only [lookW]
    rw [if_neg (h _ (List.mem_cons_self ..)), ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
def pcfg : Config := {}
def allRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
    .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]
theorem mem_allRegs (x : Reg) (h : x ≠ .x0) : x ∈ allRegs := by
  cases x <;> simp_all [allRegs]
def runB (r : PRes) (stop : Nat) (L : List (Nat × Option Nat)) (chg : List Reg) : Bool :=
  listBeq pairBeq r.st.mem (cMem L) && r.st.obl.isEmpty && !r.ecall && r.spc.isNone &&
    r.pc.toNat == (pcOf stop).toNat && keepB (allRegs.filter fun x => !chg.contains x) r &&
    (L.all fun p => decide (p.1 < 2 ^ 64))
def regIsB (r : PRes) (x : Reg) (v : Word) : Bool := E.beq (r.st.regs.get x) (.c v)
theorem regIsB_ok {r : PRes} {x : Reg} {v : Word} (h : regIsB r x v = true) (s : MachineState) :
    (r.toState s).getReg x = v := by
  rw [PRes.toState_getReg, E.beq_eq h]; rfl
theorem getReg_x0_eq (s t : MachineState) : t.getReg .x0 = s.getReg .x0 := by
  simp [MachineState.getReg]
theorem runB_spec {im : Image} (hc : NewCodeAt im) {stops : List Word} {fuel P : Nat} {dirs : List Dir}
    {known : List (Reg × Word)} {r : PRes} {stop : Nat} {L : List (Nat × Option Nat)} {chg : List Reg}
    (h : pathAux pcfg expLook stops fuel (pcOf P) dirs (σK known) [] = some r) (hb : runB r stop L chg = true)
    (s : MachineState) (hpc : s.pc = pcOf P) (hk : ∀ p ∈ known, s.getReg p.1 = p.2)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧ (r.toState s).pc = pcOf stop ∧
      RegsExcept s (r.toState s) chg ∧
      (∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) = effMem s L A) := by
  simp only [runB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, Option.isNone_iff_eq_none,
    beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hm, ho⟩, -⟩, hspc⟩, hpcr⟩, hkeep⟩, hL⟩ := hb
  obtain ⟨h1, -⟩ := pathRun_sound h (expLook_ok hc) s hpc hk (by rw [ho]; simp) hbr
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [PRes.toState_pc r s hspc]; exact BitVec.eq_of_toNat_eq hpcr
  · intro x hx
    by_cases h0 : x = .x0
    · subst h0; exact getReg_x0_eq _ _
    · exact keepB_ok hkeep s x (List.mem_filter.mpr ⟨mem_allRegs x h0, by simpa using hx⟩)
  · intro A hA
    rw [PRes.toState_getMem, listBeq_eq (fun _ _ => pairBeq_eq) hm]
    exact memEval_cMem s L hL A hA
theorem check_some {o : Option PRes} {f : PRes → Bool}
    (h : (match o with | some r => f r | none => false) = true) : ∃ r, o = some r ∧ f r = true := by
  cases o with
  | none => simp at h
  | some r => exact ⟨r, rfl, h⟩
def fW (c : Nat) : Nat := WCT9.coordBase c / 64
def fSh (c : Nat) : Nat := WCT9.coordBase c % 64
def fLen (c : Nat) : Nat := if fSh c = 0 then 8 else 9
def cOff : Nat → Nat
  | 0 => 0
  | c + 1 => cOff c + fLen c + 182
def lOff (c l : Nat) : Nat := cOff c + fLen c + 98 + 12 * l
def sigBlk (c : Nat) : Nat := 0x7010 + 224 * c
def fcWrites (c : Nat) : List (Nat × Option Nat) :=
  (List.range 7).flatMap fun t =>
    [(regBase c + 880 - 64 * t, some (sigBlk c + 16 * t)), (regBase c + 880 - 64 * t + 8, some (sigBlk c + 16 * t + 8)),
      (regBase c + (if t = 0 then 880 else 896 + 16 * t), some (sigBlk c + 16 * t)),
      (regBase c + (if t = 0 then 880 else 896 + 16 * t) + 8, some (sigBlk c + 16 * t + 8))]
def pushW (L : List (Nat × Option Nat)) (p : Nat × Option Nat) : List (Nat × Option Nat) :=
  p :: L.filter fun q => q.1 != p.1
def fcList (c : Nat) : List (Nat × Option Nat) := (fcWrites c).foldl pushW []
def sibOff (l : Nat) (d : Bool) : Nat := 64 * (6 - l) + (if d then 0 else 48)
def levList (c l : Nat) (d : Bool) : List (Nat × Option Nat) :=
  [(regBase c + sibOff l d + 8, some (sigBlk c + 112 + 16 * l + 8)), (regBase c + sibOff l d, some (sigBlk c + 112 + 16 * l))]
def childE (c : Nat) : E :=
  if fSh c = 0 then .bin .and (.ld (.c (BitVec.ofNat 64 (0x20160 + 8 * fW c)))) (.c 127)
  else .bin .and (.bin .srl (.ld (.c (BitVec.ofNat 64 (0x20160 + 8 * fW c)))) (.c (BitVec.ofNat 64 (fSh c)))) (.c 127)
def bitE (l : Nat) : E := .bin .and (.bin .srl (.reg .x24) (.c (BitVec.ofNat 64 l))) (.c 1)
def fcCheck (P c : Nat) : Bool :=
  match pathAux pcfg expLook [pcOf (P + lOff c 0)] 300 (pcOf (P + cOff c)) [] (σK []) [] with
  | some r => runB r (P + lOff c 0) (fcList c) [.x6, .x7, .x24, .x25, .x28, .x29] &&
      E.beq (r.st.regs.get .x24) (childE c) && r.brs.isEmpty && decide (r.cycles ≤ 120)
  | none => false
def levCheck (P c l : Nat) (d : Bool) : Bool :=
  match pathAux pcfg expLook [pcOf (P + lOff c l + 12)] 30 (pcOf (P + lOff c l)) [.br d] (σK []) [] with
  | some r => runB r (P + lOff c l + 12) (levList c l d) [.x6, .x7, .x28, .x29] &&
      listBeq Br.beq r.brs [⟨.ne, bitE l, .c 0, d⟩] && decide (r.cycles ≤ 12)
  | none => false
def placeOK (P : Nat) : Bool :=
  (List.range 9).all fun c => fcCheck P c && (List.range 7).all fun l => levCheck P c l true && levCheck P c l false
def wSrc (j i : Nat) : Option Nat :=
  if i / 2 < 28 then
    if (j / 2 ^ (6 - i / 8) % 2 = 1 ∧ i / 2 % 4 = 0) ∨ (j / 2 ^ (6 - i / 8) % 2 = 0 ∧ i / 2 % 4 = 3) then
      some (112 + 16 * (6 - i / 8) + 8 * (i % 2))
    else none
  else if i / 2 < 52 then
    if (i / 2 - 28) % 4 = 3 then some (16 * (6 - (i / 2 - 28) / 4) + 8 * (i % 2)) else none
  else if i / 2 = 55 then some (8 * (i % 2))
  else if 57 ≤ i / 2 ∧ i / 2 < 63 then some (16 * (i / 2 - 56) + 8 * (i % 2))
  else none
def plSt (j L i : Nat) : Option Nat := if 56 ≤ i ∨ 6 - i / 8 < L then wSrc j i else none
end ClaudeWCT.W9.Machine.Expand
