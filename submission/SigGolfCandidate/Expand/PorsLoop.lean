import SigGolfCandidate.Expand.PorsBlk2

/-!
# `expand`, phase 2: the PORS stack machine (instructions 529 .. 638)

* `segLoop_sim` : the segments of one leaf (`Ref.segLoop`, by recursion on the stack);
* `porsLeaves_sim` : the leaf loop (`Ref.porsLeaves` over `range' s n`);
* `porsEnd_sim` : the final checks of `Ref.porsRoot` (folds, `E = 1`, empty stack).

The stack lives at `STK = X + 1344` (`StkOK`); the segment pointer stays below
`4992 + 960 (2 s - k)` (`s` leaves done, `k` entries on the stack: one segment per leaf start and
one per merge, each at most 960 bytes), so every read stays inside the witness buffer.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-! ## The stack -/

/-- The stack (head = top): entry `j` from the top sits at `STK + 32 (k - 1 - j)` (`k` = the
length): its node (two dwords), then its heap index. -/
def StkOK (t : MachineState) (stk : List (Val × Nat)) : Prop :=
  ∀ j (h : j < stk.length),
    t.readWords (BitVec.ofNat 64 (0x30540 + 32 * (stk.length - 1 - j))) 2 = wordsOf stk[j].1 ∧
    t.getMem (BitVec.ofNat 64 (0x30540 + 32 * (stk.length - 1 - j) + 16)) = BitVec.ofNat 64 stk[j].2 ∧
    stk[j].1.length = 16 ∧ stk[j].2 < 2 ^ 15

/-- Stack addresses. -/
def stkA (a : Nat) : Prop := 0x30540 ≤ a ∧ a < 0x30540 + 32 * 15

theorem StkOK.frame {s t : MachineState} {stk : List (Val × Nat)} {W : Nat → Prop} (h : StkOK s stk)
    (hf : Frame s t W) (hW : ∀ a, stkA a → ¬ W a) (hk : stk.length ≤ 15) : StkOK t stk := by
  intro j hj
  obtain ⟨h1, h2, h3, h4⟩ := h j hj
  refine ⟨?_, ?_, h3, h4⟩
  · rw [hf.readWords _ _ (by omega) (fun i hi => hW _ (by unfold stkA; omega)), h1]
  · rw [hf.getMem (by omega) (hW _ (by unfold stkA; omega)), h2]

theorem StkOK.tail {t : MachineState} {p : Val × Nat} {stk : List (Val × Nat)} (h : StkOK t (p :: stk)) :
    StkOK t stk := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  simp only [List.length_cons, List.getElem_cons_succ] at this
  rwa [show stk.length + 1 - 1 - (j + 1) = stk.length - 1 - j by omega] at this

theorem StkOK.head {t : MachineState} {p : Val × Nat} {stk : List (Val × Nat)} (h : StkOK t (p :: stk)) :
    t.readWords (BitVec.ofNat 64 (0x30540 + 32 * stk.length)) 2 = wordsOf p.1 ∧
    t.getMem (BitVec.ofNat 64 (0x30540 + 32 * stk.length + 16)) = BitVec.ofNat 64 p.2 ∧
    p.1.length = 16 ∧ p.2 < 2 ^ 15 := by
  have := h 0 (by simp)
  simpa using this

theorem StkOK.push {s t : MachineState} {stk : List (Val × Nat)} (h : StkOK s stk) (hk : stk.length < 15)
    (hf : Frame s t (fun x => 0x30540 + 32 * stk.length ≤ x ∧ x < 0x30540 + 32 * stk.length + 24))
    (node : Val) (Q : Nat) (hn : node.length = 16) (hQ : Q < 2 ^ 15)
    (h1 : t.readWords (BitVec.ofNat 64 (0x30540 + 32 * stk.length)) 2 = wordsOf node)
    (h2 : t.getMem (BitVec.ofNat 64 (0x30540 + 32 * stk.length + 16)) = BitVec.ofNat 64 Q) :
    StkOK t ((node, Q) :: stk) := by
  intro j hj
  cases j with
  | zero => simpa using ⟨h1, h2, hn, hQ⟩
  | succ j =>
    simp only [List.length_cons, List.getElem_cons_succ]
    simp only [List.length_cons] at hj
    obtain ⟨g1, g2, g3, g4⟩ := h j (by omega)
    rw [show stk.length + 1 - 1 - (j + 1) = stk.length - 1 - j by omega]
    refine ⟨?_, ?_, g3, g4⟩
    · rw [hf.readWords _ _ (by omega) (fun i hi => by omega), g1]
    · rw [hf.getMem (by omega) (by omega), g2]

/-! ## The segments of one leaf -/

/-- Registers the segment loop writes. -/
def loopRegs : List Reg :=
  [.x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20, .x21, .x24, .x28, .x29]

/-- The outcome of a leaf's segments at `pr_leafend` (620); `u` is the state at `pr_seg` with
`k` stack entries, the header at `ptr` and `folds` folds. -/
def LoopOut (w : List Byte) (idx : Nat) (K : Nat → Nat) (u : MachineState) (ptr folds k : Nat) :
    Nat × Nat × Nat × Val × List (Val × Nat) → MachineState → Prop
  | (ptr', E', folds', node', stk'), t => t.pc = pcOf 620 ∧ PCtx w idx K t ∧
      t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr') ∧ t.getReg .x19 = BitVec.ofNat 64 E' ∧
      t.getReg .x20 = BitVec.ofNat 64 folds' ∧ t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * stk'.length) ∧
      StkOK t stk' ∧ stk'.length ≤ k ∧ ptr' % 8 = 0 ∧ ptr' ≤ ptr + 960 * (k - stk'.length + 1) ∧
      folds' ≤ folds + 14 * (k - stk'.length + 1) ∧ E' < 2 ^ 15 ∧ node'.length = 16 ∧
      t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf node' ∧
      RegsEq u t loopRegs ∧ Frame u t segW

theorem stkA_segW : ∀ a, stkA a → ¬ segW a := by
  intro a h1 h2; unfold stkA at h1; unfold segW at h2; omega

set_option maxRecDepth 20000 in
/-- **The segments of one leaf** (`Ref.segLoop`). -/
theorem segLoop_sim (w : List Byte) (idx : Nat) (K : Nat → Nat) :
    ∀ (stk : List (Val × Nat)) (ptr E folds : Nat) (pending : Pending) (node : Val) (t : MachineState),
    PCtx w idx K t → t.pc = pcOf 550 → t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr) →
    t.getReg .x19 = BitVec.ofNat 64 E → t.getReg .x20 = BitVec.ofNat 64 folds →
    t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * stk.length) → StkOK t stk → stk.length ≤ 15 →
    ptr % 8 = 0 → ptr + 960 * (stk.length + 1) ≤ 0x10000 → folds + 14 * (stk.length + 1) < 2 ^ 30 → E < 2 ^ 15 →
    PendOK idx node pending t →
    Sim eimg t (1100 * (stk.length + 1)) (segLoop idx w ptr E folds pending node stk)
      (OPost (LoopOut w idx K t ptr folds stk.length)) := by
  intro stk
  induction stk with
  | nil =>
    intro ptr E folds pending node t hc hpc h9 h19 h20 h21 hstk hk hptr hptr' hf hE hpend
    simp only [segLoop]
    refine (Sim.bind (segment_sim w idx K ptr E folds pending node t hc hpc h9 h19 hptr (by simp at hptr'; omega)
      hE hpend) (W₂ := 100) (fun r t1 h1 => ?_)).mono (by simp) (fun _ _ h => h)
    rcases r with _ | ⟨ptr', E', folds', node', merge⟩
    · dsimp only
      exact (Sim.pure (a := none) (Q := OPost (LoopOut w idx K t ptr folds _)) h1).mono (by omega)
        (fun _ _ h => h)
    obtain ⟨p1, c1, hp', hf', ha, hm, y6, y7, y19, hE', hl', hout, r1, f1⟩ := h1
    subst hp' hf' hm
    dsimp only
    have hb : wbyte w ptr < 256 := (w.getD ptr 0).isLt
    obtain ⟨t2, hs2, p2, z9, z20, r2, m2⟩ := blk595_run t1 p1 (wbyte w ptr) ptr folds hb (by simp at hptr'; omega)
      (by omega) y6 y7 (by rw [r1.get .x9, h9]) (by rw [r1.get .x20, h20])
    have c2 : PCtx w idx K t2 := c1.frame (W := fun _ => False) (fun x _ _ => m2 _) r2 (fun _ _ h => h)
    by_cases hmg : wbyte w ptr / 16 % 2 = 1
    · rw [if_pos (by simpa using hmg)]
      rw [if_pos hmg] at p2
      obtain ⟨t3, hs3, p3, r3, m3⟩ := blk602_run t2 p2 0 (by norm_num)
        (by rw [r2.get .x21, r1.get .x21, h21]; rfl) c2.x22
      rw [if_pos rfl] at p3
      exact (Sim.steps hs2 (fail_sim_steps hs3 p3)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg (by simpa using hmg)]
      rw [if_neg hmg] at p2
      refine (Sim.pure_steps hs2 ⟨p2, c2, z9, by rw [r2.get .x19, y19], z20,
        by rw [r2.get .x21, r1.get .x21, h21], fun j hj => by simp at hj, le_refl _, by omega,
        by simp; omega, by simp; omega, hE', hl', ?_, ?_, ?_⟩).mono (by omega) (fun _ _ h => h)
      · rw [readWords_ofNat_two, m2, m2, ← readWords_ofNat_two, hout]
      · exact (r1.trans r2).mono (by decide)
      · exact (f1.trans (fun x _ _ => m2 _ : Frame t1 t2 (fun _ => False))).mono (by
          intro x hx; simp only [or_false] at hx; exact hx)
  | cons p rest ih =>
    obtain ⟨pnode, Q⟩ := p
    intro ptr E folds pending node t hc hpc h9 h19 h20 h21 hstk hk hptr hptr' hf hE hpend
    simp only [List.length_cons] at h21 hk hptr' hf ⊢
    simp only [segLoop]
    refine (Sim.bind (segment_sim w idx K ptr E folds pending node t hc hpc h9 h19 hptr (by omega)
      hE hpend) (W₂ := 1100 * (rest.length + 1) + 100) (fun r t1 h1 => ?_)).mono (by ring_nf; omega)
      (fun _ _ h => h)
    rcases r with _ | ⟨ptr', E', folds', node', merge⟩
    · dsimp only
      exact (Sim.pure (a := none) (Q := OPost (LoopOut w idx K t ptr folds _)) h1).mono (by omega)
        (fun _ _ h => h)
    obtain ⟨p1, c1, hp', hf', ha, hm, y6, y7, y19, hE', hl', hout, r1, f1⟩ := h1
    subst hp' hf' hm
    dsimp only
    have hb : wbyte w ptr < 256 := (w.getD ptr 0).isLt
    obtain ⟨t2, hs2, p2, z9, z20, r2, m2⟩ := blk595_run t1 p1 (wbyte w ptr) ptr folds hb (by omega)
      (by omega) y6 y7 (by rw [r1.get .x9, h9]) (by rw [r1.get .x20, h20])
    have c2 : PCtx w idx K t2 := c1.frame (W := fun _ => False) (fun x _ _ => m2 _) r2 (fun _ _ h => h)
    have hstk1 : StkOK t1 ((pnode, Q) :: rest) := hstk.frame f1 stkA_segW (by simp; omega)
    have hstk2 : StkOK t2 ((pnode, Q) :: rest) := hstk1.frame (W := fun _ => False) (fun x _ _ => m2 _)
      (fun _ _ h => h) (by simp; omega)
    have z21 : t2.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * (rest.length + 1)) := by
      rw [r2.get .x21, r1.get .x21, h21]
    by_cases hmg : wbyte w ptr / 16 % 2 = 1
    swap
    · -- no merge: the leaf is done
      rw [if_pos (by simpa using hmg)]
      rw [if_neg hmg] at p2
      refine (Sim.pure_steps hs2 ⟨p2, c2, z9, by rw [r2.get .x19, y19], z20, by simpa using z21, hstk2,
        by simp, by omega, by simp; omega, by simp; omega, hE', hl', ?_, ?_, ?_⟩).mono (by omega) (fun _ _ h => h)
      · rw [readWords_ofNat_two, m2, m2, ← readWords_ofNat_two, hout]
      · exact (r1.trans r2).mono (by decide)
      · exact (f1.trans (fun x _ _ => m2 _ : Frame t1 t2 (fun _ => False))).mono (by
          intro x hx; simp only [or_false] at hx; exact hx)
    rw [if_neg (by simpa using hmg)]
    rw [if_pos hmg] at p2
    obtain ⟨t3, hs3, p3, r3, m3⟩ := blk602_run t2 p2 (rest.length + 1) (by omega) z21 c2.x22
    rw [if_neg (by omega)] at p3
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hstk2.head
    obtain ⟨t4, hs4, p4, x21', r4, m4⟩ := blk603_run t3 p3 rest.length E' Q (by omega) hE' hq4
      (by rw [r3.get .x21, z21]) (by rw [r3.get .x19, r2.get .x19, y19]) (by rw [m3, hq2])
    by_cases hQ : Q ≠ E'
    · rw [if_pos hQ]
      rw [if_pos hQ] at p4
      exact (Sim.steps hs2 (Sim.steps hs3 (fail_sim_steps hs4 p4))).mono (by omega) (fun _ _ h => h)
    rw [if_neg hQ]
    rw [if_neg hQ] at p4
    have hQE : Q = E' := by omega
    have c4 : PCtx w idx K t4 := (c2.frame (W := fun _ => False) (fun x _ _ => m3 _) r3 (fun _ _ h => h)).frame
      (W := fun _ => False) (fun x _ _ => m4 _) r4 (fun _ _ h => h)
    obtain ⟨t5, hs5, p5, x19', x24', m72, w60, w70, r5, f5⟩ := blk606_run idx t4 p4 rest.length E' (by omega) hE'
      (by rw [r4.get .x19, r3.get .x19, r2.get .x19, y19]) x21' c4.x25 c4.x26
    have c5 : PCtx w idx K t5 := c4.frame f5 r5 (fun a h1 h2 => by unfold pctxA witA at h1; omega)
    have g4 : ∀ x, t4.getMem x = t2.getMem x := fun x => by rw [m4, m3]
    have hstk5 : StkOK t5 rest := (hstk2.tail.frame (W := fun _ => False) (fun x _ _ => g4 _) (fun _ _ h => h)
      (by omega)).frame f5 (fun a h1 h2 => by unfold stkA at h1; omega) (by omega)
    have hih := ih (ptr + 64 + 64 * (wbyte w ptr % 16)) (E' / 2) (folds + wbyte w ptr % 16)
      (.merge (E' / 2) pnode) node' t5 c5 p5
      (by rw [r5.get .x9, r4.get .x9, r3.get .x9, z9]) x19'
      (by rw [r5.get .x20, r4.get .x20, r3.get .x20, z20]) (by rw [r5.get .x21, x21']) hstk5 (by omega)
      (by omega) (by omega) (by omega) (by omega)
      ⟨x24', by omega, hq3, hl', m72, by rw [w60, readWords_ofNat_two, g4, g4, ← readWords_ofNat_two, hq1],
        by rw [w70, readWords_ofNat_two, g4, g4, ← readWords_ofNat_two, readWords_ofNat_two, m2, m2,
          ← readWords_ofNat_two, hout]⟩
    refine (Sim.steps hs2 (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 hih)))).mono (by omega) ?_
    intro r t6 h6
    rcases r with _ | ⟨ptr'', E'', folds'', node'', stk''⟩
    · exact h6
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16⟩ := h6
    refine ⟨q1, q2, q3, q4, q5, q6, q7, by omega, q9, by omega, by omega, q12, q13, q14, ?_, ?_⟩
    · exact ((((r1.trans r2).trans r3).trans r4).trans (r5.trans q15)).mono (by decide)
    · have f24 : Frame t1 t4 (fun _ => False) := fun x _ _ => by rw [g4, m2]
      exact ((f1.trans f24).trans (f5.trans q16)).mono (by
        intro x hx; simp only [segW, or_false] at hx ⊢; omega)

end SigGolfCandidate.ExP
