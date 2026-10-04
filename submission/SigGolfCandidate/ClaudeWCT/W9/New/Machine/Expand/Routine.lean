import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChainSem
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChildESem
import SigGolfCandidate.T3M.Expand.Basic
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

section




namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64 zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
def qQ (k index j : Nat) : Nat := j * 2 ^ 20 + index * 2 ^ 27 + 65536 * k
theorem ftsChainLow_qQ (index k j t st : Nat) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 7)
    (hst : st < 3) : WCT9.ftsChainLow index k j t st = qQ k index j + qK t st := by
  unfold WCT9.ftsChainLow qQ qK
  rw [Nat.mod_eq_of_lt (show t < 8 by omega), Nat.mod_eq_of_lt (show st < 4 by omega),
    Nat.mod_eq_of_lt (show k < 16 by omega), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
  ring
theorem step_byte (Q t st st' : Nat) (hQ : Q % 65536 = 0) (hQb : Q < 2 ^ 63) (ht : t < 7) (hst : st < 3)
    (hst' : st' < 3) :
    replaceByte (BitVec.ofNat 64 (Q + qK t st)) 1 ((BitVec.ofNat 64 st').truncate 8) =
      BitVec.ofNat 64 (Q + qK t st') := by
  apply BitVec.eq_of_toNat_eq
  rw [replaceByte_toNat _ _ (by decide)]
  simp only [qK, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega
theorem chainInput_blk4 (index k j t st : Nat) (val : Digest) :
    WCT9.chainInput index k j t st val = Verify.blk4 0 (WCT9.ftsChainHeader index k j t st) 0 val := by
  rw [WCT9.chainInput_eq]
  simp only [Verify.blk4, Verify.bytesLE16_zero]
theorem chain_hashIn {u : MachineState} {A : Nat} {k index j t st : Nat} {val : Digest} (hk : k < 9)
    (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 7) (hst : st < 3)
    (h10 : u.getReg .x10 = BitVec.ofNat 64 A) (h11 : u.getReg .x11 = BitVec.ofNat 64 64)
    (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (p0 : u.getMem (BitVec.ofNat 64 A) = 0) (p0' : u.getMem (BitVec.ofNat 64 (A + 8)) = 0)
    (hh0 : u.getMem (BitVec.ofNat 64 (A + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st))
    (hh1 : u.getMem (BitVec.ofNat 64 (A + 24)) = 0)
    (p1 : u.getMem (BitVec.ofNat 64 (A + 32)) = 0) (p1' : u.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (hv : DigAt u (A + 48) val) :
    hashInput u = toQ (pad64 (WCT9.chainInput index k j t st val)) := by
  rw [chainInput_blk4]
  apply ClaudeWCT.W9.Machine.Expand.hashInput_blk4 u A _ _ _ _ h10 h11 hA hA'
  · exact ⟨p0.trans rfl, p0'.trans rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [hh0]; unfold WCT9.ftsChainHeader
      rw [WCT9.ftsChainHeaderP_low, ftsChainLow_qQ index k j t st hk hidx hj ht hst]
    · rw [show A + 16 + 8 = A + 24 by omega, hh1]; unfold WCT9.ftsChainHeader
      rw [WCT9.ftsChainHeaderP_high]
  · exact ⟨p1.trans rfl, by rw [show A + 32 + 8 = A + 40 by omega]; exact p1'.trans rfl⟩
  · exact hv
theorem codeAt_left {im : Image} {p : Nat} {l1 l2 : List (BitVec 32)} (h : CodeAt im (pcOf p) (l1 ++ l2)) :
    CodeAt im (pcOf p) l1 := by
  have := CodeAt.drop_prefix (pre := []) (seg := l1) (post := l2) (by simpa using h)
  simpa using this
theorem codeAt_right {im : Image} {p : Nat} {l1 l2 : List (BitVec 32)} (h : CodeAt im (pcOf p) (l1 ++ l2)) :
    CodeAt im (pcOf (p + l1.length)) l2 := by
  have := CodeAt.drop_prefix (pre := l1) (seg := l2) (post := []) (by simpa using h)
  rwa [pcOf, ofNat_add_ofNat, show 0x1000 + 4 * p + 4 * l1.length = 0x1000 + 4 * (p + l1.length) by ring] at this
structure CRegs (B H X4 Q : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 B
  x28 : s.getReg .x28 = BitVec.ofNat 64 H
  x4 : s.getReg .x4 = BitVec.ofNat 64 X4
  x31 : s.getReg .x31 = BitVec.ofNat 64 Q
  x7 : s.getReg .x7 = BitVec.ofNat 64 1
  x13 : s.getReg .x13 = BitVec.ofNat 64 2
  x5 : s.getReg .x5 = 0
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
def keepC (s u : MachineState) : Prop :=
  ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → u.getReg r = s.getReg r
theorem keepC.refl (s : MachineState) : keepC s s := fun _ _ _ _ _ _ => rfl
theorem keepC.trans {s u w : MachineState} (h1 : keepC s u) (h2 : keepC u w) : keepC s w :=
  fun r a b c d e => (h2 r a b c d e).trans (h1 r a b c d e)
theorem CRegs.of_keep {B H X4 Q : Nat} {s u : MachineState} (h : CRegs B H X4 Q s) (hk : keepC s u) :
    CRegs B H X4 Q u :=
  ⟨(hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x8,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x28,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x4,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x31,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x7,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x13,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x5,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x11⟩
def chainWr (B t : Nat) (own : Bool) (A : Nat) : Prop :=
  A = B + offC t + 16 ∨ (B + offC t + 48 ≤ A ∧ A < B + offC t + 80) ∨
    (B + slotC t ≤ A ∧ A < B + slotC t + (if own then 16 else 32))
structure CMid (B H k index j t : Nat) (own : Bool) (s u : MachineState) (st : Nat) (val : Digest) (D : Nat) :
    Prop where
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u
  x10 : u.getReg .x10 = BitVec.ofNat 64 (B + offC t)
  x12 : u.getReg .x12 = BitVec.ofNat 64 D
  keep : keepC s u
  hdr : u.getMem (BitVec.ofNat 64 (B + offC t + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st)
  x4m : u.getMem (BitVec.ofNat 64 (B + offC t + 24)) = 0
  p0 : u.getMem (BitVec.ofNat 64 (B + offC t)) = 0
  p0' : u.getMem (BitVec.ofNat 64 (B + offC t + 8)) = 0
  p1 : u.getMem (BitVec.ofNat 64 (B + offC t + 32)) = 0
  p1' : u.getMem (BitVec.ofNat 64 (B + offC t + 40)) = 0
  val : DigAt u D val
  frame : Frame s u (chainWr B t own)
theorem offC_bounds (t : Nat) (ht : t < 7) : offC t % 64 = 0 ∧ 448 ≤ offC t ∧ offC t + 48 ≤ 880 := by
  unfold offC; omega
theorem slotC_bounds (t : Nat) (ht : t < 7) : slotC t % 16 = 0 ∧ 880 ≤ slotC t ∧ slotC t + 32 ≤ 1024 := by
  unfold slotC; split <;> omega
theorem tb_chainHash {β : Type} {im : Image} {sk : BitVec 256} {u : MachineState} {A D : Nat}
    {k index j t st : Nat} {val : Digest} {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 7) (hst : st < 3)
    (hf : fetch im u = some (.base .ECALL)) (h5 : u.getReg .x5 = 0) (h10 : u.getReg .x10 = BitVec.ofNat 64 A)
    (h11 : u.getReg .x11 = BitVec.ofNat 64 64) (h12 : u.getReg .x12 = BitVec.ofNat 64 D)
    (hA8 : A % 8 = 0) (hAhi : A + 64 ≤ 2 ^ 24) (hD8 : D % 8 = 0) (hDhi : D + 32 ≤ 2 ^ 24)
    (p0 : u.getMem (BitVec.ofNat 64 A) = 0) (p0' : u.getMem (BitVec.ofNat 64 (A + 8)) = 0)
    (hh0 : u.getMem (BitVec.ofNat 64 (A + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st))
    (hh1 : u.getMem (BitVec.ofNat 64 (A + 24)) = 0)
    (p1 : u.getMem (BitVec.ofNat 64 (A + 32)) = 0) (p1' : u.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (hv : DigAt u (A + 48) val)
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash u a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim im sk u (8 + W) (shortHash (WCT9.chainInput index k j t st val) >>= f) Q := by
  have hq := chain_hashIn hk hidx hj ht hst h10 h11 hA8 (by omega) p0 p0' hh0 hh1 p1 p1' hv
  have hv' : hashArgumentsValid u = true :=
    Verify.hashArgs_of u A 64 D h10 h11 h12 hA8 (by decide) (by omega) hD8 hDhi
  have := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk) (W := W) (f := f) (Q := Q)
    hf h5 hv' hq h
  have hb : (toQ (pad64 (WCT9.chainInput index k j t st val))).blocks = 1 := by
    rw [chainInput_blk4, Verify.blocks_blk4]
  exact this.mono (by rw [hb]) (fun _ _ h => h)
def PadsZ (B t : Nat) (u : MachineState) : Prop :=
  u.getMem (BitVec.ofNat 64 (B + offC t)) = 0 ∧ u.getMem (BitVec.ofNat 64 (B + offC t + 8)) = 0 ∧
    u.getMem (BitVec.ofNat 64 (B + offC t + 32)) = 0 ∧ u.getMem (BitVec.ofNat 64 (B + offC t + 40)) = 0 ∧
    u.getMem (BitVec.ofNat 64 (B + offC t + 24)) = 0
theorem writeHash_get_out {t : MachineState} {a : BitVec 256} {D A : Nat} (h12 : t.getReg .x12 = BitVec.ofNat 64 D)
    (hD : D + 32 < 2 ^ 64) (hA : A < 2 ^ 64) (hn : A + 8 ≤ D ∨ D + 32 ≤ A) :
    (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [getMem_writeHash t a D A h12 hD hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem head_hash {β : Type} {im : Image} {sk : BitVec 256} {p t st a2 : Nat} {own : Bool} (ht : t < 7)
    (hst : st < 3) (ha : a2 = offC t + 48 ∨ (a2 = slotC t ∧ (own = false ∨ t = 0)))
    (hc : CodeAt im (pcOf p) (headW t st a2))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    (s : MachineState) (hpc : s.pc = pcOf p) (hr : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s)
    (hpad : PadsZ B t s) (v : Digest) (hv : DigAt s (B + offC t + 48) v)
    {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hK : ∀ (v' : Digest) (w : MachineState), w.pc = pcOf (p + 5) →
      CMid B H k index j t own s w st v' (B + a2) → TBSim im sk w W (f v') Q) :
    TBSim im sk s (4 + (8 + W)) (shortHash (WCT9.chainInput index k j t st v) >>= f) Q := by
  have hob := offC_bounds t ht
  have hsb := slotC_bounds t ht
  have hbb := hb.bhi
  have hb8 := hb.b8
  have ha' : a2 = offC t + 48 ∨ a2 = slotC t := by rcases ha with h | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]
  have ha2 : a2 % 8 = 0 ∧ offC t + 48 ≤ a2 ∧ a2 + 32 ≤ 1024 := by
    rcases ha' with rfl | rfl <;> omega
  obtain ⟨u1, s1, p1, e1, x10_1, x12_1, keep1, m16, f1⟩ :=
    head_spec ht hst ha' hc s hpc hr.x8 hr.x31 hb.b8 hb.bhi
  have k1 : keepC s u1 := fun r h3 h10 h12 h14 h25 => keep1 r h10 h12 h25
  have r1 := hr.of_keep k1
  have fs1 : ∀ o, o + 8 ≤ 1024 → o ≠ offC t + 16 →
      u1.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) :=
    fun o ho h1 => f1 (B + o) (by omega) (by omega)
  refine TBSim.steps s1 (tb_chainHash (A := B + offC t) (D := B + a2) hk hidx hj ht hst e1 r1.x5 x10_1 r1.x11 x12_1
    (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun a => ?_))
  · rw [fs1 _ (by omega) (by omega)]; exact hpad.1
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.1
  · rw [m16]
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.2
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.1
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.1
  · rw [Nat.add_assoc]
    exact ⟨(fs1 _ (by omega) (by omega)).trans hv.1,
      by rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; have := hv.2; rwa [Nat.add_assoc] at this⟩
  · set w := writeHash u1 a
    have hw : ∀ o, o + 8 ≤ 1024 → (o + 8 ≤ a2 ∨ a2 + 32 ≤ o) →
        w.getMem (BitVec.ofNat 64 (B + o)) = u1.getMem (BitVec.ofNat 64 (B + o)) :=
      fun o ho hn => writeHash_get_out x12_1 (by omega) (by omega) (by omega)
    refine hK _ w ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p1, pcOf_add4]
    · exact r1.of_keep (fun r _ _ _ _ _ => getReg_writeHash u1 a r)
    · rw [getReg_writeHash]; exact x10_1
    · rw [getReg_writeHash]; exact x12_1
    · exact k1.trans (fun r _ _ _ _ _ => getReg_writeHash u1 a r)
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), ← Nat.add_assoc, m16]
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.2
    · rw [hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.1
    · exact DigAt.writeHash_lo u1 a _ x12_1 (by omega)
    · have fw := Frame.writeHash u1 a (B + a2) x12_1 (by omega)
      refine (f1.trans fw).mono (fun A _ hA => ?_)
      rcases hA with h | h
      · exact Or.inl h
      · rcases ha with rfl | ⟨rfl, ho⟩
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · rcases ho with ho | rfl
          · right; right; rw [ho]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · right; left; simp only [offC, slotC] at h ⊢; norm_num at h ⊢; omega
def rdst (t step : Nat) (own : Bool) : Nat :=
  match rungDst t step own with
  | some d => d
  | none => offC t + 48
theorem rdst_cases (t step : Nat) (own : Bool) :
    rdst t step own = offC t + 48 ∨ (rdst t step own = slotC t ∧ own = false ∧ t ≠ 0) := by
  unfold rdst rungDst
  split_ifs with h
  · exact Or.inr ⟨rfl, h.2.1, h.2.2⟩
  · exact Or.inl rfl
theorem rung_hash {β : Type} {im : Image} {sk : BitVec 256} {q t step : Nat} {own : Bool} (ht : t < 7)
    (hs : step = 1 ∨ step = 2) (hc : CodeAt im (pcOf q) (rungW step (rungDst t step own)))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    {s u : MachineState} {val : Digest} (hpc : u.pc = pcOf q)
    (hm : CMid B H k index j t own s u (step - 1) val (B + offC t + 48))
    {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hK : ∀ (v' : Digest) (w : MachineState), w.pc = pcOf (q + (rungW step (rungDst t step own)).length) →
      CMid B H k index j t own s w step v' (B + rdst t step own) → TBSim im sk w W (f v') Q) :
    TBSim im sk u (2 + (8 + W)) (shortHash (WCT9.chainInput index k j t step val) >>= f) Q := by
  have hob := offC_bounds t ht
  have hsb := slotC_bounds t ht
  have hbb := hb.bhi
  have hb8 := hb.b8
  have hrd := rdst_cases t step own
  have hrd' : rdst t step own % 8 = 0 ∧ offC t + 48 ≤ rdst t step own ∧ rdst t step own + 32 ≤ 1024 := by
    rcases hrd with h | ⟨h, _⟩ <;> rw [h] <;> omega
  obtain ⟨u2, s2, p2, e2, x12_2, keep2, m16, f2⟩ :=
    rung_spec own ht hs hc u hpc hm.regs.x8 hm.x10 (by omega) (by omega)
  have hL : 2 ≤ (rungW step (rungDst t step own)).length ∧ (rungW step (rungDst t step own)).length ≤ 3 := by
    cases rungDst t step own <;> simp [rungW]
  have k2 : keepC u u2 := fun r _ _ h12 _ _ => keep2 r h12
  have r2 := hm.regs.of_keep k2
  have x10_2 : u2.getReg .x10 = BitVec.ofNat 64 (B + offC t) := (keep2 _ (by decide)).trans hm.x10
  have x12' : u2.getReg .x12 = BitVec.ofNat 64 (B + rdst t step own) := by
    rw [x12_2]; unfold rdst
    cases h : rungDst t step own with
    | some d => rfl
    | none => have := hm.x12; rwa [Nat.add_assoc] at this
  have fs2 : ∀ o, o + 8 ≤ 1024 → o ≠ offC t + 16 →
      u2.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) :=
    fun o ho h1 => f2 (B + o) (by omega) (by omega)
  have hqm : qQ k index j % 65536 = 0 ∧ qQ k index j < 2 ^ 63 := by unfold qQ; omega
  have hdr2 : u2.getMem (BitVec.ofNat 64 (B + offC t + 16)) = BitVec.ofNat 64 (qQ k index j + qK t step) := by
    rw [m16, hm.hdr]
    rcases hs with rfl | rfl
    · simp only [if_true, hm.regs.x7]; exact step_byte _ t 0 1 hqm.1 hqm.2 ht (by decide) (by decide)
    · simp only [show ¬ (2 = 1) by decide, if_false, hm.regs.x13]
      exact step_byte _ t 1 2 hqm.1 hqm.2 ht (by decide) (by decide)
  refine (TBSim.steps s2 (tb_chainHash (A := B + offC t) (D := B + rdst t step own) (W := W) hk hidx hj ht
    (by rcases hs with rfl | rfl <;> decide) e2 r2.x5
    x10_2 r2.x11 x12' (by omega) (by omega) (by omega) (by omega) ?_ ?_ hdr2 ?_ ?_ ?_ ?_ (fun a => ?_))).mono
    (by omega) (fun _ _ h => h)
  · rw [fs2 _ (by omega) (by omega)]; exact hm.p0
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p0'
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.x4m
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1'
  · rw [Nat.add_assoc]
    refine ⟨?_, ?_⟩
    · rw [fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.val.1
    · rw [Nat.add_assoc, fs2 _ (by omega) (by omega)]; have := hm.val.2; rwa [Nat.add_assoc, Nat.add_assoc] at this
  · set w := writeHash u2 a
    have hw : ∀ o, o + 8 ≤ 1024 → (o + 8 ≤ rdst t step own ∨ rdst t step own + 32 ≤ o) →
        w.getMem (BitVec.ofNat 64 (B + o)) = u2.getMem (BitVec.ofNat 64 (B + o)) :=
      fun o ho hn => writeHash_get_out x12' (by omega) (by omega) (by omega)
    refine hK _ w ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_add4, show q + ((rungW step (rungDst t step own)).length - 1) + 1 = q + (rungW step (rungDst t step own)).length by omega]
    · exact r2.of_keep (fun r _ _ _ _ _ => getReg_writeHash u2 a r)
    · rw [getReg_writeHash]; exact x10_2
    · rw [getReg_writeHash]; exact x12'
    · exact (hm.keep.trans k2).trans (fun r _ _ _ _ _ => getReg_writeHash u2 a r)
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), ← Nat.add_assoc]; exact hdr2
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.x4m
    · rw [hw _ (by omega) (by omega), fs2 _ (by omega) (by omega)]; exact hm.p0
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p0'
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1'
    · exact DigAt.writeHash_lo u2 a _ x12' (by omega)
    · have fw := Frame.writeHash u2 a (B + rdst t step own) x12' (by omega)
      refine ((hm.frame.trans f2).trans fw).mono (fun A _ hA => ?_)
      rcases hA with (h | h) | h
      · exact h
      · exact Or.inl h
      · rcases hrd with he | ⟨he, ho, _⟩
        · rw [he] at h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · rw [he] at h; right; right; rw [ho]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
def dfin (t : Nat) (own : Bool) : Nat := if own then offC t + 48 else slotC t
theorem a2C_one (t : Nat) (own : Bool) : a2C t 1 own = dfin t own := by
  unfold a2C dfin; simp
theorem rdst_two (t : Nat) (own : Bool) : rdst t 2 own = dfin t own := by
  unfold rdst rungDst dfin
  cases own
  · by_cases h : t = 0
    · subst h; simp [offC, slotC]
    · simp [h]
  · simp
def ChainPost (B H k index j t : Nat) (own : Bool) (s : MachineState) (q : Nat) (e : Digest) (u : MachineState) : Prop :=
  u.pc = pcOf q ∧ DigAt u (B + slotC t) e ∧ CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u ∧ keepC s u ∧ Frame s u (chainWr B t own)
theorem chain_finish {im : Image} {sk : BitVec 256} {q t : Nat} {own : Bool} (ht : t < 7)
    (hown : own = true → 0 < t ∧ t < 6) (hc : CodeAt im (pcOf q) (if own then copyW t else []))
    {B H k index j : Nat} (hb : Bnd B H) {s u : MachineState} {e : Digest} (hpc : u.pc = pcOf q)
    (hm : CMid B H k index j t own s u 2 e (B + dfin t own)) :
    TBSim im sk u 4 (pure e : M Digest)
      (ChainPost B H k index j t own s (q + (if own then copyW t else []).length)) := by
  cases own with
  | false =>
    simp only [dfin, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero] at hm ⊢
    exact (TBSim.pure ⟨hpc, hm.val, hm.regs, hm.keep, hm.frame⟩).mono (by omega) (fun _ _ h => h)
  | true =>
    obtain ⟨h1, h5⟩ := hown rfl
    simp only [dfin, ↓reduceIte] at hm hc ⊢
    have hob := offC_bounds t ht
    have hsb := slotC_bounds t ht
    have hbb := hb.bhi
    have hb8 := hb.b8
    obtain ⟨w, sw, pw, kw, m0, m8, fw⟩ := copy_spec h1 h5 hc u hpc hm.regs.x8 (by omega) hb.bhi
    have kk : keepC u w := fun r h3 _ _ h14 _ => kw r h3 h14
    have hv : DigAt u (B + offC t + 48) e := by have := hm.val; rwa [← Nat.add_assoc] at this
    have h56 : B + offC t + 48 + 8 = B + offC t + 56 := by omega
    refine TBSim.steps sw (TBSim.pure ⟨by rw [pw]; simp [copyW], ⟨?_, ?_⟩, hm.regs.of_keep kk, hm.keep.trans kk, ?_⟩)
    · rw [m0]; exact hv.1
    · rw [m8, ← h56]; exact hv.2
    · refine (hm.frame.trans fw).mono (fun A _ hA => ?_)
      rcases hA with h | h | h
      · exact h
      · right; right; simp only [↓reduceIte]; omega
      · right; right; simp only [↓reduceIte]; omega
def chainCost : Nat := 40
theorem chain_tb {im : Image} {sk : BitVec 256} {p t d : Nat} {own : Bool} (ht : t < 7) (hd1 : 1 ≤ d)
    (hd3 : d ≤ 3) (hown : own = true → 0 < t ∧ t < 6) (hc : CodeAt im (pcOf p) (chainW t d own))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    (s : MachineState) (hpc : s.pc = pcOf p) (hr : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s)
    (hpad : PadsZ B t s) (v : Digest) (hv : DigAt s (B + offC t + 48) v) :
    TBSim im sk s chainCost (WCT9.chain index k j t (3 - d) d v)
      (ChainPost B H k index j t own s (p + (chainW t d own).length)) := by
  have hc1 := codeAt_left (codeAt_left hc)
  have hc23 := codeAt_right (codeAt_left hc)
  have hc4 := codeAt_right hc
  have hlenW : (chainW t d own).length = 5 + (rungsW t d own).length + (if own then copyW t else []).length := by
    simp [chainW, headW]; omega
  have hd : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hd with rfl | rfl | rfl
  ·
    have hsrc : WCT9.chain index k j t (3 - 1) 1 v =
        (shortHash (WCT9.chainInput index k j t 2 v) >>= fun v1 => pure v1) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have ha : a2C t 1 own = offC t + 48 ∨ (a2C t 1 own = slotC t ∧ (own = false ∨ t = 0)) := by
      unfold a2C; cases own <;> simp
    refine (head_hash (st := 2) (a2 := a2C t 1 own) (own := own) ht (by decide) ha hc1 hb hk hidx hj s hpc hr
      hpad v hv (W := 4) (fun v' w pw hw => ?_)).mono (by unfold chainCost; omega)
      (fun _ _ h => h)
    have hr0 : rungsW t 1 own = [] := by simp [rungsW]
    rw [a2C_one] at hw
    have := chain_finish (sk := sk) ht hown (by rw [hr0] at hc4; simpa [headW] using hc4) hb pw hw
    rw [hlenW, hr0]; simpa [headW, Nat.add_assoc] using this
  ·
    have hsrc : WCT9.chain index k j t (3 - 2) 2 v =
        (shortHash (WCT9.chainInput index k j t 1 v) >>= fun v1 =>
          shortHash (WCT9.chainInput index k j t 2 v1) >>= fun v2 => pure v2) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have hr2 : rungsW t 2 own = rungW 2 (rungDst t 2 own) := by simp [rungsW]
    have ha2 : a2C t 2 own = offC t + 48 := by simp [a2C]
    rw [ha2] at hc1
    rw [hr2] at hc23 hc4
    refine (head_hash (st := 1) (a2 := offC t + 48) (own := own) ht (by decide) (Or.inl rfl) hc1 hb hk hidx hj s hpc
      hr hpad v hv (W := 2 + (8 + 4)) (fun v1 w1 pw1 hw1 => ?_)).mono
      (by unfold chainCost; omega) (fun _ _ h => h)
    rw [← Nat.add_assoc] at hw1
    refine rung_hash (step := 2) (own := own) ht (Or.inr rfl) (by simpa [headW] using hc23) hb hk hidx hj
      (by rw [pw1]) hw1 (fun v2 w2 pw2 hw2 => ?_)
    rw [rdst_two] at hw2
    have hc4' : CodeAt im (pcOf (p + 5 + (rungW 2 (rungDst t 2 own)).length)) (if own then copyW t else []) := by
      have e : p + 5 + (rungW 2 (rungDst t 2 own)).length =
          p + (headW t (3 - 2) (a2C t 2 own) ++ rungW 2 (rungDst t 2 own)).length := by
        simp only [headW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hc4
    have := chain_finish (sk := sk) ht hown hc4' hb pw2 hw2
    rw [hlenW, hr2]; simpa [headW, Nat.add_assoc] using this
  ·
    have hsrc : WCT9.chain index k j t (3 - 3) 3 v =
        (shortHash (WCT9.chainInput index k j t 0 v) >>= fun v1 =>
          shortHash (WCT9.chainInput index k j t 1 v1) >>= fun v2 =>
            shortHash (WCT9.chainInput index k j t 2 v2) >>= fun v3 => pure v3) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have hr3 : rungsW t 3 own = rungW 1 (rungDst t 1 own) ++ rungW 2 (rungDst t 2 own) := by
      simp [rungsW, List.range']
    have hd1 : rungDst t 1 own = none := by simp [rungDst]
    have ha3 : a2C t 3 own = offC t + 48 := by simp [a2C]
    rw [ha3] at hc1
    rw [hr3] at hc23 hc4
    have hc2 := codeAt_left hc23
    have hc3 := codeAt_right hc23
    refine (head_hash (st := 0) (a2 := offC t + 48) (own := own) ht (by decide) (Or.inl rfl) hc1 hb hk hidx hj s hpc
      hr hpad v hv (W := 2 + (8 + (2 + (8 + 4)))) (fun v1 w1 pw1 hw1 => ?_)).mono
      (by unfold chainCost; omega) (fun _ _ h => h)
    rw [← Nat.add_assoc] at hw1
    refine rung_hash (step := 1) (own := own) ht (Or.inl rfl) (by simpa [headW] using hc2) hb hk hidx hj
      (by rw [pw1]) hw1 (fun v2 w2 pw2 hw2 => ?_)
    have hrd1 : rdst t 1 own = offC t + 48 := by simp [rdst, hd1]
    rw [hrd1, ← Nat.add_assoc] at hw2
    refine rung_hash (step := 2) (own := own) ht (Or.inr rfl) (by simpa [headW, Nat.add_assoc] using hc3) hb hk
      hidx hj (by rw [pw2]; simp [headW, Nat.add_assoc]) hw2 (fun v3 w3 pw3 hw3 => ?_)
    rw [rdst_two] at hw3
    have hc4' : CodeAt im (pcOf (p + 5 + (rungW 1 (rungDst t 1 own)).length + (rungW 2 (rungDst t 2 own)).length))
        (if own then copyW t else []) := by
      have e : p + 5 + (rungW 1 (rungDst t 1 own)).length + (rungW 2 (rungDst t 2 own)).length =
          p + (headW t (3 - 3) (a2C t 3 own) ++ (rungW 1 (rungDst t 1 own) ++ rungW 2 (rungDst t 2 own))).length := by
        simp only [headW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hc4
    have := chain_finish (sk := sk) ht hown hc4' hb pw3 hw3
    rw [hlenW, hr3]; simpa [headW, Nat.add_assoc] using this
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M shortHash)
set_option linter.unusedSimpArgs false
def jalTo (w : BitVec 32) (n : Nat) : Option Nat :=
  match decodeInstruction w with
  | some (.base (.JAL .x0 imm)) =>
    let a := (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64
    if 0x1000 ≤ a ∧ a % 4 = 0 then some ((a - 0x1000) / 4) else none
  | _ => none
theorem jalTo_sound {w : BitVec 32} {n m : Nat} (h : jalTo w n = some m) :
    ∃ imm, decodeInstruction w = some (.base (.JAL .x0 imm)) ∧
      (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64 := by
  unfold jalTo at h
  split at h
  · rename_i imm hd
    refine ⟨imm, hd, ?_⟩
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
      rw [Nat.mod_eq_of_lt (a := 0x1000 + 4 * _) (by omega)]
      omega
    · cases h
  · cases h
def walk (z : List Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, t, n =>
    match expLook n with
    | none => none
    | some w =>
      match jalTo w n with
      | some m => (walk z fuel t m).map (· + 1)
      | none =>
        if t < 7 then
          if z.getD t 0 = 0 then walk z fuel (t + 1) n
          else if windowOK n (chainW t (z.getD t 0) (ownC z t)) then
            (walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length)).map (· + chainCost)
          else none
        else if windowOK n leafW then some 6 else none
def chainsFrom (index k j : Nat) (z : List Nat) (vals : Nat → Digest) (t : Nat) : M (List Digest) :=
  (List.range' t (7 - t)).mapM fun i => WCT9.chain index k j i (3 - z.getD i 0) (z.getD i 0) (vals i)
theorem chainsFrom_succ (index k j : Nat) (z : List Nat) (vals : Nat → Digest) (t : Nat) (ht : t < 7) :
    chainsFrom index k j z vals t =
      (WCT9.chain index k j t (3 - z.getD t 0) (z.getD t 0) (vals t) >>= fun e =>
        chainsFrom index k j z vals (t + 1) >>= fun es => pure (e :: es)) := by
  unfold chainsFrom
  rw [show 7 - t = (7 - (t + 1)) + 1 by omega, List.range'_succ, List.mapM_cons]
theorem chainsFrom_seven (index k j : Nat) (z : List Nat) (vals : Nat → Digest) :
    chainsFrom index k j z vals 7 = pure [] := rfl
theorem chain_zero (index k j t : Nat) (v : Digest) : WCT9.chain index k j t (3 - 0) 0 v = pure v := rfl
def chainsWr (B : Nat) (z : List Nat) (t : Nat) (A : Nat) : Prop :=
  ∃ t', t' < t ∧ z.getD t' 0 ≠ 0 ∧ chainWr B t' (ownC z t') A
structure RPre (B H k index j : Nat) (z : List Nat) (vals : Nat → Digest) (s0 : MachineState) : Prop where
  bnd : Bnd B H
  sep : B + 1024 + 2048 ≤ H
  hk : k < 9
  hidx : index < 2 ^ 31
  hj : j < 128
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s0
  leafHdr : s0.getMem (BitVec.ofNat 64 (H - 2048 + 456)) = BitVec.ofNat 64 (hdr0 6 k 0 0)
  pads : ∀ t, t < 7 → PadsZ B t s0
  valAt : ∀ t, t < 7 → DigAt s0 (B + offC t + 48) (vals t)
  passive : ∀ t, t < 7 → z.getD t 0 = 0 → DigAt s0 (B + slotC t) (vals t)
  digits : ∀ t, t < 7 → z.getD t 0 ≤ 3
structure RInv (B H k index j : Nat) (z : List Nat) (s0 : MachineState) (t : Nat) (pre : List Digest)
    (u : MachineState) : Prop where
  len : pre.length = t
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u
  keep : keepC s0 u
  frame : Frame s0 u (chainsWr B z t)
  done : ∀ t', t' < t → DigAt u (B + slotC t') (pre.getD t' 0)
structure RPost (B k index j : Nat) (z : List Nat) (s0 : MachineState) (ends : List Digest) (w : MachineState) :
    Prop where
  pc : w.pc = s0.getReg .x23 &&& 0xfffffffffffffffe#64
  a0 : w.getReg .x10 = BitVec.ofNat 64 (B + 880)
  a1 : w.getReg .x11 = BitVec.ofNat 64 128
  keep : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → w.getReg r = s0.getReg r
  len : ends.length = 7
  ends : ∀ t, t < 7 → DigAt w (B + slotC t) (ends.getD t 0)
  h0 : w.getMem (BitVec.ofNat 64 (B + 896)) = BitVec.ofNat 64 (hdr0 6 k 0 0)
  h1 : w.getMem (BitVec.ofNat 64 (B + 904)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)
  frame : Frame s0 w (fun A => chainsWr B z 7 A ∨ A = B + 896 ∨ A = B + 904)
theorem offC_lt_slot (t t' : Nat) (ht : t < 7) (ht' : t' < 7) : offC t + 80 ≤ slotC t' ∨ (t = 0 ∧ t' = 0) := by
  unfold offC slotC; split <;> omega
theorem slot_free_later {B t t'' : Nat} {own : Bool} (h : t < t'') (h7 : t'' < 7) (o : Nat) (ho : o < 16) :
    ¬ chainWr B t'' own (B + slotC t + o) := by
  unfold chainWr offC slotC
  split_ifs <;> omega
theorem block_free_earlier {B t' t : Nat} {own : Bool} (h : t' < t) (h7 : t < 7) (o : Nat) (ho : o < 64)
    : ¬ chainWr B t' own (B + offC t + o) := by
  unfold chainWr offC slotC
  split_ifs <;> omega
theorem passive_free_earlier {B t' t : Nat} (z : List Nat) (h : t' < t) (h7 : t < 7) (hp : z.getD t 0 = 0)
    (o : Nat) (ho : o < 16) : ¬ chainWr B t' (ownC z t') (B + slotC t + o) := by
  unfold chainWr offC slotC
  by_cases ht1 : t = t' + 1
  · subst ht1
    by_cases h0 : t' = 0
    · subst h0; norm_num; split_ifs <;> omega
    · have hown : ownC z t' = true := by
        simp only [ownC, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨by omega, by omega⟩, hp⟩
      rw [hown]; simp only [↓reduceIte]; split_ifs <;> omega
  · split_ifs <;> omega
theorem leafHdr_free {B t : Nat} (o : Nat) (ho : o < 16) :
    B + slotC t + o ≠ B + 896 ∧ B + slotC t + o ≠ B + 904 := by
  unfold slotC; split <;> omega
theorem expLook_lt {m : Nat} {w : BitVec 32} (h : expLook m = some w) : 1024 ≤ m ∧ m < 160 * 256 := by
  unfold expLook at h
  split at h
  · rename_i hm
    refine ⟨hm, ?_⟩
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [expChunks_length]; omega)] at h
    simp at h
  · cases h
theorem window_bound {n : Nat} {ws : List (BitVec 32)} (h : windowOK n ws = true) (hne : ws ≠ []) :
    n + ws.length ≤ 160 * 256 := by
  unfold windowOK at h
  have hl : 0 < ws.length := List.length_pos_of_ne_nil hne
  have := List.all_eq_true.mp h (ws.length - 1) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  have := expLook_lt this
  omega
theorem codeAt_win {im : Image} (hc : NewCodeAt im) {n : Nat} {ws : List (BitVec 32)} (h : windowOK n ws = true)
    (hne : ws ≠ []) : CodeAt im (pcOf n) ws :=
  codeAt_of_window hc (by have := window_bound h hne; omega) h
theorem codeAt_one {im : Image} (hc : NewCodeAt im) {n : Nat} {w : BitVec 32} (h : expLook n = some w) :
    CodeAt im (pcOf n) [w] :=
  codeAt_of_look (expLook_ok hc) n [w] (by have := expLook_lt h; simp; omega) (fun i hi => by
    simp at hi; subst hi; simpa using h)
theorem getD_append_lt {α : Type} (l1 l2 : List α) (d : α) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_len {α : Type} (l : List α) (a : α) (d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]
theorem chainNe (z : List Nat) (t : Nat) (h : z.getD t 0 ≠ 0) (h3 : z.getD t 0 ≤ 3) :
    1 ≤ z.getD t 0 ∧ z.getD t 0 ≤ 3 := ⟨by omega, h3⟩
theorem ownC_spec (z : List Nat) (t : Nat) : ownC z t = true → 0 < t ∧ t < 6 := by
  simp only [ownC, Bool.and_eq_true, decide_eq_true_eq]; exact fun h => h.1
theorem hbank_free {B H : Nat} {z : List Nat} {t A : Nat} (ht : t ≤ 7) (hs : B + 1024 + 2048 ≤ H) (hA : H - 2048 ≤ A) :
    ¬ chainsWr B z t A := by
  rintro ⟨t', ht', _, h⟩
  unfold chainWr offC slotC at h
  split_ifs at h <;> omega
theorem walk_tb {im : Image} (hcode : NewCodeAt im) {sk : BitVec 256} {B H k index j : Nat} {z : List Nat}
    {vals : Nat → Digest} {s0 : MachineState} (hpre : RPre B H k index j z vals s0) :
    ∀ fuel t n c (pre : List Digest) (u : MachineState), walk z fuel t n = some c → t ≤ 7 → u.pc = pcOf n →
      RInv B H k index j z s0 t pre u →
      TBSim im sk u c (chainsFrom index k j z vals t) (fun rest w => RPost B k index j z s0 (pre ++ rest) w) := by
  have hb := hpre.bnd
  have hbb := hb.bhi
  have hsep := hpre.sep
  intro fuel
  induction fuel with
  | zero => intro t n c pre u hw; simp [walk] at hw
  | succ fuel ih =>
    intro t n c pre u hw ht hpc hI
    simp only [walk] at hw
    split at hw
    · cases hw
    · rename_i w hlook
      split at hw
      ·
        rename_i m hjal
        obtain ⟨c', hw', rfl⟩ : ∃ c', walk z fuel t m = some c' ∧ c = c' + 1 := by
          cases h : walk z fuel t m <;> simp_all
        obtain ⟨imm, hd, hoff⟩ := jalTo_sound hjal
        have hs := jal_x0_step (codeAt_one hcode hlook) hd hoff u hpc
        have hI' : RInv B H k index j z s0 t pre (u.setPC (pcOf m)) :=
          ⟨hI.len, ⟨hI.regs.x8, hI.regs.x28, hI.regs.x4, hI.regs.x31, hI.regs.x7, hI.regs.x13, hI.regs.x5,
            hI.regs.x11⟩,
            fun r a b c d e => hI.keep r a b c d e, fun A hA hn => hI.frame A hA hn,
            fun t' ht' => hI.done t' ht'⟩
        exact (TBSim.steps hs (ih t m c' pre _ hw' ht rfl hI')).mono (by omega) (fun _ _ h => h)
      · rename_i hjal
        split at hw
        · rename_i ht7
          split at hw
          ·
            rename_i hz
            rw [chainsFrom_succ _ _ _ _ _ _ ht7, hz, chain_zero, pure_bind]
            have hdone : DigAt u (B + slotC t) (vals t) := by
              have hP := hpre.passive t ht7 hz
              have hs := slotC_bounds t ht7
              refine ⟨(hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ =>
                passive_free_earlier z h1 ht7 hz 0 (by omega) (by simpa using h2))).trans hP.1, ?_⟩
              rw [hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ =>
                passive_free_earlier z h1 ht7 hz 8 (by omega) h2)]
              exact hP.2
            have hI' : RInv B H k index j z s0 (t + 1) (pre ++ [vals t]) u :=
              ⟨by simp [hI.len], hI.regs, hI.keep, hI.frame.mono (fun A _ ⟨t', h1, h2, h3⟩ => ⟨t', by omega, h2, h3⟩),
                fun t' ht' => by
                  rcases Nat.lt_or_ge t' t with h | h
                  · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]; exact hI.done t' h
                  · have : t' = t := by omega
                    subst this; rw [← hI.len, getD_append_len, hI.len]; exact hdone⟩
            refine (TBSim.bind (W₂ := 0) (ih (t + 1) n c _ u hw (by omega) hpc hI') (fun es w hw' =>
              TBSim.pure (by simpa using hw'))).mono (by omega) (fun _ _ h => h)
          · split at hw
            ·
              rename_i hz hwin
              obtain ⟨c', hw', rfl⟩ : ∃ c', walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length)
                  = some c' ∧ c = c' + chainCost := by
                cases h : walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length) <;> simp_all
              have hd := chainNe z t hz (hpre.digits t ht7)
              have hcw : CodeAt im (pcOf n) (chainW t (z.getD t 0) (ownC z t)) :=
                codeAt_win hcode hwin (by simp [chainW, headW])
              have hob := offC_bounds t ht7
              have hsb := slotC_bounds t ht7
              have hfree : ∀ o, o < 64 → (o < 16 ∨ 24 ≤ o) →
                  u.getMem (BitVec.ofNat 64 (B + offC t + o)) = s0.getMem (BitVec.ofNat 64 (B + offC t + o)) :=
                fun o ho _ => hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ => block_free_earlier h1 ht7 o ho h2)
              have hpad : PadsZ B t u := by
                have hp := hpre.pads t ht7
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · have := hfree 0 (by omega) (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hp.1
                · rw [hfree 8 (by omega) (by omega)]; exact hp.2.1
                · rw [hfree 32 (by omega) (by omega)]; exact hp.2.2.1
                · rw [hfree 40 (by omega) (by omega)]; exact hp.2.2.2.1
                · rw [hfree 24 (by omega) (by omega)]; exact hp.2.2.2.2
              have hv : DigAt u (B + offC t + 48) (vals t) := by
                have hV := hpre.valAt t ht7
                exact ⟨(hfree 48 (by omega) (by omega)).trans hV.1, by
                  rw [show B + offC t + 48 + 8 = B + offC t + 56 by omega, hfree 56 (by omega) (by omega),
                    ← show B + offC t + 48 + 8 = B + offC t + 56 by omega]; exact hV.2⟩
              have hct := chain_tb (sk := sk) ht7 hd.1 hd.2 (ownC_spec z t) hcw hb hpre.hk hpre.hidx hpre.hj u hpc
                hI.regs hpad (vals t) hv
              rw [chainsFrom_succ _ _ _ _ _ _ ht7]
              refine (TBSim.bind (W₂ := c') hct (fun e w hw1 => ?_)).mono (by omega) (fun _ _ h => h)
              obtain ⟨pw, dw, rw', kw, fw⟩ := hw1
              have hI' : RInv B H k index j z s0 (t + 1) (pre ++ [e]) w := by
                refine ⟨by simp [hI.len], rw', hI.keep.trans kw, (hI.frame.trans fw).mono (fun A _ hA => ?_),
                  fun t' ht' => ?_⟩
                · rcases hA with ⟨t', h1, h2, h3⟩ | h
                  · exact ⟨t', by omega, h2, h3⟩
                  · exact ⟨t, by omega, hz, h⟩
                · rcases Nat.lt_or_ge t' t with h | h
                  · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]
                    have hD := hI.done t' h
                    have hs' := slotC_bounds t' (by omega)
                    exact ⟨(fw _ (by omega) (slot_free_later h ht7 0 (by omega) |> fun hh => by simpa using hh)).trans hD.1,
                      (fw _ (by omega) (slot_free_later h ht7 8 (by omega))).trans hD.2⟩
                  · have : t' = t := by omega
                    subst this; rw [← hI.len, getD_append_len, hI.len]; exact dw
              refine (TBSim.bind (W₂ := 0) (ih (t + 1) _ c' _ w hw' (by omega) pw hI') (fun es w' hw'' =>
                TBSim.pure (by simpa using hw''))).mono (by omega) (fun _ _ h => h)
            · cases hw
        ·
          rename_i ht7
          have h7 : t = 7 := by omega
          subst h7
          split at hw
          · rename_i hwin
            simp only [Option.some.injEq] at hw
            subst hw
            rw [chainsFrom_seven]
            have hcw : CodeAt im (pcOf n) leafW := codeAt_win hcode hwin (by simp [leafW])
            obtain ⟨w, sw, pw, a0, a1, kw, m0, m1, fw⟩ := leaf_spec hcw u hpc hI.regs.x8 hI.regs.x28 hb
            refine (TBSim.steps sw (TBSim.pure ⟨?_, a0, a1, ?_, by simp [hI.len], ?_, ?_, ?_, ?_⟩)).mono
              (by omega) (fun _ _ h => h)
            · rw [pw, hI.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
            · intro r h3 h10 h11 h12 h14 h25
              rw [kw r h10 h11 h25, hI.keep r h3 h10 h12 h14 h25]
            · intro t' ht'
              rw [List.append_nil]
              have hD := hI.done t' ht'
              have hs' := slotC_bounds t' ht'
              have hl := leafHdr_free (B := B) (t := t') 0 (by omega)
              have hl8 := leafHdr_free (B := B) (t := t') 8 (by omega)
              simp only [Nat.add_zero] at hl
              exact ⟨(fw _ (by omega) (by rintro (h | h) <;> omega)).trans hD.1,
                (fw _ (by omega) (by rintro (h | h) <;> omega)).trans hD.2⟩
            · rw [m0, hI.frame _ (by have := hb.hhi; omega) (hbank_free (by omega) hsep (by omega))]
              exact hpre.leafHdr
            · rw [m1, hI.regs.x4]
            · exact (hI.frame.trans fw).mono (fun A _ hA => by
                rcases hA with h | h
                · exact Or.inl h
                · exact Or.inr h)
          · cases hw
end ClaudeWCT.W9.Machine.Expand
end
