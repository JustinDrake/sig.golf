import SigGolfCandidate.T3M.Verify.SelCheck
import SigGolfCandidate.T3M.Verify.SelArith

/-!
# Selections: semantics (T3M verify words 17 .. 358)

From the post-digest state (`DgOut`, answer `a`): the setup loads the four words of `a` and `s6 = a mod 2^31`; for
each coordinate `c` the machine either rejects (HALT(1), no query) when the triple of coordinate `c` has a repeated
leaf, or stores the sorted heap indices `2048 + selLeaf sel_c k` at `ETAB + 24 c + 8 k`.

* `xE_eval` : the symbolic heap index evaluates to `2048 + 256 bucket + x_j`;
* `sel_step` : one coordinate (accept with cost `selCost a c`, or reject);
* **`select_good`** : the selection piece of `verifyP` (`if !selectionsOk (selections a) then pure false else …`)
  from `DgOut`, given the continuation's judgment on every state at `fts_setup` (`SelIn … 7`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)

/-- The machine's check of one selection (the lambda of `selectionsOk`). -/
def selOk1 (s : Selection) : Bool :=
  match s.leaves with
  | [x0, x1, x2] => decide (x0 < x1) && decide (x1 < x2)
  | _ => false

theorem selectionsOk_eq (chosen : List Selection) : selectionsOk chosen = chosen.all selOk1 := rfl

/-- t3-rl2: the header-table address of unsorted leaf `j` of coordinate `c`. -/
def eVal (a : HashOutput) (c j : Nat) : Nat := TAB + 8 * (128 * (selNum a.toNat c % 16) + selX a.toNat c j)

/-- The accepting path of a distinct triple. -/
def selPath (x0 x1 x2 : Nat) : Nat :=
  if x0 < x1 then (if x1 < x2 then 0 else if x0 < x2 then 1 else 2)
  else (if x1 < x2 then (if x0 < x2 then 3 else 4) else 5)

/-- The reject path of a triple with a repeated leaf. -/
def selRPath (x0 x1 x2 : Nat) : Nat :=
  if x0 < x1 then (if x0 < x2 then 0 else 1)
  else (if x1 < x2 then (if x0 < x2 then 2 else 3) else (if x2 = x1 then 4 else 5))

/-- Cycles of coordinate `c`'s accepting path. -/
def selCost (a : HashOutput) (c : Nat) : Nat :=
  selExt c + 12 + selTree (selPath (selX a.toNat c 0) (selX a.toNat c 1) (selX a.toNat c 2))

/-! ## Evaluation -/

/-- The registers of the selection code: the four words of `a`. -/
def NRegs (a : HashOutput) (s : MachineState) : Prop :=
  ∀ k, k < 4 → s.getReg (nReg k) = a.extractLsb' (64 * k) 64

theorem nReg_toNat (a : HashOutput) (s : MachineState) (h : NRegs a s) (k : Nat) (hk : k < 4) :
    (s.getReg (nReg k)).toNat = a.toNat / 2 ^ (64 * k) % 2 ^ 64 := by
  rw [h k hk, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem gpE_eval (a : HashOutput) (s : MachineState) (h : NRegs a s) (c : Nat) (hc : c < 7) :
    ((gpE c).eval s).toNat % 2 ^ 25 = selNum a.toNat c % 2 ^ 25 := by
  unfold selNum
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gp_single a.toNat _ 0 31 (nReg_toNat a s h 0 (by decide)) (by decide)
  · exact gp_double a.toNat _ _ 0 56 (nReg_toNat a s h 0 (by decide)) (nReg_toNat a s h 1 (by decide))
      (by decide) (by decide)
  · exact gp_single a.toNat _ 1 17 (nReg_toNat a s h 1 (by decide)) (by decide)
  · exact gp_double a.toNat _ _ 1 42 (nReg_toNat a s h 1 (by decide)) (nReg_toNat a s h 2 (by decide))
      (by decide) (by decide)
  · exact gp_single a.toNat _ 2 3 (nReg_toNat a s h 2 (by decide)) (by decide)
  · exact gp_single a.toNat _ 2 28 (nReg_toNat a s h 2 (by decide)) (by decide)
  · exact gp_double a.toNat _ _ 2 53 (nReg_toNat a s h 2 (by decide)) (nReg_toNat a s h 3 (by decide))
      (by decide) (by decide)

theorem xE_eval (a : HashOutput) (s : MachineState) (h : NRegs a s) (c j : Nat) (hc : c < 7) (hj : j < 3) :
    (xE c j).eval s = BitVec.ofNat 64 (eVal a c j) := by
  have := xaddr_eq ((gpE c).eval s) (BitVec.ofNat 64 TAB) (selNum a.toNat c) TAB j hj (gpE_eval a s h c hc) rfl
    (by unfold TAB; omega)
  unfold eVal selX
  rw [← this]; rfl

theorem eVal_lt (a : HashOutput) (c j : Nat) : eVal a c j < 33554432 := by
  unfold eVal selX TAB
  have := Nat.mod_lt (selNum a.toNat c) (show 0 < 16 by decide)
  have := Nat.mod_lt (selNum a.toNat c / 2 ^ (4 + 7 * j)) (show 0 < 128 by decide)
  omega

theorem geuB_holds (a : HashOutput) (s : MachineState) (h : NRegs a s) (c i j : Nat) (hc : c < 7)
    (hi : i < 3) (hj : j < 3) (d : Bool) :
    Br.holds s (geuB c i j d) ↔ d = decide (selX a.toNat c j ≤ selX a.toNat c i) := by
  simp only [geuB, Br.holds, CmpOp.eval, xE_eval a s h c i hc hi, xE_eval a s h c j hc hj, BitVec.ult,
    toNat_ofNat_lt (lt_trans (eVal_lt a c i) (by norm_num)),
    toNat_ofNat_lt (lt_trans (eVal_lt a c j) (by norm_num))]
  have e : decide (eVal a c i < eVal a c j) = decide (selX a.toNat c i < selX a.toNat c j) := by
    unfold eVal; apply decide_eq_decide.mpr; omega
  first
  | (rw [e]; cases d <;> simp)
  | (unfold eVal; cases d <;> simp <;> omega)

theorem eqB_holds (a : HashOutput) (s : MachineState) (h : NRegs a s) (c i j : Nat) (hc : c < 7)
    (hi : i < 3) (hj : j < 3) (d : Bool) :
    Br.holds s (eqB c i j d) ↔ d = decide (selX a.toNat c i = selX a.toNat c j) := by
  simp only [eqB, Br.holds, CmpOp.eval, xE_eval a s h c i hc hi, xE_eval a s h c j hc hj]
  have e : (BitVec.ofNat 64 (eVal a c i) == BitVec.ofNat 64 (eVal a c j)) =
      decide (selX a.toNat c i = selX a.toNat c j) := by
    have hi' := eVal_lt a c i
    have hj' := eVal_lt a c j
    by_cases hx : selX a.toNat c i = selX a.toNat c j
    · have : eVal a c i = eVal a c j := by unfold eVal; rw [hx]
      simp [this, hx]
    · have : eVal a c i ≠ eVal a c j := by unfold eVal; omega
      have : BitVec.ofNat 64 (eVal a c i) ≠ BitVec.ofNat 64 (eVal a c j) :=
        ofNat_ne (by omega) (by omega) this
      simp [this, hx]
  rw [e]; exact eq_comm

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)

/-! ## The invariant at the start of coordinate `c` -/

/-- Selection `c` of the digest answer. -/
abbrev selC (a : HashOutput) (c : Nat) : Selection := (selections a).getD c ⟨0, []⟩

structure SelIn (pk : Digest) (w : WBytes) (a : HashOutput) (c : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (selStart c)
  known : KnownOK baseK s
  nregs : NRegs a s
  idx : s.getReg .x22 = BitVec.ofNat 64 (a.toNat % 2 ^ 31)
  etab : ∀ c' k, c' < c → k < 3 →
    s.getMem (BitVec.ofNat 64 (ETAB + 24 * c' + 8 * k)) = BitVec.ofNat 64 (TAB + 8 * T3M.selLeaf (selC a c') k)
  ok : ∀ c', c' < c → selOk1 (selC a c') = true
  wit : WitAll w s
  pk : PkOK pk s
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x80 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → (A < ETAB ∨ ETAB + 24 * c ≤ A) →
    s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  /-- t3-rl2: `sp = TAB`. -/
  sp : s.getReg .x2 = BitVec.ofNat 64 TAB

theorem selK_of {s : MachineState} (h1 : KnownOK baseK s) (h2 : s.getReg .x2 = BitVec.ofNat 64 TAB) :
    KnownOK selK s := by
  intro p hp
  simp only [selK, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact h1 p hp
  · exact h2

theorem selK_base {s : MachineState} (h : KnownOK selK s) : KnownOK baseK s :=
  fun p hp => h p (List.mem_append_left _ hp)

theorem selK_sp {s : MachineState} (h : KnownOK selK s) : s.getReg .x2 = BitVec.ofNat 64 TAB :=
  h (.x2, BitVec.ofNat 64 TAB) (List.mem_append_right _ (List.mem_singleton_self _))

/-- HALT(1) reached. -/
def Halt1 (u : MachineState) : Prop :=
  fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1

theorem selC_eq (a : HashOutput) (c : Nat) (hc : c < 7) :
    selC a c = ⟨selNum a.toNat c % 16, [selX a.toNat c 0, selX a.toNat c 1, selX a.toNat c 2].mergeSort
      (fun x y => decide (x ≤ y))⟩ := selections_getD a c hc

/-- An accepting path: the stores are the sorted triple. -/
theorem sel_acc_path (pk : Digest) (w : WBytes) (a : HashOutput) (c p : Nat) (hc : c < 7) (hp : p < 6)
    (s : MachineState) (hs : SelIn pk w a c s) (hbr : ∀ b ∈ selBrs c p, b.holds s)
    (hsort : [selX a.toNat c 0, selX a.toNat c 1, selX a.toNat c 2].mergeSort (fun x y => decide (x ≤ y)) =
      (selPerm p).map (selX a.toNat c))
    (hok : selOk1 (selC a c) = true) :
    ∃ u, Steps image s (selExt c + 12 + selTree p) (selExt c + 12 + selTree p) u ∧ SelIn pk w a (c + 1) u := by
  obtain ⟨u, hu⟩ := spec_run (selCheck_at c p hc hp) s hs.pc (selK_of hs.known hs.sp) hbr (by simp)
  have hmem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) =
      if A = ETAB + 24 * c + 16 then (xE c ((selPerm p).getD 2 0)).eval s
      else if A = ETAB + 24 * c + 8 then (xE c ((selPerm p).getD 1 0)).eval s
      else if A = ETAB + 24 * c then (xE c ((selPerm p).getD 0 0)).eval s
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu.mem]
    simp only [selSpec, selMem]
    unfold ETAB at *
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_cons_ofNat _ _ _ _ _ hA (by omega),
      memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil]
  have hperm : ∀ k, k < 3 → (selPerm p).getD k 0 < 3 := by
    intro k hk
    rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  have hstore : ∀ k, k < 3 → u.getMem (BitVec.ofNat 64 (ETAB + 24 * c + 8 * k)) =
      BitVec.ofNat 64 (TAB + 8 * T3M.selLeaf (selC a c) k) := by
    intro k hk
    rw [hmem _ (by unfold ETAB; omega)]
    have hv : ∀ k', k' < 3 → (xE c ((selPerm p).getD k' 0)).eval s =
        BitVec.ofNat 64 (TAB + 8 * T3M.selLeaf (selC a c) k') := by
      intro k' hk'
      rw [xE_eval a s hs.nregs c _ hc (hperm k' hk'), selC_eq a c hc]
      unfold T3M.selLeaf eVal
      simp only []
      rw [hsort]
      rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 by omega) with rfl | rfl | rfl <;>
      simp only [selPerm, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] <;> ring
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; exact hv 0 (by decide)
    · rw [if_neg (by omega), if_pos (by omega)]; exact hv 1 (by decide)
    · rw [if_pos (by omega)]; exact hv 2 (by decide)
  have hframe : ∀ A, A < 2 ^ 64 → (A < ETAB + 24 * c ∨ ETAB + 24 * c + 24 ≤ A) →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    rw [hmem A hA, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨u, hu.steps, ⟨?_, selK_base hu.known, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, selK_sp hu.known⟩⟩
  · rw [hu.pc rfl]; rfl
  · intro k hk; rw [hu.keep (nReg k) (by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [selKeep, nReg])]
    exact hs.nregs k hk
  · rw [hu.keep .x22 (by simp [selKeep])]; exact hs.idx
  · intro c' k hc' hk
    by_cases hcc : c' = c
    · subst hcc; exact hstore k hk
    · rw [hframe _ (by unfold ETAB; omega) (by unfold ETAB; omega)]
      exact hs.etab c' k (by omega) hk
  · intro c' hc'
    by_cases hcc : c' = c
    · subst hcc; exact hok
    · exact hs.ok c' (by omega)
  · intro j hj
    rw [hframe _ (by unfold WIT WX at *; omega) (Or.inr (by unfold ETAB WIT; omega))]
    exact hs.wit j hj
  · exact ⟨(hframe 0xA0 (by omega) (Or.inl (by unfold ETAB; omega))).trans hs.pk.1,
      (hframe 0xA8 (by omega) (Or.inl (by unfold ETAB; omega))).trans hs.pk.2⟩
  · intro A hA hz hE
    rw [hframe A (by unfold WIT at hA; omega) (by omega)]
    exact hs.zero A hA hz (by omega)
  · apply hs.data.congr
    intro A hA hEnd
    exact hframe A (by omega) (Or.inr (by unfold ETAB TAB at *; omega))

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)

/-! ## Branch outcomes as conditions on the leaves -/

/-- A logical branch `(isGeu, i, j, d)`. -/
abbrev BrQ := Bool × Nat × Nat × Bool

def brOfQ (c : Nat) (q : BrQ) : Br := if q.1 then geuB c q.2.1 q.2.2.1 q.2.2.2 else eqB c q.2.1 q.2.2.1 q.2.2.2

def condQ (x : Nat → Nat) (q : BrQ) : Prop :=
  if q.1 then q.2.2.2 = decide (x q.2.2.1 ≤ x q.2.1) else q.2.2.2 = decide (x q.2.1 = x q.2.2.1)

def selBrsQ : Nat → List BrQ
  | 0 => [(true, 1, 2, false), (true, 0, 1, false)]
  | 1 => [(false, 2, 1, false), (true, 0, 2, false), (true, 1, 2, true), (true, 0, 1, false)]
  | 2 => [(false, 2, 0, false), (true, 0, 2, true), (true, 1, 2, true), (true, 0, 1, false)]
  | 3 => [(false, 1, 0, false), (true, 0, 2, false), (true, 1, 2, false), (true, 0, 1, true)]
  | 4 => [(false, 2, 0, false), (true, 0, 2, true), (true, 1, 2, false), (true, 0, 1, true)]
  | _ => [(false, 1, 0, false), (false, 2, 1, false), (true, 1, 2, true), (true, 0, 1, true)]

def selRBrsQ : Nat → List BrQ
  | 0 => [(false, 2, 1, true), (true, 0, 2, false), (true, 1, 2, true), (true, 0, 1, false)]
  | 1 => [(false, 2, 0, true), (true, 0, 2, true), (true, 1, 2, true), (true, 0, 1, false)]
  | 2 => [(false, 1, 0, true), (true, 0, 2, false), (true, 1, 2, false), (true, 0, 1, true)]
  | 3 => [(false, 2, 0, true), (true, 0, 2, true), (true, 1, 2, false), (true, 0, 1, true)]
  | 4 => [(false, 2, 1, true), (true, 1, 2, true), (true, 0, 1, true)]
  | _ => [(false, 1, 0, true), (false, 2, 1, false), (true, 1, 2, true), (true, 0, 1, true)]

theorem selBrs_eq (c p : Nat) (hp : p < 6) : selBrs c p = (selBrsQ p).map (brOfQ c) := by
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem selRBrs_eq (c r : Nat) (hr : r < 6) : selRBrs c r = (selRBrsQ r).map (brOfQ c) := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem brOfQ_holds (a : HashOutput) (s : MachineState) (h : NRegs a s) (c : Nat) (hc : c < 7) (q : BrQ)
    (hi : q.2.1 < 3) (hj : q.2.2.1 < 3) (hq : condQ (selX a.toNat c) q) : Br.holds s (brOfQ c q) := by
  obtain ⟨g, i, j, d⟩ := q
  simp only [brOfQ, condQ] at hq ⊢
  cases g
  · simp only [Bool.false_eq_true, if_false] at hq ⊢
    exact (eqB_holds a s h c i j hc hi hj d).mpr hq
  · simp only [if_true] at hq ⊢
    exact (geuB_holds a s h c i j hc hi hj d).mpr hq

theorem holds_of_condQ (a : HashOutput) (s : MachineState) (h : NRegs a s) (c : Nat) (hc : c < 7)
    (l : List BrQ) (hidx : ∀ q ∈ l, q.2.1 < 3 ∧ q.2.2.1 < 3) (hq : ∀ q ∈ l, condQ (selX a.toNat c) q) :
    ∀ b ∈ l.map (brOfQ c), Br.holds s b := by
  intro b hb
  obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hb
  exact brOfQ_holds a s h c hc q (hidx q hq').1 (hidx q hq').2 (hq q hq')

theorem selBrsQ_idx (p : Nat) (hp : p < 6) : ∀ q ∈ selBrsQ p, q.2.1 < 3 ∧ q.2.2.1 < 3 := by
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selRBrsQ_idx (r : Nat) (hr : r < 6) : ∀ q ∈ selRBrsQ r, q.2.1 < 3 ∧ q.2.2.1 < 3 := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A rejecting path ends at HALT(1). -/
theorem sel_rej_path (pk : Digest) (w : WBytes) (a : HashOutput) (c r : Nat) (hc : c < 7) (hr : r < 6)
    (s : MachineState) (hs : SelIn pk w a c s) (hq : ∀ q ∈ selRBrsQ r, condQ (selX a.toNat c) q) :
    ∃ u, Steps image s (selRSteps c r) (selRSteps c r) u ∧ Halt1 u := by
  have hbr : ∀ b ∈ selRBrs c r, b.holds s := by
    rw [selRBrs_eq c r hr]; exact holds_of_condQ a s hs.nregs c hc _ (selRBrsQ_idx r hr) hq
  obtain ⟨u, hu⟩ := spec_run (selRCheck_at c r hc hr) s hs.pc (selK_of hs.known hs.sp) hbr (by simp)
  exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
    hu.regs (.x10, cw 1) (by simp [rejSpec])⟩

theorem selRSteps_le (c r : Nat) (hc : c < 7) : selRSteps c r ≤ 23 := by
  unfold selRSteps selExt; split <;> split <;> omega

/-! ## One coordinate -/

theorem sel_step (pk : Digest) (w : WBytes) (a : HashOutput) (c : Nat) (hc : c < 7) (s : MachineState)
    (hs : SelIn pk w a c s) :
    (selOk1 (selC a c) = true → ∃ u, Steps image s (selCost a c) (selCost a c) u ∧ SelIn pk w a (c + 1) u) ∧
    (selOk1 (selC a c) = false → ∃ u k, Steps image s k k u ∧ k ≤ 23 ∧ Halt1 u) := by
  have hsel := selC_eq a c hc
  set x0 := selX a.toNat c 0 with hx0
  set x1 := selX a.toNat c 1 with hx1
  set x2 := selX a.toNat c 2 with hx2
  have hok : ∀ y0 y1 y2 : Nat, [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = [y0, y1, y2] →
      selOk1 (selC a c) = (decide (y0 < y1) && decide (y1 < y2)) := by
    intro y0 y1 y2 h
    rw [hsel]; unfold selOk1; simp only []; rw [h]
  -- the accepting/rejecting path from the order of the leaves
  have acc : ∀ p, p < 6 → (∀ q ∈ selBrsQ p, condQ (selX a.toNat c) q) →
      [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = (selPerm p).map (selX a.toNat c) →
      selPath x0 x1 x2 = p → selOk1 (selC a c) = true →
      ∃ u, Steps image s (selCost a c) (selCost a c) u ∧ SelIn pk w a (c + 1) u := by
    intro p hp hq hsort hpath hokc
    have hbr : ∀ b ∈ selBrs c p, b.holds s := by
      rw [selBrs_eq c p hp]; exact holds_of_condQ a s hs.nregs c hc _ (selBrsQ_idx p hp) hq
    have hcost : selCost a c = selExt c + 12 + selTree p := by
      unfold selCost; rw [← hx0, ← hx1, ← hx2, hpath]
    rw [hcost]
    exact sel_acc_path pk w a c p hc hp s hs hbr hsort hokc
  have rej : ∀ r, r < 6 → (∀ q ∈ selRBrsQ r, condQ (selX a.toNat c) q) →
      ∃ u k, Steps image s k k u ∧ k ≤ 23 ∧ Halt1 u := by
    intro r hr hq
    obtain ⟨u, hu1, hu2⟩ := sel_rej_path pk w a c r hc hr s hs hq
    exact ⟨u, _, hu1, selRSteps_le c r hc, hu2⟩
  by_cases h01 : x0 < x1
  · by_cases h12 : x1 < x2
    · have hs' := mergeSort3 x0 x1 x2 x0 x1 x2 (perm3_0 x0 x1 x2) (by omega) (by omega)
      have hk := hok _ _ _ hs'
      refine ⟨fun _ => acc 0 (by decide) ?_ hs' ?_ (by rw [hk]; simp; omega), fun h => ?_⟩
      · simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp; omega
      · simp only [selPath, if_pos h01, if_pos h12]
      · rw [hk] at h; simp at h; omega
    · by_cases h02 : x0 < x2
      · have hs' := mergeSort3 x0 x1 x2 x0 x2 x1 (perm3_1 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 1 (by decide) ?_ hs' ?_ h, fun h => rej 0 (by decide) ?_⟩
        · have : x2 < x1 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_pos h01, if_neg h12, if_pos h02]
        · have : x2 = x1 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
      · have hs' := mergeSort3 x0 x1 x2 x2 x0 x1 (perm3_2 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 2 (by decide) ?_ hs' ?_ h, fun h => rej 1 (by decide) ?_⟩
        · have : x2 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_pos h01, if_neg h12, if_neg h02]
        · have : x2 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
  · by_cases h12 : x1 < x2
    · by_cases h02 : x0 < x2
      · have hs' := mergeSort3 x0 x1 x2 x1 x0 x2 (perm3_3 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 3 (by decide) ?_ hs' ?_ h, fun h => rej 2 (by decide) ?_⟩
        · have : x1 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_neg h01, if_pos h12, if_pos h02]
        · have : x1 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
      · have hs' := mergeSort3 x0 x1 x2 x1 x2 x0 (perm3_4 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 4 (by decide) ?_ hs' ?_ h, fun h => rej 3 (by decide) ?_⟩
        · have : x2 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_neg h01, if_pos h12, if_neg h02]
        · have : x2 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
    · have hs' := mergeSort3 x0 x1 x2 x2 x1 x0 (perm3_5 x0 x1 x2) (by omega) (by omega)
      have hk := hok _ _ _ hs'
      refine ⟨fun h => acc 5 (by decide) ?_ hs' ?_ h, fun h => ?_⟩
      · have : x2 < x1 ∧ x1 < x0 := by rw [hk] at h; simp at h; omega
        simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp; omega
      · simp only [selPath, if_neg h01, if_neg h12]
      · by_cases h21 : x2 = x1
        · apply rej 4 (by decide)
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · have : x1 = x0 := by rw [hk] at h; simp at h; omega
          apply rej 5 (by decide)
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)

/-! ## The setup block -/

theorem idxE_eval (a : HashOutput) (s : MachineState)
    (h0 : s.getMem (BitVec.ofNat 64 0x60) = a.extractLsb' 0 64) :
    idxE.eval s = BitVec.ofNat 64 (a.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [idxE, nE, E.eval, show 0x60 + 8 * 0 = 0x60 by rfl, h0]
  rw [srl_toNat _ 33 (by decide), sll_toNat _ 33 (by decide), BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega

theorem sel_setup (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (hu : DgOut m pk w a u) : ∃ t, Steps image u 6 6 t ∧ SelIn pk w a 0 t := by
  have hk : KnownOK selK u := selK_of (hu.known.mono (fun p hp => by simp [proPost]; exact Or.inl hp)) hu.sp
  obtain ⟨t, ht⟩ := spec_run (show specB [] [] baseK (runAt selK [22] 16 []) setupSpec [] selK [] = true
    from setupCheck_ok) u hu.pc hk (by simp [setupSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  refine ⟨t, ht.steps, ⟨by rw [ht.pc rfl]; rfl, selK_base ht.known, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, selK_sp ht.known⟩⟩
  · intro k hk'
    have r16 : t.getReg .x16 = (nE 0).eval u := ht.regs (.x16, nE 0) (by simp [setupSpec])
    have r17 : t.getReg .x17 = (nE 1).eval u := ht.regs (.x17, nE 1) (by simp [setupSpec])
    have r27 : t.getReg .x27 = (nE 2).eval u := ht.regs (.x27, nE 2) (by simp [setupSpec])
    have r28 : t.getReg .x28 = (nE 3).eval u := ht.regs (.x28, nE 3) (by simp [setupSpec])
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · show t.getReg .x16 = _; rw [r16]; exact hu.nwords 0 (by decide)
    · show t.getReg .x17 = _; rw [r17]; exact hu.nwords 1 (by decide)
    · show t.getReg .x27 = _; rw [r27]; exact hu.nwords 2 (by decide)
    · show t.getReg .x28 = _; rw [r28]; exact hu.nwords 3 (by decide)
  · have r22 : t.getReg .x22 = idxE.eval u := ht.regs (.x22, idxE) (by simp [setupSpec])
    rw [r22]
    exact idxE_eval a u (hu.nwords 0 (by decide))
  · intro c' k hc' _; omega
  · intro c' hc'; omega
  · intro j hj; rw [hmem]; exact hu.wit j hj
  · exact ⟨(hmem _).trans hu.pk.1, (hmem _).trans hu.pk.2⟩
  · intro A hA hz _; rw [hmem]; exact hu.zero A hA hz
  · exact hu.data.congr (fun A _ _ => hmem _)

/-! ## All seven coordinates -/

theorem selCost_le (a : HashOutput) (c : Nat) : selCost a c ≤ 23 := by
  unfold selCost selExt selTree; split <;> split <;> omega

theorem sumTo_selCost_le (a : HashOutput) : ∀ n, sumTo (selCost a) n ≤ 23 * n
  | 0 => by simp [sumTo]
  | n + 1 => by simp only [sumTo]; have := selCost_le a n; have := sumTo_selCost_le a n; omega

theorem sel_prefix (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) (hs : SelIn pk w a 0 s) :
    ∀ n, n ≤ 7 →
      (∃ u, Steps image s (sumTo (selCost a) n) (sumTo (selCost a) n) u ∧ SelIn pk w a n u) ∨
      (∃ u k, Steps image s k k u ∧ k ≤ 23 * n ∧ Halt1 u ∧ ∃ c, c < n ∧ selOk1 (selC a c) = false) := by
  intro n
  induction n with
  | zero => intro _; exact Or.inl ⟨s, Steps.refl s, hs⟩
  | succ n ih =>
    intro hn
    rcases ih (by omega) with ⟨u, hst, hu⟩ | ⟨u, k, hst, hk, hh, c, hc, hc'⟩
    · obtain ⟨hacc, hrej⟩ := sel_step pk w a n (by omega) u hu
      cases hok : selOk1 (selC a n)
      · obtain ⟨v, k, hst', hk, hh⟩ := hrej hok
        right
        have := sumTo_selCost_le a n
        exact ⟨v, _, hst.trans hst', by omega, hh, n, by omega, hok⟩
      · obtain ⟨v, hst', hv⟩ := hacc hok
        left
        exact ⟨v, (hst.trans hst').of_eq (by simp [sumTo]) (by simp [sumTo]), hv⟩
    · right; exact ⟨u, k, hst, by omega, hh, c, by omega, hc'⟩

theorem selectionsOk_iff (a : HashOutput) :
    selectionsOk (selections a) = true ↔ ∀ c, c < 7 → selOk1 (selC a c) = true := by
  rw [selectionsOk_eq, List.all_eq_true]
  have hl := selections_length a
  constructor
  · intro h c hc
    apply h
    simp only [selC, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c < (selections a).length),
      Option.getD_some]
    exact List.getElem_mem _
  · intro h x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp hx
    have := h c (by omega)
    simp only [selC, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at this
    exact this

/-- The cycles of the seven accepting coordinates (`≤ 153`; `P = Σ selTree ≤ 56`). -/
def selCostAll (a : HashOutput) : Nat := sumTo (selCost a) 7

theorem selCostAll_le (a : HashOutput) : selCostAll a ≤ 153 := by
  have h : ∀ c, selCost a c ≤ selExt c + 20 := fun c => by
    unfold selCost selTree; split <;> omega
  have e0 : selExt 0 = 1 := rfl
  have e1 : selExt 1 = 3 := rfl
  have e2 : selExt 2 = 1 := rfl
  have e3 : selExt 3 = 3 := rfl
  have e4 : selExt 4 = 1 := rfl
  have e5 : selExt 5 = 1 := rfl
  have e6 : selExt 6 = 3 := rfl
  unfold selCostAll
  simp only [sumTo]
  have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5; have := h 6
  omega

theorem select_phase (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) (hs : SelIn pk w a 0 s) :
    (selectionsOk (selections a) = true →
      ∃ u, Steps image s (selCostAll a) (selCostAll a) u ∧ SelIn pk w a 7 u) ∧
    (selectionsOk (selections a) = false → ∃ u k, Steps image s k k u ∧ k ≤ 161 ∧ Halt1 u) := by
  constructor
  · intro h
    rcases sel_prefix pk w a s hs 7 (le_refl _) with hu | ⟨u, k, _, _, _, c, hc, hc'⟩
    · exact hu
    · rw [(selectionsOk_iff a).mp h c hc] at hc'; cases hc'
  · intro h
    rcases sel_prefix pk w a s hs 7 (le_refl _) with ⟨u, _, hu⟩ | ⟨u, k, hst, hk, hh, _⟩
    · have : selectionsOk (selections a) = true := (selectionsOk_iff a).mpr hu.ok
      rw [this] at h; cases h
    · exact ⟨u, k, hst, by omega, hh⟩

/-! ## The selection piece of `verifyP` -/

/-- `verifyP` after the selection check: the FTS, the layers, the comparison. -/
def afterFts (pk : Digest) (w : WBytes) (index : Nat) (r : Option Digest) : T3.M Bool :=
  match r with
  | some root => do
      let __x ← layersP w index 4 root
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false

def afterSel (pk : Digest) (w : WBytes) (N : HashOutput) : T3.M Bool :=
  if !T3.digestGate N then pure false else
  ftsP w (N.toNat % 2 ^ 31) (selections N) >>= afterFts pk w (N.toNat % 2 ^ 31)

/-- `verifyP` as digest, selection check and `afterSel`. -/
theorem verifyP_eq (m : T3.Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = (digestP m w >>= fun o => match o with
      | some N => if (!selectionsOk (selections N)) = true then pure false else afterSel pk w N
      | none => pure false) := by
  unfold verifyP afterSel afterFts
  congr 1; funext o
  cases o <;> rfl

theorem select_good (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (hu : DgOut m pk w a u) {N C A : Nat} {Q : Prop} (REST : T3.M Bool) (K : Bool → OracleComp HashSpec Obs)
    (hK : K false = pure (false, 0))
    (hrest : ∀ t, SelIn pk w a 7 t → GoodQ t N C Q A (ccM REST K)) :
    GoodQ u (N + 168) (C + 168) Q (A + 159)
      (ccM (if (!selectionsOk (selections a)) = true then pure false else REST) K) := by
  obtain ⟨t0, hst0, ht0⟩ := sel_setup m pk w a u hu
  obtain ⟨hacc, hrej⟩ := select_phase pk w a t0 ht0
  have hle := selCostAll_le a
  cases hsel : selectionsOk (selections a)
  · simp only [Bool.not_false, if_true, ccM_pure, hK]
    obtain ⟨v, k, hst, hk, hh⟩ := hrej hsel
    exact GoodQ.steps' (hst0.trans hst) (GoodQ.reject (Q := False) (A := 0) hh.1 hh.2.1 hh.2.2)
      (by omega) (by omega) (fun q => q.elim)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨v, hst, hv⟩ := hacc hsel
    exact GoodQ.steps' (hst0.trans hst) (hrest v hv) (by omega) (by omega) (fun q => ⟨q, by omega⟩)

/-- **`verifyP` up to the FTS**: from the initial state, given the judgment of `afterSel` on every state at
`fts_setup` (word 359). -/
theorem verifyP_good_sel (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s)
    {N C A : Nat} {Q : Prop}
    (hfts : ∀ a t, SelIn pk w a 7 t → GoodQ t N C Q A (ccM (afterSel pk w a) Kb)) :
    GoodQ s (N + 185) (C + 192) Q (A + 182) (ccM (verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  have := digestP_good m pk w s hs (N := N + 168) (C := C + 168) (A := A + 159) (Q := Q)
    (fun o => ccM (match o with
      | some N => if (!selectionsOk (selections N)) = true then pure false else afterSel pk w N
      | none => pure false) Kb) (by simp [Kb])
    (fun a u hu => select_good m pk w a u hu (afterSel pk w a) Kb rfl (hfts a))
  exact this.mono (by omega) (by omega) (fun q => ⟨q, by omega⟩)

end SigGolfCandidate.T3M.Verify
