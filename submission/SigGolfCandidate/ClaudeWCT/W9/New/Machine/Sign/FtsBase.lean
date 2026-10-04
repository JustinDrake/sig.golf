import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheck

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
section pres
variable (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k : Nat)
  (brs : List Br) (s : MachineState)
theorem pres_pc : ((pres regs mem obl pc ec k brs).toState s).pc = pcOf pc := rfl
theorem pres_getReg (x : Reg) :
    ((pres regs mem obl pc ec k brs).toState s).getReg x = ((regsOf regs).get x).eval s :=
  SymState.toState_getReg _ _ _ _
theorem pres_getMem (a : Word) : ((pres regs mem obl pc ec k brs).toState s).getMem a = memEval s mem a := rfl
theorem pres_steps : (pres regs mem obl pc ec k brs).steps = k := rfl
theorem pres_cycles : (pres regs mem obl pc ec k brs).cycles = k := rfl
theorem pres_ecall : (pres regs mem obl pc ec k brs).ecall = ec := rfl
theorem pres_obl : (pres regs mem obl pc ec k brs).st.obl = obl := rfl
theorem pres_brs : (pres regs mem obl pc ec k brs).brs = brs := rfl
end pres
theorem foldl_set_get_ne (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    ∀ rf : RegFile, (l.foldl (fun rf p => rf.set p.1 p.2) rf).get x = rf.get x := by
  induction l with
  | nil => intro rf; rfl
  | cons p l ih =>
    intro rf
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), RegFile.get_set_ne _ _ (fun he => h p (by simp) he.symm)]
theorem regsOf_get_ne (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    (regsOf l).get x = RegFile.init.get x := foldl_set_get_ne l x h _
theorem pres_regsExcept (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k : Nat)
    (brs : List Br) (s : MachineState) :
    RegsExcept s ((pres regs mem obl pc ec k brs).toState s) (regs.map Prod.fst) := by
  intro x hx
  rw [pres_getReg, regsOf_get_ne _ _ (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem memEval_mwc (s : MachineState) (a A : Nat) (e : E) (ws : SymMem) (hA : A < 2 ^ 64) (ha : a < 2 ^ 64) :
    memEval s (mwc a e :: ws) (BitVec.ofNat 64 A) = if A = a then e.eval s else memEval s ws (BitVec.ofNat 64 A) :=
  memEval_cons_ofNat s a A e ws hA ha
theorem memEval_nil' (s : MachineState) (a : Word) : memEval s [] a = s.getMem a := rfl
set_option maxRecDepth 100000 in
theorem pathIdx_eq : ∀ sel, sel < 128 → ∀ l, l < 7 → (sel + 128) / 2 ^ l ^^^ 1 = 2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) := by
  decide +kernel
theorem ofNat_or_hi (lo hi : Nat) (hlo : lo < 2 ^ 32) :
    BitVec.ofNat 64 (hi * 2 ^ 32) ||| BitVec.ofNat 64 lo = BitVec.ofNat 64 (lo + 2 ^ 32 * hi) := by
  rw [ofNat_or_add lo hi 32 hlo]; congr 1; ring
theorem eval_bin (s : MachineState) (op : BinOp) (a b : E) : (E.bin op a b).eval s = op.eval (a.eval s) (b.eval s) :=
  rfl
theorem eval_cE (s : MachineState) (n : Nat) : (cE n).eval s = BitVec.ofNat 64 n := rfl
theorem binop_sll (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem binop_srl (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem ofNat_shl_lt (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := ofNat_shl a k
theorem eval_w1E (s : MachineState) {j index : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    w1E.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * j) := by
  show BinOp.eval .or (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [binop_sll _ _ (by norm_num), h18, h22, ofNat_shl]
  exact ofNat_or_hi index j hidx
theorem eval_x18x4 (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    x18x4.eval s = BitVec.ofNat 64 (4 * j) := by
  show s.getReg .x18 + s.getReg .x18 + s.getReg .x18 + s.getReg .x18 = _
  rw [h18, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat]; congr 1; ring
theorem eval_privW1E (s : MachineState) {j index : Nat} (p : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    (privW1E p).eval s = BitVec.ofNat 64 (index + 2 ^ 32 * (4 * j + p)) := by
  have hx : (if p = 0 then x18x4 else .bin .add x18x4 (cE p)).eval s = BitVec.ofNat 64 (4 * j + p) := by
    split_ifs with hp
    · subst hp; exact eval_x18x4 s h18
    · show BinOp.eval .add (x18x4.eval s) (BitVec.ofNat 64 p) = _
      rw [eval_x18x4 s h18]; exact ofNat_add_ofNat _ _
  show BinOp.eval .or (BinOp.eval .sll ((if p = 0 then x18x4 else .bin .add x18x4 (cE p)).eval s)
    (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [binop_sll _ _ (by norm_num), hx, h22, ofNat_shl]
  exact ofNat_or_hi index _ hidx
theorem eval_dE (s : MachineState) {w : Nat} (i : Nat) (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64)
    (hi : 2 * i < 64) : (dE i).eval s = BitVec.ofNat 64 (3 - w / 4 ^ i % 4) := by
  show BinOp.eval .sub (BitVec.ofNat 64 3) (BinOp.eval .and (BinOp.eval .srl (s.getReg .x25)
    (BitVec.ofNat 64 (2 * i))) (BitVec.ofNat 64 3)) = _
  rw [binop_srl _ _ hi, h25]
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : Nat) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
  have h3 : w / 4 ^ i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [BinOp.eval, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hw, ← h4]
  have e : w / 4 ^ i &&& 3 = w / 4 ^ i % 4 := by
    rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (show 3 < 2 ^ 64 by norm_num), e]
  omega
theorem eval_x18p1 (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    x18p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x18 + BitVec.ofNat 64 1 = _
  rw [h18, ofNat_add_ofNat]
theorem eval_x18m1 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : 1 ≤ h)
    (hh' : h < 2 ^ 64) : x18m1.eval s = BitVec.ofNat 64 (h - 1) := by
  show s.getReg .x18 + BitVec.ofNat 64 (2 ^ 64 - 1) = _
  rw [h18, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem eval_sll_reg (s : MachineState) {x : Reg} {a : Nat} (hx : s.getReg x = BitVec.ofNat 64 a) (k : Nat)
    (hk : k < 64) : (E.bin .sll (.reg x) (cE k)).eval s = BitVec.ofNat 64 (a * 2 ^ k) := by
  show BinOp.eval .sll (s.getReg x) (BitVec.ofNat 64 k) = _
  rw [binop_sll _ _ hk, hx, ofNat_shl]
theorem eval_sh5 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    sh5.eval s = BitVec.ofNat 64 (32 * h) := by
  rw [sh5, eval_sll_reg s h18 5 (by norm_num)]; congr 1; ring
theorem eval_sh4 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    sh4.eval s = BitVec.ofNat 64 (16 * h) := by
  rw [sh4, eval_sll_reg s h18 4 (by norm_num)]; congr 1; ring
theorem eval_heapLeafE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    heapLeafE.eval s = BitVec.ofNat 64 (16 * (j + 128)) := by
  show BinOp.eval .sll (s.getReg .x18 + BitVec.ofNat 64 128) (BitVec.ofNat 64 4) = _
  rw [binop_sll _ _ (by norm_num), h18, ofNat_add_ofNat, ofNat_shl,
    show (j + 128) * 2 ^ 4 = 16 * (j + 128) by ring]
theorem eval_pathE (s : MachineState) {sel : Nat} (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (hsel : sel < 128)
    (l : Nat) (hl : l < 7) : (pathE l).eval s = BitVec.ofNat 64 (16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1))) := by
  show BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .srl (s.getReg .x24 + BitVec.ofNat 64 128) (BitVec.ofNat 64 l))
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 4) = _
  rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by omega), h24, ofNat_add_ofNat,
    ofNat_shr _ _ (by omega)]
  simp only [BinOp.eval]
  rw [show BitVec.ofNat 64 ((sel + 128) / 2 ^ l) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 ((sel + 128) / 2 ^ l ^^^ 1) by
    apply BitVec.eq_of_toNat_eq
    have h1 : (sel + 128) / 2 ^ l < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have h2 : (sel + 128) / 2 ^ l ^^^ 1 < 2 ^ 64 := Nat.xor_lt_two_pow h1 (by norm_num)
    simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2],
    pathIdx_eq sel hsel l hl, ofNat_shl]
  congr 1; ring
theorem chainK_lt (c i : Nat) (hc : c < 9) (hi : i < 7) : chainK c i < 2 ^ 20 := by unfold chainK; omega
theorem eval_qE (s : MachineState) {c i j index : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128) (hk : chainK c i < 2 ^ 20) :
    (qE c i).eval s = BitVec.ofNat 64 (index * 2 ^ 27 + j * 2 ^ 20 + chainK c i) := by
  show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 27))
    (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 20))) (BitVec.ofNat 64 (chainK c i)) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), h18, h22, ofNat_shl, ofNat_shl]
  simp only [BinOp.eval]
  rw [ofNat_or_add (j * 2 ^ 20) index 27 (by omega),
    show index * 2 ^ 27 + j * 2 ^ 20 = (index * 2 ^ 7 + j) * 2 ^ 20 by ring,
    ofNat_or_add (chainK c i) (index * 2 ^ 7 + j) 20 hk]
theorem nodeK_lt (c : Nat) (hc : c < 9) : nodeK c < 2 ^ 32 := by unfold nodeK; omega
theorem eval_nodeLoE (s : MachineState) {c index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hk : nodeK c < 2 ^ 32) :
    (nodeLoE c).eval s = BitVec.ofNat 64 (nodeK c + 2 ^ 32 * index) := by
  show BinOp.eval .or (BitVec.ofNat 64 (nodeK c)) (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 32)) = _
  rw [binop_sll _ _ (by norm_num), h22, ofNat_shl]
  simp only [BinOp.eval]
  rw [BitVec.or_comm, ofNat_or_add (nodeK c) index 32 hk]
  all_goals (congr 1; ring)
theorem replaceByte_toNat8 (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
end ClaudeWCT.W9.Machine.Sign
