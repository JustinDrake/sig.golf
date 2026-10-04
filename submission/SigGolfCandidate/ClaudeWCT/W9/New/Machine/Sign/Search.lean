import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Common
section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def mw (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def fs : List Nat := [2099,2111,2122,2134,2146,2157,2169,2181,2192,2204]
def fsi (k : Nat) : Nat := fs.getD k 0
def dw (k : Nat) : Nat := WCT9.coordBase k / 64
def sh (k : Nat) : Nat := WCT9.coordBase k % 64
def resH153 : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 2074, false, 1, 1, [], none⟩
def resHead (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst (2 ^ 21))], [], []⟩, if d then pcOf 2078 else pcOf 2212, false,
    if d then 3 else 4, if d then 3 else 4, [⟨.ltu, .reg .x19, cst (2 ^ 21), d⟩], none⟩
def ctrE : E := .bin .sll (.reg .x19) (cst 32)
def resTrial : PRes :=
  ⟨⟨rfs [(.x6, ctrE), (.x10, cst DIG), (.x11, cst 64), (.x12, cst NBUF), (.x28, cst DIG)],
    [mw (DIG + 24) ctrE, mw (DIG + 16) (cst 3073)], []⟩, pcOf 2090, true, 12, 12, [], none⟩
def gateE : E := .bin .and (.bin .srl (.ld (cst NBUF)) (cst 31)) (cst 4095)
def resGate (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, gateE), (.x7, cst 4095), (.x22, .ld (cst NBUF)), (.x28, cst NBUF)], [], []⟩,
    if d then pcOf 2210 else pcOf 2099, false, 8, 8, [⟨.ne, gateE, .c 0, d⟩], none⟩
def grpE (k : Nat) : E :=
  if sh k = 0 then .ld (cst (NBUF + 8 * dw k)) else .bin .srl (.ld (cst (NBUF + 8 * dw k))) (cst (sh k))
def fieldE (k : Nat) : E := .bin .and (.bin .srl (grpE k) (cst 7)) (cst 16383)
def fieldLen (k : Nat) : Nat := if sh k = 0 then 11 else 12
def resField (k : Nat) (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst 16016), (.x24, .bin .and (grpE k) (cst 127)), (.x25, fieldE k), (.x28, cst NBUF)], [], []⟩,
    if d then pcOf 2210 else pcOf (fsi (k + 1)), false, fieldLen k, fieldLen k,
    [⟨.geu, fieldE k, cst 16016, d⟩], none⟩
def idxE : E := .bin .srl (.bin .sll (.reg .x22) (cst 33)) (cst 33)
def resFinal : PRes :=
  ⟨⟨rfs [(.x22, idxE), (.x28, cst IDXV)], [mw IDXV idxE], []⟩, pcOf 2215, false, 6, 6, [], none⟩
def resNext : PRes :=
  ⟨⟨rfs [(.x19, .bin .add (.reg .x19) (cst 1))], [], []⟩, pcOf 2074, false, 2, 2, [], none⟩
def resFail : PRes :=
  ⟨⟨rfs [(.x5, cst 1), (.x10, cst 1)], [], []⟩, pcOf 2214, true, 2, 2, [], none⟩
theorem chk_h153 : optBeq (run hookLook [2074] 153 []) resH153 = true := by decide +kernel
theorem chk_head : (optBeq (run headLook [2078, 2212] 2074 [.br true]) (resHead true) &&
    optBeq (run headLook [2078, 2212] 2074 [.br false]) (resHead false)) = true := by decide +kernel
theorem chk_trial : optBeq (run headLook [] 2078 []) resTrial = true := by decide +kernel
theorem chk_gate : (optBeq (run headLook [2210, 2099] 2091 [.br true]) (resGate true) &&
    optBeq (run headLook [2210, 2099] 2091 [.br false]) (resGate false)) = true := by decide +kernel
theorem chk_fields : (List.range 9).all (fun k =>
    optBeq (run headLook [2210, fsi (k + 1)] (fsi k) [.br true]) (resField k true) &&
    optBeq (run headLook [2210, fsi (k + 1)] (fsi k) [.br false]) (resField k false)) = true := by
  decide +kernel
theorem chk_final : optBeq (run headLook [2215] 2204 []) resFinal = true := by decide +kernel
theorem chk_next : optBeq (run headLook [2074] 2210 []) resNext = true := by decide +kernel
theorem chk_fail : optBeq (run headLook [] 2212 []) resFail = true := by decide +kernel
theorem run_h153 : run hookLook [2074] 153 [] = some resH153 := optBeq_eq chk_h153
theorem run_head (d : Bool) : run headLook [2078, 2212] 2074 [.br d] = some (resHead d) := by
  have h := chk_head
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_trial : run headLook [] 2078 [] = some resTrial := optBeq_eq chk_trial
theorem run_gate (d : Bool) : run headLook [2210, 2099] 2091 [.br d] = some (resGate d) := by
  have h := chk_gate
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_field (k : Nat) (hk : k < 9) (d : Bool) :
    run headLook [2210, fsi (k + 1)] (fsi k) [.br d] = some (resField k d) := by
  have h := List.all_eq_true.mp chk_fields k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_final : run headLook [2215] 2204 [] = some resFinal := optBeq_eq chk_final
theorem run_next : run headLook [2074] 2210 [] = some resNext := optBeq_eq chk_next
theorem run_fail : run headLook [] 2212 [] = some resFail := optBeq_eq chk_fail
end ClaudeWCT.W9.Machine.Sign.SearchM
end
section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3 (Digest HashOutput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem rfs_get_other (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    (rfs l).get x = RegFile.init.get x := by
  unfold rfs
  suffices ∀ rf : RegFile, (l.foldl (fun rf p => rf.set p.1 p.2) rf).get x = rf.get x from this _
  induction l with
  | nil => intro rf; rfl
  | cons p l ih =>
    intro rf
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), RegFile.get_set_ne _ _ (Ne.symm (h p (by simp)))]
theorem piece {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat} {n : Nat}
    {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState) (hpc : s.pc = pcOf n)
    (hobl : r.st.obl = []) (hbr : ∀ b ∈ r.brs, b.holds s) (hspc : r.spc = none) :
    Steps im s r.steps r.cycles (r.toState s) ∧ (r.toState s).pc = r.pc ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) ∧
      (∀ x, (r.toState s).getReg x = (r.st.regs.get x).eval s) ∧
      (∀ a, (r.toState s).getMem a = memEval s r.st.mem a) := by
  obtain ⟨h1, h2⟩ := run_sound hl h s hpc (by rw [hobl]; intro o ho; cases ho) hbr
  exact ⟨h1, PRes.toState_pc' r s hspc, h2, fun x => PRes.toState_getReg' r s x,
    fun a => PRes.toState_getMem' r s a⟩
theorem regs_rfs {t s : MachineState} {l : List (Reg × E)} (h : ∀ x, t.getReg x = ((rfs l).get x).eval s) :
    RegsExcept s t (l.map Prod.fst) := by
  intro x hx
  rw [h x, rfs_get_other l x (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem mod64_div_mod (x p q : Nat) (h : p + q ≤ 64) : x % 2 ^ 64 / 2 ^ p % 2 ^ q = x / 2 ^ p % 2 ^ q := by
  have e : (2 : Nat) ^ 64 = 2 ^ p * 2 ^ (64 - p) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
theorem ofNat_and_mask (x : Word) (q : Nat) (hq : q ≤ 64) :
    x &&& BitVec.ofNat 64 (2 ^ q - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ q) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (2 : Nat) ^ q - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hq; omega
  have h2 : x.toNat % 2 ^ q < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) hq)
  rw [BitVec.toNat_and, toNat_ofNat_lt h1, Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat_lt h2]
theorem and_eval (x y : Word) : BinOp.eval .and x y = x &&& y := rfl
theorem ofNat_bne_zero (g : Nat) (hg : g < 2 ^ 64) : (BitVec.ofNat 64 g != 0#64) = decide (g ≠ 0) := by
  by_cases h : g = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 g ≠ 0#64 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [toNat_ofNat_lt hg] at this
      exact h this
    simp [h, this]
theorem srl_eval (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, toNat_ofNat_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
theorem shl33_shr33' (w : Word) : (w <<< 33) >>> 33 = BitVec.ofNat 64 (w.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega
theorem sh_bound (k : Nat) (hk : k < 9) : sh k + 21 ≤ 64 ∧ 64 * dw k + sh k = WCT9.coordBase k ∧ dw k < 4 := by
  interval_cases k <;> decide
theorem gateE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) :
    gateE.eval s = BitVec.ofNat 64 (a.toNat / 2 ^ 31 % 2 ^ 12) := by
  have h0 := ha 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  simp only [gateE, cst, E.eval, h0]
  rw [srl_eval _ 31 (by decide), and_eval, show (4095 : Nat) = 2 ^ 12 - 1 from rfl, ofNat_and_mask _ 12 (by decide)]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    mod64_div_mod _ 31 12 (by decide)]
theorem grpE_toNat (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    ((grpE k).eval s).toNat = a.toNat / 2 ^ (64 * dw k) % 2 ^ 64 / 2 ^ sh k := by
  obtain ⟨h21, -, hd⟩ := sh_bound k hk
  have hm := ha (dw k) hd
  unfold grpE
  split_ifs with h0
  · simp only [cst, E.eval, hm, h0, pow_zero, Nat.div_one, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  · simp only [cst, E.eval, hm]
    rw [srl_eval _ _ (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
theorem fieldE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (fieldE k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ (WCT9.coordBase k + 7) % 2 ^ 14) := by
  obtain ⟨h21, hcb, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  simp only [fieldE, cst, E.eval]
  rw [srl_eval _ 7 (by decide), and_eval, show (16383 : Nat) = 2 ^ 14 - 1 from rfl, ofNat_and_mask _ 14 (by decide)]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hg, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    mod64_div_mod _ (sh k + 7) 14 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega
section pieces
variable {im : Image}
theorem h153_spec (hl : LookOK im hookLook) (s : MachineState) (hpc : s.pc = pcOf 153) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 2074 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_h153 s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem head_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2074) (i : Nat)
    (hi : i ≤ 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ t.pc = (if i < 2 ^ 21 then pcOf 2078 else pcOf 2212) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (resHead (decide (i < 2 ^ 21))).brs, b.holds s := by
    intro b hb
    simp only [resHead, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h19, BitVec.ult, toNat_ofNat_lt (by omega : i < 2 ^ 64),
      toNat_ofNat_lt (by decide : 2 ^ 21 < 2 ^ 64)]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_head _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · simp only [resHead]; split <;> decide
  · rw [hp]; simp only [resHead]; by_cases h : i < 2 ^ 21 <;> simp [h]
theorem trial_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2078) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 12 12 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 2090 ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 3073 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 (i * 2 ^ 32) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 24 ∨ A = DIG + 16) := by
  obtain ⟨hs, hp, he, hr, hm⟩ := piece hl run_trial s hpc rfl (by intro b hb; cases hb) rfl
  have hctr : ctrE.eval s = BitVec.ofNat 64 (i * 2 ^ 32) := by
    simp only [ctrE, cst, E.eval, BinOp.eval, h19, toNat_ofNat_lt (by decide : (32 : Nat) < 2 ^ 64)]
    exact ofNat_shl i 32
  refine ⟨_, hs, he rfl, hp, by rw [hr]; rfl, by rw [hr]; rfl, by rw [hr]; rfl, ?_, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_neg (by decide),
      memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl]; rfl
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hctr]
  · intro A hA hn
    simp only [not_or] at hn
    rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), if_neg hn.1, memEval_cons_ofNat _ _ _ _ _ hA (by decide),
      if_neg hn.2]; rfl
theorem gate_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2091) (a : BitVec 256)
    (ha : OutAt s NBUF a) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = (if a.toNat / 2 ^ 31 % 2 ^ 12 = 0 then pcOf 2099 else pcOf 2210) ∧
      t.getReg .x22 = a.extractLsb' 0 64 ∧ RegsExcept s t [.x6, .x7, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  have hg := gateE_eval s a ha
  have hlt : a.toNat / 2 ^ 31 % 2 ^ 12 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hbr : ∀ b ∈ (resGate (decide (a.toNat / 2 ^ 31 % 2 ^ 12 ≠ 0))).brs, b.holds s := by
    intro b hb
    simp only [resGate, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hg]
    exact ofNat_bne_zero _ hlt
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_gate _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · rw [hp]; simp only [resGate]
    by_cases h0 : a.toNat / 2 ^ 31 % 2 ^ 12 = 0 <;> simp [h0]
  · rw [hr]
    have h0 := ha 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    show s.getMem (BitVec.ofNat 64 NBUF) = _
    exact h0
theorem field_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState)
    (hpc : s.pc = pcOf (fsi k)) (a : BitVec 256) (ha : OutAt s NBUF a) :
    ∃ t c, Steps im s c c t ∧ c ≤ 12 ∧
      t.pc = (if WCT9.field a ⟨k, hk⟩ < 16016 then pcOf (fsi (k + 1)) else pcOf 2210) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  have hf := fieldE_eval s a ha k hk
  have hfd : WCT9.field a ⟨k, hk⟩ = a.toNat / 2 ^ (WCT9.coordBase k + 7) % 2 ^ 14 := rfl
  have hlt : a.toNat / 2 ^ (WCT9.coordBase k + 7) % 2 ^ 14 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hbr : ∀ b ∈ (resField k (decide ¬ (WCT9.field a ⟨k, hk⟩ < 16016))).brs, b.holds s := by
    intro b hb
    simp only [resField, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, hf, BitVec.ult, toNat_ofNat_lt hlt,
      toNat_ofNat_lt (by decide : 16016 < 2 ^ 64), hfd]
    rw [decide_not]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_field k hk _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · simp only [resField, fieldLen]; split <;> omega
  · rw [hp]; simp only [resField]
    by_cases h : WCT9.field a ⟨k, hk⟩ < 16016 <;> simp [h]
theorem final_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2204) (a : BitVec 256)
    (h22 : s.getReg .x22 = a.extractLsb' 0 64) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 2215 ∧ t.getReg .x22 = BitVec.ofNat 64 (a.toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (a.toNat % 2 ^ 31) ∧
      RegsExcept s t [.x22, .x28] ∧ Frame s t (fun A => A = IDXV) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_final s hpc rfl (by intro b hb; cases hb) rfl
  have hidx : idxE.eval s = BitVec.ofNat 64 (a.toNat % 2 ^ 31) := by
    simp only [idxE, cst, E.eval, BinOp.eval, h22, toNat_ofNat_lt (by decide : (33 : Nat) < 2 ^ 64)]
    rw [shl33_shr33', BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 31 ≤ 64))]
  refine ⟨_, hs, hp, by rw [hr]; exact hidx, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hidx]
  · intro A hA hn
    rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), if_neg hn]; rfl
theorem next_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2210) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 2074 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_next s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]
  show s.getReg .x19 + BitVec.ofNat 64 1 = _
  rw [h19, ofNat_add_ofNat]
theorem fail_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 2212) :
    ∃ t, Steps im s 2 2 t ∧ fetch im t = some (.base .ECALL) ∧ FailedS t := by
  obtain ⟨hs, hp, he, hr, -⟩ := piece hl run_fail s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, he rfl, ⟨hp, by rw [hr]; rfl, by rw [hr]; rfl⟩⟩
theorem fields_from (hl : LookOK im headLook) (a : BitVec 256) :
    ∀ n k, k + n = 9 → ∀ v : MachineState, v.pc = pcOf (fsi k) → OutAt v NBUF a →
      ∃ t c, Steps im v c c t ∧ c ≤ 12 * n ∧ RegsExcept v t [.x6, .x24, .x25, .x28] ∧
        Frame v t (fun _ => False) ∧
        t.pc = (if ∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16016 then pcOf 2204 else pcOf 2210) := by
  intro n
  induction n with
  | zero =>
    intro k hk v hv _
    refine ⟨v, 0, Steps.refl v, le_refl _, RegsExcept.refl _ _, Frame.refl _ _, ?_⟩
    rw [if_pos (fun k' hk' hle => by omega), hv]
    rw [show k = 9 by omega]; rfl
  | succ n ih =>
    intro k hk v hv ha
    have hk9 : k < 9 := by omega
    obtain ⟨t1, c1, s1, hc1, p1, r1, f1⟩ := field_spec hl k hk9 v hv a ha
    by_cases hf : WCT9.field a ⟨k, hk9⟩ < 16016
    · rw [if_pos hf] at p1
      have ha1 : OutAt t1 NBUF a := fun j hj => by rw [f1.get (by simp only [NBUF]; omega) (fun h => h)]; exact ha j hj
      obtain ⟨t, c, s2, hc, r2, f2, p2⟩ := ih (k + 1) (by omega) t1 p1 ha1
      refine ⟨t, c1 + c, s1.trans s2, by omega, (r1.trans r2).mono (by decide),
        (f1.trans f2).mono (fun _ _ h => by simp at h), ?_⟩
      rw [p2]
      congr 1
      apply propext
      constructor
      · intro h k' hk' hle
        by_cases he : k' = k
        · subst he; exact hf
        · exact h k' hk' (by omega)
      · intro h k' hk' hle
        exact h k' hk' (by omega)
    · rw [if_neg hf] at p1
      refine ⟨t1, c1, s1, by omega, r1, f1, ?_⟩
      rw [p1, if_neg (fun h => hf (h k hk9 le_rfl))]
theorem checks_spec (hl : LookOK im headLook) (u : MachineState) (hpc : u.pc = pcOf 2091) (a : BitVec 256)
    (ha : OutAt u NBUF a) :
    ∃ t c, Steps im u c c t ∧ c ≤ 116 ∧ RegsExcept u t [.x6, .x7, .x22, .x24, .x25, .x28] ∧
      Frame u t (fun _ => False) ∧
      (if WCT9.admissible a = true then t.pc = pcOf 2204 ∧ t.getReg .x22 = a.extractLsb' 0 64
        else t.pc = pcOf 2210) := by
  obtain ⟨t1, s1, p1, x22, r1, f1⟩ := gate_spec hl u hpc a ha
  have hadm := WCT9.admissible_iff a
  by_cases hg : a.toNat / 2 ^ 31 % 2 ^ 12 = 0
  · rw [if_pos hg] at p1
    have ha1 : OutAt t1 NBUF a := fun j hj => by rw [f1.get (by simp only [NBUF]; omega) (fun h => h)]; exact ha j hj
    obtain ⟨t, c, s2, hc, r2, f2, p2⟩ := fields_from hl a 9 0 rfl t1 p1 ha1
    refine ⟨t, 8 + c, s1.trans s2, by omega, (r1.trans r2).mono (by decide),
      (f1.trans f2).mono (fun _ _ h => by simp at h), ?_⟩
    have hall : (∀ k' (hk' : k' < 9), 0 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16016) ↔ WCT9.admissible a = true := by
      rw [hadm]
      constructor
      · intro h; exact ⟨hg, fun coord => h coord.val coord.isLt (Nat.zero_le _)⟩
      · intro h k' hk' _; exact h.2 ⟨k', hk'⟩
    by_cases hA : WCT9.admissible a = true
    · rw [if_pos hA]
      rw [if_pos (hall.2 hA)] at p2
      exact ⟨p2, by rw [r2.get (by decide)]; exact x22⟩
    · rw [if_neg hA]
      rw [if_neg (fun h => hA (hall.1 h))] at p2
      exact p2
  · rw [if_neg hg] at p1
    refine ⟨t1, 8, s1, by omega, r1.mono (by decide), f1, ?_⟩
    have hA : ¬ WCT9.admissible a = true := fun h => hg ((hadm.1 h).1)
    rw [if_neg hA]; exact p1
end pieces
theorem digestInput_length' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (SigGolfCandidate.T3.digestInput rho m c).length = 64 := by
  simp only [SigGolfCandidate.T3.digestInput, List.length_append, bytesLE_length]
theorem pad64_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c) = SigGolfCandidate.T3.digestInput rho m c := by
  unfold SigGolfCandidate.T3.pad64
  rw [digestInput_length']
  simp
theorem wordsOf_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    wordsOf (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 3073,
        BitVec.ofNat 64 (c.toNat * 2 ^ 32), m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput']
  unfold SigGolfCandidate.T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE32]
  have hc := c.isLt
  have e1 : hdr1 0 c.toNat = c.toNat * 2 ^ 32 := by unfold hdr1; omega
  simp only [show ¬ SigGolfCandidate.T3.packedNodeTag 12 by decide, if_false, e1]
  rfl
theorem blocks_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (toQ (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput', blocks_toQ (by rw [Aligned, digestInput_length']; omega), digestInput_length']
structure LInv (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 2074
  hi : i ≤ 2 ^ 21
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t searchRegs
  frame : Frame s0 t SearchW
theorem outAt_writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    OutAt (writeHash t a) NBUF a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
section loop
variable {im : Image} {sk : BitVec 256}
theorem loop (hl : LookOK im headLook) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : SearchPre rho m s0) :
    ∀ F i t, i + F = 2 ^ 21 → LInv s0 i t →
      TBSim im sk t (F * 150 + 150) (WCT9.digestSearch rho m i F) (SearchPost s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, k1, s1, hk1, p1, -, -⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, s2, -, hf⟩ := fail_spec hl t1 p1
    exact (TBSim.pure_steps' (sk := sk) (s1.trans s2) (Q := SearchPost s0) (a := none) hf).mono
      (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 21 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_pos hi] at p1
    obtain ⟨u, s2, hfu, p2, h10, h11, h12, h16, h24, r2, f2⟩ :=
      trial_spec hl t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u searchRegs :=
      ((hI.regs.trans r1).trans r2).mono (by decide)
    have fu : Frame s0 u SearchW := ((hI.frame.trans f1).trans f2).mono (fun A _ hA => by
      simp only [or_false] at hA
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; rcases hA with hA | hA <;> simp [hA])
    have mem : ∀ A, A < 2 ^ 64 → ¬ SearchW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ SearchW A := by
      intro A hA; simp only [SearchW, DIG, NBUF, IDXV] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput', digestInput_length']) h10 (by decide)
        (by decide) h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput', hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : WCT9.digestSearch rho m i (F + 1) =
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if WCT9.admissible output = true then pure (some (BitVec.ofNat 32 i, output))
          else WCT9.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind' hfu h5 hv hq
      (W := 122 + (F * 150 + 150)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput']; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf 2091 := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : OutAt (writeHash u a) NBUF a := outAt_writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    obtain ⟨v, c, sv, hcv, rv, fv, pv⟩ := checks_spec hl (writeHash u a) pw a hN
    have rv' : RegsExcept s0 v searchRegs :=
      ((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono
        (by decide)
    have fv' : Frame s0 v SearchW := ((fu.trans fw).trans fv).mono (fun A _ hA => by
      simp only [or_false] at hA
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; right; right; left; exact hA)
    have hNv : OutAt v NBUF a := fun j hj => by
      rw [fv.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
    have x19v : v.getReg .x19 = BitVec.ofNat 64 i := by
      rw [rv.get (by decide), getReg_writeHash, r2.get (by decide), r1.get (by decide), hI.x19]
    by_cases hadm : WCT9.admissible a = true
    · rw [if_pos hadm] at pv
      simp only [hadm, ↓reduceIte]
      obtain ⟨w, sw, pw', x22w, idxw, rw', fw'⟩ := final_spec hl v pv.1 a pv.2
      refine (TBSim.pure_steps' (sv.trans sw) ?_).mono (by omega) (fun _ _ h => h)
      refine ⟨pw', by rw [rw'.get (by decide), rv'.get (by decide), hpre.x5], hadm, ?_, x22w, idxw,
        by rw [hc]; exact hi, ?_, ?_⟩
      · intro j hj; rw [fw'.get (by simp only [NBUF]; omega) (by simp only [IDXV, NBUF]; omega)]; exact hNv j hj
      · exact (rv'.trans rw').mono (by decide)
      · exact (fv'.trans fw').mono (fun A _ hA => by
          rcases hA with hA | hA
          · exact hA
          · unfold SearchW; right; right; right; exact hA)
    · rw [if_neg hadm] at pv
      simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, sw, pw', x19w, rw', fw'⟩ := next_spec hl v pv i hi x19v
      have hI' : LInv s0 (i + 1) w :=
        ⟨pw', by omega, x19w, (rv'.trans rw').mono (by decide),
          (fv'.trans fw').mono (fun A _ hA => by simp only [or_false] at hA; exact hA)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i + 1) w (by omega) hI')).mono (by omega) (fun _ _ h => h)
end loop
end ClaudeWCT.W9.Machine.Sign.SearchM
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign.SearchM
theorem searchGood (im : Image) : SearchGood im := by
  intro hnew hhooks sk rho m s hpre
  obtain ⟨t0, s0, p0, r0, f0⟩ := h153_spec (hookLook_ok hhooks) s hpre.pc
  have hI : LInv s 0 t0 :=
    ⟨p0, by norm_num, by rw [r0.get (by simp), hpre.x19], r0.mono (by intro x hx; simp at hx),
      f0.mono (fun _ _ h => h.elim)⟩
  have := TBSim.steps (sk := sk) s0
    (loop (headLook_ok hnew) hpre (2 ^ 21) 0 t0 (by norm_num) hI)
  refine this.mono ?_ (fun _ _ h => h)
  unfold searchC trialC WCT9.digestAttemptLimit
  omega
end ClaudeWCT.W9.Machine.Sign
end
