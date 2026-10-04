import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsTable
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search

section


set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem run_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : run look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  run_sound hl h s hpc hobl hbr
theorem runA_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : runA look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem no_obl (s : MachineState) : ∀ o ∈ ([] : List Oblig), o.holds s := by intro o ho; cases ho
theorem no_br (s : MachineState) : ∀ b ∈ ([] : List Br), b.holds s := by intro b hb; cases hb
theorem valid_ofNat {s : MachineState} {b : E} {B off w : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) :
    (Oblig.valid ⟨some b, BitVec.ofNat 64 off⟩ w).holds s := by
  unfold MEMORY_BYTES at hhi
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat, accessValid, rangeValid, Bool.and_eq_true,
    decide_eq_true_eq, toNat_ofNat_lt (show B + off < 2 ^ 64 by omega), MEMORY_BYTES]
  exact ⟨hhi, hal⟩
theorem ne_ofNat {s : MachineState} {b : E} {B off K : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hlt : B + off < 2 ^ 64) (hk : K < 2 ^ 64) (hne : B + off ≠ K) :
    (Oblig.ne ⟨some b, BitVec.ofNat 64 off⟩ ⟨none, BitVec.ofNat 64 K⟩).holds s := by
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]
  intro h
  exact hne ((ofNat_inj hlt hk).mp h)
theorem br_ne_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ne, x, y, d⟩ ↔ ((x.eval s != y.eval s) = d) := Iff.rfl
theorem br_ltu_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ltu, x, y, d⟩ ↔ (BitVec.ult (x.eval s) (y.eval s) = d) := Iff.rfl
theorem ofNat_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [h, this]
theorem ofNat_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
theorem frame_of_memEval {s t : MachineState} {ws : SymMem} (ht : ∀ a, t.getMem a = memEval s ws a)
    (W : Nat → Prop) (hW : ∀ p ∈ ws, p.1.base = none ∧ W p.1.off.toNat) : Frame s t W := by
  intro A hA hn
  rw [ht, memEval_frame_ofNat s ws A hA (fun p hp => ⟨(hW p hp).1, fun he => hn (he ▸ (hW p hp).2)⟩)]
theorem off_mwc (a : Nat) (e : E) (ha : a < 2 ^ 64) : (mwc a e).1.off.toNat = a := toNat_ofNat_lt ha
theorem memEval_mwc_self (s : MachineState) (a : Nat) (e : E) (ws : SymMem) (ha : a < 2 ^ 64) :
    memEval s (mwc a e :: ws) (BitVec.ofNat 64 a) = e.eval s := by
  rw [memEval_mwc s a a e ws ha ha, if_pos rfl]
theorem memEval_mwc_ne (s : MachineState) {a A : Nat} (e : E) (ws : SymMem) (hA : A < 2 ^ 64) (ha : a < 2 ^ 64)
    (hne : A ≠ a) : memEval s (mwc a e :: ws) (BitVec.ofNat 64 A) = memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_mwc s a A e ws hA ha, if_neg hne]
macro "ao" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and]) <;> omega))
macro "aoh" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and] at *) <;> omega))
section pieces
variable {im : Image}
theorem step_SK (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 2215) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (cbase 0) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 8 * k))) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 32 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 16 + 8 * k))) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = PRIVW + 40 ∨ A = PRIVW + 32 ∨ A = PRIVW + 8 ∨ A = PRIVW) := by
  obtain ⟨hst, -⟩ := run_pres (headLook_ok hcode) runSK_eq s hpc (no_obl s) (no_br s)
  have hm : ∀ a, ((expSK).toState s).getMem a = memEval s expSK.st.mem a := fun a => rfl
  refine ⟨_, hst, rfl, fun k hk => ?_, fun k hk => ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · refine frame_of_memEval hm _ (fun p hp => ?_)
    simp only [expSK, pres, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [mwc, PRIVW, BitVec.toNat_ofNat] <;> decide
def fk (c : Nat) : Nat := if WCT9.coordBase c % 64 = 0 then 12 else 13
theorem fsrcE_eq (c : Nat) : fsrcE c = SearchM.grpE c := rfl
theorem fieldE_eq (c : Nat) : fieldE c = SearchM.fieldE c := rfl
theorem childE_eval (s : MachineState) (N : BitVec 256) (hN : OutAt s NBUF N) (c : Nat) (hc : c < 9) :
    (E.bin .and (fsrcE c) (cE 127)).eval s = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.coordBase c % 128) := by
  obtain ⟨h21, hcb, -⟩ := SearchM.sh_bound c hc
  have hg := SearchM.grpE_toNat s N hN c hc
  show BinOp.eval .and ((fsrcE c).eval s) (BitVec.ofNat 64 127) = _
  rw [fsrcE_eq, SearchM.and_eval, show (127 : Nat) = 2 ^ 7 - 1 from rfl, SearchM.ofNat_and_mask _ 7 (by decide)]
  congr 1
  rw [hg, SearchM.mod64_div_mod _ (SearchM.sh c) 7 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, hcb]
  rfl
theorem step_F (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (cbase c))
    {N : BitVec 256} (hN : OutAt s NBUF N) :
    ∃ t, Steps im s (fk c) (fk c) t ∧ t.pc = pcOf (lwuI c) ∧
      t.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.coordBase c % 128) ∧
      t.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runF_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · rw [pres_getReg]; exact childE_eval s N hN c hc
  · rw [pres_getReg]
    show BinOp.eval .add (BinOp.eval .sll ((fieldE c).eval s) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 TBL) = _
    rw [fieldE_eq, SearchM.fieldE_eval s N hN c hc, binop_sll _ _ (by norm_num), ofNat_shl]
    simp only [BinOp.eval, ofNat_add_ofNat]
    congr 1; ring
theorem step_Z (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lwuI c + 1)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x18] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runZ_eq hc) s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
theorem step_P (hcode : NewCodeAt im) {c p j index : Nat} (hc : c < 9) (hp : p < 4) (s : MachineState)
    (hpc : s.pc = pcOf (pI c p)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 19 19 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (pI c p + 19) ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 PAIRW ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * (4 * j + p)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = PRIVW + 24 ∨ A = PRIVW + 16) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runP_eq hc hp) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_privW1E s p h18 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expP, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
def chainW0 (c i j index p : Nat) : Nat := index * 2 ^ 27 + j * 2 ^ 20 + chainK c i + 256 * p
theorem chainW0_merge (c i j index p q : Nat) (hc : c < 9) (hi : i < 7) (hp : p < 4) (hq : q < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i j index p)) 1 (BitVec.ofNat 64 q) =
      BitVec.ofNat 64 (chainW0 c i j index q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat8 _ _ (by omega)]
  simp only [chainW0, chainK, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem step_Pre (hcode : NewCodeAt im) {c i j index w : Nat} (hc : c < 9) (hi : i < 7) (s : MachineState)
    (hpc : s.pc = pcOf (preI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) {seed : Digest}
    (hseed : DigAt s (PAIRW + 16 * (i % 2)) seed) :
    ∃ t, Steps im s (if c = 0 then 19 else 20) (if c = 0 then 19 else 20) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (3 - w / 4 ^ i % 4) ∧ DigAt t (CHAINW + 48) seed ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index 0) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x26, .x28, .x29] ∧
      Frame s t (fun A => A = CHAINW + 24 ∨ A = CHAINW + 16 ∨ A = CHAINW + 56 ∨ A = CHAINW + 48) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runPre_eq hc hi) s hpc (no_obl s) (no_br s)
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  refine ⟨_, hst, rfl, ?_, ⟨?_, ?_⟩, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; exact eval_dE s i h25 hw (by omega)
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact hseed.1
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
    rw [show CHAINW + 48 + 8 = CHAINW + 56 from rfl] at *
    exact hseed.2
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_qE s h18 h22 hj (chainK_lt c i hc hi)]
    simp only [chainW0, Nat.mul_zero, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPre, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_Chk (hcode : NewCodeAt im) {c i st j sel e : Nat} (hc : c < 9) (hi : i < 7) (hst : st < 4)
    (s : MachineState) (hpc : s.pc = pcOf (chkI c i st)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (h26 : s.getReg .x26 = BitVec.ofNat 64 e) (hj : j < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (he : e < 2 ^ 64) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t k, Steps im s k k t ∧ k ≤ 11 ∧ t.pc = pcOf (skipI c i st) ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = slotV c i + 8 ∨ A = slotV c i) ∧ (j = sel → e = st → DigAt t (slotV c i) v) ∧
      (¬ (j = sel ∧ e = st) → Frame s t (fun _ => False)) := by
  have hl := coordLook_ok hcode hc
  by_cases hjs : j = sel
  · subst hjs
    by_cases hes : e = st
    · subst hes
      obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 2 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      refine ⟨_, 11, hst', le_rfl, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_, fun _ _ => ⟨?_, ?_⟩, ?_⟩
      · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
        simp only [expChk, pres, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
          List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
      · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
      · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
      · intro h; exact absurd ⟨rfl, rfl⟩ h
    · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 1 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp [hes]
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      exact ⟨_, 3, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
        fun _ h => absurd h hes, fun _ A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 0 < 3)) s hpc (no_obl s) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hsel]; simp [hjs])
    exact ⟨_, 1, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
      fun h => absurd h hjs, fun _ A _ _ => rfl⟩
theorem step_Stp (hcode : NewCodeAt im) {c i st j index : Nat} (hc : c < 9) (hi : i < 7) (h1 : 1 ≤ st) (h4 : st < 4)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c i j index pv (st - 1) hc hi hpv (by omega)]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStp, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; refine ⟨rfl, ?_⟩; rw [off_mwc _ _ (by ao)]
theorem step_Lc (hcode : NewCodeAt im) {c i : Nat} (hc : c < 9) (hi : i < 7) (s : MachineState)
    (hpc : s.pc = pcOf (skipI c i 3)) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) v ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFW + leafOff i + 8 ∨ A = LEAFW + leafOff i) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runLc_eq hc hi) s hpc (no_obl s) (no_br s)
  have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ⟨?_, ?_⟩, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expLc, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_L (hcode : NewCodeAt im) {c j index : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lI c))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s (if c = 0 then 15 else 16) (if c = 0 then 15 else 16) t ∧ fetch im t = some (.base .ECALL) ∧
      t.pc = pcOf (tI c - 1) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFW ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 (HEAPW + 16 * (j + 128)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (hdr6 c) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = LEAFW + 24 ∨ A = LEAFW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runL_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]
    show BinOp.eval .add (heapLeafE.eval s) (BitVec.ofNat 64 HEAPW) = _
    rw [eval_heapLeafE s h18]; simp only [BinOp.eval, ofNat_add_ofNat]
    rw [Nat.add_comm]
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_w1E s h18 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expL, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_T (hcode : NewCodeAt im) {c j : Nat} (hc : c < 9) (hj : j < 128) (s : MachineState)
    (hpc : s.pc = pcOf (tI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ (j + 1 < 128 → t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 (j + 1)) ∧
      (j + 1 = 128 → t.pc = pcOf (nodeI c) ∧ t.getReg .x18 = BitVec.ofNat 64 127) ∧
      RegsExcept s t [.x6, .x18] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  by_cases hb : j + 1 < 128
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc true) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 3, hst', by norm_num, fun _ => ⟨rfl, by rw [pres_getReg]; exact eval_x18p1 s h18⟩,
      fun h => absurd h (by omega), pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc false) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 4, hst', le_rfl, fun h => absurd h hb, fun _ => ⟨rfl, rfl⟩, pres_regsExcept _ _ _ _ _ _ _ s,
      fun A _ _ => rfl⟩
theorem eval_nodeLd (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (off : Nat) :
    (nodeLd off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + off)) := by
  show s.getMem (sh5.eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_sh5 s h18, ofNat_add_ofNat]; congr 2; ring
theorem step_N (hcode : NewCodeAt im) {c h index : Nat} (hc : c < 9) (hh1 : 1 ≤ h) (hh : h < 128)
    (s : MachineState) (hpc : s.pc = pcOf (nodeI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (_hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 25 25 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ntI c - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODEW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUTW ∧
      t.getMem (BitVec.ofNat 64 NODEW) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 48)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 56)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (nodeK c + 2 ^ 32 * index) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 h ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29] ∧
      Frame s t (fun A => A = NODEW + 24 ∨ A = NODEW + 16 ∨ A = NODEW + 56 ∨ A = NODEW + 48 ∨ A = NODEW + 8 ∨
        A = NODEW) := by
  have hb := eval_sh5 s h18
  obtain ⟨hst', hec⟩ := runA_pres (coordLook_ok hcode hc) (runN_eq hc) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  have m : ∀ A, A < 2 ^ 64 → ((expN c).toState s).getMem (BitVec.ofNat 64 A) =
      memEval s (expN c).st.mem (BitVec.ofNat 64 A) := fun A _ => rfl
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem]; simp only [memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 24 < 2 ^ 64 by ao)
      (by ao), memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 16 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 56 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 48 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 8 < 2 ^ 64 by ao) (by ao)]
    rw [memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18, Nat.add_zero]
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_nodeLoE s h22 (nodeK_lt c hc)
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact h18
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expN, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_NT (hcode : NewCodeAt im) {c h : Nat} (hc : c < 9) (hh1 : 2 ≤ h) (hh : h < 128) (s : MachineState)
    (hpc : s.pc = pcOf (ntI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 13 13 t ∧ (3 ≤ h → t.pc = pcOf (nodeI c)) ∧ (h = 2 → t.pc = pcOf (rI c)) ∧
      t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 NOUTW) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + 8)) ∧
      RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
      Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h) := by
  have hl := coordLook_ok hcode hc
  have hb := eval_sh4 s h18
  have hm1 := eval_x18m1 s h18 (by omega) (by omega)
  have obl : ∀ o ∈ [Oblig.valid (heapAddr 8) 8, .valid (heapAddr 0) 8], o.holds s := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
  have hea : ∀ off, Addr.eval s (heapAddr off) = BitVec.ofNat 64 (HEAPW + 16 * h + off) := by
    intro off
    show sh4.eval s + BitVec.ofNat 64 (HEAPW + off) = _
    rw [hb, ofNat_add_ofNat]; congr 1; ring
  have post : ∀ (b : Bool), (b = true ↔ 3 ≤ h) → run (coordLook c) [nodeI c, rI c] (ntI c) [.br b] = some (expNT c b) →
      ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (if b then nodeI c else rI c) ∧
        t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 NOUTW) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + 8)) ∧
        RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
        Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h) := by
    intro b hbh hrun
    obtain ⟨hst', -⟩ := run_pres hl hrun s hpc obl (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      rw [br_ne_holds, hm1, eval_cE, ofNat_bne (by omega) (by norm_num)]
      cases b <;> simp_all <;> omega)
    refine ⟨_, hst', rfl, by rw [pres_getReg]; exact hm1, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
    · rw [pres_getMem, memEval_cons, memEval_cons, hea, hea, if_neg (by
        intro he; have := (ofNat_inj (by ao) (by ao)).mp he; omega), if_pos (by rw [Nat.add_zero])]; rfl
    · rw [pres_getMem, memEval_cons, hea, if_pos rfl]; rfl
    · intro A hA hn
      simp only [not_or] at hn
      rw [pres_getMem, memEval_cons, memEval_cons, hea, hea, if_neg (by
        intro he; exact hn.1 ((ofNat_inj hA (by ao)).mp he)), if_neg (by
        intro he; exact hn.2 (by rw [(ofNat_inj hA (by ao)).mp he, Nat.add_zero]))]
      rfl
  by_cases h2 : 3 ≤ h
  · obtain ⟨t, h1', h2', h3', h4', h5', h6', h7'⟩ := post true (by simp [h2]) (runNT_eq hc true)
    exact ⟨t, h1', fun _ => h2', fun h => absurd h (by omega), h3', h4', h5', h6', h7'⟩
  · obtain ⟨t, h1', h2', h3', h4', h5', h6', h7'⟩ := post false (by simp [h2]) (runNT_eq hc false)
    exact ⟨t, h1', fun h => absurd h h2, fun _ => h2', h3', h4', h5', h6', h7'⟩
theorem step_R0 (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (rI c)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (pcI c 0) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 40)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 16)) = s.getMem (BitVec.ofNat 64 (HEAPW + 48)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 24)) = s.getMem (BitVec.ofNat 64 (HEAPW + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = FORW + forOff c + 24 ∨ A = FORW + forOff c + 16 ∨ A = FORW + forOff c + 8 ∨
        A = FORW + forOff c) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runR0_eq hc) s hpc (no_obl s) (no_br s)
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expR0, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_pathLd (s : MachineState) {sel : Nat} (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (hsel : sel < 128)
    {l : Nat} (hl : l < 7) (off : Nat) :
    (pathLd l off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + off)) := by
  show s.getMem ((pathE l).eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_pathE s h24 hsel l hl, ofNat_add_ofNat]; congr 2; ring
set_option maxRecDepth 100000 in
theorem pathHeap_lt_all : ∀ sel, sel < 128 → ∀ l, l < 7 → 2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := by
  decide +kernel
theorem pathHeap_lt (sel l : Nat) (hsel : sel < 128) (hl : l < 7) :
    2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := pathHeap_lt_all sel hsel l hl
theorem step_PC (hcode : NewCodeAt im) {c l sel : Nat} (hc : c < 9) (hl : l < 7) (hsel : sel < 128) (s : MachineState)
    (hpc : s.pc = pcOf (pcI c l)) (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (pcI c (l + 1)) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)))) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l + 8)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun A => A = slotP c l + 8 ∨ A = slotP c l) := by
  have hb := eval_pathE s h24 hsel l hl
  have hlt := pathHeap_lt sel l hsel hl
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runPC_eq hc hl) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_pathLd s h24 hsel hl, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao), eval_pathLd s h24 hsel hl]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPC, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_For (hcode : NewCodeAt im) {index : Nat} (s : MachineState) (hpc : s.pc = pcOf 10963)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 10976 ∧
      t.getReg .x10 = BitVec.ofNat 64 FORW ∧ t.getReg .x11 = BitVec.ofNat 64 320 ∧
      t.getReg .x12 = BitVec.ofNat 64 FOUT ∧
      t.getMem (BitVec.ofNat 64 FORW) = 0 ∧ t.getMem (BitVec.ofNat 64 (FORW + 8)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (FORW + 16)) = BitVec.ofNat 64 3841 ∧
      t.getMem (BitVec.ofNat 64 (FORW + 24)) = BitVec.ofNat 64 index ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧
      Frame s t (fun A => A = FORW + 8 ∨ A = FORW ∨ A = FORW + 24 ∨ A = FORW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (tailLook_ok hcode) runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; exact h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_J (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 10977) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 370 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst', -⟩ := run_pres (tailLook_ok hcode) runJ_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst', rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
end pieces
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest header pad64 privateInput zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem readWords_of_getD (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_getD t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem hashInput_of_words (t : MachineState) (l : List UInt8) (n A : Nat) (hl : l.length = 64 * (n + 1))
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 * (n + 1) < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hw : ∀ j < 8 * (n + 1), t.getMem (BitVec.ofNat 64 (A + 8 * j)) = (wordsOf l).getD j 0) :
    hashInput t = toQ l :=
  hashInput_toQ t l n A hl h10 hA (by omega) h11 (by omega)
    (readWords_of_getD t A _ _ (length_wordsOf _ _ (by rw [hl]; ring)) hw)
theorem header_words (tag lay tree pos idx : Nat) (ht : ¬ SigGolfCandidate.T3.packedNodeTag tag) (htag : tag < 256)
    (hlay : lay < 256) (htree : tree < 2 ^ 32) (hpos : pos < 2 ^ 32) (hidx : idx < 2 ^ 32) :
    wordsOf (bytesLE 16 (header tag lay tree pos idx)) =
      [BitVec.ofNat 64 (1 + 256 * tag + 65536 * lay + 2 ^ 32 * pos), BitVec.ofNat 64 (tree + 2 ^ 32 * idx)] := by
  rw [wordsOf_header, if_neg ht, if_neg ht, hdr0_eq tag lay tree pos htag hlay htree hpos, hdr1_eq tree idx htree hidx]
theorem wordsOf_priv (sk : BitVec 256) (c index q : Nat) (hc : c < 256) (hidx : index < 2 ^ 32) (hq : q < 2 ^ 32) :
    wordsOf (privateInput sk (.inl (header 8 c index 0 q))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 (hdr8 c), BitVec.ofNat 64 (index + 2 ^ 32 * q),
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  rw [wordsOf_privateInput_tweak, header_lo, header_hi, if_neg (by decide), if_neg (by decide),
    hdr0_eq 8 c index 0 (by norm_num) hc hidx (by norm_num), hdr1_eq index q hidx hq]
  simp only [hdr8]; congr 3
theorem chainInput_len (index c j i st : Nat) (v : Digest) : (WCT9.chainInput index c j i st v).length = 64 := by
  simp only [WCT9.chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem ftsChainLow_eq (index c j i st : Nat) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4) (hi : i < 7)
    (hj : j < 128) : WCT9.ftsChainLow index c j i st = chainW0 c i j index st := by
  unfold WCT9.ftsChainLow chainW0 chainK
  rw [Nat.mod_eq_of_lt (show i < 8 by omega), Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt (show c < 16 by omega),
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_chain (index c j i st : Nat) (v : Digest) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4)
    (hi : i < 7) (hj : j < 128) :
    wordsOf (pad64 (WCT9.chainInput index c j i st v)) =
      [0, 0, BitVec.ofNat 64 (chainW0 c i j index st), 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_len]), WCT9.chainInput_eq,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  unfold WCT9.ftsChainHeader
  rw [WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high, ftsChainLow_eq index c j i st hc hidx hst hi hj]
  rfl
def leafIn (index c j : Nat) (ends : List Digest) : List UInt8 :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.wctHeader 6 c index 0 j) ++ (ends.drop 1).flatMap (bytesLE 16)
theorem leafHash_eq (index c j : Nat) (ends : List Digest) :
    WCT9.leafHash index c j ends = SigGolfCandidate.T3.shortHash (leafIn index c j ends) := rfl
theorem leafIn_len (index c j : Nat) (ends : List Digest) (h : ends.length = 7) : (leafIn index c j ends).length = 128 := by
  have : ((ends.drop 1).flatMap (bytesLE 16)).length = 96 := by
    rw [List.length_flatMap]; simp [bytesLE_length, h]
  simp only [leafIn, List.length_append, bytesLE_length, this]
theorem wordsOf_leaf (index c j : Nat) (ends : List Digest) (h : ends.length = 7) (hc : c < 256)
    (hidx : index < 2 ^ 32) (hj : j < 2 ^ 32) :
    wordsOf (pad64 (leafIn index c j ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [BitVec.ofNat 64 (hdr6 c), BitVec.ofNat 64 (index + 2 ^ 32 * j)] ++
        (ends.drop 1).flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ h]), leafIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    WCT9.leaf_header_eq, header_words 6 c index 0 j (by decide) (by norm_num) hc hidx (by norm_num) hj,
    wordsOf_flatMap16]
  simp only [hdr6]; congr 4
def nodeIn (c index h : Nat) (L R : Digest) : List UInt8 :=
  bytesLE 16 L ++ bytesLE 16 (WCT9.wctNodeHeader c index h) ++ zero16 ++ bytesLE 16 R
theorem nodeHash_eq (c index h : Nat) (L R : Digest) :
    WCT9.wctNodeHash c index h L R = SigGolfCandidate.T3.shortHash (nodeIn c index h L R) := rfl
theorem nodeIn_len (c index h : Nat) (L R : Digest) : (nodeIn c index h L R).length = 64 := by
  simp only [nodeIn, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem hdr0_node (c index : Nat) (hc : c < 9) (hidx : index < 2 ^ 32) :
    hdr0 3 (4 + c) index index = nodeK c + 2 ^ 32 * index := by
  unfold hdr0 nodeK
  rw [Nat.mod_eq_of_lt (show 3 < 256 by norm_num), Nat.mod_eq_of_lt (show 4 + c < 256 by omega),
    Nat.div_eq_of_lt hidx, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_node (c index h : Nat) (L R : Digest) (hc : c < 9) (hidx : index < 2 ^ 32) (hh : h < 2 ^ 32) :
    wordsOf (pad64 (nodeIn c index h L R)) =
      [L.extractLsb' 0 64, L.extractLsb' 64 64, BitVec.ofNat 64 (nodeK c + 2 ^ 32 * index), BitVec.ofNat 64 h, 0, 0,
        R.extractLsb' 0 64, R.extractLsb' 64 64] := by
  have h1 : hdr1 h 0 = h := by unfold hdr1; rw [Nat.mod_eq_of_lt hh]; simp
  rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16, WCT9.wctNodeHeader, WCT9.nodeLayer,
    wordsOf_packed_header_3, wordsOf_bytesLE16, wordsOf_bytesLE16, hdr0_node c index hc hidx, h1]
  rfl
theorem forestPk_eq (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = SigGolfCandidate.T3.shortHash (WCT9.forestInput index pairs) := rfl
def pairWords (p : Digest × Digest) : List Word :=
  [p.1.extractLsb' 0 64, p.1.extractLsb' 64 64, p.2.extractLsb' 0 64, p.2.extractLsb' 64 64]
theorem wordsOf_pairs (ps : List (Digest × Digest)) :
    wordsOf (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = ps.flatMap pairWords := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
    rfl
theorem pairs_bytes_len (ps : List (Digest × Digest)) :
    (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2).length = 32 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_append, bytesLE_length, bytesLE_length,
      List.length_cons]
    ring
theorem forestIn_len (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (WCT9.forestInput index pairs).length = 320 := by
  simp only [WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_len, h]
theorem wordsOf_forest (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9)
    (hidx : index < 2 ^ 32) :
    wordsOf (pad64 (WCT9.forestInput index pairs)) =
      [0, 0, BitVec.ofNat 64 3841, BitVec.ofNat 64 index] ++ pairs.flatMap pairWords := by
  rw [pad64_of_aligned _ (by rw [forestIn_len _ _ h]), WCT9.forestInput,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_zero16, header_words 15 0 index 0 0 (by decide) (by norm_num) (by norm_num) hidx (by norm_num)
      (by norm_num), wordsOf_pairs]
  rfl
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
def chainRest (index c j i d : Nat) : Nat → List Digest → M (Digest × Digest)
  | 0, L => pure (L.getD (3 - d) 0, L.getD 3 0)
  | r + 1, L => shortHash (WCT9.chainInput index c j i (2 - r) (L.getD (2 - r) 0)) >>= fun v =>
      chainRest index c j i d r (L ++ [v])
theorem chain3_eq (index c j i d : Nat) (hd : d ≤ 3) (seed : Digest) :
    (WCT9.chain index c j i 0 (3 - d) seed >>= fun value =>
      WCT9.chain index c j i (3 - d) d value >>= fun last => pure (value, last)) =
      chainRest index c j i d 3 [seed] := by
  interval_cases d <;>
    simp only [WCT9.chain, chainRest, show List.range' 0 3 = [0, 1, 2] from rfl,
      show List.range' 0 2 = [0, 1] from rfl, show List.range' 0 1 = [0] from rfl,
      show List.range' 0 0 = [] from rfl, show List.range' 3 0 = [] from rfl, show List.range' 2 1 = [2] from rfl,
      show List.range' 1 2 = [1, 2] from rfl, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind,
      Nat.sub_self, Nat.sub_zero] <;> rfl
def chainW (c i : Nat) (A : Nat) : Prop :=
  (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ A = LEAFW + leafOff i ∨
    A = LEAFW + leafOff i + 8 ∨ A = slotV c i ∨ A = slotV c i + 8
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
structure ChkSt (c i j index sel w d r : Nat) (L : List Digest) (s0 t : MachineState) : Prop where
  pc : t.pc = pcOf (chkI c i (3 - r))
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  x26 : t.getReg .x26 = BitVec.ofNat 64 (3 - d)
  len : L.length = 4 - r
  val : DigAt t (CHAINW + 48) (L.getD (3 - r) 0)
  h16 : t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (3 - r - 1))
  h24 : t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
  op : j = sel → 3 - d < 3 - r → DigAt t (slotV c i) (L.getD (3 - d) 0)
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (chainW c i)
  nosel : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
def ChainPost (c i j sel : Nat) (s0 : MachineState) (r : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) r.2 ∧ (j = sel → DigAt t (slotV c i) r.1) ∧
    RegsExcept s0 t chainRegs ∧ Frame s0 t (chainW c i) ∧
    (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
      t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A))
theorem chkI_pos : ∀ c, c < 9 → ∀ i, i < 7 → ∀ st, st < 4 → 1 ≤ chkI c i st := by decide +kernel
theorem blocks64 (l : List UInt8) (hl : l.length = 64) : (toQ (pad64 l)).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; norm_num, by rw [hl]⟩, hl]
theorem pcOf_pred4 (n : Nat) (hn : 1 ≤ n) : pcOf (n - 1) + 4 = pcOf n := by
  rw [pcOf_add4, Nat.sub_add_cancel hn]
theorem DigAt.frame' {s t : MachineState} {W : Nat → Prop} {A : Nat} {d : Digest} (h : DigAt s A d)
    (hf : Frame s t W) (hA : A + 8 < 2 ^ 64) (h0 : ¬ W A) (h1 : ¬ W (A + 8)) : DigAt t A d :=
  h.frame hf hA h0 h1
section chain
variable {im : Image} {sk : BitVec 256}
theorem chain_from (hcode : NewCodeAt im) {c i j index sel w d : Nat} (hc : c < 9) (hi : i < 7) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hd : d ≤ 3) {s0 : MachineState} :
    ∀ r, r ≤ 3 → ∀ (L : List Digest) (t : MachineState), ChkSt c i j index sel w d r L s0 t →
      TBSim im sk t (11 + 28 * r + 8) (chainRest index c j i d r L) (ChainPost c i j sel s0) := by
  intro r
  induction r with
  | zero =>
    intro _ L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by norm_num : 3 < 4) t h.pc h.x18 h.x24 h.x26 (by omega) (by omega) (by omega) h.val
    obtain ⟨t2, s2, p2, l2, r2, f2⟩ := step_Lc hcode hc hi t1 p1 (h.val.frame f1 (by ao) (by ao) (by ao))
    have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
    refine (TBSim.pure_steps' (s1.trans s2) ⟨p2, l2, fun hjs => ?_, ?_, ?_, ?_⟩).mono (by omega) (fun _ _ h => h)
    · by_cases hd0 : d = 0
      · subst hd0
        have := o1 hjs rfl
        exact this.frame f2 (by ao) (by ao) (by ao)
      · have := h.op hjs (by omega)
        exact (this.frame (n1 (fun h' => hd0 (by omega))) (by ao) (fun h => h) (fun h => h)).frame f2
          (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA <;> [exact hA; (rcases hA with rfl | rfl <;> simp); (rcases hA with rfl | rfl <;> simp)]
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; rcases h' with rfl | rfl <;> aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
  | succ r ih =>
    intro hr L t h
    have hpos := chkI_pos c hc i hi (3 - r) (by omega)
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by omega : 2 - r < 4) t (by rw [h.pc]; congr 2; omega) h.x18 h.x24 h.x26
        (by omega) (by omega) (by omega) h.val
    have h16 : t1.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (3 - (r + 1) - 1)) := by
      rw [f1.get (by ao) (by unfold slotV; ao)]; exact h.h16
    obtain ⟨t2, s2, e2, p2, x10, x11, x12, m16, r2, f2⟩ :=
      step_Stp hcode hc hi (by omega : 1 ≤ 3 - r) (by omega : 3 - r < 4) t1
        (by rw [p1]; congr 2; omega) (by omega : 3 - (r + 1) - 1 < 4) h16
    have g12 : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → A < 2 ^ 64 →
        t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 hA => by
      rw [f2.get hA (by simpa using h1), f1.get hA (by simp [h2, h3])]
    have hx5 : t2.getReg .x5 = 0 := by
      rw [r2.get (by simp), r1.get (by simp)]; exact h.x5
    have hv := h.val
    have hq : hashInput t2 = toQ (pad64 (WCT9.chainInput index c j i (2 - r) (L.getD (2 - r) 0))) := by
      refine hashInput_of_words t2 _ 0 CHAINW (by rw [pad64_of_aligned _ (by rw [chainInput_len]), chainInput_len])
        x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chain index c j i (2 - r) _ hc hidx (by omega) hi hj]
      intro k hk
      interval_cases k
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z0
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z8
      · rw [show CHAINW + 8 * 2 = CHAINW + 16 by ao, m16, show 3 - r - 1 = 2 - r by omega]; rfl
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.h24
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z32
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z40
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 3 - (r + 1) = 2 - r by omega] at hv; exact hv.1
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 3 - (r + 1) = 2 - r by omega] at hv; exact hv.2
    have hbl := blocks64 _ (chainInput_len index c j i (2 - r) (L.getD (2 - r) 0))
    refine (TBSim.steps (s1.trans s2) (TBSim.shortHash_bind' (W := 11 + 28 * r + 8) e2 hx5
      (hashArgs_const t2 CHAINW 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => ih (by omega) (L ++ [a.extractLsb' 0 128]) (writeHash t2 a) ?_))).mono
      (by rw [hbl]; omega) (fun _ _ h => h)
    have fw := Frame.writeHash t2 a (CHAINW + 48) x12 (by ao)
    have g : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → ¬ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) →
        A < 2 ^ 64 → (writeHash t2 a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2 h3 h4 hA
      rw [fw.get hA (by intro h; exact h4 ⟨h.1, by omega⟩), g12 A h1 h2 h3 hA]
    have hlen : L.length = 3 - r := by have := h.len; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_pred4 _ hpos]
    · rw [getReg_writeHash]; exact hx5
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x18
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x22
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x24
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x25
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x26
    · simp [hlen]; omega
    · have := DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)
      refine this.congr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show 3 - r - L.length = 0 by omega]
      rfl
    · rw [fw.get (by ao) (by intro h; ao), m16]
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.h24
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z0
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z8
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z32
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z40
    · intro hjs hlt
      have e : (L ++ [a.extractLsb' 0 128]).getD (3 - d) 0 = L.getD (3 - d) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [e]
      have hslot : DigAt t2 (slotV c i) (L.getD (3 - d) 0) := by
        by_cases hlt' : 3 - d < 3 - (r + 1)
        · exact ((h.op hjs hlt').frame (n1 (fun h' => by omega)) (by unfold slotV; ao) (fun h => h)
            (fun h => h)).frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
        · have heq : 3 - d = 2 - r := by omega
          have := o1 hjs heq
          rw [heq]
          rw [show 3 - (r + 1) = 2 - r by omega] at this
          exact this.frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
      exact hslot.frame fw (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact (((h.regs.trans r1).trans r2).trans
        (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).mono (by simp [chainRegs])
    · refine (((h.frame.trans f1).trans f2).trans fw).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with ((hA | hA) | hA) | hA
      · exact hA
      · rcases hA with rfl | rfl <;> simp
      · subst hA; left; constructor <;> omega
      · right; left; constructor <;> omega
    · intro hjs A hA h1 h2
      have hs : slotV c 0 = SIG + 16 + 224 * c := by unfold slotV; omega
      rw [fw.get hA (by intro h'; unfold slotV at h1 h2; aoh), f2.get hA (by intro h'; unfold slotV at h1 h2; aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
structure ChainPre (c i j index sel w : Nat) (seed : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (preI c i)
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  seed : DigAt t (PAIRW + 16 * (i % 2)) seed
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
def chainC : Nat := 20 + (11 + 28 * 3 + 8)
theorem chain_unit (hcode : NewCodeAt im) {c i j index sel w : Nat} (hc : c < 9) (hi : i < 7) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) {seed : Digest} {s : MachineState}
    (h : ChainPre c i j index sel w seed s) :
    TBSim im sk s chainC (chainRest index c j i (w / 4 ^ i % 4) 3 [seed]) (ChainPost c i j sel s) := by
  obtain ⟨t1, s1, p1, x26, v1, m16, m24, r1, f1⟩ :=
    step_Pre hcode hc hi s h.pc h.x18 h.x22 hj h.x25 hw h.seed
  have hd : w / 4 ^ i % 4 ≤ 3 := by have := Nat.mod_lt (w / 4 ^ i) (show 0 < 4 by norm_num); omega
  have g : ∀ A, A ≠ CHAINW + 16 → A ≠ CHAINW + 24 → A ≠ CHAINW + 56 → A ≠ CHAINW + 48 → A < 2 ^ 64 →
      t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 h4 hA =>
    f1.get hA (by simp [h1, h2, h3, h4])
  have hst : ChkSt c i j index sel w (w / 4 ^ i % 4) 3 [seed] s t1 :=
    { pc := p1
      x5 := by rw [r1.get (by simp)]; exact h.x5
      x18 := by rw [r1.get (by simp)]; exact h.x18
      x22 := by rw [r1.get (by simp)]; exact h.x22
      x24 := by rw [r1.get (by simp)]; exact h.x24
      x25 := by rw [r1.get (by simp)]; exact h.x25
      x26 := x26
      len := rfl
      val := v1
      h16 := m16
      h24 := m24
      z0 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z0
      z8 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z8
      z32 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z32
      z40 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z40
      op := fun _ h => absurd h (by omega)
      regs := r1.mono (by simp [chainRegs])
      frame := f1.mono (fun A _ hA => by
        unfold chainW
        rcases hA with rfl | rfl | rfl | rfl
        · left; constructor <;> omega
        · left; constructor <;> omega
        · right; left; constructor <;> omega
        · right; left; constructor <;> omega)
      nosel := fun _ A hA h1 h2 => f1.get hA (by unfold slotV at h1 h2; intro h'; aoh) }
  refine (TBSim.steps s1 (chain_from hcode hc hi hj hsel hidx hw hd 3 le_rfl [seed] t1 hst)).mono ?_ (fun _ _ h => h)
  unfold chainC; split_ifs <;> omega
end chain
end ClaudeWCT.W9.Machine.Sign
end
