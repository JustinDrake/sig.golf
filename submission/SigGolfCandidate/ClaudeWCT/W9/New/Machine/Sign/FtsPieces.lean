import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsTable
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search

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
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr5, hdr6, hdr8, hdr11, true_or, or_true,
  and_true, true_and]) <;> omega))
macro "aoh" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr5, hdr6, hdr8, hdr11, true_or, or_true,
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
theorem step_Pre (hcode : NewCodeAt im) {c i j index w : Nat} (hc : c < 9) (hi : i < 7) (s : MachineState)
    (hpc : s.pc = pcOf (preI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) {seed : Digest}
    (hseed : DigAt s (PAIRW + 16 * (i % 2)) seed) :
    ∃ t, Steps im s (if c = 0 then 19 else 20) (if c = 0 then 19 else 20) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (3 - w / 4 ^ i % 4) ∧ DigAt t (CHAINW + 48) seed ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (hdr5 c + 2 ^ 40 * i) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j) ∧
      RegsExcept s t [.x6, .x7, .x26, .x28, .x29] ∧
      Frame s t (fun A => A = CHAINW + 16 ∨ A = CHAINW + 24 ∨ A = CHAINW + 56 ∨ A = CHAINW + 48) := by
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
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_w1E s h18 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPre, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
def chainW0 (c i p : Nat) : Nat := hdr5 c + 2 ^ 32 * p + 2 ^ 40 * i
theorem chainW0_merge : ∀ c, c < 9 → ∀ i, i < 7 → ∀ p, p < 4 → ∀ q, q < 4 →
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i p)) 4 (BitVec.ofNat 64 q) = BitVec.ofNat 64 (chainW0 c i q) := by
  decide +kernel
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
theorem step_Stp (hcode : NewCodeAt im) {c i st : Nat} (hc : c < 9) (hi : i < 7) (h1 : 1 ≤ st) (h4 : st < 4)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 4 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c hc i hi pv hpv (st - 1) (by omega)]
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
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 25 25 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ntI c - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODEW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUTW ∧
      t.getMem (BitVec.ofNat 64 NODEW) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 48)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 56)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (hdr11 c) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * h) ∧
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
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_w1E s h18 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expN, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_NT (hcode : NewCodeAt im) {c h : Nat} (hc : c < 9) (hh1 : 1 ≤ h) (hh : h < 128) (s : MachineState)
    (hpc : s.pc = pcOf (ntI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 12 12 t ∧ (2 ≤ h → t.pc = pcOf (nodeI c)) ∧ (h = 1 → t.pc = pcOf (rI c)) ∧
      t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 NOUTW) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + 8)) ∧
      RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
      Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h) := by
  have hl := coordLook_ok hcode hc
  have hb := eval_sh4 s h18
  have hm1 := eval_x18m1 s h18 hh1 (by omega)
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
  have post : ∀ (b : Bool), (b = true ↔ 2 ≤ h) → run (coordLook c) [nodeI c, rI c] (ntI c) [.br b] = some (expNT c b) →
      ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (if b then nodeI c else rI c) ∧
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
  by_cases h2 : 2 ≤ h
  · obtain ⟨t, h1', h2', h3', h4', h5', h6', h7'⟩ := post true (by simp [h2]) (runNT_eq hc true)
    exact ⟨t, h1', fun _ => h2', fun h => absurd h (by omega), h3', h4', h5', h6', h7'⟩
  · obtain ⟨t, h1', h2', h3', h4', h5', h6', h7'⟩ := post false (by simp [h2]) (runNT_eq hc false)
    exact ⟨t, h1', fun h => absurd h h2, fun _ => h2', h3', h4', h5', h6', h7'⟩
theorem step_R0 (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (rI c)) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (pcI c 0) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c)) = s.getMem (BitVec.ofNat 64 (HEAPW + 16)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = FORW + forOff c + 8 ∨ A = FORW + forOff c) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runR0_eq hc) s hpc (no_obl s) (no_br s)
  have hfo : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expR0, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
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
theorem step_For (hcode : NewCodeAt im) {index : Nat} (s : MachineState) (hpc : s.pc = pcOf 10918)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 11 11 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 10929 ∧
      t.getReg .x10 = BitVec.ofNat 64 FORW ∧ t.getReg .x11 = BitVec.ofNat 64 192 ∧
      t.getReg .x12 = BitVec.ofNat 64 FOUT ∧
      t.getMem (BitVec.ofNat 64 (FORW + 16)) = BitVec.ofNat 64 3841 ∧
      t.getMem (BitVec.ofNat 64 (FORW + 24)) = BitVec.ofNat 64 index ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = FORW + 24 ∨ A = FORW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (tailLook_ok hcode) runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_J (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 10930) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 370 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst', -⟩ := run_pres (tailLook_ok hcode) runJ_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst', rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
end pieces
end ClaudeWCT.W9.Machine.Sign
