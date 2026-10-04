import SigGolfCandidate.T3M.Keygen.Blocks
import SigGolfCandidate.T3M.Keygen.PackedInput
import SigGolfCandidate.T3M.Keygen.PackedShared

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
abbrev PRIV : Nat := 0x20000
abbrev SEEDS : Nat := 0x20040
abbrev CHAIN : Nat := 0x201A0
abbrev NODE : Nat := 0x20200
abbrev NOUT : Nat := 0x20240
abbrev LOUT : Nat := 0x203C0
abbrev LEAFPK : Nat := 0x20600
macro "sc_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK] at *); omega))
theorem sub0_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_0 h) s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]
theorem sub1_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1)) (m cap : Nat) (hm : m < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h17 : s.getReg .x17 = BitVec.ofNat 64 cap) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = cap then pcOf (b + 2) else pcOf (b + 8)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_1 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_1 h) s hpc (by simp [st_1, blk117_1.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_1, rebase, blk117_1.res, E.eval, CmpOp.eval, h20, h17]
    by_cases hmc : m = cap
    · subst hmc; simp
    · rw [if_neg hmc]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 cap := fun he => hmc ((ofNat_inj hm hcap).mp he)
      simp [this]
  · intro r hr; cases r <;> simp_all [st_1, blk117_1.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_1, blk117_1.res, rv_simp]
theorem sub2_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 h.2.1
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_2 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_2, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_2, blk117_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub8_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (b + 26) else pcOf (b + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_8 h) s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]
abbrev sub9_spec {image : Image} {b : Nat} := @shared_header_source image b
theorem sub24_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 24)) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_24 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_24 h) s hpc (by simp [st_24, blk117_24.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_24, Result.toState_pc, E.eval]
  · t3n [st_24, blk117_24.res, h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_24, blk117_24.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_24, blk117_24.res, rv_simp]
theorem sub26_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_26 h) s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]
theorem fetch_sub23 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 23)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_23 h).fetch s hpc).trans rfl
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, zero16]
theorem wordsOf_chainInput (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (chainInput lay tree leaf i step v) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] :=
  Packed.wordsOf_chainInput lay tree leaf i step v
theorem toQ_chainInput_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length]), blocks_toQ ⟨by rw [chainInput_length]; omega,
    by rw [chainInput_length]⟩, chainInput_length]
structure ChainPre (s : MachineState) (lay : Layer) (tree leaf i cap e valp ret : Nat) : Prop where
  x5 : s.getReg .x5 = 0
  x1 : s.getReg .x1 = pcOf ret
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 cap
  x19 : s.getReg .x19 = BitVec.ofNat 64 i
  x21 : s.getReg .x21 = BitVec.ofNat 64 e
  x23 : s.getReg .x23 = BitVec.ofNat 64 valp
  htree : tree < 2 ^ 32
  hi : i < 64
  hroute : tree * 2 ^ T3.height lay + leaf < 2 ^ 31
  hleaf : leaf < 2 ^ T3.height lay
  hcap : cap ≤ e
  he : e ≤ 8
  hv8 : valp % 8 = 0
  hv : valp + 16 ≤ 2 ^ 24
  hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 80 ≤ valp
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  z32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x29, .x30]
def ChainW (valp A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨
    (CHAIN + 48 ≤ A ∧ A < CHAIN + 80) ∨ (valp ≤ A ∧ A < valp + 16)
structure ChainHead (b : Nat) (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (b + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (ChainW valp)
  val : DigAt t (CHAIN + 48) v
section loop
variable {image : Image} {b : Nat} (hsub : SubAt image b) (sk : BitVec 256) {s0 : MachineState}
  {lay : Layer} {tree leaf i cap e valp ret : Nat} (hpre : ChainPre s0 lay tree leaf i cap e valp ret)
include hsub hpre
omit hpre in
theorem chain_entry (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    ∃ t, Steps image s0 1 1 t ∧ ChainHead b s0 valp 0 seed t := by
  obtain ⟨t, st, tpc, t20, tr, tf⟩ := sub0_spec hsub s0 (by simpa using hpc)
  exact ⟨t, st, ⟨tpc, t20, tr.mono (by simp [chainRegs]), tf.mono (fun _ _ h => h.elim),
    hseed.frame tf (by decide) (by simp) (by simp)⟩⟩
omit hsub in
theorem chain_hash {m : Nat} (hm : m < e) {v : Digest} {t u : MachineState}
    (ht : ChainHead b s0 valp m v t)
    (hu : Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (valp ≤ A ∧ A < valp + 16)))
    (h10 : u.getReg .x10 = BitVec.ofNat 64 CHAIN) (h11 : u.getReg .x11 = BitVec.ofNat 64 64)
    (h16 : u.getMem (BitVec.ofNat 64 (CHAIN + 16)) =
      (T3.chainHeader lay tree leaf i m).extractLsb' 0 64)
    (h24 : u.getMem (BitVec.ofNat 64 (CHAIN + 24)) =
      (T3.chainHeader lay tree leaf i m).extractLsb' 64 64) :
    hashInput u = toQ (pad64 (chainInput lay tree leaf i m v)) := by
  have hl := chainInput_length lay tree leaf i m v
  rw [pad64_of_aligned _ (by rw [hl])]
  refine hashInput_toQ u _ 0 CHAIN hl h10 (by decide) (by decide) h11 (by decide) ?_
  have hvc := hpre.hvc
  have fr : ∀ A, A < 2 ^ 64 → ¬ ChainW valp A →
      u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := fun A hA h1 =>
    (hu.get hA (fun h => h1 (by unfold ChainW; rcases h with h | h <;> simp_all))).trans
      (ht.frame.get hA h1)
  have hv := ht.val.frame hu (by decide) (by simp; omega) (by simp; omega)
  rw [wordsOf_chainInput, readWords_eight, fr CHAIN (by decide) (by simp [ChainW]; omega),
    fr (CHAIN + 8) (by decide) (by simp [ChainW]; omega), h16, h24,
    fr (CHAIN + 32) (by decide) (by simp [ChainW]; omega),
    fr (CHAIN + 40) (by decide) (by simp [ChainW]; omega), hv.1, hv.2, hpre.z0, hpre.z8,
    hpre.z32, hpre.z40]
omit hpre in
theorem chain_tail {m : Nat} {u : MachineState} (hupc : u.pc = pcOf (b + 23))
    (h20 : u.getReg .x20 = BitVec.ofNat 64 m) (h12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48))
    (hregs : RegsExcept s0 u chainRegs) (hfr : Frame s0 u (ChainW valp)) (a : BitVec 256) :
    ∃ w, Steps image (writeHash u a) 2 2 w ∧ ChainHead b s0 valp (m + 1) (a.extractLsb' 0 128) w ∧
      Frame u w (fun A => CHAIN + 48 ≤ A ∧ A < CHAIN + 80) := by
  have hwf := Frame.writeHash u a (CHAIN + 48) h12 (by decide)
  obtain ⟨w, st, wpc, w20, wr, wf⟩ := sub24_spec hsub (writeHash u a)
    (by rw [pc_writeHash, hupc, pcOf_add4]) m (by rw [getReg_writeHash, h20])
  refine ⟨w, st, ⟨wpc, w20, ?_, ?_, ?_⟩, (hwf.trans wf).mono (fun A _ h => h.elim id False.elim)⟩
  · have h1 : RegsExcept u (writeHash u a) [] := fun r _ => getReg_writeHash u a r
    refine ((hregs.trans h1).trans wr).mono ?_
    intro r hr
    simp only [chainRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto
  · refine (hfr.trans (hwf.trans wf)).mono ?_
    intro A _ h; unfold ChainW; rcases h with h | h | h
    · exact h
    · exact Or.inr (Or.inl h)
    · exact h.elim
  · exact (DigAt.writeHash_lo u a (CHAIN + 48) h12 (by decide)).frame wf (by decide) (by simp)
      (by simp)
theorem chain_step {m : Nat} (hm : m < e) (hmc : m ≠ cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (rungK lay) (rungC lay) 1 1 (shortHash (chainInput lay tree leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80))) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hi := hpre.hi
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h19 : t.getReg .x19 = BitVec.ofNat 64 i := by rw [g _ (by simp [chainRegs]), hpre.x19]
  have h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [g _ (by simp [chainRegs]), hpre.x8]
  have h5 : t.getReg .x5 = 0 := by rw [g _ (by simp [chainRegs]), hpre.x5]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_neg hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc m e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20) (by rw [t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t2pc
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3w, t3w24, t3r, t3f⟩ :=
    sub9_spec hsub t2 t2pc lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)
    (by rw [e12.get (by simp)]; exact h8)
    (by rw [e12.get (by simp), g _ (by simp [chainRegs]), hpre.x9])
    (by rw [e12.get (by simp), g _ (by simp [chainRegs]), hpre.x18])
    (by rw [e12.get (by simp)]; exact h19)
    (by rw [e12.get (by simp)]; exact ht.x20)
  have f13 : Frame t t3 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)
  have r13 : RegsExcept t t3 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (e12.trans t3r).mono (by simp)
  have hq := chain_hash hpre hm ht (f13.mono (fun A _ h => Or.inl h)) t3x10 t3x11 t3w t3w24
  have hv : hashArgumentsValid t3 = true :=
    hashArgs_const t3 CHAIN 64 (CHAIN + 48) t3x10 t3x11 t3x12 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : t3.getReg .x5 = 0 := by rw [r13.get (by simp), h5]
  have h20' : t3.getReg .x20 = BitVec.ofNat 64 m := by rw [r13.get (by simp), ht.x20]
  have hr3 : RegsExcept s0 t3 chainRegs := (ht.regs.trans r13).mono (by simp [chainRegs])
  have hf3 : Frame s0 t3 (ChainW valp) :=
    (ht.frame.trans f13).mono (fun A _ h => by unfold ChainW at *; rcases h with h | h <;> simp_all)
  refine (TSim.steps (st1.trans (st2.trans st3)) ((TSim.shortHash_bind (k := 2) (c := 2) (n := 0) (b := 0)
    (f := Pure.pure) (fetch_sub23 hsub t3 t3pc) h5' hv hq (fun a => ?_)).of_eq (bind_pure _) rfl rfl
    rfl rfl)).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, stw, hw, wf⟩ := chain_tail hsub t3pc h20' t3x12 hr3 hf3 a
    exact TSim.pure_steps stw ⟨hw, (f13.trans wf).mono (fun A _ h => by rcases h with h | h <;> simp_all)⟩
  all_goals simp [toQ_chainInput_blocks, rungK, rungC] <;> omega
theorem chain_step_cap {m : Nat} (hm : m < e) (hmc : m = cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (rungK lay + 6) (rungC lay + 6) 1 1 (shortHash (chainInput lay tree leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧ DigAt u valp v ∧ Frame t u (ChainW valp)) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hi := hpre.hi
  have hvc := hpre.hvc
  have hvb := hpre.hv
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h19 : t.getReg .x19 = BitVec.ofNat 64 i := by rw [g _ (by simp [chainRegs]), hpre.x19]
  have h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [g _ (by simp [chainRegs]), hpre.x8]
  have h5 : t.getReg .x5 = 0 := by rw [g _ (by simp [chainRegs]), hpre.x5]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 valp := by rw [g _ (by simp [chainRegs]), hpre.x23]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_pos hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp)]; exact h23) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc m e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t3pc
  have e13 : RegsExcept t t3 [.x6, .x7, .x29] := ((t1r.trans t2r).trans t3r).mono (by simp)
  obtain ⟨t4, st4, t4pc, t4x10, t4x11, t4x12, t4w, t4w24, t4r, t4f⟩ :=
    sub9_spec hsub t3 t3pc lay tree leaf i m hpre.hroute hpre.hleaf hi (by omega)
    (by rw [e13.get (by simp)]; exact h8)
    (by rw [e13.get (by simp), g _ (by simp [chainRegs]), hpre.x9])
    (by rw [e13.get (by simp), g _ (by simp [chainRegs]), hpre.x18])
    (by rw [e13.get (by simp)]; exact h19)
    (by rw [e13.get (by simp)]; exact ht.x20)
  have f14 : Frame t t4 (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (valp ≤ A ∧ A < valp + 16)) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | (right; omega) | (left; exact h))
  have r14 : RegsExcept t t4 [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] :=
    (e13.trans t4r).mono (by simp)
  have hq := chain_hash hpre hm ht f14 t4x10 t4x11 t4w t4w24
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 CHAIN 64 (CHAIN + 48) t4x10 t4x11 t4x12 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : t4.getReg .x5 = 0 := by rw [r14.get (by simp), h5]
  have h20' : t4.getReg .x20 = BitVec.ofNat 64 m := by rw [r14.get (by simp), ht.x20]
  have hr4 : RegsExcept s0 t4 chainRegs := (ht.regs.trans r14).mono (by simp [chainRegs])
  have hf4 : Frame s0 t4 (ChainW valp) :=
    (ht.frame.trans f14).mono (fun A _ h => by unfold ChainW at *; rcases h with h | h | h <;> simp_all)
  have hvv4 : DigAt t4 valp v := hvv.frame (t3f.trans t4f) (by omega)
    (by simp; sc_omega) (by simp; sc_omega)
  refine (TSim.steps (st1.trans (st2.trans (st3.trans st4))) ((TSim.shortHash_bind (k := 2) (c := 2)
    (n := 0) (b := 0) (f := Pure.pure) (fetch_sub23 hsub t4 t4pc) h5' hv hq (fun a => ?_)).of_eq
    (bind_pure _) rfl rfl rfl rfl)).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, stw, hw, wf⟩ := chain_tail hsub t4pc h20' t4x12 hr4 hf4 a
    refine TSim.pure_steps stw ⟨hw, hvv4.frame wf (by omega) (by simp; omega) (by simp; omega), ?_⟩
    refine (f14.trans wf).mono (fun A _ h => ?_)
    unfold ChainW; rcases h with (h | h) | h <;> simp_all
  all_goals simp [toQ_chainInput_blocks, rungK, rungC] <;> omega
theorem chain_exit {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e ≠ cap) :
    ∃ u, Steps image t 3 3 u ∧ u.pc = pcOf ret ∧ RegsExcept t u [] ∧ Frame t u (fun _ => False) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_neg hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc e e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20)
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t2pc
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub26_spec hsub t2 t2pc ret
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  exact ⟨t3, st1.trans (st2.trans st3), t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by simp_all)⟩
theorem chain_exit_cap {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e = cap) :
    ∃ u, Steps image t 9 9 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧ RegsExcept t u [.x6, .x7, .x29] ∧
      Frame t u (fun A => valp ≤ A ∧ A < valp + 16) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_pos hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x23]) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc e e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t3pc
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := sub26_spec hsub t3 t3pc ret
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  refine ⟨t4, st1.trans (st2.trans (st3.trans st4)), t4pc, ?_, (((t1r.trans t2r).trans t3r).trans t4r).mono
    (by simp), (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | omega)⟩
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  exact hvv.frame (t3f.trans t4f) (by have := hpre.hv; omega) (by simp) (by simp)
theorem chainRun_tsim (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    TSim image sk s0 (rungK lay * e + 10) (rungC lay * e + 10) e e
      (do let v ← chain lay tree leaf i 0 cap seed
          let last ← chain lay tree leaf i cap (e - cap) v
          pure (v, last))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
        RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
  have hcap := hpre.hcap
  have hvc := hpre.hvc
  have hvb := hpre.hv
  obtain ⟨t0, st0, h0⟩ := chain_entry hsub hpc seed hseed
  have p1 : TSim image sk t0 (sumTo (fun _ => rungK lay) cap) (sumTo (fun _ => rungC lay) cap)
      (sumTo (fun _ => 1) cap) (sumTo (fun _ => 1) cap)
      (chain lay tree leaf i 0 cap seed) (fun v t => ChainHead b s0 valp cap v t) := by
    unfold chain
    exact TSim.foldlM_range' 0 cap _ seed (fun j v t => ChainHead b s0 valp j v t) _ _ _ _
      (fun j hj v t ht => (chain_step hsub sk hpre (m := 0 + j) (by omega) (by omega)
        (by simpa using ht)).mono (fun v' u hu => by simpa using hu.1)) h0
  rcases Nat.lt_or_ge cap e with hlt | hge
  ·
    have hsplit : chain lay tree leaf i cap (e - cap) = fun v =>
        shortHash (chainInput lay tree leaf i cap v) >>= fun v1 =>
          (List.range' (cap + 1) (e - cap - 1)).foldlM
            (fun value step => shortHash (chainInput lay tree leaf i step value)) v1 := by
      funext v
      unfold chain
      rw [show e - cap = e - cap - 1 + 1 by omega, List.range'_succ, List.foldlM_cons]
      rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t (rungK lay + 6 + (sumTo (fun _ => rungK lay) (e - cap - 1) + 3))
          (rungC lay + 6 + (sumTo (fun _ => rungC lay) (e - cap - 1) + 3)) (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (do let last ← chain lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hsplit, bind_assoc]
      refine TSim.bind (chain_step_cap hsub sk hpre hlt rfl ht) (fun v1 u hu => ?_)
      have p2 := TSim.foldlM_range' (image := image) (sk := sk) (cap + 1) (e - cap - 1)
        (fun value step => shortHash (chainInput lay tree leaf i step value)) v1
        (fun j v' w => ChainHead b s0 valp (cap + 1 + j) v' w ∧ DigAt w valp v)
        (fun _ => rungK lay) (fun _ => rungC lay) (fun _ => 1) (fun _ => 1)
        (fun j hj v' w hw => (chain_step hsub sk hpre (m := cap + 1 + j) (by omega) (by omega)
          hw.1).mono (fun v'' w' hw' => ⟨by simpa [Nat.add_assoc] using hw'.1,
            hw.2.frame hw'.2 (by omega) (by simp; omega) (by simp; omega)⟩))
        ⟨by simpa using hu.1, hu.2.1⟩
      refine TSim.bind p2 (fun last w hw => ?_)
      have hw1 : ChainHead b s0 valp e last w := by
        have := hw.1; rwa [show cap + 1 + (e - cap - 1) = e by omega] at this
      obtain ⟨x, stx, xpc, xr, xf⟩ := chain_exit hsub hpre hw1 (by omega)
      exact TSim.pure_steps stx ⟨xpc, hw.2.frame xf (by omega) (by simp) (by simp),
        hw1.val.frame xf (by decide) (by simp) (by simp), (hw1.regs.trans xr).mono (by simp),
        (hw1.frame.trans xf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    all_goals simp only [sumTo_const]
    all_goals fin_cases lay <;> norm_num [rungK, rungC, headerK] at * <;> omega
  ·
    have he : cap = e := by omega
    have hz : chain lay tree leaf i cap (e - cap) = fun v => pure v := by
      funext v; rw [show e - cap = 0 by omega]; rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t 9 9 0 0
          (do let last ← chain lay tree leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hz]
      simp only [pure_bind]
      have ht' : ChainHead b s0 valp e v t := he ▸ ht
      obtain ⟨x, stx, xpc, xv, xr, xf⟩ := chain_exit_cap hsub hpre ht' he.symm
      exact TSim.pure_steps stx ⟨xpc, xv, ht'.val.frame xf (by decide) (by simp; omega)
        (by simp; omega), (ht'.regs.trans xr).mono (by simp [chainRegs]),
        (ht'.frame.trans xf).mono (fun A _ h => by
          unfold ChainW at *; rcases h with h | h; exact h; exact Or.inr (Or.inr h))⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    all_goals simp only [sumTo_const]
    all_goals subst he; simp [Nat.mul_comm] <;> omega
end loop
end SigGolfCandidate.T3M.Keygen
