import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PlaceDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.SearchCode
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Place
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CoordTb
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region

section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runM (r : PRes) (stop : Nat) (M : SymMem) (chg : List Reg) : Bool :=
  listBeq pairBeq r.st.mem M && r.st.obl.isEmpty && !r.ecall && r.spc.isNone &&
    r.pc.toNat == (pcOf stop).toNat && keepB (allRegs.filter fun x => !chg.contains x) r
theorem runM_spec {im : Image} (hc : NewCodeAt im) {stops : List Word} {fuel P : Nat} {dirs : List Dir}
    {known : List (Reg × Word)} {r : PRes} {stop : Nat} {M : SymMem} {chg : List Reg}
    (h : pathAux pcfg expLook stops fuel (pcOf P) dirs (σK known) [] = some r) (hb : runM r stop M chg = true)
    (s : MachineState) (hpc : s.pc = pcOf P) (hk : ∀ p ∈ known, s.getReg p.1 = p.2)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧ (r.toState s).pc = pcOf stop ∧
      RegsExcept s (r.toState s) chg ∧ (∀ A, (r.toState s).getMem A = memEval s M A) := by
  simp only [runM, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, Option.isNone_iff_eq_none,
    beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨⟨hm, ho⟩, -⟩, hspc⟩, hpcr⟩, hkeep⟩ := hb
  obtain ⟨h1, -⟩ := pathRun_sound h (expLook_ok hc) s hpc hk (by rw [ho]; simp) hbr
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [PRes.toState_pc r s hspc]; exact BitVec.eq_of_toNat_eq hpcr
  · intro x hx
    by_cases h0 : x = .x0
    · subst h0; exact getReg_x0_eq _ _
    · exact keepB_ok hkeep s x (List.mem_filter.mpr ⟨mem_allRegs x h0, by simpa using hx⟩)
  · intro A
    rw [PRes.toState_getMem, listBeq_eq (fun _ _ => pairBeq_eq) hm]
def optCheck (o : Option PRes) (f : PRes → Bool) : Bool :=
  match o with
  | some r => f r
  | none => false
theorem optCheck_some {o : Option PRes} {f : PRes → Bool} (h : optCheck o f = true) :
    ∃ r, o = some r ∧ f r = true := by
  unfold optCheck at h
  cases o with
  | none => simp at h
  | some r => exact ⟨r, rfl, h⟩
def srchdM : SymMem :=
  cMem [(120, some 131448), (112, some 131440), (104, some 131432), (96, some 131424)] ++
    [(⟨none, BitVec.ofNat 64 2064⟩, .bin (.st .w 0) (.ld (.c (BitVec.ofNat 64 2064))) (.reg .x19))]
def srchdCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 1435] 30 (pcOf 1421) [] (σK []) []) fun r =>
    runM r 1435 srchdM [.x6, .x7, .x28, .x29] && r.brs.isEmpty && decide (r.cycles ≤ 14)
def mvA (k : Nat) : Nat := 0x8540 - 16 * k
def mvB (k : Nat) : Nat := 0x85e0 - 16 * k
def mvInitCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 3157] 10 (pcOf 3151) [] (σK []) []) fun r =>
    runB r 3157 [] [.x28, .x29, .x30] && regIsB r .x28 (BitVec.ofNat 64 (mvA 0)) &&
      regIsB r .x29 (BitVec.ofNat 64 (mvB 0)) && regIsB r .x30 (BitVec.ofNat 64 0x77f0) && r.brs.isEmpty &&
      decide (r.cycles ≤ 6)
def mvCheck (k : Nat) : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 3157, pcOf 3164] 20 (pcOf 3157) []
      (σK [(.x28, BitVec.ofNat 64 (mvA k)), (.x29, BitVec.ofNat 64 (mvB k)), (.x30, BitVec.ofNat 64 0x77f0)]) []) fun r =>
    runB r (if k < 213 then 3157 else 3164) [(mvB k + 8, some (mvA k + 8)), (mvB k, some (mvA k))]
      [.x6, .x7, .x28, .x29, .x30] && regIsB r .x28 (BitVec.ofNat 64 (mvA (k + 1))) &&
      regIsB r .x29 (BitVec.ofNat 64 (mvB (k + 1))) && regIsB r .x30 (BitVec.ofNat 64 0x77f0) && r.brs.isEmpty &&
      decide (r.cycles ≤ 7)
def mvOK : Bool := (List.range 214).all mvCheck
def sufCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 39153] 20 (pcOf 39142) [] (σK []) []) fun r =>
    runB r 39153 [(0x20260 + 8, some 264), (0x20260, some 256)] [.x6, .x7, .x28, .x29] &&
      regIsB r .x28 (BitVec.ofNat 64 0x840) && regIsB r .x29 (BitVec.ofNat 64 0x2c48) && r.brs.isEmpty &&
      decide (r.cycles ≤ 11)
def clA (k : Nat) : Nat := 0x840 + 8 * k
def clCheck (k : Nat) : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 39153, pcOf 39156] 10 (pcOf 39153) []
      (σK [(.x28, BitVec.ofNat 64 (clA k)), (.x29, BitVec.ofNat 64 0x2c48)]) []) fun r =>
    runB r (if k < 1152 then 39153 else 39156) [(clA k, none)] [.x28, .x29] &&
      regIsB r .x28 (BitVec.ofNat 64 (clA (k + 1))) && regIsB r .x29 (BitVec.ofNat 64 0x2c48) && r.brs.isEmpty &&
      decide (r.cycles ≤ 3)
def clOK : Bool := (List.range 1153).all clCheck
def finCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 249] 10 (pcOf 40872) [] (σK []) []) fun r =>
    runB r 249 [] [.x2] && regIsB r .x2 (BitVec.ofNat 64 0x22000) && r.brs.isEmpty && decide (r.cycles ≤ 3)
end ClaudeWCT.W9.Machine.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem srchdCheck_ok : srchdCheck = true := by decide +kernel
theorem mvInitCheck_ok : mvInitCheck = true := by decide +kernel
theorem mvOK_ok : mvOK = true := by decide +kernel
theorem sufCheck_ok : sufCheck = true := by decide +kernel
theorem clOK_ok : clOK = true := by decide +kernel
theorem finCheck_ok : finCheck = true := by decide +kernel
theorem searchWindow : windowOK 1280 SearchCode.code = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
set_option linter.unusedSimpArgs false
theorem frame_of_eff {s t : MachineState} {L : List (Nat × Option Nat)}
    (h : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = effMem s L A) (W : Nat → Prop)
    (hW : ∀ p ∈ L, W p.1) : Frame s t W := by
  intro A hA hn
  rw [h A hA]
  exact effMem_none (lookW_none_of fun p hp he => hn (he ▸ hW p hp))
theorem replaceWord32_get (w : BitVec 64) (k : Nat) (hk : k < 2) (v : BitVec 32) :
    (replaceWord32 w k v).extractLsb' (32 * k) 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  interval_cases k <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm]
theorem replaceWord32_other (w : BitVec 64) (k k' : Nat) (hk : k < 2) (hk' : k' < 2) (hne : k ≠ k')
    (v : BitVec 32) : (replaceWord32 w k v).extractLsb' (32 * k') 32 = w.extractLsb' (32 * k') 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  have hm2 : Nat.testBit 4294967295 (32 + i) = false := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp
  interval_cases k <;> interval_cases k' <;> simp at hne <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm, hm2]
theorem srchd_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 1421) {N : HashOutput}
    (hN : OutAt s NBUF N) {counter : BitVec 32} (h19 : s.getReg .x19 = BitVec.ofNat 64 counter.toNat) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 14 ∧ t.pc = pcOf 1435 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      OutAt t 0x60 N ∧ (t.getMem (BitVec.ofNat 64 0x810)).extractLsb' 0 32 = counter ∧
      (t.getMem (BitVec.ofNat 64 0x810)).extractLsb' 32 32 = (s.getMem (BitVec.ofNat 64 0x810)).extractLsb' 32 32 ∧
      Frame s t (fun A => (0x60 ≤ A ∧ A < 0x80) ∨ A = 0x810) := by
  obtain ⟨r, hr, hb⟩ := optCheck_some srchdCheck_ok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨hrun, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runM_spec hc hr hrun s hpc (by simp) (by rw [hbr]; simp)
  have hM : ∀ A, A < 2 ^ 64 → memEval s srchdM (BitVec.ofNat 64 A) =
      if A = 120 then s.getMem (BitVec.ofNat 64 131448) else if A = 112 then s.getMem (BitVec.ofNat 64 131440)
      else if A = 104 then s.getMem (BitVec.ofNat 64 131432) else if A = 96 then s.getMem (BitVec.ofNat 64 131424)
      else if A = 2064 then StoreKind.merge .w (s.getMem (BitVec.ofNat 64 2064)) 0 (s.getReg .x19)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    simp only [srchdM, cMem, List.cons_append, List.nil_append]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), memEval_cons_ofNat _ _ _ _ _ hA (by decide),
      memEval_cons_ofNat _ _ _ _ _ hA (by decide), memEval_cons_ofNat _ _ _ _ _ hA (by decide),
      memEval_cons_ofNat _ _ _ _ _ hA (by decide)]
    rfl
  refine ⟨_, _, _, st, hcy, p, rg, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [mm, hM _ (by omega)]
    have := hN k hk
    simp only [NBUF] at this
    interval_cases k
    · simp only [show (0x60 : Nat) + 8 * 0 = 96 from rfl]; simp; exact this
    · simp only [show (0x60 : Nat) + 8 * 1 = 104 from rfl]; simp; exact this
    · simp only [show (0x60 : Nat) + 8 * 2 = 112 from rfl]; simp; exact this
    · simp only [show (0x60 : Nat) + 8 * 3 = 120 from rfl]; simp; exact this
  · rw [mm, hM _ (by decide)]
    simp only [show ((0x810 : Nat) = 120) = False by decide, show ((0x810 : Nat) = 112) = False by decide,
      show ((0x810 : Nat) = 104) = False by decide, show ((0x810 : Nat) = 96) = False by decide,
      show ((0x810 : Nat) = 2064) = True by decide, if_false, if_true]
    simp only [StoreKind.merge, Nat.zero_div]
    have := replaceWord32_get (s.getMem (BitVec.ofNat 64 2064)) 0 (by decide)
      ((s.getReg .x19).truncate 32)
    simp only [Nat.mul_zero] at this
    rw [this, h19]
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [mm, hM _ (by decide)]
    simp only [show ((0x810 : Nat) = 120) = False by decide, show ((0x810 : Nat) = 112) = False by decide,
      show ((0x810 : Nat) = 104) = False by decide, show ((0x810 : Nat) = 96) = False by decide,
      show ((0x810 : Nat) = 2064) = True by decide, if_false, if_true]
    simp only [StoreKind.merge, Nat.zero_div]
    have := replaceWord32_other (s.getMem (BitVec.ofNat 64 2064)) 0 1 (by decide) (by decide) (by decide)
      ((s.getReg .x19).truncate 32)
    simp only [Nat.mul_one] at this
    exact this
  · intro A hA hn
    rw [mm, hM A hA]
    rw [if_neg (fun h => hn (Or.inl (by omega))), if_neg (fun h => hn (Or.inl (by omega))),
      if_neg (fun h => hn (Or.inl (by omega))), if_neg (fun h => hn (Or.inl (by omega))),
      if_neg (fun h => hn (Or.inr (by omega)))]
theorem mvInit_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 3151) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 6 ∧ t.pc = pcOf 3157 ∧ t.getReg .x28 = BitVec.ofNat 64 (mvA 0) ∧
      t.getReg .x29 = BitVec.ofNat 64 (mvB 0) ∧ t.getReg .x30 = BitVec.ofNat 64 0x77f0 ∧
      RegsExcept s t [.x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨r, hr, hb⟩ := optCheck_some mvInitCheck_ok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨hrun, h28⟩, h29⟩, h30⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun s hpc (by simp) (by rw [hbr]; simp)
  exact ⟨_, _, _, st, hcy, p, regIsB_ok h28 s, regIsB_ok h29 s, regIsB_ok h30 s, rg,
    frame_of_eff mm _ (by simp)⟩
structure MvInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 214 then 3157 else 3164)
  x28 : t.getReg .x28 = BitVec.ofNat 64 (mvA k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (mvB k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 0x77f0
  regs : RegsExcept s0 t [.x6, .x7, .x28, .x29, .x30]
  moved : ∀ i, i < k → t.getMem (BitVec.ofNat 64 (mvB i)) = s0.getMem (BitVec.ofNat 64 (mvA i)) ∧
    t.getMem (BitVec.ofNat 64 (mvB i + 8)) = s0.getMem (BitVec.ofNat 64 (mvA i + 8))
  frame : Frame s0 t (fun A => mvB k + 16 ≤ A ∧ A < mvB 0 + 16)
theorem mv_step {im : Image} (hc : NewCodeAt im) {s0 : MachineState} (k : Nat) (hk : k < 214) (t : MachineState)
    (hI : MvInv s0 k t) : ∃ u n cy, Steps im t n cy u ∧ cy ≤ 7 ∧ MvInv s0 (k + 1) u := by
  obtain ⟨r, hr, hb⟩ := optCheck_some (List.all_eq_true.mp mvOK_ok k (List.mem_range.mpr hk))
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨hrun, h28⟩, h29⟩, h30⟩, hbr⟩, hcy⟩ := hb
  have hpc : t.pc = pcOf 3157 := by rw [hI.pc, if_pos hk]
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun t hpc (by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hI.x28
    · exact hI.x29
    · exact hI.x30) (by rw [hbr]; simp)
  have hA : mvA k + 8 < mvB k := by unfold mvA mvB; omega
  have hB : mvB k + 16 ≤ mvB 0 + 16 := by unfold mvB; omega
  have h1 : mvB (k + 1) + 16 = mvB k := by unfold mvB; omega
  refine ⟨_, _, _, st, hcy, ⟨?_, regIsB_ok h28 t, regIsB_ok h29 t, regIsB_ok h30 t,
    (hI.regs.trans rg).mono (by simp), ?_, ?_⟩⟩
  · rw [p]; congr 1; split_ifs <;> omega
  · intro i hi
    have hBi : ∀ i, i ≤ k → mvB k ≤ mvB i := fun i h => by unfold mvB; omega
    have hlt : mvB k < 2 ^ 64 := by unfold mvB; omega
    rcases Nat.lt_or_ge i k with hik | hik
    · have := hI.moved i hik
      have hBik : mvB k + 16 ≤ mvB i := by unfold mvB; omega
      rw [mm _ (by unfold mvB; omega), mm _ (by unfold mvB; omega)]
      unfold effMem
      rw [lookW_cons, if_neg (by omega), lookW_cons, if_neg (by omega), lookW_cons, if_neg (by omega),
        lookW_cons, if_neg (by omega)]
      exact this
    · have hik' : i = k := by omega
      subst hik'
      rw [mm _ (by unfold mvB; omega), mm _ (by unfold mvB; omega)]
      unfold effMem
      rw [lookW_cons, if_neg (by omega), lookW_cons, if_pos rfl, lookW_cons, if_pos rfl]
      simp only
      refine ⟨hI.frame _ (by unfold mvA; omega) (fun h => by unfold mvA mvB at h; omega),
        hI.frame _ (by unfold mvA; omega) (fun h => by unfold mvA mvB at h; omega)⟩
  · have F := frame_of_eff mm (fun A => mvB k ≤ A ∧ A < mvB k + 16) (by
      intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> simp <;> omega)
    refine (hI.frame.trans F).mono (fun A _ h => ?_)
    rw [h1]
    rcases h with h | h <;> constructor <;> omega
theorem mv_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 3151) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 6 + 214 * 7 ∧ t.pc = pcOf 3164 ∧ RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      (∀ i, i < 214 → t.getMem (BitVec.ofNat 64 (mvB i)) = s.getMem (BitVec.ofNat 64 (mvA i)) ∧
        t.getMem (BitVec.ofNat 64 (mvB i + 8)) = s.getMem (BitVec.ofNat 64 (mvA i + 8))) ∧
      Frame s t (fun A => 0x7890 ≤ A ∧ A < 0x85f0) := by
  obtain ⟨t0, k0, c0, s0', hc0, p0, x28, x29, x30, r0, f0⟩ := mvInit_spec hc s hpc
  have I0 : MvInv t0 0 t0 := ⟨by rw [p0]; rfl, x28, x29, x30, RegsExcept.refl _ _, fun i h => absurd h (by omega),
    fun A _ h => rfl⟩
  have gen : ∀ k, k ≤ 214 → ∃ u n cy, Steps im t0 n cy u ∧ cy ≤ 7 * k ∧ MvInv t0 k u := by
    intro k
    induction k with
    | zero => intro _; exact ⟨t0, 0, 0, Steps.refl _, le_refl _, I0⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, n, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, n', cy', sv, hcy', hv⟩ := mv_step hc k (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, n, cy, su, hcy, hu⟩ := gen 214 le_rfl
  have g0 : ∀ A, A < 2 ^ 64 → t0.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f0 A hA (fun h => h)
  refine ⟨u, _, _, s0'.trans su, by omega, by rw [hu.pc]; rfl, (r0.trans hu.regs).mono (by simp), ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hu.moved i hi
    rw [h1, h2, g0 _ (by unfold mvA; omega), g0 _ (by unfold mvA; omega)]
    exact ⟨rfl, rfl⟩
  · refine (f0.trans hu.frame).mono (fun A _ h => ?_)
    rcases h with h | h
    · exact h.elim
    · unfold mvB at h; constructor <;> omega
theorem suf_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 39142) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 11 ∧ t.pc = pcOf 39153 ∧ t.getReg .x28 = BitVec.ofNat 64 (clA 0) ∧
      t.getReg .x29 = BitVec.ofNat 64 0x2c48 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      t.getMem (BitVec.ofNat 64 0x20260) = s.getMem (BitVec.ofNat 64 0x100) ∧
      t.getMem (BitVec.ofNat 64 (0x20260 + 8)) = s.getMem (BitVec.ofNat 64 0x108) ∧
      Frame s t (fun A => A = 0x20260 ∨ A = 0x20260 + 8) := by
  obtain ⟨r, hr, hb⟩ := optCheck_some sufCheck_ok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hrun, h28⟩, h29⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun s hpc (by simp) (by rw [hbr]; simp)
  refine ⟨_, _, _, st, hcy, p, regIsB_ok h28 s, regIsB_ok h29 s, rg, ?_, ?_, ?_⟩
  · rw [mm _ (by decide)]; rfl
  · rw [mm _ (by decide)]; rfl
  · exact frame_of_eff mm _ (by
      intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl
      · right; rfl
      · left; rfl)
structure ClInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 1153 then 39153 else 39156)
  x28 : t.getReg .x28 = BitVec.ofNat 64 (clA k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 0x2c48
  regs : RegsExcept s0 t [.x28, .x29]
  mem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
    if 0x840 ≤ A ∧ A < clA k ∧ A % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem cl_step {im : Image} (hc : NewCodeAt im) {s0 : MachineState} (k : Nat) (hk : k < 1153) (t : MachineState)
    (hI : ClInv s0 k t) : ∃ u n cy, Steps im t n cy u ∧ cy ≤ 3 ∧ ClInv s0 (k + 1) u := by
  obtain ⟨r, hr, hb⟩ := optCheck_some (List.all_eq_true.mp clOK_ok k (List.mem_range.mpr hk))
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hrun, h28⟩, h29⟩, hbr⟩, hcy⟩ := hb
  have hpc : t.pc = pcOf 39153 := by rw [hI.pc, if_pos hk]
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun t hpc (by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact hI.x28
    · exact hI.x29) (by rw [hbr]; simp)
  refine ⟨_, _, _, st, hcy, ⟨?_, regIsB_ok h28 t, regIsB_ok h29 t, (hI.regs.trans rg).mono (by simp), ?_⟩⟩
  · rw [p]; congr 1; split_ifs <;> omega
  · intro A hA
    rw [mm A hA]
    unfold effMem
    rw [lookW_cons]
    by_cases h : clA k = A
    · rw [if_pos h]
      simp only
      rw [if_pos ⟨by unfold clA at h; omega, by unfold clA at h ⊢; omega, by unfold clA at h; omega⟩]
    · rw [if_neg h]
      simp only [lookW]
      rw [hI.mem A hA]
      unfold clA at h ⊢
      by_cases h1 : 0x840 ≤ A ∧ A < 0x840 + 8 * k ∧ A % 8 = 0
      · rw [if_pos h1, if_pos ⟨h1.1, by omega, h1.2.2⟩]
      · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.1, by omega, h2.2.2⟩)]
theorem cl_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 39153)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (clA 0)) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x2c48) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 3 * 1153 ∧ t.pc = pcOf 39156 ∧ RegsExcept s t [.x28, .x29] ∧
      ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
        if 0x840 ≤ A ∧ A < 0x2c48 ∧ A % 8 = 0 then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have I0 : ClInv s 0 s := ⟨by rw [hpc]; rfl, h28, h29, RegsExcept.refl _ _, fun A _ => by
    rw [if_neg (fun h => by unfold clA at h; omega)]⟩
  have gen : ∀ k, k ≤ 1153 → ∃ u n cy, Steps im s n cy u ∧ cy ≤ 3 * k ∧ ClInv s k u := by
    intro k
    induction k with
    | zero => intro _; exact ⟨s, 0, 0, Steps.refl _, le_refl _, I0⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, n, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, n', cy', sv, hcy', hv⟩ := cl_step hc k (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, n, cy, su, hcy, hu⟩ := gen 1153 le_rfl
  exact ⟨u, n, cy, su, hcy, by rw [hu.pc]; rfl, hu.regs, fun A hA => by rw [hu.mem A hA]; rfl⟩
theorem fin_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 40872) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 3 ∧ t.pc = pcOf 249 ∧ t.getReg .x2 = BitVec.ofNat 64 0x22000 ∧
      RegsExcept s t [.x2] ∧ Frame s t (fun _ => False) := by
  obtain ⟨r, hr, hb⟩ := optCheck_some finCheck_ok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hrun, h2⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun s hpc (by simp) (by rw [hbr]; simp)
  exact ⟨_, _, _, st, hcy, p, regIsB_ok h2 s, rg, frame_of_eff mm _ (by simp)⟩
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def pairDigs (pairs : List (Digest × Digest)) : List Digest := pairs.flatMap fun p => [p.1, p.2]
theorem pairDigs_length (pairs : List (Digest × Digest)) : (pairDigs pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp [pairDigs, List.flatMap_cons] at ih ⊢; omega
theorem pairDigs_bytes (pairs : List (Digest × Digest)) :
    pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = (pairDigs pairs).flatMap (bytesLE 16) := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairDigs, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih]; simp
theorem pairDigs_getD (pairs : List (Digest × Digest)) (k : Nat) :
    (pairDigs pairs).getD (2 * k) 0 = (pairs.getD k (0, 0)).1 ∧
      (pairDigs pairs).getD (2 * k + 1) 0 = (pairs.getD k (0, 0)).2 := by
  induction pairs generalizing k with
  | nil => simp [pairDigs]
  | cons p ps ih =>
    rcases k with _ | k
    · simp [pairDigs, List.flatMap_cons]
    · have := ih k
      simp only [pairDigs, List.flatMap_cons] at this ⊢
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 1 + 2 by ring]
      simp only [List.getD_eq_getElem?_getD] at this ⊢
      simpa using this
theorem forestInput_eq (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestInput index pairs = zero16 ++ bytesLE 16 (header 15 0 index 0 0) ++ (pairDigs pairs).flatMap (bytesLE 16) := by
  unfold WCT9.forestInput; rw [pairDigs_bytes]
theorem forestInput_length (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    (WCT9.forestInput index pairs).length = 320 := by
  have hfl : ((pairDigs pairs).flatMap (bytesLE 16)).length = 288 := by
    rw [List.length_flatMap]; simp [bytesLE_length, pairDigs_length, hlen]
  rw [forestInput_eq]
  simp only [List.length_append, bytesLE_length, hfl, zero16, List.length_replicate]
theorem pad64_forest (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    pad64 (WCT9.forestInput index pairs) = WCT9.forestInput index pairs := by
  unfold pad64; rw [forestInput_length index pairs hlen]; simp
theorem forest_words (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    wordsOf (pad64 (WCT9.forestInput index pairs)) =
      [0, 0] ++ [BitVec.ofNat 64 (hdr0 15 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        wordsOf ((pairDigs pairs).flatMap (bytesLE 16)) := by
  rw [pad64_forest index pairs hlen, forestInput_eq,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length, zero16, List.length_replicate]),
    wordsOf_append _ _ (by simp only [zero16, List.length_replicate]), wordsOf_header,
    show zero16 = List.replicate (8 * 2) 0 from rfl, wordsOf_replicate_zero]
  rfl
def FtsW (A : Nat) : Prop := (0x840 ≤ A ∧ A < 0x2c40) ∨ (0x400 ≤ A ∧ A < 0x550) ∨ (0x100 ≤ A ∧ A < 0x120)
def ftsCost : Nat := 31 + (9 * coordCost + (9 + (8 * 5 + 1)))
theorem drvInv_zero {sig : WCT9.Signature} {N : HashOutput} {sF t : MachineState}
    (hpc : t.pc = pcOf (base + 34)) (hr : DRegs (N.toNat % 2 ^ 31) t)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)))
    (h28 : t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1)))
    (h15 : t.getReg .x15 = BitVec.ofNat 64 (N.toNat % 2 ^ 31 * 2 ^ 27 + 65536 * (0 - 1)))
    (hf : Frame sF t (fun _ => False)) :
    DrvInv sig N sF 0 [] t :=
  ⟨hpc, hr, h8, h28, h15, fun h => absurd h (by omega), rfl, fun _ h => absurd h (by omega),
    hf.mono (fun _ _ h => h.elim)⟩
theorem fts_tb {im : Image} (hc : NewCodeAt im) {sk : BitVec 256} {sig : WCT9.Signature} {N : HashOutput}
    {sF : MachineState} (hin : FtsIn sig N sF) (hpc : sF.pc = pcOf base) (h5 : sF.getReg .x5 = 0) :
    TBSim im sk sF ftsCost (WCT9.recoverFts sig (N.toNat % 2 ^ 31) N)
      (fun root t => t.pc = pcOf 39142 ∧ t.getReg .x5 = 0 ∧ DigAt t 0x100 root ∧ Frame sF t FtsW) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hg : N.toNat / 2 ^ 234 % 2 ^ 14 < 5 := ((admissible_iff N).mp hin.adm).1
  obtain ⟨t0, s0, p0, r0, x8_0, x28_0, x15_0, f0⟩ := drv_entry hc N sF hpc h5 hin.out hg
  have hI0 : DrvInv sig N sF 0 [] t0 := drvInv_zero (by rw [p0]) r0 x8_0 x28_0 x15_0 f0
  unfold WCT9.recoverFts
  have hbody : ∀ (i : Fin 9) (pre : List (Digest × Digest)) (t : MachineState), pre.length = i.val →
      DrvInv sig N sF pre.length pre t →
      TBSim im sk t coordCost (WCT9.recoverCoordinate sig (N.toNat % 2 ^ 31) N i)
        (fun d u => DrvInv sig N sF (pre ++ [d]).length (pre ++ [d]) u) := by
    intro i pre t hlen hI
    rw [hlen] at hI
    have h1 := coord_tb (sk := sk) hc hin i.val i.isLt pre t hI
    refine h1.mono (le_refl _) (fun d u h => ?_)
    rw [List.length_append, List.length_singleton, hlen]
    exact h
  have hmap := SigGolfCandidate.T3M.Expand.tb_mapM_finRange (image := im) (sk := sk) 9
    (WCT9.recoverCoordinate sig (N.toNat % 2 ^ 31) N) coordCost
    (fun pre t => DrvInv sig N sF pre.length pre t) hbody hI0
  refine (TBSim.steps s0 (TBSim.bind (W₂ := 9 + (8 * 5 + 1)) hmap (fun pairs u hu => ?_))).mono
    (by unfold ftsCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hI⟩ := hu
  rw [hlen] at hI
  obtain ⟨t1, s1, p1, e1, m400, m408, m410, m418, h10, h11, h12, k1, f1⟩ := forest_blk hc u (by rw [hI.pc]; rfl)
  have hpd : DigsAt t1 0x420 (pairDigs pairs) := by
    intro i hi
    rw [pairDigs_length, hlen] at hi
    have g1 : ∀ A, 0x420 ≤ A → A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
      fun A hA hA' => f1 A hA' (by omega)
    obtain ⟨k', hk'⟩ : ∃ k', i = 2 * k' ∨ i = 2 * k' + 1 := ⟨i / 2, by omega⟩
    have hP := hI.pairs k' (by omega)
    have hg := pairDigs_getD pairs k'
    rcases hk' with rfl | rfl
    · rw [hg.1, show 0x420 + 16 * (2 * k') = pslot k' by unfold pslot; ring]
      exact ⟨(g1 _ (by unfold pslot; omega) (by unfold pslot; omega)).trans hP.1.1, (g1 _ (by unfold pslot; omega) (by unfold pslot; omega)).trans hP.1.2⟩
    · rw [hg.2, show 0x420 + 16 * (2 * k' + 1) = pslot k' + 16 by unfold pslot; ring]
      exact ⟨(g1 _ (by unfold pslot; omega) (by unfold pslot; omega)).trans hP.2.1, (g1 _ (by unfold pslot; omega) (by unfold pslot; omega)).trans hP.2.2⟩
  have x22u : u.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31) := hI.regs.x22
  have hw : t1.readWords (BitVec.ofNat 64 0x400) (8 * (4 + 1)) =
      wordsOf (pad64 (WCT9.forestInput (N.toNat % 2 ^ 31) pairs)) := by
    rw [forest_words _ pairs hlen]
    have hd : (pairDigs pairs).length = 18 := by rw [pairDigs_length, hlen]
    have hz : t1.readWords (BitVec.ofNat 64 0x400) 2 = [0, 0] := by
      rw [readWords_two, m400, show 0x400 + 8 = 0x408 from rfl, m408]
    have hhd : t1.readWords (BitVec.ofNat 64 (0x400 + 8 * 2)) 2 =
        [BitVec.ofNat 64 (hdr0 15 0 (N.toNat % 2 ^ 31) 0), BitVec.ofNat 64 (hdr1 (N.toNat % 2 ^ 31) 0)] := by
      rw [readWords_two, show 0x400 + 8 * 2 = 0x410 from rfl, m410, show 0x410 + 8 = 0x418 from rfl, m418, x22u, hdr0_index _ _ _ hidx, hdr1_eq _ 0 (by omega) (by decide)]
      simp; rfl
    have e40 : 8 * (4 + 1) = 2 + (2 + 2 * (pairDigs pairs).length) := by rw [hd]
    rw [e40, readWords_add, readWords_add, hz, hhd, show 0x400 + 8 * 2 + 8 * 2 = 0x420 from rfl, hpd.words]
    simp only [List.append_assoc]
  have hq : hashInput t1 = toQ (pad64 (WCT9.forestInput (N.toNat % 2 ^ 31) pairs)) :=
    hashInput_toQ t1 _ 4 0x400 (by rw [pad64_forest _ pairs hlen, forestInput_length _ pairs hlen])
      h10 (by decide) (by decide) h11 (by decide) hw
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 0x400 320 0x100 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5' : t1.getReg .x5 = 0 := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x5
  have hblk : (toQ (pad64 (WCT9.forestInput (N.toNat % 2 ^ 31) pairs))).blocks = 5 := by
    rw [blocks_toQ ⟨by rw [pad64_forest _ pairs hlen, forestInput_length _ pairs hlen]; decide,
      by rw [pad64_forest _ pairs hlen, forestInput_length _ pairs hlen]⟩,
      pad64_forest _ pairs hlen, forestInput_length _ pairs hlen]
  have hprog : WCT9.forestPk (N.toNat % 2 ^ 31) pairs =
      (shortHash (WCT9.forestInput (N.toNat % 2 ^ 31) pairs) >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.steps s1 (SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (W := 1) e1 h5' hv hq
    (fun a => ?_))).mono (by rw [hblk]) (fun _ _ h => h)
  have p2 : (writeHash t1 a).pc = pcOf (base + 204) := by rw [pc_writeHash, p1, pcOf_add4]
  obtain ⟨t2, s2, p3, k2, m2⟩ := end_blk hc (writeHash t1 a) p2
  have hd := DigAt.writeHash_lo t1 a 0x100 h12 (by decide)
  have fw := Frame.writeHash t1 a 0x100 h12 (by decide)
  refine TBSim.steps s2 (TBSim.pure ⟨p3, ?_, ⟨(m2 _).trans hd.1, (m2 _).trans hd.2⟩, ?_⟩)
  · rw [k2, getReg_writeHash]; exact h5'
  have F2 : Frame (writeHash t1 a) t2 (fun _ => False) := fun A _ _ => m2 _
  refine ((((hI.frame.trans f1).trans fw).trans F2)).mono (fun A _ h => ?_)
  rcases h with (((h | h) | h) | h) | h
  · left; exact ⟨h.1, by unfold regBase at h; omega⟩
  · right; left; omega
  · right; left; omega
  · right; right; omega
  · exact h.elim
end ClaudeWCT.W9.Machine.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (regionBytes merkleBytes chainBytes leafBytes regionBytes_length region_merkle region_chain
  region_prefix region_leaf merkleBytes_window chainBytes_window leafBytes_window_zero leafBytes_window_succ
  openingList sigDigests sigDigests_opening)
set_option linter.unusedSimpArgs false
def cellD (j : Nat) (op : WCT9.Opening) (m : Nat) : Digest :=
  match wSrc j (2 * m) with
  | some o => (openingList op).getD (o / 16) 0
  | none => 0
theorem openingList_val (op : WCT9.Opening) (t : Nat) (ht : t < 7) : (openingList op).getD t 0 = op.values ⟨t, ht⟩ := by
  unfold openingList
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega), List.getElem_ofFn]
theorem openingList_path (op : WCT9.Opening) (l : Nat) (hl : l < 7) :
    (openingList op).getD (7 + l) 0 = op.path ⟨l, hl⟩ := by
  unfold openingList
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
theorem region_guard (c : Nat) (op : WCT9.Opening) : window (regionBytes c op) 1008 16 = zeros 16 := by
  unfold regionBytes
  rw [window_append_right _ _ _ _ (by simp [ClaudeWCT.W9.T3M.merkleBytes_length, ClaudeWCT.W9.T3M.chainBytes_length,
    ClaudeWCT.W9.T3M.leafBytes_length, zeros])]
  simp only [List.length_append, ClaudeWCT.W9.T3M.merkleBytes_length, ClaudeWCT.W9.T3M.chainBytes_length,
    ClaudeWCT.W9.T3M.leafBytes_length, zeros, List.length_replicate]
  exact window_zeros _ _ _ (by omega)
theorem zeros_eq : zeros 16 = bytesLE 16 (0 : Digest) := zeros16
theorem cell_window (j : Nat) (op : WCT9.Opening) (m : Nat) (hm : m < 64) :
    window (regionBytes j op) (16 * m) 16 = bytesLE 16 (cellD j op m) := by
  unfold cellD wSrc
  have h2 : 2 * m / 2 = m := by omega
  have h8 : 2 * m / 8 = m / 4 := by omega
  have h1 : 2 * m % 2 = 0 := by omega
  simp only [h2, h8, h1, Nat.mul_zero, Nat.add_zero]
  by_cases hA : m < 28
  ·
    rw [if_pos hA]
    set l : Fin 7 := ⟨6 - m / 4, by omega⟩ with hl
    have ho : 16 * m = 64 * (6 - l.val) + 16 * (m % 4) := by simp only [hl]; omega
    rw [region_merkle _ _ _ _ (by omega), ho, merkleBytes_window _ _ l _ (by omega)]
    have hlv : l.val = 6 - m / 4 := rfl
    have hb : j / 2 ^ l.val % 2 < 2 := Nat.mod_lt _ (by decide)
    have hq : m % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [hlv] at hb ⊢
    by_cases hbit : j / 2 ^ (6 - m / 4) % 2 = 1
    · rw [if_pos hbit]
      by_cases hq0 : m % 4 = 0
      · rw [if_pos (Or.inl ⟨hbit, hq0⟩), hq0, Nat.mul_zero, window_append_left _ _ _ _ (by simp [bytesLE_length]),
          window_full _ _ (bytesLE_length _ _)]
        dsimp only
        rw [show (112 + 16 * (6 - m / 4)) / 16 = 7 + (6 - m / 4) by omega,
          openingList_path op _ (by omega)]
      · rw [if_neg (by omega), window_append_right _ _ _ _ (by simp [bytesLE_length]; omega), window_zeros _ _ _
          (by simp [bytesLE_length]; omega), zeros_eq]
    · have hbit0 : j / 2 ^ (6 - m / 4) % 2 = 0 := by omega
      rw [if_neg (by omega)]
      by_cases hq3 : m % 4 = 3
      · rw [if_pos (Or.inr ⟨hbit0, hq3⟩), hq3, window_append_right _ _ _ _ (by simp [zeros]),
          show 16 * 3 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
        dsimp only
        rw [show (112 + 16 * (6 - m / 4)) / 16 = 7 + (6 - m / 4) by omega, openingList_path op _ (by omega)]
      · rw [if_neg (by omega), window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega),
          zeros_eq]
  rw [if_neg hA]
  by_cases hB : m < 52
  ·
    rw [if_pos hB]
    set i : Fin 6 := ⟨5 - (m - 28) / 4, by omega⟩ with hi
    have ho : 16 * m - 448 = 64 * (5 - i.val) + 16 * ((m - 28) % 4) := by simp only [hi]; omega
    rw [region_chain _ _ _ _ (by omega) (by omega), ho, chainBytes_window _ i _ (by omega)]
    by_cases hq3 : (m - 28) % 4 = 3
    · rw [if_pos hq3, hq3, window_append_right _ _ _ _ (by simp [zeros]),
        show 16 * 3 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
      dsimp only
      rw [show 16 * (6 - (m - 28) / 4) / 16 = 6 - (m - 28) / 4 by omega, openingList_val op _ (by omega)]
      have e : i.succ = ⟨6 - (m - 28) / 4, by omega⟩ := by ext; simp [hi]; omega
      rw [e]
    · rw [if_neg hq3, window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega), zeros_eq]
  rw [if_neg hB]
  by_cases hC : m = 55
  · subst hC
    rw [if_pos rfl, region_leaf _ _ _ _ (by omega) (by omega), show 16 * 55 - 880 = 0 by rfl, leafBytes_window_zero]
    dsimp only
    rw [show 0 / 16 = 0 from rfl, openingList_val op 0 (by omega)]
    rfl
  rw [if_neg hC]
  by_cases hD : 57 ≤ m ∧ m < 63
  · rw [if_pos hD, region_leaf _ _ _ _ (by omega) (by omega),
      show 16 * m - 880 = 32 + 16 * (⟨m - 57, by omega⟩ : Fin 6).val by simp; omega, leafBytes_window_succ]
    dsimp only
    rw [show 16 * (m - 56) / 16 = m - 56 by omega, openingList_val op _ (by omega)]
    congr 2
    ext; simp; omega
  rw [if_neg hD]
  by_cases hE : m < 55
  · rw [region_prefix _ _ _ _ (by omega) (by omega), zeros_eq]
  by_cases hF : m = 56
  · subst hF
    rw [region_leaf _ _ _ _ (by omega) (by omega), show 16 * 56 - 880 = 16 by rfl]
    unfold ClaudeWCT.W9.T3M.leafBytes
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
      window_append_right _ _ _ _ (by simp [bytesLE_length]), show 16 - (bytesLE 16 (op.values 0)).length = 0 by
        simp [bytesLE_length], window_zeros _ _ _ (by omega), zeros_eq]
  have : m = 63 := by omega
  subst this
  rw [show 16 * 63 = 1008 by rfl, region_guard, zeros_eq]
theorem wSrc_split (j i : Nat) : wSrc j i = (wSrc j (2 * (i / 2))).map (· + 8 * (i % 2)) := by
  unfold wSrc
  have h2 : 2 * (i / 2) / 2 = i / 2 := by omega
  have h8 : 2 * (i / 2) / 8 = i / 8 := by omega
  have h1 : 2 * (i / 2) % 2 = 0 := by omega
  simp only [h2, h8, h1, Nat.mul_zero, Nat.add_zero]
  split_ifs <;> simp
theorem wSrc_even (j m o : Nat) (h : wSrc j (2 * m) = some o) : o % 16 = 0 ∧ o < 224 := by
  unfold wSrc at h
  have h2 : 2 * m / 2 = m := by omega
  have h8 : 2 * m / 8 = m / 4 := by omega
  have h1 : 2 * m % 2 = 0 := by omega
  simp only [h2, h8, h1, Nat.mul_zero, Nat.add_zero] at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h; omega)
theorem placed_of {N : HashOutput} {sig : WCT9.Signature} {s0 t : MachineState}
    (hsig : ∀ n, n < 127 → DigAt s0 (0x7000 + 16 * n) ((sigDigests sig).getD n 0))
    (hdone : ∀ k i, (hk : k < 9) → i < 128 → t.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) =
      match wSrc (WCT9.child N ⟨k, hk⟩).val i with
      | some o => s0.getMem (BitVec.ofNat 64 (sigBlk k + o))
      | none => 0) :
    Placed N sig t := by
  intro k i hk hi
  have hk' : (⟨k % 9, Nat.mod_lt _ (by decide)⟩ : WCT9.Coord) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
  unfold regionWord
  rw [hk', hdone k i hk hi]
  set j := (WCT9.child N ⟨k, hk⟩).val
  set op := sig.openings ⟨k, hk⟩
  have hw := words_of_window16 (regionBytes j op) (regionBytes_length _ _) (16 * (i / 2)) (by omega) (by omega)
    _ (cell_window j op (i / 2) (by omega))
  rw [show 16 * (i / 2) / 8 = 2 * (i / 2) by omega] at hw
  have hgi : (wordsOf (regionBytes j op)).getD i 0 =
      if i % 2 = 0 then (cellD j op (i / 2)).extractLsb' 0 64 else (cellD j op (i / 2)).extractLsb' 64 64 := by
    split
    · rw [show i = 2 * (i / 2) by omega]; rw [show 2 * (i / 2) / 2 = i / 2 by omega]; exact hw.1
    · rw [show i = 2 * (i / 2) + 1 by omega]; rw [show (2 * (i / 2) + 1) / 2 = i / 2 by omega]; exact hw.2
  rw [hgi, wSrc_split]
  unfold cellD
  cases hs : wSrc j (2 * (i / 2)) with
  | none => simp
  | some o =>
    simp only [Option.map_some]
    obtain ⟨h16, h224⟩ := wSrc_even j (i / 2) o hs
    have hd := hsig (1 + 14 * k + o / 16) (by omega)
    have hop := sigDigests_opening sig ⟨k, hk⟩ (o / 16) (by omega)
    simp only at hop
    rw [hop] at hd
    split
    · rename_i h0
      rw [h0, Nat.mul_zero, Nat.add_zero, show sigBlk k + o = 0x7000 + 16 * (1 + 14 * k + o / 16) by
        unfold sigBlk; omega]
      exact hd.1
    · rename_i h0
      rw [show i % 2 = 1 by omega, show sigBlk k + (o + 8 * 1) = 0x7000 + 16 * (1 + 14 * k + o / 16) + 8 by
        unfold sigBlk; omega]
      exact hd.2
end ClaudeWCT.W9.Machine.Expand
end

section



namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
theorem hdrBank_frame {s t : MachineState} {W : Nat → Prop} (h : HdrBankOK s) (hf : Frame s t W)
    (hW : ∀ A, HB0 ≤ A → A < HB0 + 4608 → ¬ W A) : HdrBankOK t := by
  intro k hk
  obtain ⟨h2, h3⟩ := h k hk
  have g : ∀ A, HB0 ≤ A → A < HB0 + 4608 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A a b => hf A (by unfold HB0 at *; omega) (hW A a b)
  refine ⟨?_, ?_⟩
  · rw [g _ (by omega) (by unfold HB0; omega)]; exact h2
  · rw [g _ (by omega) (by unfold HB0; omega)]; exact h3
theorem searchAt_new {im : Image} (hc : NewCodeAt im) : SearchAt im 1280 :=
  codeAt_of_window hc (by decide +kernel) searchWindow
theorem hook_step {im : Image} (hh : HookAt im) (s : MachineState) (hpc : s.pc = pcOf 30) :
    Steps im s 1 1 (s.setPC (pcOf 1280)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo hookWord 30 = some 1280 by decide)
  exact jal_x0_step hh hd hoff s hpc
theorem newCost_split : 1 + (2 ^ 21 * 150 + 6 + 20000) ≤ newCost := by unfold newCost; norm_num
def NewPostHi (sig : WCT9.Signature) (s0 : MachineState) (r : Option (BitVec 32 × HashOutput × Digest))
    (t : MachineState) : Prop :=
  NewPost sig s0 r t ∧ (r.isSome → (t.getMem (BitVec.ofNat 64 0x810)).extractLsb' 32 32 =
    (s0.getMem (BitVec.ofNat 64 0x810)).extractLsb' 32 32)
theorem newCode_tb {im : Image} (hc : NewCodeAt im) (hh : HookAt im) (sk : BitVec 256) (m : Message)
    (sig : WCT9.Signature) (s : MachineState) (hpre : Pre30 m sig s) :
    TBSim im sk s newCost (newProg m sig) (NewPostHi sig s) := by
  have s1 := hook_step hh s hpre.pc
  set u1 := s.setPC (pcOf 1280) with hu1
  have g1 : ∀ A, u1.getMem A = s.getMem A := fun _ => rfl
  have r1 : ∀ x, u1.getReg x = s.getReg x := fun _ => rfl
  have hS : SrchPre 1280 u1 sig.rho m :=
    ⟨rfl, by rw [r1]; exact hpre.x5, by rw [r1]; exact hpre.x19, hpre.rho, hpre.msg⟩
  unfold newProg
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 20000) (search_tbsim (sk := sk) (searchAt_new hc) hS)
    (fun res t2 h2 => ?_))).mono newCost_split (fun _ _ h => h)
  rcases res with _ | ⟨counter, N⟩
  · exact (TBSim.pure (Q := NewPostHi sig s) (a := none) ⟨h2, fun h => absurd h (by simp)⟩).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨p2, x5_2, adm2, out2, idx2, x22_2, r2, f2, hc2, x19_2⟩ := h2
  obtain ⟨t3, k3, c3, st3, hc3, p3, r3, out3, dc3, hi3, f3⟩ := srchd_spec hc t2 p2 out2 x19_2
  have nS : ∀ A, (A < 0x60 ∨ 0x80 ≤ A) → A ≠ 0x810 → ¬ ((0x60 ≤ A ∧ A < 0x80) ∨ A = 0x810) := by
    intro A h1 h2 h; omega
  have nW : ∀ A, ¬ (A = 0x20130 ∨ A = 0x20138) → (A < 0x20160 ∨ 0x20180 ≤ A) → A ≠ 0x20550 → ¬ SrchW A := by
    intro A h1 h2 h3 h; unfold SrchW at h; simp only [DIG, NBUF, IDXV] at h; omega
  have g3 : ∀ A, A < 2 ^ 64 → (A < 0x60 ∨ 0x80 ≤ A) → A ≠ 0x810 → ¬ (A = 0x20130 ∨ A = 0x20138) →
      (A < 0x20160 ∨ 0x20180 ≤ A) → A ≠ 0x20550 → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4 h5
    rw [f3 A hA (nS A h1 h2), f2 A hA (nW A h3 h4 h5)]; rfl
  have nbuf3 : OutAt t3 NBUF N := fun k hk => by
    rw [f3 _ (by simp only [NBUF]; omega) (nS _ (by simp only [NBUF]; omega) (by simp only [NBUF]; omega))]
    exact out2 k hk
  have hz3 : ∀ k i, k < 9 → i < 128 → t3.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0 := by
    intro k i hk hi
    rw [g3 _ (by unfold regBase; omega) (by unfold regBase; omega) (by unfold regBase; omega)
      (by unfold regBase; omega) (by unfold regBase; omega) (by unfold regBase; omega)]
    exact hpre.zeroW _ (by unfold regBase; omega) (by unfold regBase; omega)
  obtain ⟨t4, k4, c4, st4, hc4, hI4⟩ := place_spec hc placeOK_init p3 nbuf3 hz3
  have p4 : t4.pc = pcOf 3151 := by rw [hI4.pc, cOff_nine]
  obtain ⟨t5, k5, c5, st5, hc5, p5, r5, mv5, f5⟩ := mv_spec hc t4 p4
  have x5_5 : t5.getReg .x5 = 0 := by
    rw [r5.get (by decide), hI4.regs.get (by decide), r3.get (by decide)]; exact x5_2
  have g5 : ∀ A, A < 2 ^ 64 → (A < 0x60 ∨ 0x80 ≤ A) → A ≠ 0x810 → ¬ (A = 0x20130 ∨ A = 0x20138) →
      (A < 0x20160 ∨ 0x20180 ≤ A) → A ≠ 0x20550 → (A < 0x840 ∨ 0x2c40 ≤ A) → (A < 0x7890 ∨ 0x85f0 ≤ A) →
      t5.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4 h5 h6 h7
    rw [f5 A hA (by omega), hI4.frame A hA (by unfold regBase; omega), g3 A hA h1 h2 h3 h4 h5]
  have hsig3 : ∀ n, n < 127 → DigAt t3 (0x7000 + 16 * n) ((ClaudeWCT.W9.T3M.sigDigests sig).getD n 0) := by
    intro n hn
    have := hpre.sigAt n (by omega)
    exact ⟨(g3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans this.1,
      (g3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans this.2⟩
  have hplaced5 : Placed N sig t5 := placed_of hsig3 (fun k i hk hi => by
    rw [f5 _ (by unfold regBase; omega) (by unfold regBase; omega)]
    exact hI4.done k i (by omega) hk hi)
  have hin : FtsIn sig N t5 := by
    have F1 : Frame s u1 (fun _ => False) := fun _ _ _ => rfl
    have F5 := (((F1.trans f2).trans f3).trans hI4.frame).trans f5
    refine ⟨fun k hk => ?_, adm2, hplaced5, hdrBank_frame hpre.bank F5 ?_⟩
    · rw [f5 _ (by omega) (by omega), hI4.frame _ (by omega) (by unfold regBase; omega)]; exact out3 k hk
    · intro A h1 h2 h
      unfold HB0 at h1 h2
      rcases h with ((((h | h) | h) | h) | h)
      · exact h
      · unfold SrchW at h; simp only [DIG, NBUF, IDXV] at h; omega
      · omega
      · unfold regBase at h; omega
      · omega
  refine (TBSim.steps (st3.trans (st4.trans st5)) (TBSim.bind (W₂ := 11 + 3 * 1153 + 9 * 204 + 3)
    (fts_tb hc hin p5 x5_5) (fun root t6 h6 => ?_))).mono
    (by unfold ftsCost coordCost; omega) (fun _ _ h => h)
  obtain ⟨p6, x5_6, root6, f6⟩ := h6
  obtain ⟨t7, k7, c7, st7, hc7, p7, x28_7, x29_7, r7, enc7lo, enc7hi, f7⟩ := suf_spec hc t6 p6
  obtain ⟨t8, k8, c8, st8, hc8, p8, r8, m8⟩ := cl_spec hc t7 p7 x28_7 x29_7
  have g8 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x2c48 ≤ A) → t8.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => by rw [m8 A hA, if_neg (by omega)]
  have nF : ∀ A, (A < 0x840 ∨ 0x2c40 ≤ A) → (A < 0x400 ∨ 0x550 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → ¬ FtsW A := by
    intro A h1 h2 h3 h; unfold FtsW at h; omega
  have g7 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x2c40 ≤ A) → (A < 0x400 ∨ 0x550 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) →
      A ≠ 0x20260 → A ≠ 0x20268 → t7.getMem (BitVec.ofNat 64 A) = t5.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4 h5
    rw [f7 A hA (by omega), f6 A hA (nF A h1 h2 h3)]
  have nbuf8 : OutAt t8 NBUF N := fun k hk => by
    rw [g8 _ (by simp only [NBUF]; omega) (by simp only [NBUF]; omega),
      g7 _ (by simp only [NBUF]; omega) (by simp only [NBUF]; omega) (by simp only [NBUF]; omega)
        (by simp only [NBUF]; omega) (by simp only [NBUF]; omega) (by simp only [NBUF]; omega),
      f5 _ (by simp only [NBUF]; omega) (by simp only [NBUF]; omega),
      hI4.frame _ (by simp only [NBUF]; omega) (by simp only [NBUF]; unfold regBase; omega)]
    exact nbuf3 k hk
  have hz8 : ∀ k i, k < 9 → i < 128 → t8.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0 := by
    intro k i hk hi
    rw [m8 _ (by unfold regBase; omega), if_pos (by unfold regBase; omega)]
  obtain ⟨t9, k9, c9, st9, hc9, hI9⟩ := place_spec hc placeOK_rest p8 nbuf8 hz8
  have p9 : t9.pc = pcOf 40872 := by rw [hI9.pc, cOff_nine]
  obtain ⟨t10, k10, c10, st10, hc10, p10, x2_10, r10, f10⟩ := fin_spec hc t9 p9
  refine (TBSim.steps (st7.trans (st8.trans (st9.trans st10))) (TBSim.pure (Q := NewPostHi sig s)
    (a := some (counter, N, root)) ⟨?_, fun _ => ?_⟩)).mono (by omega) (fun _ _ h => h)
  swap
  ·
    have e3 : t10.getMem (BitVec.ofNat 64 0x810) = t3.getMem (BitVec.ofNat 64 0x810) := by
      rw [f10 _ (by decide) (fun h => h), hI9.frame _ (by decide) (by unfold regBase; decide),
        g8 _ (by decide) (by decide), g7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        f5 _ (by decide) (by decide), hI4.frame _ (by decide) (by unfold regBase; decide)]
    have e2 : t2.getMem (BitVec.ofNat 64 0x810) = s.getMem (BitVec.ofNat 64 0x810) := by
      rw [f2 _ (by decide) (nW _ (by decide) (by decide) (by decide))]; rfl
    rw [e3, hi3, e2]
  have g10 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x2c48 ≤ A) →
      t10.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) := by
    intro A hA h
    rw [f10 A hA (fun h => h), hI9.frame A hA (by unfold regBase; omega), g8 A hA h]
  have gall : ∀ A, A < 2 ^ 64 → (A < 0x60 ∨ 0x80 ≤ A) → A ≠ 0x810 → ¬ (A = 0x20130 ∨ A = 0x20138) →
      (A < 0x20160 ∨ 0x20180 ≤ A) → A ≠ 0x20550 → (A < 0x840 ∨ 0x2c48 ≤ A) → (A < 0x7890 ∨ 0x85f0 ≤ A) →
      (A < 0x400 ∨ 0x550 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → A ≠ 0x20260 → A ≠ 0x20268 →
      t10.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [g10 A hA h6, g7 A hA (by omega) h8 h9 h10 h11, g5 A hA h1 h2 h3 h4 h5 (by omega) h7]
  refine ⟨p10, ?_, x2_10, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r10.get (by decide), hI9.regs.get (by decide), r8.get (by decide), r7.get (by decide)]; exact x5_6
  ·
    have : t10.getMem (BitVec.ofNat 64 IDXV) = t2.getMem (BitVec.ofNat 64 IDXV) := by
      simp only [IDXV]
      rw [g10 _ (by decide) (by decide), g7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        f5 _ (by decide) (by decide), hI4.frame _ (by decide) (by unfold regBase; decide),
        f3 _ (by decide) (nS _ (by decide) (by decide))]
    rw [this]; exact idx2
  ·
    have e1 : t10.getMem (BitVec.ofNat 64 0x20260) = t7.getMem (BitVec.ofNat 64 0x20260) := g10 _ (by decide) (by decide)
    have e2 : t10.getMem (BitVec.ofNat 64 (0x20260 + 8)) = t7.getMem (BitVec.ofNat 64 (0x20260 + 8)) :=
      g10 _ (by decide) (by decide)
    refine ⟨?_, ?_⟩
    · show t10.getMem (BitVec.ofNat 64 0x20260) = _
      rw [e1, enc7lo]; exact root6.1
    · show t10.getMem (BitVec.ofNat 64 (0x20260 + 8)) = _
      rw [e2, enc7hi]; exact root6.2
  ·
    have : t10.getMem (BitVec.ofNat 64 0x810) = t3.getMem (BitVec.ofNat 64 0x810) := by
      rw [g10 _ (by decide) (by decide), g7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        f5 _ (by decide) (by decide), hI4.frame _ (by decide) (by unfold regBase; decide)]
    rw [this]; exact dc3
  ·
    have hsig8 : ∀ n, n < 127 → DigAt t8 (0x7000 + 16 * n) ((ClaudeWCT.W9.T3M.sigDigests sig).getD n 0) := by
      intro n hn
      have h3 := hsig3 n hn
      have e : ∀ A, 0x7000 ≤ A → A < 0x77f0 → t8.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) := by
        intro A h1 h2
        rw [g8 _ (by omega) (by omega), g7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          f5 _ (by omega) (by omega), hI4.frame _ (by omega) (by unfold regBase; omega)]
      exact ⟨(e _ (by omega) (by omega)).trans h3.1, (e _ (by omega) (by omega)).trans h3.2⟩
    exact placed_of hsig8 (fun k i hk hi => by
      rw [f10 _ (by unfold regBase; omega) (fun h => h)]
      exact hI9.done k i (by omega) hk hi)
  ·
    intro A h1 h2
    rw [f10 A (by omega) (fun h => h), hI9.frame A (by omega) (by unfold regBase; omega), m8 A (by omega)]
    split
    · rfl
    · rw [g7 A (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g5 A (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hpre.zeroW A (by omega) h2
  ·
    intro i hi
    have hm := mv5 (213 - i) (by omega)
    have eB : mvB (213 - i) = 0x7000 + 2192 + 16 * i := by unfold mvB; omega
    have eA : mvA (213 - i) = 0x7000 + 16 * (127 + i) := by unfold mvA; omega
    rw [eB, eA] at hm
    have hd := hpre.sigAt (127 + i) (by omega)
    have e4 : ∀ A, 0x77f0 ≤ A → A < 0x7000 + 5456 → t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2
      rw [hI4.frame _ (by omega) (by unfold regBase; omega), g3 _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
    have e10 : ∀ A, 0x7890 ≤ A → A < 0x85f0 → t10.getMem (BitVec.ofNat 64 A) = t5.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2
      rw [g10 _ (by omega) (by omega), g7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    refine ⟨?_, ?_⟩
    · rw [e10 _ (by omega) (by omega), hm.1, e4 _ (by omega) (by omega)]; exact hd.1
    · rw [show 0x7000 + 2192 + 16 * i + 8 = 0x7000 + 2192 + 16 * i + 8 from rfl, e10 _ (by omega) (by omega), hm.2,
        e4 _ (by omega) (by omega)]
      exact hd.2
  ·
    intro A hA hn
    unfold NewW at hn
    simp only [DIG, NBUF, IDXV, ENC] at hn
    rw [gall A hA (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
theorem newCodeSpec_holds {im : Image} (hc : NewCodeAt im) (hh : HookAt im) : NewCodeSpec im :=
  fun sk m sig s hpre => (newCode_tb hc hh sk m sig s hpre).mono (le_refl _) (fun _ _ h => h.1)
end ClaudeWCT.W9.Machine.Expand
end
