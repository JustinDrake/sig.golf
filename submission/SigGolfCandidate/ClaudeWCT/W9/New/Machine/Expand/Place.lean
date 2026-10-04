import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PlaceDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits

section

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem placeOK_init : placeOK 1435 = true := by decide +kernel
theorem placeOK_rest : placeOK 39156 = true := by decide +kernel
theorem cOff_nine : cOff 9 = 1716 := by decide +kernel
def fcLookB : Bool :=
  (List.range 9).all fun c =>
    ((fcList c).all fun p => decide (regBase c ≤ p.1 ∧ p.1 < regBase c + 1024)) &&
    (List.range 128).all fun i => decide (lookW (fcList c) (regBase c + 8 * i) = (plSt 0 0 i).map (fun o => some (sigBlk c + o)))
theorem fcLookB_ok : fcLookB = true := by decide +kernel
def plSt0B : Bool := (List.range 128).all fun j => (List.range 128).all fun i => decide (plSt j 0 i = plSt 0 0 i)
theorem plSt0B_ok : plSt0B = true := by decide +kernel
def plStepB : Bool :=
  (List.range 128).all fun j => (List.range 7).all fun L => (List.range 128).all fun i =>
    decide (plSt j (L + 1) i =
      if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) then some (112 + 16 * L)
      else if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) + 8 then some (112 + 16 * L + 8)
      else plSt j L i)
theorem plStepB_ok : plStepB = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
set_option linter.unusedSimpArgs false
theorem placeOK_fc {P c : Nat} (h : placeOK P = true) (hc : c < 9) : fcCheck P c = true := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  exact this.1
theorem placeOK_lev {P c l : Nat} (h : placeOK P = true) (hc : c < 9) (hl : l < 7) (d : Bool) :
    levCheck P c l d = true := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  have := List.all_eq_true.mp this.2 l (List.mem_range.mpr hl)
  simp only [Bool.and_eq_true] at this
  cases d
  · exact this.2
  · exact this.1
theorem fcLook {c i : Nat} (hc : c < 9) (hi : i < 128) :
    lookW (fcList c) (regBase c + 8 * i) = (plSt 0 0 i).map (fun o => some (sigBlk c + o)) := by
  have := List.all_eq_true.mp fcLookB_ok c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  have := List.all_eq_true.mp this.2 i (List.mem_range.mpr hi)
  simpa using this
theorem fcDst {c : Nat} (hc : c < 9) : ∀ p ∈ fcList c, regBase c ≤ p.1 ∧ p.1 < regBase c + 1024 := by
  have := List.all_eq_true.mp fcLookB_ok c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  intro p hp
  have := List.all_eq_true.mp this.1 p hp
  simpa using this
theorem plSt0 {j i : Nat} (hj : j < 128) (hi : i < 128) : plSt j 0 i = plSt 0 0 i := by
  have := List.all_eq_true.mp plSt0B_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simpa using this
theorem plStep {j L i : Nat} (hj : j < 128) (hL : L < 7) (hi : i < 128) :
    plSt j (L + 1) i =
      if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) then some (112 + 16 * L)
      else if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) + 8 then some (112 + 16 * L + 8)
      else plSt j L i := by
  have := List.all_eq_true.mp plStepB_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this L (List.mem_range.mpr hL)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simpa using this
theorem plSt_seven (j i : Nat) : plSt j 7 i = wSrc j i := by
  unfold plSt; rw [if_pos (Or.inr (by omega))]
theorem regBase_lt (k : Nat) (hk : k < 9) : regBase k + 1024 ≤ 0x2c40 := by unfold regBase; omega
theorem coordBase_split (c : Nat) : 64 * fW c + fSh c = WCT9.coordBase c := by
  unfold fW fSh; omega
theorem fSh_le (c : Nat) (hc : c < 9) : fSh c + 7 ≤ 64 := by
  unfold fSh WCT9.coordBase; interval_cases c <;> decide
theorem fW_lt (c : Nat) (hc : c < 9) : fW c < 4 := by
  unfold fW WCT9.coordBase; interval_cases c <;> decide
theorem childE_eval {c : Nat} (hc : c < 9) {N : HashOutput} {s : MachineState} (hN : OutAt s NBUF N) :
    (childE c).eval s = BitVec.ofNat 64 (WCT9.child N ⟨c, hc⟩).val := by
  have hw := hN (fW c) (fW_lt c hc)
  simp only [NBUF] at hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (WCT9.child N ⟨c, hc⟩).isLt; omega)]
  have e127 : (127 : Word) = 127#64 := rfl
  unfold childE
  split
  · rename_i h0
    simp only [E.eval, BinOp.eval, hw]
    have := child_bits N (fW c) 0 (by omega)
    simp only [BitVec.ushiftRight_zero, Nat.add_zero] at this
    rw [e127, this]
    unfold WCT9.child
    simp only
    rw [← coordBase_split c, h0, Nat.add_zero]
  · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ofNat]
    have hs := fSh_le c hc
    rw [Nat.mod_eq_of_lt (show fSh c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show fSh c < 64 by omega), e127,
      child_bits N (fW c) (fSh c) hs]
    unfold WCT9.child
    simp only
    rw [← coordBase_split c]
theorem bit_holds (j L : Nat) (hj : j < 128) (hL : L < 7) (s : MachineState) (h24 : s.getReg .x24 = BitVec.ofNat 64 j) :
    Br.holds s ⟨.ne, bitE L, .c 0, decide (j / 2 ^ L % 2 = 1)⟩ := by
  rw [br_ne_zero]
  have hv : (bitE L).eval s = (BitVec.ofNat 64 j >>> L) &&& (1 : Word) := by
    simp only [bitE, E.eval, BinOp.eval, h24, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show L < 64 by omega)]
  rw [hv]
  have e : ((BitVec.ofNat 64 j >>> L) &&& (1 : Word)).toNat = j / 2 ^ L % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (1 : Word).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      pow_one]
  have hb : j / 2 ^ L % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h1 : j / 2 ^ L % 2 = 1
  · rw [decide_eq_true h1]
    simp only [decide_eq_true_eq]
    intro h0
    have := congrArg BitVec.toNat h0
    rw [e, h1] at this
    exact absurd this (by decide)
  · rw [decide_eq_false h1]
    simp only [decide_eq_false_iff_not, not_not]
    apply BitVec.eq_of_toNat_eq
    rw [e]
    show j / 2 ^ L % 2 = 0
    omega
structure PlInv (P : Nat) (N : HashOutput) (s0 : MachineState) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (P + cOff c)
  regs : RegsExcept s0 t [.x6, .x7, .x24, .x25, .x28, .x29]
  done : ∀ k i, (hk : k < c) → (hk9 : k < 9) → i < 128 →
    t.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) =
      match wSrc (WCT9.child N ⟨k, hk9⟩).val i with
      | some o => s0.getMem (BitVec.ofNat 64 (sigBlk k + o))
      | none => 0
  frame : Frame s0 t (fun A => 0x840 ≤ A ∧ A < regBase c)
structure LvInv (P : Nat) (N : HashOutput) (s0 t : MachineState) (c : Nat) (hc : c < 9) (L : Nat)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf (P + lOff c L)
  regs : RegsExcept t u [.x6, .x7, .x24, .x25, .x28, .x29]
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WCT9.child N ⟨c, hc⟩).val
  reg : ∀ i, i < 128 → u.getMem (BitVec.ofNat 64 (regBase c + 8 * i)) =
    match plSt (WCT9.child N ⟨c, hc⟩).val L i with
    | some o => s0.getMem (BitVec.ofNat 64 (sigBlk c + o))
    | none => 0
  frame : Frame t u (fun A => regBase c ≤ A ∧ A < regBase c + 1024)
theorem sigBlk_lt (c : Nat) (hc : c < 9) (o : Nat) (ho : o < 224) : sigBlk c + o < 0x7000 + 16 + 2016 := by
  unfold sigBlk; omega
def RegZero (c : Nat) (t : MachineState) : Prop :=
  ∀ i, i < 128 → t.getMem (BitVec.ofNat 64 (regBase c + 8 * i)) = 0
theorem wSrc_lt (j i : Nat) : ∀ o, wSrc j i = some o → o < 224 := by
  intro o h
  unfold wSrc at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h; omega)
theorem plSt_lt (j L i : Nat) : ∀ o, plSt j L i = some o → o < 224 := by
  intro o h
  unfold plSt at h
  split_ifs at h
  · exact wSrc_lt j i o h
theorem fc_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 : MachineState} (c : Nat) (hc9 : c < 9) (t : MachineState) (hpc : t.pc = pcOf (P + cOff c))
    (hN : OutAt t NBUF N) (hz : RegZero c t)
    (hsig : ∀ o, o < 224 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∃ u k cy, Steps im t k cy u ∧ cy ≤ 120 ∧ LvInv P N s0 t c hc9 0 u := by
  obtain ⟨r, hr, hb⟩ := check_some (placeOK_fc hP hc9)
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hrun, h24⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun t hpc (by simp) (by rw [hbr]; simp)
  refine ⟨_, _, _, st, hcy, p, rg, ?_, ?_, ?_⟩
  · rw [PRes.toState_getReg, E.beq_eq h24, childE_eval hc9 hN]
  · intro i hi
    have hA : regBase c + 8 * i < 2 ^ 64 := by unfold regBase; omega
    rw [mm _ hA, plSt0 (WCT9.child N ⟨c, hc9⟩).isLt hi]
    have hl := fcLook hc9 hi
    cases hs : plSt 0 0 i with
    | none =>
      rw [hs] at hl
      rw [effMem_none hl]
      exact hz i hi
    | some o =>
      rw [hs] at hl
      rw [effMem_some hl]
      exact hsig o (plSt_lt 0 0 i o hs)
  · intro A hA hn
    rw [mm A hA]
    apply effMem_none
    apply lookW_none_of
    intro p hp he
    have := fcDst hc9 p hp
    exact hn ⟨by omega, by omega⟩
theorem lev_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 t : MachineState} (c : Nat) (hc9 : c < 9) (L : Nat) (hL : L < 7) (u : MachineState)
    (hI : LvInv P N s0 t c hc9 L u)
    (hsig : ∀ o, o < 224 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∃ v k cy, Steps im u k cy v ∧ cy ≤ 12 ∧ LvInv P N s0 t c hc9 (L + 1) v := by
  set j := (WCT9.child N ⟨c, hc9⟩).val with hjdef
  have hj : j < 128 := (WCT9.child N ⟨c, hc9⟩).isLt
  obtain ⟨r, hr, hb⟩ := check_some (placeOK_lev hP hc9 hL (decide (j / 2 ^ L % 2 = 1)))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hrun, hbr⟩, hcy⟩ := hb
  have hbr' := listBeq_eq (fun _ _ => Br.beq_eq) hbr
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun u hI.pc (by simp) (by
    rw [hbr']; intro b hb; simp only [List.mem_singleton] at hb; subst hb
    exact bit_holds j L hj hL u hI.x24)
  have hsrc : ∀ o, o < 224 → u.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) := by
    intro o ho
    rw [hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega), hsig o ho]
  have hlu : lOff c L + 12 = lOff c (L + 1) := by unfold lOff; ring
  refine ⟨_, _, _, st, hcy, by rw [p, Nat.add_assoc, hlu], hI.regs.trans rg |>.mono (by simp), ?_, ?_, ?_⟩
  · rw [rg.get (by simp)]; exact hI.x24
  · intro i hi
    have hA : regBase c + 8 * i < 2 ^ 64 := by unfold regBase; omega
    rw [mm _ hA, plStep hj hL hi]
    unfold levList
    by_cases h1 : 8 * i = sibOff L (decide (j / 2 ^ L % 2 = 1))
    · rw [if_pos h1]
      have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 112 + 16 * L + 8)),
          (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 112 + 16 * L))] (regBase c + 8 * i) =
          some (some (sigBlk c + 112 + 16 * L)) := by
        rw [lookW_cons, if_neg (by omega), lookW_cons, if_pos (by omega)]
      rw [effMem_some this, show sigBlk c + 112 + 16 * L = sigBlk c + (112 + 16 * L) by ring]
      exact hsrc _ (by omega)
    · rw [if_neg h1]
      by_cases h2 : 8 * i = sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8
      · rw [if_pos h2]
        have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 112 + 16 * L + 8)),
            (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 112 + 16 * L))] (regBase c + 8 * i) =
            some (some (sigBlk c + 112 + 16 * L + 8)) := by
          rw [lookW_cons, if_pos (by omega)]
        rw [effMem_some this, show sigBlk c + 112 + 16 * L + 8 = sigBlk c + (112 + 16 * L + 8) by ring]
        exact hsrc _ (by omega)
      · rw [if_neg h2]
        have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 112 + 16 * L + 8)),
            (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 112 + 16 * L))] (regBase c + 8 * i) =
            none := by
          rw [lookW_cons, if_neg (by omega), lookW_cons, if_neg (by omega)]; rfl
        rw [effMem_none this]
        exact hI.reg i hi
  · have hs : ∀ d : Bool, sibOff L d + 16 ≤ 1024 := fun d => by unfold sibOff; split <;> omega
    have F : Frame u (r.toState u) (fun A => regBase c ≤ A ∧ A < regBase c + 1024) := by
      intro A hA hn
      rw [mm A hA]
      apply effMem_none
      unfold levList
      have := hs (decide (j / 2 ^ L % 2 = 1))
      rw [lookW_cons, if_neg (fun h => hn ⟨by omega, by omega⟩), lookW_cons,
        if_neg (fun h => hn ⟨by omega, by omega⟩)]; rfl
    exact (hI.frame.trans F).mono (fun A _ h => by rcases h with h | h <;> exact h)
theorem levs_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 t : MachineState} (c : Nat) (hc9 : c < 9)
    (hsig : ∀ o, o < 224 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∀ L, L ≤ 7 → ∀ u, LvInv P N s0 t c hc9 0 u → ∃ v k cy, Steps im u k cy v ∧ cy ≤ 12 * L ∧ LvInv P N s0 t c hc9 L v := by
  intro L
  induction L with
  | zero => intro _ u h; exact ⟨u, 0, 0, Steps.refl u, le_refl _, h⟩
  | succ L ih =>
    intro hL u h0
    obtain ⟨v, k, cy, sv, hcy, hv⟩ := ih (by omega) u h0
    obtain ⟨w, k', cy', sw, hcy', hw⟩ := lev_spec hc hP c hc9 L (by omega) v hv hsig
    exact ⟨w, _, _, sv.trans sw, by rw [Nat.mul_succ]; omega, hw⟩
theorem coordPl_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 : MachineState} (hN : OutAt s0 NBUF N) (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0)
    (c : Nat) (hc9 : c < 9) (t : MachineState) (hI : PlInv P N s0 c t) :
    ∃ u k cy, Steps im t k cy u ∧ cy ≤ 204 ∧ PlInv P N s0 (c + 1) u := by
  have hrb := regBase_lt c hc9
  have hNt : OutAt t NBUF N := fun k hk => by
    rw [hI.frame _ (by simp only [NBUF]; omega) (by simp only [NBUF]; unfold regBase; omega)]; exact hN k hk
  have hzt : RegZero c t := fun i hi => by
    rw [hI.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
    exact hz c i hc9 hi
  have hsig : ∀ o, o < 224 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) :=
    fun o ho => hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega)
  obtain ⟨u0, k0, c0, s0', hc0, h0⟩ := fc_spec hc hP c hc9 t hI.pc hNt hzt hsig
  obtain ⟨u7, k7, c7, s7, hc7, h7⟩ := levs_spec hc hP c hc9 hsig 7 le_rfl u0 h0
  refine ⟨u7, _, _, s0'.trans s7, by omega, ?_, ?_, ?_, ?_⟩
  · rw [h7.pc]; unfold lOff; simp only [cOff]; try ring_nf
  · exact (hI.regs.trans h7.regs).mono (by simp)
  · intro k i hk hk9 hi
    by_cases hkc : k = c
    · subst hkc
      rw [h7.reg i hi, plSt_seven]
    · have hk' : k < c := by omega
      have hrk := regBase_lt k hk9
      rw [h7.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
      exact hI.done k i hk' hk9 hi
  · have := (hI.frame.trans h7.frame)
    refine this.mono (fun A _ h => ?_)
    have e : regBase (c + 1) = regBase c + 1024 := by unfold regBase; ring
    rcases h with h | h
    · exact ⟨h.1, by omega⟩
    · exact ⟨by unfold regBase at h; omega, by omega⟩
theorem place_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 : MachineState} (hpc : s0.pc = pcOf P) (hN : OutAt s0 NBUF N)
    (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0) :
    ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 9 * 204 ∧ PlInv P N s0 9 u := by
  have gen : ∀ c, c ≤ 9 → ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 204 * c ∧ PlInv P N s0 c u := by
    intro c
    induction c with
    | zero =>
      intro _
      refine ⟨s0, 0, 0, Steps.refl _, le_refl _, ⟨by rw [hpc]; rfl, RegsExcept.refl _ _,
        fun k i hk => absurd hk (by omega), Frame.refl _ _⟩⟩
    | succ c ih =>
      intro hc9
      obtain ⟨u, k, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, k', cy', sv, hcy', hv⟩ := coordPl_spec hc hP hN hz c (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, k, cy, su, hcy, hu⟩ := gen 9 le_rfl
  exact ⟨u, k, cy, su, by omega, hu⟩
end ClaudeWCT.W9.Machine.Expand
end
