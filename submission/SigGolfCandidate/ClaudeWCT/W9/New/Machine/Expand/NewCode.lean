import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PlaceDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.SearchCode
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Fts

section

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem placeOK_init : placeOK 1402 = true := by decide +kernel
theorem placeOK_rest : placeOK 39966 = true := by decide +kernel
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
  optCheck (pathAux pcfg expLook [pcOf 1402] 30 (pcOf 1388) [] (σK []) []) fun r =>
    runM r 1402 srchdM [.x6, .x7, .x28, .x29] && r.brs.isEmpty && decide (r.cycles ≤ 14)
def mvA (k : Nat) : Nat := 0x8540 - 16 * k
def mvB (k : Nat) : Nat := 0x85e0 - 16 * k
def mvInitCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 3124] 10 (pcOf 3118) [] (σK []) []) fun r =>
    runB r 3124 [] [.x28, .x29, .x30] && regIsB r .x28 (BitVec.ofNat 64 (mvA 0)) &&
      regIsB r .x29 (BitVec.ofNat 64 (mvB 0)) && regIsB r .x30 (BitVec.ofNat 64 0x77f0) && r.brs.isEmpty &&
      decide (r.cycles ≤ 6)
def mvCheck (k : Nat) : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 3124, pcOf 3131] 20 (pcOf 3124) []
      (σK [(.x28, BitVec.ofNat 64 (mvA k)), (.x29, BitVec.ofNat 64 (mvB k)), (.x30, BitVec.ofNat 64 0x77f0)]) []) fun r =>
    runB r (if k < 213 then 3124 else 3131) [(mvB k + 8, some (mvA k + 8)), (mvB k, some (mvA k))]
      [.x6, .x7, .x28, .x29, .x30] && regIsB r .x28 (BitVec.ofNat 64 (mvA (k + 1))) &&
      regIsB r .x29 (BitVec.ofNat 64 (mvB (k + 1))) && regIsB r .x30 (BitVec.ofNat 64 0x77f0) && r.brs.isEmpty &&
      decide (r.cycles ≤ 7)
def mvOK : Bool := (List.range 214).all mvCheck
def sufCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 39963] 20 (pcOf 39952) [] (σK []) []) fun r =>
    runB r 39963 [(0x20260 + 8, some 264), (0x20260, some 256)] [.x6, .x7, .x28, .x29] &&
      regIsB r .x28 (BitVec.ofNat 64 0x840) && regIsB r .x29 (BitVec.ofNat 64 0x3418) && r.brs.isEmpty &&
      decide (r.cycles ≤ 11)
def clA (k : Nat) : Nat := 0x840 + 8 * k
def clCheck (k : Nat) : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 39963, pcOf 39966] 10 (pcOf 39963) []
      (σK [(.x28, BitVec.ofNat 64 (clA k)), (.x29, BitVec.ofNat 64 0x3418)]) []) fun r =>
    runB r (if k < 1402 then 39963 else 39966) [(clA k, none)] [.x28, .x29] &&
      regIsB r .x28 (BitVec.ofNat 64 (clA (k + 1))) && regIsB r .x29 (BitVec.ofNat 64 0x3418) && r.brs.isEmpty &&
      decide (r.cycles ≤ 3)
def clOK : Bool := (List.range 1403).all clCheck
def finCheck : Bool :=
  optCheck (pathAux pcfg expLook [pcOf 249] 10 (pcOf 41682) [] (σK []) []) fun r =>
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
theorem searchWindow : windowOK 1247 SearchCode.code = true := by decide +kernel
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
theorem srchd_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 1388) {N : HashOutput}
    (hN : OutAt s NBUF N) {counter : BitVec 32} (h19 : s.getReg .x19 = BitVec.ofNat 64 counter.toNat) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 14 ∧ t.pc = pcOf 1402 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      OutAt t 0x60 N ∧ (t.getMem (BitVec.ofNat 64 0x810)).extractLsb' 0 32 = counter ∧
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
  refine ⟨_, _, _, st, hcy, p, rg, ?_, ?_, ?_⟩
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
    have := SigGolfCandidate.T3M.Expand.replaceWord32_get (s.getMem (BitVec.ofNat 64 2064)) 0 (by decide)
      ((s.getReg .x19).truncate 32)
    simp only [Nat.mul_zero] at this
    rw [this, h19]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro A hA hn
    rw [mm, hM A hA]
    rw [if_neg (fun h => hn (Or.inl (by omega))), if_neg (fun h => hn (Or.inl (by omega))),
      if_neg (fun h => hn (Or.inl (by omega))), if_neg (fun h => hn (Or.inl (by omega))),
      if_neg (fun h => hn (Or.inr (by omega)))]
theorem mvInit_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 3118) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 6 ∧ t.pc = pcOf 3124 ∧ t.getReg .x28 = BitVec.ofNat 64 (mvA 0) ∧
      t.getReg .x29 = BitVec.ofNat 64 (mvB 0) ∧ t.getReg .x30 = BitVec.ofNat 64 0x77f0 ∧
      RegsExcept s t [.x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨r, hr, hb⟩ := optCheck_some mvInitCheck_ok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨hrun, h28⟩, h29⟩, h30⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun s hpc (by simp) (by rw [hbr]; simp)
  exact ⟨_, _, _, st, hcy, p, regIsB_ok h28 s, regIsB_ok h29 s, regIsB_ok h30 s, rg,
    frame_of_eff mm _ (by simp)⟩
structure MvInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 214 then 3124 else 3131)
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
  have hpc : t.pc = pcOf 3124 := by rw [hI.pc, if_pos hk]
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
theorem mv_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 3118) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 6 + 214 * 7 ∧ t.pc = pcOf 3131 ∧ RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
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
theorem suf_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 39952) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 11 ∧ t.pc = pcOf 39963 ∧ t.getReg .x28 = BitVec.ofNat 64 (clA 0) ∧
      t.getReg .x29 = BitVec.ofNat 64 0x3418 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
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
  pc : t.pc = pcOf (if k < 1403 then 39963 else 39966)
  x28 : t.getReg .x28 = BitVec.ofNat 64 (clA k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 0x3418
  regs : RegsExcept s0 t [.x28, .x29]
  mem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
    if 0x840 ≤ A ∧ A < clA k ∧ A % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem cl_step {im : Image} (hc : NewCodeAt im) {s0 : MachineState} (k : Nat) (hk : k < 1403) (t : MachineState)
    (hI : ClInv s0 k t) : ∃ u n cy, Steps im t n cy u ∧ cy ≤ 3 ∧ ClInv s0 (k + 1) u := by
  obtain ⟨r, hr, hb⟩ := optCheck_some (List.all_eq_true.mp clOK_ok k (List.mem_range.mpr hk))
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hrun, h28⟩, h29⟩, hbr⟩, hcy⟩ := hb
  have hpc : t.pc = pcOf 39963 := by rw [hI.pc, if_pos hk]
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
theorem cl_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 39963)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (clA 0)) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x3418) :
    ∃ t k cy, Steps im s k cy t ∧ cy ≤ 3 * 1403 ∧ t.pc = pcOf 39966 ∧ RegsExcept s t [.x28, .x29] ∧
      ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
        if 0x840 ≤ A ∧ A < 0x3418 ∧ A % 8 = 0 then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have I0 : ClInv s 0 s := ⟨by rw [hpc]; rfl, h28, h29, RegsExcept.refl _ _, fun A _ => by
    rw [if_neg (fun h => by unfold clA at h; omega)]⟩
  have gen : ∀ k, k ≤ 1403 → ∃ u n cy, Steps im s n cy u ∧ cy ≤ 3 * k ∧ ClInv s k u := by
    intro k
    induction k with
    | zero => intro _; exact ⟨s, 0, 0, Steps.refl _, le_refl _, I0⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, n, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, n', cy', sv, hcy', hv⟩ := cl_step hc k (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, n, cy, su, hcy, hu⟩ := gen 1403 le_rfl
  exact ⟨u, n, cy, su, hcy, by rw [hu.pc]; rfl, hu.regs, fun A hA => by rw [hu.mem A hA]; rfl⟩
theorem fin_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 41682) :
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
  obtain ⟨h1, h2, h3⟩ := h k hk
  have g : ∀ A, HB0 ≤ A → A < HB0 + 4608 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A a b => hf A (by unfold HB0 at *; omega) (hW A a b)
  refine ⟨fun t' st ht hst => ?_, ?_, ?_⟩
  · rw [g _ (by omega) (by unfold HB0; omega)]; exact h1 t' st ht hst
  · rw [g _ (by omega) (by unfold HB0; omega)]; exact h2
  · rw [g _ (by omega) (by unfold HB0; omega)]; exact h3
theorem searchAt_new {im : Image} (hc : NewCodeAt im) : SearchAt im 1247 :=
  codeAt_of_window hc (by decide +kernel) searchWindow
theorem hook_step {im : Image} (hh : HookAt im) (s : MachineState) (hpc : s.pc = pcOf 30) :
    Steps im s 1 1 (s.setPC (pcOf 1247)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo hookWord 30 = some 1247 by decide)
  exact jal_x0_step hh hd hoff s hpc
theorem newCost_split : 1 + (2 ^ 21 * 150 + 6 + 20000) ≤ newCost := by unfold newCost; norm_num
theorem newCodeSpec_holds {im : Image} (hc : NewCodeAt im) (hh : HookAt im) : NewCodeSpec im := by
  intro sk m sig s hpre
  have s1 := hook_step hh s hpre.pc
  set u1 := s.setPC (pcOf 1247) with hu1
  have g1 : ∀ A, u1.getMem A = s.getMem A := fun _ => rfl
  have r1 : ∀ x, u1.getReg x = s.getReg x := fun _ => rfl
  have hS : SrchPre 1247 u1 sig.rho m :=
    ⟨rfl, by rw [r1]; exact hpre.x5, by rw [r1]; exact hpre.x19, hpre.rho, hpre.msg⟩
  unfold newProg
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 20000) (search_tbsim (sk := sk) (searchAt_new hc) hS)
    (fun res t2 h2 => ?_))).mono newCost_split (fun _ _ h => h)
  rcases res with _ | ⟨counter, N⟩
  · exact (TBSim.pure (Q := NewPost sig s) (a := none) h2).mono (by omega) (fun _ _ h => h)
  obtain ⟨p2, x5_2, adm2, out2, idx2, x22_2, r2, f2, hc2, x19_2⟩ := h2
  obtain ⟨t3, k3, c3, st3, hc3, p3, r3, out3, dc3, f3⟩ := srchd_spec hc t2 p2 out2 x19_2
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
  have p4 : t4.pc = pcOf 3118 := by rw [hI4.pc, cOff_nine]
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
  refine (TBSim.steps (st3.trans (st4.trans st5)) (TBSim.bind (W₂ := 11 + 3 * 1403 + 9 * 204 + 3)
    (fts_tb hc hin p5 x5_5) (fun root t6 h6 => ?_))).mono
    (by unfold ftsCost coordCost; omega) (fun _ _ h => h)
  obtain ⟨p6, x5_6, root6, f6⟩ := h6
  obtain ⟨t7, k7, c7, st7, hc7, p7, x28_7, x29_7, r7, enc7lo, enc7hi, f7⟩ := suf_spec hc t6 p6
  obtain ⟨t8, k8, c8, st8, hc8, p8, r8, m8⟩ := cl_spec hc t7 p7 x28_7 x29_7
  have g8 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x3418 ≤ A) → t8.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => by rw [m8 A hA, if_neg (by omega)]
  have nF : ∀ A, (A < 0x840 ∨ 0x2c40 ≤ A) → (A < 0x700 ∨ 0x7c0 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → ¬ FtsW A := by
    intro A h1 h2 h3 h; unfold FtsW at h; omega
  have g7 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x2c40 ≤ A) → (A < 0x700 ∨ 0x7c0 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) →
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
  have p9 : t9.pc = pcOf 41682 := by rw [hI9.pc, cOff_nine]
  obtain ⟨t10, k10, c10, st10, hc10, p10, x2_10, r10, f10⟩ := fin_spec hc t9 p9
  refine (TBSim.steps (st7.trans (st8.trans (st9.trans st10))) (TBSim.pure (Q := NewPost sig s)
    (a := some (counter, N, root)) ?_)).mono (by omega) (fun _ _ h => h)
  have g10 : ∀ A, A < 2 ^ 64 → (A < 0x840 ∨ 0x3418 ≤ A) →
      t10.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) := by
    intro A hA h
    rw [f10 A hA (fun h => h), hI9.frame A hA (by unfold regBase; omega), g8 A hA h]
  have gall : ∀ A, A < 2 ^ 64 → (A < 0x60 ∨ 0x80 ≤ A) → A ≠ 0x810 → ¬ (A = 0x20130 ∨ A = 0x20138) →
      (A < 0x20160 ∨ 0x20180 ≤ A) → A ≠ 0x20550 → (A < 0x840 ∨ 0x3418 ≤ A) → (A < 0x7890 ∨ 0x85f0 ≤ A) →
      (A < 0x700 ∨ 0x7c0 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → A ≠ 0x20260 → A ≠ 0x20268 →
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
end ClaudeWCT.W9.Machine.Expand
end
