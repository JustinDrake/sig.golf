import SigGolfCandidate.T3M.Keygen.LeafLoop
import SigGolfCandidate.T3M.Keygen.PairedBlocks

/-! Exact full-cache paired mask loop, levels0..11,4095 queries and8190 digests. -/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest pairedMask maskedLevel header privateInput)

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Steps after a refined program (`p >>= pure = p`). -/
theorem TSim.post_steps {α : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {k c n b k' c' : Nat}
    {p : T3.M α} {Q Q' : α → MachineState → Prop} (h : TSim image sk s k c n b p Q)
    (hs : ∀ a t, Q a t → ∃ u, Steps image t k' c' u ∧ Q' a u) :
    TSim image sk s (k + k') (c + c') n b p Q' :=
  (TSim.bind (k₂ := k') (c₂ := c') (n₂ := 0) (b₂ := 0) (f := fun a => (Pure.pure a : T3.M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TSim.pure_steps hu hq)).of_eq (bind_pure p)
    rfl rfl (Nat.add_zero n) (Nat.add_zero b)

def MW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (MOUT ≤ X ∧ X < MOUT + 32) ∨ (REGION ≤ X ∧ X < REGION + 131040)

def maskRegs : List Reg := [.x2, .x6, .x7, .x10, .x11, .x12, .x20, .x21, .x22, .x23, .x24, .x26, .x28]

structure MaskPre (sk : SecretKey) (s : MachineState) (levels : List (List Digest)) : Prop where
  pc : s.pc = pcOf 289
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = 0
  x20 : s.getReg .x20 = BitVec.ofNat 64 4096
  x24 : s.getReg .x24 = BitVec.ofNat 64 REGION
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  nodes : ∀ l, l ≤ 11 → (levels.getD l []).length = 2 ^ (12 - l) ∧
    DigsAt s (TOP + 16 * 2 ^ (12 - l)) (levels.getD l [])

structure LevelInv (s4 : MachineState) (pre : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if pre.length < 12 then pcOf 289 else pcOf 334
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * pre.flatten.length)
  flen : pre.flatten.length + 2 ^ (13 - pre.length) = 8192
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION pre.flatten

structure MaskInv (s4 : MachineState) (pre cur : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if cur.length < 2 ^ (11 - pre.length) then pcOf 295 else pcOf 330
  x23 : t.getReg .x23 = BitVec.ofNat 64 cur.length
  x26 : t.getReg .x26 = BitVec.ofNat 64 (2 ^ (11 - pre.length))
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x21 : t.getReg .x21 = BitVec.ofNat 64 (TOP + 16 * (2 ^ (12 - pre.length) + 2 * cur.length))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * (pre.flatten.length + cur.flatten.length))
  flen : cur.flatten.length = 2 * cur.length
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION (pre.flatten ++ cur.flatten)

theorem two_pow_twelve_sub {j : Nat} (hj : j < 12) :
    2 ≤ 2 ^ (12-j) ∧ 2 ^ (12-j) ≤ 4096 ∧ 1 ≤ 2 ^ (11-j) ∧
    2 ^ (12-j) = 2 * 2 ^ (11-j) ∧
    2 ^ (13-j) = 2 * 2 ^ (12-j) ∧
    2 ^ (12-(j+1)) = 2 ^ (12-j) / 2 ∧
    2 ^ (13-(j+1)) = 2 ^ (12-j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (12-j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ (12-j) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4096 := by norm_num
  · exact Nat.one_le_pow _ _ (by decide)
  · rw [show 12-j=(11-j)+1 by omega, pow_succ]; ring
  · rw [show 13-j=(12-j)+1 by omega, pow_succ]; ring
  · rw [show 12-j=(12-(j+1))+1 by omega, pow_succ]; omega
  · congr 1; omega

section masks
variable {sk : SecretKey} {s4 : MachineState} {levels : List (List Digest)} (hm : MaskPre sk s4 levels)
include hm

theorem mask_one {pre : List (List Digest)} (hpl : pre.length < 12) {cur : List (List Digest)}
    (hcl : cur.length < 2 ^ (11 - pre.length))
    (hfl : pre.flatten.length + 2 ^ (13 - pre.length) = 8192) {t : MachineState}
    (ht : MaskInv s4 pre cur t) :
    TSim image sk t 35 42 1 1
      (do
        let values ← pairedMask pre.length cur.length
        pure [(levels.getD pre.length []).getD (2*cur.length) 0 ^^^ values.1,
          (levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ values.2])
      (fun ds u => MaskInv s4 pre (cur ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, -, -⟩ := two_pow_twelve_sub hpl
  have g : ∀ r, r ∉ maskRegs → t.getReg r = s4.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2a, t2b, t2r, t2f⟩ :=
    blk295_spec t (by simpa only [if_pos hcl] using ht.pc) pre.length cur.length
      (by omega) (by omega) ht.x22 ht.x23
  have fr : ∀ X, (X = PRIV ∨ X = PRIV+8 ∨ X = PRIV+32 ∨ X = PRIV+40 ∨ X = PRIV+48 ∨ X = PRIV+56) →
      t2.getMem (BitVec.ofNat 64 X) = s4.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (t2f.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (by kg_omega)).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
        (by unfold MW; kg_omega))
  have hq : hashInput t2 = toQ (privateInput sk (.inl (header 13 0 0 pre.length cur.length))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide)
      t2x11 (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV+8) (by simp), t2a, t2b, fr (PRIV+32) (by simp), fr (PRIV+40) (by simp),
      fr (PRIV+48) (by simp), fr (PRIV+56) (by simp), hm.p0, hm.p8, hm.p32, hm.p40, hm.p48, hm.p56]
    rfl
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by decide), g _ (by decide), hm.x5]
  unfold pairedMask
  refine (TSim.steps st2 (TSim.privatePair_bind (k := 20) (c := 20) (n := 0) (b := 0)
    (fetch_309 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc = pcOf 310 := by rw [pc_writeHash, t2pc, pcOf_add4]
  have hmo0 := DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
  have hmo1 := DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have fsu := ht.frame.trans (t2f.trans hwf)
  obtain ⟨hlen, hds⟩ := hm.nodes pre.length (by omega)
  have hnode (i : Nat) (hi : i < 2 ^ (12-pre.length)) :
      DigAt (writeHash t2 a) (TOP + 16 * (2 ^ (12-pre.length)+i)) ((levels.getD pre.length []).getD i 0) := by
    have hn := hds.get (show i < _ by rw [hlen]; exact hi)
    rw [show TOP+16*2^(12-pre.length)+16*i=TOP+16*(2^(12-pre.length)+i) by ring] at hn
    exact hn.frame fsu (by kg_omega) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  have hn0 := hnode (2*cur.length) (by omega)
  have hn1 := hnode (2*cur.length+1) (by omega)
  have rw2 : RegsExcept t (writeHash t2 a) [.x6, .x7, .x10, .x11, .x12, .x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hcf := ht.flen
  obtain ⟨t3, st3, t3pc, t3mem, t3x21, t3x24, t3x23, t3r, t3f⟩ :=
    blk310_spec (writeHash t2 a) upc
      (TOP+16*(2^(12-pre.length)+2*cur.length))
      (REGION+16*(pre.flatten.length+cur.flatten.length)) cur.length (2^(11-pre.length))
      (by kg_omega) (by kg_omega) (by kg_omega)
      (by kg_omega) (by kg_omega) (by kg_omega) (by omega) (by omega)
      (by rw [rw2.get (by decide)]; exact ht.x21)
      (by rw [rw2.get (by decide)]; exact ht.x24)
      (by rw [rw2.get (by decide)]; exact ht.x23)
      (by rw [rw2.get (by decide)]; exact ht.x26) (by rw [getReg_writeHash]; exact t2x12)
  have t3a := t3mem ⟨0,by decide⟩
  have t3b := t3mem ⟨1,by decide⟩
  have t3c := t3mem ⟨2,by decide⟩
  have t3d := t3mem ⟨3,by decide⟩
  simp only [Fin.val_mk, Nat.reduceMul, Nat.add_zero] at t3a t3b t3c t3d
  have r23 := rw2.trans t3r
  refine TSim.pure_steps st3 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using t3pc
  · rw [t3x23, List.length_append, List.length_singleton]
  · rw [r23.get (by decide)]; exact ht.x26
  · rw [r23.get (by decide)]; exact ht.x20
  · rw [r23.get (by decide)]; exact ht.x22
  · rw [t3x21, List.length_append, List.length_singleton]
    congr 1
  · rw [t3x24, List.flatten_concat, List.length_append]
    simp only [List.length_cons, List.length_nil]
    congr 1
  · rw [List.flatten_concat, List.length_append, ht.flen, List.length_append, List.length_singleton]
    simp only [List.length_cons, List.length_nil]; omega
  · exact (ht.regs.trans r23).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold MW at h ⊢
    have hc := ht.flen
    kg_omega
  · rw [List.flatten_concat, ← List.append_assoc]
    have hout := ht.out.frame ((t2f.trans hwf).trans t3f)
      (by rw [List.length_append]; have hc := ht.flen; kg_omega)
      (fun B h1 h2 h => by rw [List.length_append] at h2; kg_omega)
    have hd0 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length))
        ((levels.getD pre.length []).getD (2*cur.length) 0 ^^^ a.extractLsb' 0 128) := by
      constructor
      · rw [t3a, hn0.1, hmo0.1, ← BitVec.extractLsb'_xor]
      · rw [t3b, hn0.2, hmo0.2, ← BitVec.extractLsb'_xor]
    have hd1 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length)+16)
        ((levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ a.extractLsb' 128 128) := by
      constructor
      · rw [t3c, show TOP+16*(2^(12-pre.length)+2*cur.length)+16=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1)) by ring, hn1.1, hmo1.1, ← BitVec.extractLsb'_xor]
      · rw [t3d, show TOP+16*(2^(12-pre.length)+2*cur.length)+24=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1))+8 by ring, hn1.2, hmo1.2, ← BitVec.extractLsb'_xor]
    have hs0 := DigsAt.snoc hout (by simpa only [List.length_append] using hd0)
    have hs1 := DigsAt.snoc hs0 (by
      simpa only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hd1)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs1

theorem levelInv_zero : LevelInv s4 [] s4 :=
  ⟨hm.pc, hm.x20, hm.x22, hm.x24, rfl, RegsExcept.refl _ _, Frame.refl _ _, DigsAt.nil _ _⟩

theorem mask_level {pre : List (List Digest)} (hpl : pre.length < 12) {t : MachineState}
    (ht : LevelInv s4 pre t) :
    TSim image sk t (10+35*2^(11-pre.length)) (10+42*2^(11-pre.length))
      (2^(11-pre.length)) (2^(11-pre.length))
      (maskedLevel (levels.getD pre.length []) pre.length)
      (fun ds u => LevelInv s4 (pre ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, h12', h13'⟩ := two_pow_twelve_sub hpl
  have hfl := ht.flen
  obtain ⟨t2, st2, t2pc, t2x23, t2x26, t2x21, t2x2, t2r, t2f⟩ :=
    blk289_spec t (by simpa only [if_pos hpl] using ht.pc) (2^(12-pre.length)) (by omega) ht.x20
  have h0 : MaskInv s4 pre [] t2 := by
    refine ⟨?_, t2x23, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [List.length_nil, if_pos (by omega : 0<2^(11-pre.length))] using t2pc
    · rw [t2x26, hpair, Nat.mul_div_cancel_left _ (by decide)]
    · rw [t2r.get (by decide)]; exact ht.x20
    · rw [t2r.get (by decide)]; exact ht.x22
    · simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using t2x21
    · rw [t2r.get (by decide), ht.x24]; rfl
    · exact (ht.regs.trans t2r).mono (by decide)
    · exact (ht.frame.trans t2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · simpa only [List.flatten_nil, List.append_nil] using ht.out.frame t2f (by kg_omega) (fun _ _ _ h => h)
  have hin := TSim.mapM_range (image := image) (sk := sk) (2^(11-pre.length))
    (fun i => do
      let values ← pairedMask pre.length i
      pure [(levels.getD pre.length []).getD (2*i) 0 ^^^ values.1,
        (levels.getD pre.length []).getD (2*i+1) 0 ^^^ values.2])
    (fun _ => 35) (fun _ => 42) (fun _ => 1) (fun _ => 1) (MaskInv s4 pre)
    (fun cur u hc hu => mask_one hm hpl hc ht.flen hu) h0
  simp only [sumTo_const] at hin
  refine (TSim.steps st2 (TSim.map List.flatten
    (TSim.post_steps (k' := 4) (c' := 4) hin (fun ds u hu => ?_)))).of_eq ?_
      (by ring) (by ring) (by simp) (by simp)
  · obtain ⟨hdl, hu⟩ := hu
    obtain ⟨u2, su2, u2pc, u2x20, u2x22, u2r, u2f⟩ :=
      blk330_spec u (by simpa only [hdl, if_neg (Nat.lt_irrefl _)] using hu.pc)
        (2^(12-pre.length)) pre.length (by omega) (by omega) hu.x20 hu.x22
    refine ⟨u2, su2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using u2pc
    · rw [u2x20, List.length_append, List.length_singleton, h12']
    · rw [u2x22, List.length_append, List.length_singleton]
    · rw [u2r.get (by decide), hu.x24, List.flatten_concat, List.length_append]
    · rw [List.flatten_concat, List.length_append, hu.flen, hdl,
        List.length_append, List.length_singleton, h13', ← hpair]
      omega
    · exact (hu.regs.trans u2r).mono (by decide)
    · exact (hu.frame.trans u2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · rw [List.flatten_concat]
      exact hu.out.frame u2f (by rw [List.length_append, hu.flen, hdl]; kg_omega) (fun _ _ _ h => h)
  · simp only [maskedLevel, map_eq_bind_pure_comp]
    rfl

theorem masks_tsim :
    TSim image sk s4 143445 172110 4095 4095
      ((List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level)
      (fun masked u => masked.length = 12 ∧ LevelInv s4 masked u) := by
  rw [List.range'_eq_map_range, List.mapM_map]
  simp only [Nat.zero_add]
  exact (TSim.mapM_range 12 _ (fun j => 10+35*2^(11-j)) (fun j => 10+42*2^(11-j))
    (fun j => 2^(11-j)) (fun j => 2^(11-j)) (LevelInv s4)
    (fun pre t hl ht => mask_level hm hl ht) (levelInv_zero hm)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)

end masks
end SigGolfCandidate.T3M.Keygen
