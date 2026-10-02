import SigGolfCandidate.T3M.Keygen.LeafLoop

/-!
# The keygen masks (`kg_level` / `kg_mask`, words 48..84)

For the levels `2 + j` (`j < 10`, `lo = 2^(10-j)` nodes) and `i < lo`: the mask header `T13(level, i)`
at `PRIV+16`, the HASH `PRIV -> MOUT`, then `[ENDP] := node (lo + i) xor MOUT`, `ENDP += 16`.
`masks_tsim` refines Core's `(List.range' 2 10).mapM fun level => (List.range (2^(12-level))).mapM ..`
exactly (`61,450` steps, `75,772` cycles, `2046` calls and compressions) and leaves the 2046 masked
nodes at `REGION`.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest mask header privateInput)

/-- Steps after a refined program (`p >>= pure = p`). -/
theorem TSim.post_steps {α : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {k c n b k' c' : Nat}
    {p : T3.M α} {Q Q' : α → MachineState → Prop} (h : TSim image sk s k c n b p Q)
    (hs : ∀ a t, Q a t → ∃ u, Steps image t k' c' u ∧ Q' a u) :
    TSim image sk s (k + k') (c + c') n b p Q' :=
  (TSim.bind (k₂ := k') (c₂ := c') (n₂ := 0) (b₂ := 0) (f := fun a => (Pure.pure a : T3.M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TSim.pure_steps hu hq)).of_eq (bind_pure p)
    rfl rfl (Nat.add_zero n) (Nat.add_zero b)

/-- The doublewords the mask loop may change. -/
def MW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (MOUT ≤ X ∧ X < MOUT + 32) ∨ (REGION ≤ X ∧ X < REGION + 32736)

/-- The registers the mask loop may change. -/
def maskRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x24, .x28, .x29, .x30]

/-- Entry conditions of the mask loop (word 48): the private prefix and the nodes of levels 2..11. -/
structure MaskPre (sk : SecretKey) (s : MachineState) (levels : List (List Digest)) : Prop where
  pc : s.pc = pcOf 48
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x13 : s.getReg .x13 = BitVec.ofNat 64 2
  x20 : s.getReg .x20 = BitVec.ofNat 64 1024
  x24 : s.getReg .x24 = BitVec.ofNat 64 REGION
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  nodes : ∀ l, 2 ≤ l → l ≤ 11 → (levels.getD l []).length = 2 ^ (12 - l) ∧
    DigsAt s (TOP + 16 * 2 ^ (12 - l)) (levels.getD l [])

/-- At `kg_level` (word 48) after the levels `2 .. 2 + |pre| - 1` (`pre`: their masked nodes). -/
structure LevelInv (s4 : MachineState) (pre : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = pcOf 48
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (10 - pre.length))
  x13 : t.getReg .x13 = BitVec.ofNat 64 (2 + pre.length)
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * pre.flatten.length)
  flen : pre.flatten.length + 2 ^ (11 - pre.length) = 2048
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION pre.flatten

/-- At `kg_mask` (word 51) in level `2 + |pre|` after the nodes `cur`. -/
structure MaskInv (s4 : MachineState) (pre : List (List Digest)) (cur : List Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 51
  x19 : t.getReg .x19 = BitVec.ofNat 64 cur.length
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (10 - pre.length))
  x13 : t.getReg .x13 = BitVec.ofNat 64 (2 + pre.length)
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * (pre.flatten.length + cur.length))
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION (pre.flatten ++ cur)

theorem two_pow_ten_sub {j : Nat} (hj : j < 10) : 2 ≤ 2 ^ (10 - j) ∧ 2 ^ (10 - j) ≤ 1024 ∧
    2 ^ (11 - j) = 2 * 2 ^ (10 - j) ∧ 2 ^ (10 - (j + 1)) = 2 ^ (10 - j) / 2 ∧
    2 ^ (11 - (j + 1)) = 2 ^ (10 - j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (10 - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ (10 - j) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1024 := by norm_num
  · rw [show 11 - j = (10 - j) + 1 by omega, pow_succ]; ring
  · rw [show 10 - j = (10 - (j + 1)) + 1 by omega, pow_succ]; omega
  · congr 1; omega

section masks
variable {sk : SecretKey} {s4 : MachineState} {levels : List (List Digest)} (hm : MaskPre sk s4 levels)
include hm

/-- One mask: the header, the HASH, the xor into the region. -/
theorem mask_one {pre : List (List Digest)} (hpl : pre.length < 10) {cur : List Digest}
    (hcl : cur.length < 2 ^ (10 - pre.length))
    (hfl : pre.flatten.length + 2 ^ (11 - pre.length) = 2048) {t : MachineState}
    (ht : MaskInv s4 pre cur t) :
    TSim image sk t 30 37 1 1
      (do
        let value ← mask (2 + pre.length) cur.length
        pure ((levels.getD (2 + pre.length) []).getD cur.length 0 ^^^ value))
      (fun d u => MaskInv s4 pre (cur ++ [d]) u) := by
  obtain ⟨hl2, hl1024, h11, -, -⟩ := two_pow_ten_sub hpl
  have g : ∀ r, r ∉ maskRegs → t.getReg r = s4.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk51_spec t ht.pc cur.length (2 ^ (10 - pre.length))
    (by omega) (by omega) ht.x19 ht.x20
  rw [if_pos hcl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2a, t2b, t2r, t2f⟩ := blk52_spec t1 t1pc (2 + pre.length)
    cur.length (by omega) (by omega) (by rw [t1r.get (by decide)]; exact ht.x13)
    (by rw [t1r.get (by decide)]; exact ht.x19)
  have r02 : RegsExcept t t2 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (t1r.trans t2r).mono (by decide)
  have f02 : Frame t t2 (fun X => X = PRIV + 16 ∨ X = PRIV + 24) :=
    (t1f.trans t2f).mono (fun X _ h => by rcases h with h | h; exact h.elim; exact h)
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t2.getMem (BitVec.ofNat 64 X) = s4.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (f02.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (by kg_omega)).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
        (by unfold MW; kg_omega))
  have hq : hashInput t2 =
      toQ (privateInput sk (.inl (header 13 0 0 (2 + pre.length) cur.length))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), t2a, t2b, fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hm.p0, hm.p8, hm.p32, hm.p40, hm.p48, hm.p56]
    rfl
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [r02.get (by decide), g _ (by decide), hm.x5]
  refine (TSim.steps (st1.trans st2) (TSim.mask_bind (k := 16) (c := 16) (n := 0) (b := 0)
    (fetch_64 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc = pcOf 65 := by rw [pc_writeHash, t2pc, pcOf_add4]
  have hmo := DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
  have fsu : Frame s4 (writeHash t2 a) (fun X => MW X ∨ (X = PRIV + 16 ∨ X = PRIV + 24) ∨
      (MOUT ≤ X ∧ X < MOUT + 32)) := ht.frame.trans (f02.trans hwf)
  obtain ⟨hlen, hds⟩ := hm.nodes (2 + pre.length) (by omega) (by omega)
  rw [show 12 - (2 + pre.length) = 10 - pre.length by omega] at hlen hds
  have hnode : DigAt (writeHash t2 a) (TOP + 16 * (2 ^ (10 - pre.length) + cur.length))
      ((levels.getD (2 + pre.length) []).getD cur.length 0) := by
    have := hds.get (show cur.length < _ by rw [hlen]; exact hcl)
    rw [show TOP + 16 * 2 ^ (10 - pre.length) + 16 * cur.length =
      TOP + 16 * (2 ^ (10 - pre.length) + cur.length) by ring] at this
    exact this.frame fsu (by kg_omega) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  have rw2 : RegsExcept t (writeHash t2 a) [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := fun r hr => by
    rw [getReg_writeHash]; exact r02.get hr
  obtain ⟨t3, st3, t3pc, t3a, t3b, t3x24, t3x19, t3r, t3f⟩ := blk65_spec (writeHash t2 a) upc
    (2 ^ (10 - pre.length)) cur.length (REGION + 16 * (pre.flatten.length + cur.length)) (by kg_omega)
    (by kg_omega) (by kg_omega) (by rw [rw2.get (by decide)]; exact ht.x20)
    (by rw [rw2.get (by decide)]; exact ht.x19) (by rw [rw2.get (by decide), g _ (by decide), hm.x2])
    (by rw [rw2.get (by decide)]; exact ht.x24)
  have r23 : RegsExcept t t3 ([.x6, .x7, .x10, .x11, .x12, .x28, .x30] ++
      [.x6, .x7, .x19, .x24, .x28, .x29]) := rw2.trans t3r
  refine TSim.pure_steps st3 ⟨t3pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t3x19, List.length_append, List.length_singleton]
  · rw [r23.get (by decide)]; exact ht.x20
  · rw [r23.get (by decide)]; exact ht.x13
  · rw [t3x24, List.length_append, List.length_singleton, show REGION + 16 * (pre.flatten.length + cur.length) + 16 =
      REGION + 16 * (pre.flatten.length + (cur.length + 1)) by ring]
  · exact (ht.regs.trans r23).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold MW at h ⊢
    kg_omega
  · rw [← List.append_assoc]
    refine DigsAt.snoc ((ht.out.frame ((f02.trans hwf).trans t3f) (by rw [List.length_append]; kg_omega)
      (fun B h1 h2 h => ?_))) ?_
    · rw [List.length_append] at h2
      kg_omega
    · rw [List.length_append]
      constructor
      · rw [t3a, hnode.1, hmo.1, ← BitVec.extractLsb'_xor]
      · rw [show REGION + 16 * (pre.flatten.length + cur.length) + 8 =
          REGION + 16 * (pre.flatten.length + cur.length) + 8 from rfl, t3b,
          show TOP + 16 * (2 ^ (10 - pre.length) + cur.length) + 8 =
          TOP + 16 * (2 ^ (10 - pre.length) + cur.length) + 8 from rfl, hnode.2, hmo.2,
          ← BitVec.extractLsb'_xor]

theorem levelInv_zero : LevelInv s4 [] s4 :=
  ⟨hm.pc, hm.x20, hm.x13, hm.x24, rfl, RegsExcept.refl _ _, Frame.refl _ _, DigsAt.nil _ _⟩

/-- One level `2 + |pre|`: `kg_level`, `I := 0`, the `lo` masks, `kg_next_level`. -/
theorem mask_level {pre : List (List Digest)} (hpl : pre.length < 10) {t : MachineState}
    (ht : LevelInv s4 pre t) :
    TSim image sk t (7 + 30 * 2 ^ (10 - pre.length)) (7 + 37 * 2 ^ (10 - pre.length))
      (2 ^ (10 - pre.length)) (2 ^ (10 - pre.length))
      ((List.range (2 ^ (12 - (2 + pre.length)))).mapM fun i => do
        let value ← mask (2 + pre.length) i
        pure ((levels.getD (2 + pre.length) []).getD i 0 ^^^ value))
      (fun ds u => LevelInv s4 (pre ++ [ds]) u) := by
  obtain ⟨hl2, hl1024, h11, h10', h11'⟩ := two_pow_ten_sub hpl
  have hfl := ht.flen
  rw [show 12 - (2 + pre.length) = 10 - pre.length by omega]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk48_spec t ht.pc (2 ^ (10 - pre.length)) (by omega) ht.x20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x19, t2r, t2f⟩ := blk50_spec t1 t1pc
  have r02 : RegsExcept t t2 [.x6, .x19] := t1r.trans t2r
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp at h)
  have h0 : MaskInv s4 pre [] t2 :=
    ⟨t2pc, t2x19, by rw [r02.get (by decide)]; exact ht.x20, by rw [r02.get (by decide)]; exact ht.x13,
      by rw [r02.get (by decide), ht.x24]; rfl, (ht.regs.trans r02).mono (by decide),
      (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      by rw [List.append_nil]; exact ht.out.frame f02 (by kg_omega) (fun _ _ _ h => h)⟩
  have hin := TSim.mapM_range (image := image) (sk := sk) (2 ^ (10 - pre.length))
    (fun i => do
      let value ← mask (2 + pre.length) i
      pure ((levels.getD (2 + pre.length) []).getD i 0 ^^^ value))
    (fun _ => 30) (fun _ => 37) (fun _ => 1) (fun _ => 1) (MaskInv s4 pre)
    (fun cur u hc hu => mask_one hm hpl hc ht.flen hu) h0
  simp only [sumTo_const] at hin
  refine (TSim.steps (st1.trans st2) (TSim.post_steps (k' := 4) (c' := 4) hin
    (fun ds u hu => ?_))).of_eq rfl (by ring) (by ring) (by ring) (by ring)
  obtain ⟨hdl, hu⟩ := hu
  obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := blk51_spec u hu.pc ds.length (2 ^ (10 - pre.length)) (by omega)
    (by omega) hu.x19 hu.x20
  rw [if_neg (by omega)] at u1pc
  obtain ⟨u2, su2, u2pc, u2x20, u2x13, u2r, u2f⟩ := blk81_spec u1 u1pc (2 ^ (10 - pre.length))
    (2 + pre.length) (by omega) (by rw [u1r.get (by decide)]; exact hu.x20)
    (by rw [u1r.get (by decide)]; exact hu.x13)
  have r12 : RegsExcept u u2 [.x13, .x20] := (u1r.trans u2r).mono (by decide)
  have f12 : Frame u u2 (fun _ => False) := (u1f.trans u2f).mono (fun X _ h => by simp at h)
  refine ⟨u2, su1.trans su2, u2pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u2x20, List.length_append, List.length_singleton, h10']
  · rw [u2x13, List.length_append, List.length_singleton, Nat.add_assoc]
  · rw [r12.get (by decide), hu.x24, List.flatten_concat, List.length_append, hdl]
  · rw [List.flatten_concat, List.length_append, hdl, List.length_append, List.length_singleton, h11']
    omega
  · exact (hu.regs.trans r12).mono (by decide)
  · exact (hu.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  · rw [List.flatten_concat]
    exact hu.out.frame f12 (by rw [List.length_append, hdl]; kg_omega) (fun _ _ _ h => h)

/-- **The keygen masks**: Core's masked levels 2..11, exactly. -/
theorem masks_tsim :
    TSim image sk s4 61450 75772 2046 2046
      ((List.range' 2 10).mapM fun level => (List.range (2 ^ (12 - level))).mapM fun i => do
        let value ← mask level i
        pure ((levels.getD level []).getD i 0 ^^^ value))
      (fun masked u => masked.length = 10 ∧ LevelInv s4 masked u) := by
  rw [List.range'_eq_map_range, List.mapM_map]
  exact (TSim.mapM_range 10 _ (fun j => 7 + 30 * 2 ^ (10 - j)) (fun j => 7 + 37 * 2 ^ (10 - j))
    (fun j => 2 ^ (10 - j)) (fun j => 2 ^ (10 - j)) (LevelInv s4) (fun pre t hl ht => mask_level hm hl ht)
    (levelInv_zero hm)).of_eq rfl (by decide) (by decide) (by decide) (by decide)

end masks

end SigGolfCandidate.T3M.Keygen
