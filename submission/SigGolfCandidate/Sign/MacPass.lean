import SigGolfCandidate.Expand.Mem
import SigGolfCandidate.Ref.Lemmas

/-!
# The arithmetic cache MAC on the machine

One pass of the polynomial MAC is the same 40 instructions in `keygen` and in `sign` (`macPassCode`):
load the key (masked to 61 bits) and the pad from the answer buffer, fold the region's doublewords two
32-bit chunks at a time with lazy reduction modulo `2^61 - 1`, reduce to the canonical residue, add the
pad. `mac_pass` proves it at any code address of any image.
-/

namespace SigGolfCandidate.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ## Lazy reduction modulo `2^61 - 1` -/

/-- Fold at bit 61: congruent modulo `2^61 - 1`. -/
def fold61 (x : Nat) : Nat := x / 2 ^ 61 + x % 2 ^ 61

theorem fold61_mod (x : Nat) : fold61 x % macP = x % macP := by
  unfold fold61 macP
  have := Nat.div_add_mod x (2 ^ 61)
  simp only [Nat.reducePow, Nat.reduceSub] at *
  omega

/-- One chunk step as the machine computes it. -/
def macStep (acc c k : Nat) : Nat := fold61 (fold61 ((acc + c) * k))

theorem macStep_mod (acc c k : Nat) : macStep acc c k % macP = (acc + c) * k % macP := by
  unfold macStep; rw [fold61_mod, fold61_mod]

theorem mul_lt_123 (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    (acc + c) * k < 2 ^ 123 :=
  calc (acc + c) * k < 2 ^ 62 * 2 ^ 61 := Nat.mul_lt_mul'' (by omega) hk
    _ = 2 ^ 123 := by norm_num

theorem fold61_lt_64 (m : Nat) (hm : m < 2 ^ 123) : fold61 m < 2 ^ 64 := by
  unfold fold61
  have h1 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h2 := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  omega

theorem fold61_small (s : Nat) (hs : s < 2 ^ 64) : fold61 s < 2 ^ 61 + 7 := by
  unfold fold61
  have h2 := Nat.mod_lt s (show 0 < 2 ^ 61 by norm_num)
  omega

theorem macStep_lt (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    macStep acc c k < 2 ^ 61 + 7 :=
  fold61_small _ (fold61_lt_64 _ (mul_lt_123 acc c k hacc hc hk))

/-- Both chunk steps of one doubleword `w` (low half first). -/
def macStep2 (k acc w : Nat) : Nat := macStep (macStep acc (w % 2 ^ 32) k) (w / 2 ^ 32) k

/-- The machine's accumulator after a pass over the doublewords `ws` (not yet canonical). -/
def passAcc (k : Nat) (ws : List Nat) : Nat := ws.foldl (macStep2 k) 0

/-- The 32-bit chunks of a doubleword list, low half first. -/
def chunksOf (ws : List Nat) : List Nat := ws.flatMap fun w => [w % 2 ^ 32, w / 2 ^ 32]

theorem foldl_macStep2 (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 61 + 7) (hab : a % macP = b % macP) :
    ws.foldl (macStep2 k) a < 2 ^ 61 + 7 ∧
      ws.foldl (macStep2 k) a % macP =
        (chunksOf ws).foldl (fun acc c => (acc + c) * k % macP) b % macP := by
  induction ws generalizing a b with
  | nil => exact ⟨ha, hab⟩
  | cons w ws ih =>
    have hw := hws w (by simp)
    have h1 : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    have h2 : w / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
    have hlt1 := macStep_lt a (w % 2 ^ 32) k ha h1 hk
    have hlt2 := macStep_lt _ (w / 2 ^ 32) k hlt1 h2 hk
    simp only [List.foldl_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append]
    refine ih (fun x hx => hws x (by simp [hx])) _ _ hlt2 ?_
    unfold macStep2
    rw [macStep_mod, Nat.mod_mod]
    refine Nat.ModEq.mul_right k (Nat.ModEq.add_right _ ?_)
    show macStep a (w % 2 ^ 32) k % macP = (b + w % 2 ^ 32) * k % macP % macP
    rw [macStep_mod, Nat.mod_mod]
    exact Nat.ModEq.mul_right k (Nat.ModEq.add_right _ hab)

/-- A pass computes the polynomial MAC of the chunks, up to the final reduction. -/
theorem passAcc_spec (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64) :
    passAcc k ws < 2 ^ 61 + 7 ∧ passAcc k ws % macP = polyMac k (chunksOf ws) := by
  obtain ⟨h1, h2⟩ := foldl_macStep2 k hk ws hws 0 0 (by norm_num) rfl
  refine ⟨h1, h2.trans ?_⟩
  unfold polyMac
  generalize chunksOf ws = cs
  -- a fold of canonical residues is canonical
  rcases List.eq_nil_or_concat cs with rfl | ⟨cs', c, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.mod_mod]

/-- The canonical residue of a lazily reduced accumulator, as the machine computes it. -/
theorem canon_eq (acc : Nat) (hacc : acc < 2 ^ 61 + 7) :
    (if fold61 acc = macP then 0 else fold61 acc) = acc % macP := by
  have hm := fold61_mod acc
  have hlt : fold61 acc ≤ macP := by
    unfold fold61 macP
    have h2 := Nat.mod_lt acc (show 0 < 2 ^ 61 by norm_num)
    simp only [Nat.reducePow, Nat.reduceSub] at *
    omega
  split_ifs with h
  · rw [← hm, h, Nat.mod_self]
  · rw [← hm, Nat.mod_eq_of_lt (lt_of_le_of_ne hlt h)]

/-! ## The same steps on machine words -/

theorem mulhu_toNat (a b : Word) : (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  unfold rv64_mulhu
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show a.toNat * b.toNat < 2 ^ 128 by omega)]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  exact hab

theorem and_p_toNat (x : Word) : (x &&& BitVec.ofNat 64 (2 ^ 61 - 1)).toNat = x.toNat % 2 ^ 61 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.and_two_pow_sub_one_eq_mod]

/-- One chunk step on words: the twelve instructions `lwu / add / mulhu / mul / slli / srli / add / and /
add / srli / and / add` (the load gives `c`). -/
def stepW (acc c k p : Word) : Word :=
  let t := c + acc
  let hi := rv64_mulhu t k
  let lo := t * k
  let s := (hi <<< 3) + (lo >>> 61) + (lo &&& p)
  (s >>> 61) + (s &&& p)

theorem stepW_ofNat (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    stepW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 c) (BitVec.ofNat 64 k) (BitVec.ofNat 64 (2 ^ 61 - 1)) =
      BitVec.ofNat 64 (macStep acc c k) := by
  have hm := mul_lt_123 acc c k hacc hc hk
  have hs := fold61_lt_64 _ hm
  apply BitVec.eq_of_toNat_eq
  unfold stepW macStep
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, and_p_toNat,
    mulhu_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c + acc < 2 ^ 64 by omega),
    Nat.add_comm c acc]
  generalize (acc + c) * k = m at hm hs ⊢
  -- hi * 8 + lo / 2^61 = m / 2^61 and lo % 2^61 = m % 2^61
  have hhi : m / 2 ^ 64 < 2 ^ 59 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have e1 : m / 2 ^ 64 * 2 ^ 3 % 2 ^ 64 = m / 2 ^ 64 * 8 := by
    rw [show (2 : Nat) ^ 3 = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e2 : m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 = m / 2 ^ 61 := by
    have := Nat.div_add_mod m (2 ^ 64)
    omega
  have e3 : m % 2 ^ 64 % 2 ^ 61 = m % 2 ^ 61 := Nat.mod_mod_of_dvd m (by norm_num)
  have h61 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h61' := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  rw [e1, e3, Nat.mod_eq_of_lt (show m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 < 2 ^ 64 by omega), e2,
    Nat.mod_eq_of_lt (show m / 2 ^ 61 + m % 2 ^ 61 < 2 ^ 64 by omega)]
  rfl

/-- The end of a pass on words: fold once more, map `p` to `0`, add the pad. -/
def tailW (acc p pad : Word) : Word :=
  let a := (acc &&& p) + (acc >>> 61)
  let b : Word := if BitVec.ult (a ^^^ p) 1 then 1 else 0
  (a &&& (b + 18446744073709551615#64)) + pad

theorem tailW_ofNat (acc : Nat) (hacc : acc < 2 ^ 61 + 7) (pad : Word) :
    tailW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 (2 ^ 61 - 1)) pad =
      BitVec.ofNat 64 (acc % macP) + pad := by
  have hc := canon_eq acc hacc
  have ha : (BitVec.ofNat 64 acc &&& BitVec.ofNat 64 (2 ^ 61 - 1)) + (BitVec.ofNat 64 acc >>> 61) =
      BitVec.ofNat 64 (fold61 acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, and_p_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega), BitVec.toNat_ofNat]
    unfold fold61
    rw [Nat.add_comm]
  unfold tailW
  simp only [ha]
  have hf : fold61 acc < 2 ^ 64 := by have := fold61_small acc (by omega); omega
  by_cases h : fold61 acc = macP
  · rw [if_pos h] at hc
    rw [← hc, h]
    have : BitVec.ult (BitVec.ofNat 64 macP ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true := by
      show BitVec.ult (BitVec.ofNat 64 (2 ^ 61 - 1) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true
      rw [BitVec.xor_self]; rfl
    have e : ((1 : Word) + 18446744073709551615#64) = 0 := by decide
    rw [this, if_pos rfl, e]
    simp
  · rw [if_neg h] at hc
    have hx : BitVec.ult (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = false := by
      rw [Bool.eq_false_iff]
      intro hu
      apply h
      have hu' : (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)).toNat < (1#64).toNat :=
        of_decide_eq_true hu
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf,
        Nat.mod_eq_of_lt (by norm_num)] at hu'
      have h0 := Nat.lt_one_iff.mp hu'
      have hm : macP = fold61 acc := by
        calc macP = (fold61 acc ^^^ fold61 acc) ^^^ (2 ^ 61 - 1) := by rw [Nat.xor_self, Nat.zero_xor]; rfl
          _ = fold61 acc ^^^ (fold61 acc ^^^ (2 ^ 61 - 1)) := Nat.xor_assoc _ _ _
          _ = fold61 acc := by rw [h0, Nat.xor_zero]
      exact hm.symm
    rw [hx, ← hc]
    have e : ((0 : Word) + 18446744073709551615#64) = BitVec.allOnes 64 := by decide
    simp only [Bool.false_eq_true, if_false]
    rw [e, BitVec.and_allOnes]

/-! ## The pass on the machine -/

open SigGolfCandidate.Mem

/-- `Steps.micro` for an instruction of any cycle cost. -/
theorem microN {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    {s t u : MachineState} (m : Micro) {k c n : Nat}
    (hc : CodeAt image pc (w :: ws)) (hpc : s.pc = pc)
    (hd : ∃ i, decodeInstruction w = some i ∧ classify i = some m ∧ instructionCycles i = n)
    (hex : m.exec s = some t) (tail : Steps image t k c u) : Steps image s (k + 1) (n + c) u := by
  obtain ⟨i, h1, h2, h3⟩ := hd
  have := Steps.step (hc.fetch s hpc ▸ h1) ((classify_sound h2 s).trans hex) tail
  rwa [h3] at this

theorem codeAt_drop {image : Image} : ∀ (n : Nat) {pc : Word} {code : List (BitVec 32)},
    CodeAt image pc code → n ≤ code.length → CodeAt image (pc + BitVec.ofNat 64 (4 * n)) (code.drop n)
  | 0, pc, code, h, _ => by simpa using h
  | n + 1, pc, [], h, hn => by simp at hn
  | n + 1, pc, w :: ws, h, hn => by
      have h' := codeAt_drop n h.tail (by simpa using hn)
      have e : pc + 4 + BitVec.ofNat 64 (4 * n) = pc + BitVec.ofNat 64 (4 * (n + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]
        omega
      rw [List.drop_succ_cons, ← e]
      exact h'

/-- The 40 instructions of one pass. -/
def macPassCode : List (BitVec 32) :=
  [0x000b3b83, 0x012bfbb3, 0x008b3c03, 0x000056b7, 0xb2068693, 0x00000713,
   0x0006e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733,
   0x0046e783, 0x00e787b3, 0x0377b833, 0x037787b3, 0x00381813, 0x03d7d893, 0x01180833, 0x0127f7b3, 0x00f80833, 0x03d85713, 0x01287833, 0x01070733,
   0x00868693, 0xf9369ee3,
   0x03d75793, 0x01277733, 0x00f70733, 0x012747b3, 0x0017b793, 0xfff78793, 0x00f77733, 0x01870733]

/-- `lwu` at an aligned doubleword address `A` plus `0` or `4`: the low or the high half. -/
theorem read_wu0 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 0) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat % 2 ^ 32) := by
  have e0 : BitVec.ofNat 64 A + 0 = BitVec.ofNat 64 A := by simp
  rw [e0, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega),
    alignToDword_ofNat_aligned (by omega) hA]
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, hA, Nat.shiftRight_eq_div_pow]

theorem read_wu4 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 4) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat / 2 ^ 32) := by
  have e : BitVec.ofNat 64 A + 4 = BitVec.ofNat 64 (A + 4) := by
    apply BitVec.eq_of_toNat_eq; simp
  have ea : alignToDword (BitVec.ofNat 64 (A + 4)) = BitVec.ofNat 64 A := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]; omega
  rw [e, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega), ea]
  apply BitVec.eq_of_toNat_eq
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  simp [LoadKind.fromWord, extractWord32, show (A + 4) % 8 = 4 by omega, Nat.shiftRight_eq_div_pow]
  omega

/-- One chunk step: `lwu a5, 0(a3)` and the eleven instructions that fold it into `a4`. -/
theorem chunk0_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0006e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 0) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 0)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 0) hc hpc ⟨_, rfl, rfl, rfl⟩ (Micro.exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp

/-- One chunk step: `lwu a5, 4(a3)` and the eleven instructions that fold it into `a4`. -/
theorem chunk4_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0046e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 4) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 4)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 4) hc hpc ⟨_, rfl, rfl, rfl⟩ (Micro.exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp

/-- One loop iteration: both chunks of the doubleword at `a3`, advance, branch back unless at the end. -/
theorem body_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (A acc k E : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 acc) (hacc : acc < 2 ^ 61 + 7)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 E) (hE : E < 2 ^ 64) :
    ∃ u, Steps image s 26 38 u ∧
      u.pc = (if A + 8 = E then pc + 104 else pc) ∧
      u.getReg .x13 = BitVec.ofNat 64 (A + 8) ∧
      u.getReg .x14 = BitVec.ofNat 64 (macStep2 k acc (s.getMem (BitVec.ofNat 64 A)).toNat) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hv : ∀ off : Nat, off = 0 ∨ off = 4 →
      accessValid (BitVec.ofNat 64 A + BitVec.ofNat 64 off) 4 = true := by
    intro off hoff
    rw [accessValid_iff, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show A + off < 2 ^ 64 by omega)]
    exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  generalize hwdef : (s.getMem (BitVec.ofNat 64 A)).toNat = w at hw
  have hlo : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhi : w / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
  -- chunk 0
  obtain ⟨u0, st0, pc0, a0, r0, m0⟩ := chunk0_steps (rest := macPassCode.drop 18) hc s hpc
    (by rw [h13]; exact hv 0 (Or.inl rfl))
  rw [h13, h14, h23, h18, read_wu0 s A hA hA', hwdef,
    stepW_ofNat acc (w % 2 ^ 32) k hacc hlo hk] at a0
  have hlt1 := macStep_lt acc (w % 2 ^ 32) k hacc hlo hk
  -- chunk 4
  have hc4 : CodeAt image (pc + 48) (macPassCode.drop 18) := codeAt_drop 12 hc (by decide)
  have e13 : u0.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r0 .x13 (by decide) (by decide) (by decide) (by decide), h13]
  have e23 : u0.getReg .x23 = BitVec.ofNat 64 k := by
    rw [r0 .x23 (by decide) (by decide) (by decide) (by decide), h23]
  have e18 : u0.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1) := by
    rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18]
  obtain ⟨u1, st1, pc1, a1, r1, m1⟩ := chunk4_steps (rest := macPassCode.drop 30) hc4 u0 pc0
    (by rw [e13]; exact hv 4 (Or.inr rfl))
  rw [e13, a0, e23, e18, read_wu4 u0 A hA hA', m0, hwdef,
    stepW_ofNat _ (w / 2 ^ 32) k hlt1 hhi hk] at a1
  -- advance and branch
  have hc5 : CodeAt image (pc + 48 + 48) (macPassCode.drop 30) := codeAt_drop 12 hc4 (by decide)
  have hc6 := hc5.tail
  have x13 : u1.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r1 .x13 (by decide) (by decide) (by decide) (by decide), e13]
  have x19 : u1.getReg .x19 = BitVec.ofNat 64 E := by
    rw [r1 .x19 (by decide) (by decide) (by decide) (by decide),
      r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]
  have st2 : Steps image u1 2 2 _ :=
    microN (.alu .x13 .add (.reg .x13) (.imm 8)) hc5 pc1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.branch .ne .x13 .x19 0xffffffffffffff9c) hc6 (by simp [pc1]) ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _
  have e8 : BitVec.ofNat 64 A + 8#64 = BitVec.ofNat 64 (A + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hcond : (BitVec.ofNat 64 (A + 8) = BitVec.ofNat 64 E) ↔ A + 8 = E := by
    constructor
    · intro hh
      have := congrArg BitVec.toNat hh
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hE] at this
    · rintro rfl; rfl
  refine ⟨_, (st0.trans (st1.trans st2)).of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [getReg_setReg', Src.eval, BinOp.eval, CmpOp.eval, x13, x19, pc1]
    simp only [e8, hcond]
    split_ifs
    · bv_omega
    · bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, x13, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval, a1, macStep2]
  · intro r h1 h2 h3 h4 h5
    simp [getReg_setReg', h1]
    rw [r1 r h2 h3 h4 h5, r0 r h2 h3 h4 h5]
  · intro a
    simp [m1, m0]

/-- The loop: `n` doublewords from `B0`, accumulator from `0`. -/
theorem loop_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (B0 n k : Nat) (ws : List Nat) (hn : 0 < n)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 B0) (hB : B0 % 8 = 0) (hB' : B0 + 8 * n ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 (B0 + 8 * n))
    (hlen : ws.length = n)
    (hmem : ∀ i < n, (s.getMem (BitVec.ofNat 64 (B0 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s (n * 26) (n * 38) u ∧ u.pc = pc + 104 ∧
      u.getReg .x14 = BitVec.ofNat 64 (passAcc k ws) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  let Inv : Nat → MachineState → Prop := fun i t =>
    i ≤ n ∧ t.pc = (if i = 0 then pc + 104 else pc) ∧
    t.getReg .x13 = BitVec.ofNat 64 (B0 + 8 * (n - i)) ∧
    t.getReg .x14 = BitVec.ofNat 64 ((ws.take (n - i)).foldl (macStep2 k) 0) ∧
    (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → t.getReg r = s.getReg r) ∧
    ∀ a, t.getMem a = s.getMem a
  have body : ∀ i t, Inv (i + 1) t → ∃ u, Steps image t 26 38 u ∧ Inv i u := by
    intro i t ⟨hi, tpc, t13, t14, treg, tmem⟩
    have hj : n - (i + 1) < n := by omega
    have hacc := (foldl_macStep2 k hk (ws.take (n - (i + 1)))
      (fun w hw => hws w (List.mem_of_mem_take hw)) 0 0 (by norm_num) rfl).1
    obtain ⟨u, st, upc, u13, u14, ureg, umem⟩ := body_steps hc t (by simpa using tpc)
      (B0 + 8 * (n - (i + 1))) _ k (B0 + 8 * n) t13 (by omega) (by omega) t14 hacc
      (by rw [treg .x23 (by decide) (by decide) (by decide) (by decide) (by decide), h23]) hk
      (by rw [treg .x18 (by decide) (by decide) (by decide) (by decide) (by decide), h18])
      (by rw [treg .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h19]) (by omega)
    refine ⟨u, st, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [upc]
      by_cases h0 : i = 0
      · subst h0; rw [if_pos (by omega), if_pos rfl]
      · rw [if_neg (by omega), if_neg h0]
    · rw [u13]; congr 1; omega
    · rw [u14, tmem, hmem _ hj]
      congr 1
      have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e, List.take_add_one, List.foldl_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    · intro r h1 h2 h3 h4 h5
      rw [ureg r h1 h2 h3 h4 h5, treg r h1 h2 h3 h4 h5]
    · intro a; rw [umem, tmem]
  have hinit : Inv n s := by
    refine ⟨le_refl _, ?_, ?_, ?_, fun _ _ _ _ _ _ => rfl, fun _ => rfl⟩
    · rw [hpc, if_neg (by omega)]
    · simpa using h13
    · simpa using h14
  obtain ⟨u, st, _, upc, _, u14, ureg, umem⟩ := Steps.iterate Inv body n s hinit
  refine ⟨u, st, by simpa using upc, ?_, ureg, umem⟩
  rw [u14, Nat.sub_zero, ← hlen, List.take_length]
  rfl

theorem valid_d (B : Nat) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24) (off : Word) (hoff : off = 0 ∨ off = 8) :
    accessValid (BitVec.ofNat 64 B + off) 8 = true := by
  have z : BitVec.ofNat 64 B + (0 : Word) = BitVec.ofNat 64 B := by simp
  have e0 : (BitVec.ofNat 64 B + (0 : Word)).toNat = B := by
    rw [z, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e8 : (BitVec.ofNat 64 B + (8 : Word)).toNat = B + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [accessValid_iff]
  rcases hoff with rfl | rfl
  · rw [e0]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  · rw [e8]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩

/-- The head of a pass: key (masked to 61 bits) into `s7`, pad into `s8`, `a3` at the first doubleword of
the region, `a4 = 0`. -/
theorem head_steps {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1)) :
    ∃ u, Steps image s 6 6 u ∧ u.pc = pc + 24 ∧
      u.getReg .x23 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) ∧
      u.getReg .x24 = s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      u.getReg .x13 = BitVec.ofNat 64 0x4B20 ∧ u.getReg .x14 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x23 → r ≠ .x24 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have e8 : BitVec.ofNat 64 B + 8#64 = BitVec.ofNat 64 (B + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have k_eq : s.getMem (BitVec.ofNat 64 B) &&& s.getReg .x18 =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) := by
    rw [h18]
    apply BitVec.eq_of_toNat_eq
    rw [and_p_toNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt (s.getMem (BitVec.ofNat 64 B)).toNat
      (show 0 < 2 ^ 61 by norm_num)) (show 2 ^ 61 ≤ 2 ^ 64 by norm_num))).symm
  refine ⟨_, microN (.load .d .x23 .x22 0) hc hpc ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_load (by rw [h22]; exact valid_d B hB hB' 0 (Or.inl rfl))) <|
    microN (.alu .x23 .and (.reg .x23) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.load .d .x24 .x22 8) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_load (by simp only [getReg_setReg', MachineState.getReg_setPC]
                           simp [h22]; exact valid_d B hB hB' 8 (Or.inr rfl))) <|
    microN (.alu .x13 .add (.imm 0x5000) (.imm 0)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x13 .add (.reg .x13) (.imm 0xfffffffffffffb20)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x0) (.imm 0)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, k_eq]
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
    rfl
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp

/-- The end of a pass: the canonical residue plus the pad, in `a4`. -/
theorem tail_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 32))
    (s : MachineState) (hpc : s.pc = pc) :
    ∃ u, Steps image s 8 8 u ∧ u.pc = pc + 32 ∧
      u.getReg .x14 = tailW (s.getReg .x14) (s.getReg .x18) (s.getReg .x24) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  refine ⟨_, microN (.alu .x15 .srl (.reg .x14) (.imm 61)) hc hpc ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x15)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .xor (.reg .x14) (.reg .x18)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .sltu (.reg .x15) (.imm 1)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .add (.reg .x15) (.imm 0xffffffffffffffff)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x15)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x24)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, tailW]
  · intro r h1 h2
    simp [getReg_setReg', h1, h2]
  · intro a; simp

/-- **One pass**: key and pad from the doublewords at `B`, `B + 8` (the answer buffer); the tag word
`polyMac k chunks + pad` in `a4`. Memory is not written. -/
theorem mac_pass {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (ws : List Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0x14B00)
    (hlen : ws.length = 8188)
    (hmem : ∀ i < 8188, (s.getMem (BitVec.ofNat 64 (0x4B20 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s 212902 311158 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunksOf ws)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hk : (s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61 < 2 ^ 61 := Nat.mod_lt _ (by norm_num)
  obtain ⟨u0, st0, pc0, k0, p0, a13, a14, r0, m0⟩ := head_steps hc s hpc B h22 hB hB' h18
  have hcl : CodeAt image (pc + 24) (macPassCode.drop 6) := codeAt_drop 6 hc (by decide)
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  obtain ⟨u1, st1, pc1, b14, r1, m1⟩ := loop_steps hcl u0 pc0 0x4B20 8188 _ ws (by norm_num) a13
    (by norm_num) (by norm_num) a14 k0 hk
    (by rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18])
    (by rw [r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]) hlen
    (fun i hi => by rw [m0]; exact hmem i hi)
  have hct : CodeAt image (pc + 24 + 104) (macPassCode.drop 32) := codeAt_drop 26 hcl (by decide)
  obtain ⟨u2, st2, pc2, c14, r2, m2⟩ := tail_steps hct u1 pc1
  obtain ⟨hlt, hmod⟩ := passAcc_spec _ hk ws hws
  refine ⟨u2, (st0.trans (st1.trans st2)).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [pc2]; bv_omega
  · rw [c14, b14, r1 .x18 (by decide) (by decide) (by decide) (by decide) (by decide),
      r0 .x18 (by decide) (by decide) (by decide) (by decide), h18,
      r1 .x24 (by decide) (by decide) (by decide) (by decide) (by decide), p0,
      tailW_ofNat _ hlt, hmod]
  · intro r h13 h14 h15 h16 h17 h23 h24
    rw [r2 r h14 h15, r1 r h13 h14 h15 h16 h17, r0 r h13 h14 h23 h24]
  · intro a; rw [m2, m1, m0]

/-! ## The region as bytes -/

theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i < n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0 = t.getMem (BitVec.ofNat 64 (a + 8 * i))
  | 0, _, _, h => by omega
  | n + 1, a, i, h => by
      have e : BitVec.ofNat 64 a + 8 = BitVec.ofNat 64 (a + 8) := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [MachineState.readWords_succ, e]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, readWords_getD t n (a + 8) i (by omega)]
        congr 2; omega

/-- Doublewords that spell a byte list: their 32-bit chunks are the list's. -/
theorem chunksOf_of_wordsToNat : ∀ (n : Nat) (R : List Word) (l : List Byte), R.length = n →
    l.length = 8 * n → wordsToNat R = leNat l → chunksOf (R.map BitVec.toNat) = chunks32 l
  | 0, R, l, hR, hl, _ => by
      rw [List.length_eq_zero_iff.mp hR, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
      rfl
  | n + 1, R, l, hR, hl, h => by
      obtain ⟨w, R', rfl⟩ : ∃ w R', R = w :: R' := by
        cases R with
        | nil => simp at hR
        | cons w R' => exact ⟨w, R', rfl⟩
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, l', rfl⟩ :
          ∃ b0 b1 b2 b3 b4 b5 b6 b7 l', l = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' := by
        match l, hl with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l', _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        | [], h => simp at h <;> omega
        | [_], h => simp at h <;> omega
        | [_, _], h => simp at h <;> omega
        | [_, _, _], h => simp at h <;> omega
        | [_, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _, _], h => simp at h <;> omega
      simp only [List.length_cons] at hR hl
      have hw := w.isLt
      have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
      have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
      simp only [wordsToNat, leNat] at h
      have hsplit : w.toNat = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
          256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) ∧
          wordsToNat R' = leNat l' := by
        constructor <;> omega
      have ih := chunksOf_of_wordsToNat n R' l' (by omega) (by omega) hsplit.2
      simp only [List.map_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append, chunks32]
      rw [show List.flatMap (fun w => [w % 2 ^ 32, w / 2 ^ 32]) (List.map BitVec.toNat R') =
        chunksOf (R'.map BitVec.toNat) from rfl, ih]
      congr 1
      · rw [hsplit.1]; omega
      · congr 1
        rw [hsplit.1]; omega

/-- **One pass over the region**, given as bytes. -/
theorem mac_pass_region {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (region : List Byte)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0x14B00)
    (hlen : region.length = 65504)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat region) :
    ∃ u, Steps image s 212902 311158 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunks32 region)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hR := readWords_length s (BitVec.ofNat 64 0x4B20) 8188
  have hch := chunksOf_of_wordsToNat 8188 _ region hR (by rw [hlen]) hreg
  have := mac_pass hc s hpc B ((s.readWords (BitVec.ofNat 64 0x4B20) 8188).map BitVec.toNat) h22 hB hB' h18
    h19 (by rw [List.length_map, hR]) (fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, ← readWords_getD s 8188 0x4B20 i hi,
        List.getD_eq_getElem?_getD]
      cases h : (s.readWords (BitVec.ofNat 64 0x4B20) 8188)[i]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff, hR] at h
        omega
      | some w => rfl)
  rwa [hch] at this

/-- The tag word of half `h` of a key answer `a` (its doublewords `2h`, `2h + 1`), as the reference
writes it. -/
theorem tagWord_eq (a : BitVec 256) (h : Nat) (cs : List Nat) :
    BitVec.ofNat 64 (polyMac ((a.extractLsb' (64 * (2 * h)) 64).toNat % 2 ^ 61) cs) +
        a.extractLsb' (64 * (2 * h + 1)) 64 =
      BitVec.ofNat 64 ((polyMac (answerWord a (2 * h) % 2 ^ 61) cs + answerWord a (2 * h + 1)) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    answerWord, Nat.mod_mod, Nat.mod_add_mod]

/-! ## The tag bytes as doublewords -/

theorem length_macTag (a0 a1 a2 : BitVec 256) (region : List Byte) :
    (macTag a0 a1 a2 region).length = 48 := by
  simp [macTag, macWords]

theorem leNat_six (w0 w1 w2 w3 w4 w5 : Nat) :
    leNat (([w0, w1, w2, w3, w4, w5].map (leBytes 8)).flatten) =
      w0 % 2 ^ 64 + 2 ^ 64 * (w1 % 2 ^ 64 + 2 ^ 64 * (w2 % 2 ^ 64 + 2 ^ 64 * (w3 % 2 ^ 64 +
        2 ^ 64 * (w4 % 2 ^ 64 + 2 ^ 64 * (w5 % 2 ^ 64))))) := by
  have e : ∀ v, leNat (leBytes 8 v) = v % 2 ^ 64 := fun v => by
    rw [leBytes, leNat_map_range]; norm_num
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    leNat_append, length_leBytes, e]
  norm_num

set_option exponentiation.threshold 400 in
theorem six_word (w0 w1 w2 w3 w4 w5 : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) (h4 : w4 < 2 ^ 64) (h5 : w5 < 2 ^ 64) (j : Nat) (hj : j < 6) :
    (w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * (w3 + 2 ^ 64 * (w4 + 2 ^ 64 * w5))))) / 2 ^ (64 * j) % 2 ^ 64 =
      [w0, w1, w2, w3, w4, w5].getD j 0 := by
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one, Nat.reduceMul, Nat.reducePow] at * <;> omega

/-- Doubleword `j` of the 48 tag bytes is tag word `j`. -/
theorem macTag_word (a0 a1 a2 : BitVec 256) (region : List Byte) (j : Nat) (hj : j < 6) :
    leNat (macTag a0 a1 a2 region) / 2 ^ (64 * j) % 2 ^ 64 =
      (macWords a0 (chunks32 region) ++ macWords a1 (chunks32 region) ++
        macWords a2 (chunks32 region)).getD j 0 := by
  have hp : (0 : Nat) < 2 ^ 64 := by norm_num
  unfold macTag macWords
  simp only [List.cons_append, List.nil_append]
  rw [leNat_six]
  simp only [Nat.mod_mod]
  exact six_word _ _ _ _ _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) j hj

set_option exponentiation.threshold 400 in
/-- Two 48-byte strings are equal when their six doublewords are. -/
theorem eq_of_words48 (x y : List Byte) (hx : x.length = 48) (hy : y.length = 48)
    (h : ∀ j < 6, leNat x / 2 ^ (64 * j) % 2 ^ 64 = leNat y / 2 ^ (64 * j) % 2 ^ 64) : x = y := by
  have hlx := leNat_lt x
  have hly := leNat_lt y
  rw [hx] at hlx
  rw [hy] at hly
  have e : leNat x = leNat y := by
    have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num); have h5 := h 5 (by norm_num)
    simp only [Nat.reduceMul, Nat.reducePow, Nat.div_one, Nat.mul_zero, Nat.pow_zero] at h0 h1 h2 h3 h4 h5 hlx hly
    omega
  calc x = toList (ofList 48 x) := (toList_ofList 48 x hx).symm
    _ = toList (ofList 48 y) := by unfold ofList; rw [e]
    _ = y := toList_ofList 48 y hy

/-- The tag word of the first half of a key answer. -/
theorem tagWord0 (a : BitVec 256) (cs : List Nat) :
    BitVec.ofNat 64 (polyMac ((a.extractLsb' 0 64).toNat % 2 ^ 61) cs) + a.extractLsb' 64 64 =
      BitVec.ofNat 64 ((macWords a cs).getD 0 0) := tagWord_eq a 0 cs

/-- The tag word of the second half of a key answer. -/
theorem tagWord1 (a : BitVec 256) (cs : List Nat) :
    BitVec.ofNat 64 (polyMac ((a.extractLsb' 128 64).toNat % 2 ^ 61) cs) + a.extractLsb' 192 64 =
      BitVec.ofNat 64 ((macWords a cs).getD 1 0) := tagWord_eq a 1 cs

end SigGolfCandidate.MacPass
