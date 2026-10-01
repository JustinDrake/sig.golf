import SigGolfCandidate.Expand.Pad

/-!
# The word-copy loop of `expand` (counter `s6 = x22`)

```
loop: lwu  gp, 0(t1)
      sw   gp, 0(t2)
      addi t1, t1, 4
      addi t2, t2, 4
      addi s6, s6, -1
      bne  s6, x0, loop
```
`copy_loop`: at any `pc` where this code sits, with `t1 = src`, `t2 = dst`, `s6 = n ≥ 1`
(4-aligned, in bounds, disjoint), the loop runs `6 n` steps / cycles, exits at `pc + 24`, and the
byte view of memory is `applyCopy (src, dst, n)` of the old one.
-/

namespace SigGolfCandidate.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.Mem

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def loopCode : List (BitVec 32) :=
  [0x00036183, 0x0033a023, 0x00430313, 0x00438393, 0xfffb0b13, 0xfe0b16e3]

theorem copy_body {image : Image} {pc : Word} (hc : CodeAt image pc loopCode)
    (s : MachineState) (hpc : s.pc = pc) (src dst : Nat)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 src) (h7 : s.getReg .x7 = BitVec.ofNat 64 dst)
    (hs : src % 4 = 0) (hd : dst % 4 = 0) (hsb : src + 4 ≤ 2 ^ 24) (hdb : dst + 4 ≤ 2 ^ 24) :
    ∃ u, Steps image s 6 6 u ∧ u.getReg .x6 = BitVec.ofNat 64 (src + 4) ∧
      u.getReg .x7 = BitVec.ofNat 64 (dst + 4) ∧ u.getReg .x22 = s.getReg .x22 - 1 ∧
      u.pc = (if s.getReg .x22 - 1 = 0 then pc + 24 else pc) ∧
      ∀ a < 2 ^ 64, u.getByte (BitVec.ofNat 64 a) =
        if dst ≤ a ∧ a < dst + 4 then s.getByte (BitVec.ofNat 64 (a - dst + src))
        else s.getByte (BitVec.ofNat 64 a) := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hv : ∀ x : Nat, x % 4 = 0 → x + 4 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 4 = true := by
    intro x h1 h2
    rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by simp [MEMORY_BYTES]; omega, h1⟩
  refine ⟨_, Steps.micro (.load .wu .x3 .x6 0) hc hpc ⟨_, rfl, rfl, rfl⟩
    (Micro.exec_load (by simpa [h6, LoadKind.width] using hv src hs hsb)) <|
    Steps.micro (.store .w .x7 .x3 0) hc1 (by simp [hpc, pc_setPC]) ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_store (by simpa [getReg_setReg', h7, StoreKind.width] using hv dst hd hdb)) <|
    Steps.micro (.alu .x6 .add (.reg .x6) (.imm 4)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.alu .x7 .add (.reg .x7) (.imm 4)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.alu .x22 .add (.reg .x22) (.imm 0xffffffffffffffff)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.branch .ne .x22 .x0 0xffffffffffffffec) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p2 | p3 | p4 | p5 => simp [hpc, StoreKind.write]
  simp [getReg_setReg', getByte_setReg, getByte_setPC, h6, h7, hpc, StoreKind.write, LoadKind.read, Src.eval, BinOp.eval, CmpOp.eval]
  have e24 : pc + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 = pc + 24 := by bv_omega
  have e0 : pc + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 18446744073709551596#64 = pc := by bv_omega
  have e8 : s.getReg .x22 + 18446744073709551615#64 = s.getReg .x22 - 1 := by bv_omega
  refine ⟨?_, ?_, e8, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp
  · rw [e24, e0, e8]; rfl
  · intro a ha
    exact getByte_copyWord s _ (by simp) src dst a hs hd (by omega) (by omega) ha

/-- Byte view: `t` agrees with `f` on every address below `2^64`. -/
def BytesEq (t : MachineState) (f : Nat → Byte) : Prop :=
  ∀ a < 2 ^ 64, t.getByte (BitVec.ofNat 64 a) = f a

/-- Copy `4 n` bytes from `src` to `dst` (byte view). -/
def applyCopy (c : Nat × Nat × Nat) (f : Nat → Byte) : Nat → Byte := fun a =>
  if c.2.1 ≤ a ∧ a < c.2.1 + 4 * c.2.2 then f (a - c.2.1 + c.1) else f a

theorem copy_loop {image : Image} {pc : Word} (hc : CodeAt image pc loopCode)
    (s : MachineState) (hpc : s.pc = pc) (src dst n : Nat) (f : Nat → Byte) (hf : BytesEq s f)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 src) (h7 : s.getReg .x7 = BitVec.ofNat 64 dst)
    (h8 : s.getReg .x22 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hs : src % 4 = 0) (hd : dst % 4 = 0) (hsb : src + 4 * n ≤ 2 ^ 24) (hdb : dst + 4 * n ≤ 2 ^ 24)
    (hdisj : src + 4 * n ≤ dst ∨ dst + 4 * n ≤ src) :
    ∃ u, Steps image s (n * 6) (n * 6) u ∧ u.pc = pc + 24 ∧ BytesEq u (applyCopy (src, dst, n) f) := by
  let Inv : Nat → MachineState → Prop := fun i t =>
    i ≤ n ∧ t.getReg .x6 = BitVec.ofNat 64 (src + 4 * (n - i)) ∧
    t.getReg .x7 = BitVec.ofNat 64 (dst + 4 * (n - i)) ∧ t.getReg .x22 = BitVec.ofNat 64 i ∧
    t.pc = (if i = 0 then pc + 24 else pc) ∧
    ∀ a < 2 ^ 64, t.getByte (BitVec.ofNat 64 a) =
      if dst ≤ a ∧ a < dst + 4 * (n - i) then f (a - dst + src) else f a
  have body : ∀ i t, Inv (i + 1) t → ∃ u, Steps image t 6 6 u ∧ Inv i u := by
    intro i t ⟨hi, t6, t7, t8, tpc, tmem⟩
    obtain ⟨u, hst, u6, u7, u8, upc, umem⟩ := copy_body hc t (by simpa using tpc)
      (src + 4 * (n - (i + 1))) (dst + 4 * (n - (i + 1))) t6 t7 (by omega) (by omega)
      (by omega) (by omega)
    have hx8 : t.getReg .x22 - 1 = BitVec.ofNat 64 i := by
      rw [t8]; apply BitVec.eq_of_toNat_eq; simp; omega
    refine ⟨u, hst, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u6]; congr 1; omega
    · rw [u7]; congr 1; omega
    · rw [u8, hx8]
    · rw [upc, hx8]
      by_cases h0 : i = 0
      · subst h0; simp
      · have : BitVec.ofNat 64 i ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        simp only [h0, if_false]; rw [if_neg this]
    · intro a ha
      rw [umem a ha]
      by_cases h1 : dst + 4 * (n - (i + 1)) ≤ a ∧ a < dst + 4 * (n - (i + 1)) + 4
      · rw [if_pos h1, if_pos (by omega), tmem _ (by omega), if_neg (by omega)]
        congr 1; omega
      · rw [if_neg h1, tmem a ha]
        by_cases h2 : dst ≤ a ∧ a < dst + 4 * (n - (i + 1))
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
  have hinit : Inv n s := by
    refine ⟨le_refl _, ?_, ?_, h8, ?_, ?_⟩
    · simpa using h6
    · simpa using h7
    · rw [hpc, if_neg (by omega)]
    · intro a ha; rw [hf a ha, if_neg (by omega)]
  obtain ⟨u, hst, _, _, _, _, upc, umem⟩ := Steps.iterate Inv body n s hinit
  refine ⟨u, hst, by simpa using upc, ?_⟩
  intro a ha
  rw [umem a ha]
  simp [applyCopy]

/-- A straight-line prelude (a symbolic block without memory accesses or side conditions that
sets `t1 = src`, `t2 = dst`, `s0 = n` and falls through to the loop at `pcl`), followed by the
copy loop. -/
theorem stage {image : Image} {pcp pcl : Word} {code : List (BitVec 32)} {fuel : Nat} {r : Result}
    {cfg : Config} {src dst n : Nat} (hrun : symRun cfg code pcp fuel = some r) (hcode : CodeAt image pcp code)
    (hmem : r.st.mem = []) (hobl : r.st.obl = [])
    (h6 : r.st.regs.get .x6 = .c (BitVec.ofNat 64 src))
    (h7 : r.st.regs.get .x7 = .c (BitVec.ofNat 64 dst))
    (h8 : r.st.regs.get .x22 = .c (BitVec.ofNat 64 n)) (hpcl : r.pc = .c pcl)
    (hloop : CodeAt image pcl loopCode)
    (hcond : 0 < n ∧ src % 4 = 0 ∧ dst % 4 = 0 ∧ src + 4 * n ≤ 2 ^ 24 ∧ dst + 4 * n ≤ 2 ^ 24 ∧
      (src + 4 * n ≤ dst ∨ dst + 4 * n ≤ src))
    (t : MachineState) (htpc : t.pc = pcp) (f : Nat → Byte) (hf : BytesEq t f) :
    ∃ u, Steps image t (r.steps + n * 6) (r.cycles + n * 6) u ∧ u.pc = pcl + 24 ∧
      BytesEq u (applyCopy (src, dst, n) f) := by
  have hst := symRun_sound hrun hcode t htpc (by simp [Result.obligs, hobl, Oblig.all])
  obtain ⟨hn, hs, hd, hsb, hdb, hdisj⟩ := hcond
  have hf' : BytesEq (r.toState t) f := by
    intro a ha
    rw [← hf a ha]
    simp only [MachineState.getByte, Result.toState_getMem, hmem, memEval_nil]
  obtain ⟨u, hst2, upc, umem⟩ := copy_loop hloop (r.toState t) (by simp [hpcl, E.eval])
    src dst n f hf' (by simp [h6, E.eval]) (by simp [h7, E.eval]) (by simp [h8, E.eval])
    hn hs hd hsb hdb hdisj
  exact ⟨u, hst.trans hst2, upc, umem⟩

/-- Copies applied in list order. -/
def applyCopies (cs : List (Nat × Nat × Nat)) (f : Nat → Byte) : Nat → Byte :=
  cs.foldl (fun g c => applyCopy c g) f

/-- Disjointness of the interval `[a, a + n)` and `[b, b + m)`. -/
def Disj (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

instance (a n b m : Nat) : Decidable (Disj a n b m) := by unfold Disj; infer_instance

theorem applyCopies_frame : ∀ (cs : List (Nat × Nat × Nat)) (f : Nat → Byte) (x : Nat),
    (∀ c ∈ cs, ¬ (c.2.1 ≤ x ∧ x < c.2.1 + 4 * c.2.2)) → applyCopies cs f x = f x := by
  intro cs
  induction cs with
  | nil => intro f x _; rfl
  | cons c rest ih =>
    intro f x h
    simp only [applyCopies, List.foldl_cons] at ih ⊢
    rw [ih _ x (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')), applyCopy,
      if_neg (h c List.mem_cons_self)]

theorem applyCopies_hit : ∀ (cs : List (Nat × Nat × Nat)) (f : Nat → Byte),
    cs.Pairwise (fun c c' => Disj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) →
    (∀ c ∈ cs, ∀ c' ∈ cs, Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) →
    ∀ c ∈ cs, ∀ x, c.2.1 ≤ x → x < c.2.1 + 4 * c.2.2 →
      applyCopies cs f x = f (x - c.2.1 + c.1) := by
  intro cs
  induction cs with
  | nil => intro _ _ _ c hc; cases hc
  | cons c' rest ih =>
    intro f hpw hsd c hc x hx1 hx2
    simp only [applyCopies, List.foldl_cons] at ih ⊢
    rw [List.pairwise_cons] at hpw
    by_cases hr : c ∈ rest
    · rw [ih _ hpw.2 (fun a ha b hb => hsd a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) c hr x hx1 hx2, applyCopy, if_neg]
      have := hsd c (List.mem_cons_of_mem _ hr) c' List.mem_cons_self
      unfold Disj at this; omega
    · have hcc : c = c' := by
        rcases List.mem_cons.mp hc with h | h
        · exact h
        · exact absurd h hr
      subst hcc
      rw [show List.foldl (fun g c => applyCopy c g) (applyCopy c f) rest x =
        applyCopies rest (applyCopy c f) x from rfl, applyCopies_frame rest _ x (fun c'' hc'' => by
        have := hpw.1 c'' hc''; unfold Disj at this; omega), applyCopy, if_pos ⟨hx1, hx2⟩]

open SigGolfCandidate.Ref


theorem extractByte_replaceByte' (w : Word) (b : BitVec 8) (p q : Nat) (hp : p < 8) (hq : q < 8) :
    extractByte (replaceByte w p b) q = if q = p then b else extractByte w q := by
  interval_cases p <;> interval_cases q <;> (simp only [extractByte, replaceByte]; ext i hi; interval_cases i <;> simp)



theorem alignToDword_ofNat (x : Nat) (hx : x < 2 ^ 64) : alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x / 8 * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show x / 8 * 8 < 2 ^ 64 by omega)]; omega

theorem getByte_setByte_ofNat (s : MachineState) (a a' : Nat) (b : BitVec 8) (ha : a < 2 ^ 64)
    (ha' : a' < 2 ^ 64) :
    (s.setByte (BitVec.ofNat 64 a) b).getByte (BitVec.ofNat 64 a') =
      if a' = a then b else s.getByte (BitVec.ofNat 64 a') := by
  simp only [MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem]
  rw [byteOffset_ofNat ha, byteOffset_ofNat ha', alignToDword_ofNat a ha, alignToDword_ofNat a' ha']
  by_cases h1 : a' / 8 * 8 = a / 8 * 8
  · rw [h1]; simp only [beq_self_eq_true, if_true]
    rw [extractByte_replaceByte' _ _ _ _ (by omega) (by omega)]
    by_cases h2 : a' = a
    · subst h2; simp
    · rw [if_neg (by omega), if_neg h2]
  · have : (BitVec.ofNat 64 (a' / 8 * 8) == BitVec.ofNat 64 (a / 8 * 8)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; rw [ofNat_eq_iff]; omega
    rw [this, if_neg (show ¬ a' = a by omega)]; rfl

theorem getMem_setByte_other (s : MachineState) (a : Nat) (b : BitVec 8) (ha : a < 2 ^ 64) (x : Word)
    (hx : x ≠ BitVec.ofNat 64 (a / 8 * 8)) : (s.setByte (BitVec.ofNat 64 a) b).getMem x = s.getMem x := by
  simp only [MachineState.setByte, MachineState.getMem, MachineState.setMem]
  rw [alignToDword_ofNat a ha]
  simp [hx]



theorem CodeAt.prefix {image : Image} {pc : Word} {l1 l2 : List (BitVec 32)}
    (h : CodeAt image pc (l1 ++ l2)) : CodeAt image pc l1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_append] at h3
  exact ⟨h1, h2, by omega, (List.prefix_append l1 l2).trans h4⟩

def piA : List (BitVec 32) := [0x00341193#32, 0x6e01b483#32, 0x008c81b3#32]
def piB : List (BitVec 32) := [0x00140413#32, 0x00f00893#32, 0xff1414e3#32]

theorem codeAt_piA : CodeAt image (pcOf 153) piA :=
  CodeAt.prefix (l2 := [0x00918023#32, 0x00140413#32, 0x00f00893#32, 0xff1414e3#32]) codeAt_153
theorem codeAt_piS : CodeAt image (pcOf 156) [0x00918023#32] := by
  have := codeAt_153.tail.tail.tail
  rw [show pcOf 153 + 4 + 4 + 4 = pcOf 156 by rfl] at this
  exact CodeAt.prefix (l2 := piB) this
theorem codeAt_piB : CodeAt image (pcOf 157) piB := by
  have := codeAt_153.tail.tail.tail.tail
  rwa [show pcOf 153 + 4 + 4 + 4 + 4 = pcOf 157 by rfl] at this

sym_block blkPiA := symRun { noAlias := true } piA (pcOf 153) 4
sym_block blkPiB := symRun { noAlias := true } piB (pcOf 157) 4

theorem pi_body (s : MachineState) (hpc : s.pc = pcOf 153) (j K : Nat)
    (hj : j < 15) (h8 : s.getReg .x8 = BitVec.ofNat 64 j) (h25 : s.getReg .x25 = BitVec.ofNat 64 0x810)
    (hk : s.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 K) :
    Run s 7 (fun u => u.getReg .x8 = BitVec.ofNat 64 (j + 1) ∧
      u.getReg .x25 = BitVec.ofNat 64 0x810 ∧ u.pc = (if j + 1 = 15 then pcOf 160 else pcOf 153) ∧
      (∀ a < 2 ^ 64, u.getByte (BitVec.ofNat 64 a) =
        if a = 0x810 + j then BitVec.ofNat 8 K else s.getByte (BitVec.ofNat 64 a)) ∧
      ∀ x, x ≠ BitVec.ofNat 64 ((0x810 + j) / 8 * 8) → u.getMem x = s.getMem x) := by
  have hobl : blkPiA.res.obligs s := by
    simp only [blkPiA.res, rv_simp, h8]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blkPiA codeAt_piA hpc hobl (B := 4) ?_).mono (by rw [show blkPiA.res.cycles = 3 from rfl]) (fun _ h => h)
  set s1 := blkPiA.res.toState s with hs1
  have p1 : s1.pc = pcOf 156 := by simp only [hs1, blkPiA.res, rv_simp]
  have x3 : s1.getReg .x3 = BitVec.ofNat 64 (0x810 + j) := by
    simp only [hs1, blkPiA.res, rv_simp, h8, h25]; ex_bvsimp []
  have x9 : s1.getReg .x9 = BitVec.ofNat 64 K := by
    simp only [hs1, blkPiA.res, rv_simp, h8]; ex_bvsimp []
    rw [show j * 8 + 1760 = 0x6E0 + 8 * j by ring, hk]
  have r1 : RegsEq s s1 [.x3, .x9] := by regs_eq
  have m1 : ∀ a, s1.getMem a = s.getMem a := toState_getMem_nil rfl s
  have hv : accessValid (s1.getReg .x3 + 0#64) 1 = true := by
    rw [x3, BitVec.add_zero, accessValid_ofNat]; omega
  have hst := Steps.micro (.store .b .x3 .x9 0#64) codeAt_piS p1 ⟨_, rfl, rfl, rfl⟩ (Micro.exec_store hv)
    (Steps.refl _)
  set s2 := (StoreKind.write s1 (s1.getReg .x3 + 0#64) (s1.getReg .x9) .b).setPC (s1.pc + 4) with hs2
  refine (Run.steps hst (B := 3) ?_).mono (by norm_num) (fun _ h => h)
  have p2 : s2.pc = pcOf 157 := by rw [hs2, pc_setPC, p1]; rfl
  refine Run.of (symRun_sound blkPiB codeAt_piB s2 p2 (by simp only [blkPiB.res, rv_simp])) (le_refl _) ?_
  have hw : s2 = (s1.setByte (BitVec.ofNat 64 (0x810 + j)) (BitVec.ofNat 8 K)).setPC (s1.pc + 4) := by
    rw [hs2, x3, x9, BitVec.add_zero]; simp only [StoreKind.write, truncate8_ofNat]
  have r2 : ∀ r, s2.getReg r = s1.getReg r := by intro r; rw [hw]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [blkPiB.res, rv_simp, r2, r1.get .x8 (by simp), h8]; ex_bvsimp []
  · simp only [blkPiB.res, rv_simp, r2, r1.get .x25 (by simp), h25]
  · simp only [blkPiB.res, rv_simp, r2, r1.get .x8 (by simp), h8]; ex_bvsimp [ofNat_bne_ofNat]
    by_cases h : j + 1 = 15 <;> simp [h] <;> omega
  · intro a ha
    rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, hw]
    show (s1.setByte (BitVec.ofNat 64 (0x810 + j)) (BitVec.ofNat 8 K)).getByte (BitVec.ofNat 64 a) = _
    rw [getByte_setByte_ofNat _ _ _ _ (by omega) ha]
    split
    · rfl
    · rw [getByte_ofNat _ _ ha, m1, ← getByte_ofNat _ _ ha]
  · intro x hx
    rw [toState_getMem_nil rfl, hw]
    show (s1.setByte (BitVec.ofNat 64 (0x810 + j)) (BitVec.ofNat 8 K)).getMem x = _
    rw [getMem_setByte_other _ _ _ (by omega) x hx, m1]



theorem stageRun {cfg : Config} {code : List (BitVec 32)} {i l e fuel : Nat} {r : Result}
    {src dst n : Nat} (hrun : symRun cfg code (pcOf i) fuel = some r) (hcode : CodeAt image (pcOf i) code)
    (hmem : r.st.mem = []) (hobl : r.st.obl = [])
    (h6 : r.st.regs.get .x6 = .c (BitVec.ofNat 64 src))
    (h7 : r.st.regs.get .x7 = .c (BitVec.ofNat 64 dst))
    (h22 : r.st.regs.get .x22 = .c (BitVec.ofNat 64 n)) (hpcl : r.pc = .c (pcOf l))
    (hloop : CodeAt image (pcOf l) loopCode)
    (hcond : 0 < n ∧ src % 4 = 0 ∧ dst % 4 = 0 ∧ src + 4 * n ≤ 2 ^ 24 ∧ dst + 4 * n ≤ 2 ^ 24 ∧
      (src + 4 * n ≤ dst ∨ dst + 4 * n ≤ src)) (hexit : pcOf l + 24 = pcOf e)
    (t : MachineState) (htpc : t.pc = pcOf i) (f : Nat → Byte) (hf : BytesEq t f) :
    Run t (r.cycles + n * 6) (fun u => u.pc = pcOf e ∧ BytesEq u (applyCopy (src, dst, n) f)) := by
  obtain ⟨u, hst, upc, hu⟩ := stage hrun hcode hmem hobl h6 h7 h22 hpcl hloop hcond t htpc f hf
  exact Run.of hst (le_refl _) ⟨by rw [upc, hexit], hu⟩

theorem word_eq_of_bytes (w w' : Word) (h : ∀ k < 8, extractByte w k = extractByte w' k) : w = w' := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun b => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at this
  rw [show i / 8 * 8 + i % 8 = i by omega, show decide (i % 8 < 8) = true by simp; omega] at this
  simpa using this

/-- A dword whose bytes agree. -/
theorem getMem_eq_of_bytes (t u : MachineState) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 < 2 ^ 64)
    (h : ∀ k < 8, u.getByte (BitVec.ofNat 64 (d + k)) = t.getByte (BitVec.ofNat 64 (d + k))) :
    u.getMem (BitVec.ofNat 64 d) = t.getMem (BitVec.ofNat 64 d) := by
  apply word_eq_of_bytes
  intro k hk
  have := h k hk
  rw [getByte_ofNat _ _ (by omega), getByte_ofNat _ _ (by omega), show (d + k) / 8 * 8 = d by omega,
    show (d + k) % 8 = k by omega] at this
  exact this



/-! ### The W1a scatter: 16-byte stride-64 copies -/

/-- The 16-byte stride-64 copy loop body (`ld gp,0(t1); ld tp,8(t1); sd gp,0(t2); sd tp,8(t2);
addi t1,16; addi t2,64; addi s6,-1; bne s6,x0,loop`). -/
def loop16Code : List (BitVec 32) :=
  [0x00033183, 0x00833203, 0x0033b023, 0x0043b423, 0x01030313, 0x04038393, 0xfffb0b13, 0xfe0b12e3]

theorem getByte_setMem_aligned (s : MachineState) (B a : Nat) (w : Word) (hB : B + 8 ≤ 2 ^ 64) (h8 : B % 8 = 0)
    (ha : a < 2 ^ 64) :
    (s.setMem (BitVec.ofNat 64 B) w).getByte (BitVec.ofNat 64 a) =
      if B ≤ a ∧ a < B + 8 then extractByte w (a - B) else s.getByte (BitVec.ofNat 64 a) := by
  rw [getByte_setMem _ _ _ _ (by omega) h8 ha]
  by_cases h : B ≤ a ∧ a < B + 8
  · rw [if_pos (by omega), if_pos h, show a % 8 = a - B by omega]
  · rw [if_neg (by omega), if_neg h]

theorem extractByte_getMem (s : MachineState) (src k : Nat) (hs : src % 8 = 0) (hk : k < 8) (hb : src + 8 ≤ 2 ^ 64) :
    extractByte (s.getMem (BitVec.ofNat 64 src)) k = s.getByte (BitVec.ofNat 64 (src + k)) := by
  rw [getByte_ofNat _ _ (by omega), show (src + k) / 8 * 8 = src by omega, show (src + k) % 8 = k by omega]

@[simp] theorem getReg_setMem'' (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := rfl

theorem copy16_body {image : Image} {pc : Word} (hc : CodeAt image pc loop16Code)
    (s : MachineState) (hpc : s.pc = pc) (src dst : Nat)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 src) (h7 : s.getReg .x7 = BitVec.ofNat 64 dst)
    (hs : src % 8 = 0) (hd : dst % 8 = 0) (hsb : src + 16 ≤ 2 ^ 24) (hdb : dst + 16 ≤ 2 ^ 24) :
    ∃ u, Steps image s 8 8 u ∧ u.getReg .x6 = BitVec.ofNat 64 (src + 16) ∧
      u.getReg .x7 = BitVec.ofNat 64 (dst + 64) ∧ u.getReg .x22 = s.getReg .x22 - 1 ∧
      u.pc = (if s.getReg .x22 - 1 = 0 then pc + 32 else pc) ∧
      ∀ a < 2 ^ 64, u.getByte (BitVec.ofNat 64 a) =
        if dst ≤ a ∧ a < dst + 16 then s.getByte (BitVec.ofNat 64 (a - dst + src))
        else s.getByte (BitVec.ofNat 64 a) := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hv : ∀ x : Nat, x % 8 = 0 → x + 8 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 8 = true := by
    intro x h1 h2
    rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by simp [MEMORY_BYTES]; omega, h1⟩
  have e8 : ∀ x : Nat, x + 8 < 2 ^ 64 → BitVec.ofNat 64 x + 8#64 = BitVec.ofNat 64 (x + 8) := by
    intro x hx; apply BitVec.eq_of_toNat_eq; simp; try omega
  refine ⟨_, Steps.micro (.load .d .x3 .x6 0) hc hpc ⟨_, rfl, rfl, rfl⟩
    (Micro.exec_load (by simpa [h6, LoadKind.width] using hv src hs (by omega))) <|
    Steps.micro (.load .d .x4 .x6 8) hc1 (by simp [hpc, pc_setPC]) ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_load (by simpa [getReg_setReg', h6, LoadKind.width, e8 src (by omega)] using hv (src + 8) (by omega) (by omega))) <|
    Steps.micro (.store .d .x7 .x3 0) hc2 (by simp [hpc, pc_setPC]) ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_store (by simpa [getReg_setReg', h7, StoreKind.width] using hv dst hd (by omega))) <|
    Steps.micro (.store .d .x7 .x4 8) hc3 (by simp [hpc, pc_setPC, StoreKind.write]) ⟨_, rfl, rfl, rfl⟩
      (Micro.exec_store (by simpa [getReg_setReg', h7, StoreKind.width, StoreKind.write, e8 dst (by omega)] using hv (dst + 8) (by omega) (by omega))) <|
    Steps.micro (.alu .x6 .add (.reg .x6) (.imm 16)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.alu .x7 .add (.reg .x7) (.imm 64)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.alu .x22 .add (.reg .x22) (.imm 0xffffffffffffffff)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.micro (.branch .ne .x22 .x0 0xffffffffffffffe4) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p4 | p5 | p6 | p7 => simp [hpc, StoreKind.write]
  simp [getReg_setReg', getByte_setReg, getByte_setPC, h6, h7, hpc, StoreKind.write, LoadKind.read, Src.eval, BinOp.eval, CmpOp.eval, e8 src (by omega), e8 dst (by omega)]
  have e32 : pc + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 = pc + 32 := by bv_omega
  have e0 : pc + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 18446744073709551588#64 = pc := by bv_omega
  have e1 : s.getReg .x22 + 18446744073709551615#64 = s.getReg .x22 - 1 := by bv_omega
  refine ⟨?_, ?_, e1, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp
  · rw [e32, e0, e1]; rfl
  · intro a ha
    rw [getByte_setMem_aligned _ _ _ _ (by omega) (by omega) ha, getByte_setPC,
      getByte_setMem_aligned _ _ _ _ (by omega) hd ha, getByte_setPC, getByte_setReg, getByte_setPC, getByte_setReg]
    by_cases h1 : dst + 8 ≤ a ∧ a < dst + 8 + 8
    · rw [if_pos h1, if_pos (by omega), extractByte_getMem _ _ _ (by omega) (by omega) (by omega)]
      congr 2; omega
    · rw [if_neg h1]
      by_cases h2 : dst ≤ a ∧ a < dst + 8
      · rw [if_pos h2, if_pos (by omega), extractByte_getMem _ _ _ hs (by omega) (by omega)]
        congr 2; omega
      · rw [if_neg h2, if_neg (by omega)]

/-- The copies of the stride loop: `n` chunks of 4 words, source stride 16, destination stride 64. -/
def strideCopies (src dst n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).map fun k => (src + 16 * k, dst + 64 * k, 4)

theorem applyCopies_append (l1 l2 : List (Nat × Nat × Nat)) (f : Nat → Byte) :
    applyCopies (l1 ++ l2) f = applyCopies l2 (applyCopies l1 f) := by
  simp [applyCopies, List.foldl_append]

theorem applyCopies_single (c : Nat × Nat × Nat) (f : Nat → Byte) : applyCopies [c] f = applyCopy c f := rfl

theorem strideCopies_succ (src dst n : Nat) :
    strideCopies src dst (n + 1) = strideCopies src dst n ++ [(src + 16 * n, dst + 64 * n, 4)] := by
  simp [strideCopies, List.range_succ]

theorem copy16_loop {image : Image} {pc : Word} (hc : CodeAt image pc loop16Code)
    (s : MachineState) (hpc : s.pc = pc) (src dst n : Nat) (f : Nat → Byte) (hf : BytesEq s f)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 src) (h7 : s.getReg .x7 = BitVec.ofNat 64 dst)
    (h8 : s.getReg .x22 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hs : src % 8 = 0) (hd : dst % 8 = 0) (hsb : src + 16 * n ≤ 2 ^ 24) (hdb : dst + 64 * n ≤ 2 ^ 24)
    (hdisj : src + 16 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    ∃ u, Steps image s (n * 8) (n * 8) u ∧ u.pc = pc + 32 ∧ BytesEq u (applyCopies (strideCopies src dst n) f) := by
  let Inv : Nat → MachineState → Prop := fun i t =>
    i ≤ n ∧ t.getReg .x6 = BitVec.ofNat 64 (src + 16 * (n - i)) ∧
    t.getReg .x7 = BitVec.ofNat 64 (dst + 64 * (n - i)) ∧ t.getReg .x22 = BitVec.ofNat 64 i ∧
    t.pc = (if i = 0 then pc + 32 else pc) ∧ BytesEq t (applyCopies (strideCopies src dst (n - i)) f)
  have body : ∀ i t, Inv (i + 1) t → ∃ u, Steps image t 8 8 u ∧ Inv i u := by
    intro i t ⟨hi, t6, t7, t8, tpc, tmem⟩
    obtain ⟨u, hst, u6, u7, u8, upc, umem⟩ := copy16_body hc t (by simpa using tpc)
      (src + 16 * (n - (i + 1))) (dst + 64 * (n - (i + 1))) t6 t7 (by omega) (by omega)
      (by omega) (by omega)
    have hx8 : t.getReg .x22 - 1 = BitVec.ofNat 64 i := by
      rw [t8]; apply BitVec.eq_of_toNat_eq; simp; omega
    refine ⟨u, hst, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u6]; congr 1; omega
    · rw [u7]; congr 1; omega
    · rw [u8, hx8]
    · rw [upc, hx8]
      by_cases h0 : i = 0
      · subst h0; simp
      · have : BitVec.ofNat 64 i ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        simp only [h0, if_false]; rw [if_neg this]
    · intro a ha
      rw [umem a ha, show n - i = (n - (i + 1)) + 1 by omega, strideCopies_succ, applyCopies_append,
        applyCopies_single]
      unfold applyCopy
      dsimp only
      by_cases h1 : dst + 64 * (n - (i + 1)) ≤ a ∧ a < dst + 64 * (n - (i + 1)) + 16
      · rw [if_pos h1, if_pos (by omega), tmem _ (by omega)]
      · rw [if_neg h1, if_neg (by omega), tmem a ha]
  have hinit : Inv n s := by
    refine ⟨le_refl _, ?_, ?_, h8, ?_, ?_⟩
    · simpa using h6
    · simpa using h7
    · rw [hpc, if_neg (by omega)]
    · intro a ha; rw [hf a ha]; simp [strideCopies, applyCopies]
  obtain ⟨u, hst, _, _, _, _, upc, umem⟩ := Steps.iterate Inv body n s hinit
  exact ⟨u, hst, by simpa using upc, by simpa using umem⟩

theorem stageRun16 {cfg : Config} {code : List (BitVec 32)} {i l e fuel : Nat} {r : Result}
    {src dst n : Nat} (hrun : symRun cfg code (pcOf i) fuel = some r) (hcode : CodeAt image (pcOf i) code)
    (hmem : r.st.mem = []) (hobl : r.st.obl = [])
    (h6 : r.st.regs.get .x6 = .c (BitVec.ofNat 64 src))
    (h7 : r.st.regs.get .x7 = .c (BitVec.ofNat 64 dst))
    (h22 : r.st.regs.get .x22 = .c (BitVec.ofNat 64 n)) (hpcl : r.pc = .c (pcOf l))
    (hloop : CodeAt image (pcOf l) loop16Code)
    (hcond : 0 < n ∧ src % 8 = 0 ∧ dst % 8 = 0 ∧ src + 16 * n ≤ 2 ^ 24 ∧ dst + 64 * n ≤ 2 ^ 24 ∧
      (src + 16 * n ≤ dst ∨ dst + 64 * n ≤ src)) (hexit : pcOf l + 32 = pcOf e)
    (t : MachineState) (htpc : t.pc = pcOf i) (f : Nat → Byte) (hf : BytesEq t f) :
    Run t (r.cycles + n * 8) (fun u => u.pc = pcOf e ∧ BytesEq u (applyCopies (strideCopies src dst n) f)) := by
  have hst := symRun_sound hrun hcode t htpc (by simp [Result.obligs, hobl, Oblig.all])
  obtain ⟨hn, hs, hd, hsb, hdb, hdisj⟩ := hcond
  have hf' : BytesEq (r.toState t) f := by
    intro a ha
    rw [← hf a ha]
    simp only [MachineState.getByte, Result.toState_getMem, hmem, memEval_nil]
  obtain ⟨u, hst2, upc, umem⟩ := copy16_loop hloop (r.toState t) (by simp [hpcl, E.eval])
    src dst n f hf' (by simp [h6, E.eval]) (by simp [h7, E.eval]) (by simp [h22, E.eval])
    hn hs hd hsb hdb hdisj
  exact Run.of (hst.trans hst2) (le_refl _) ⟨by rw [upc, hexit], umem⟩


end SigGolfCandidate.Expand
