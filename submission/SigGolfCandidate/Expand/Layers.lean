import SigGolfCandidate.Expand.LayFold
import SigGolfCandidate.Sign.Bytes

/-!
# `expand`, phase 2: the counter phase (`Ref.expandLayers`, instructions 316 .. 494)

`layers_sim` : from `layer_loop` with `LAY = n - 1` and the message `M` at `0x120`, the machine
refines `expandLayers w idx n M`: per layer the sign's header and least-counter search, the
counter into `CT + 8 LAY`, and below layer 0 verify's chains, leaf and folds (the root is the next
message); at layer 0 `halt_ok` writes the five counters into the witness and halts with
`withCounters w cs` in the witness buffer.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-! ## The final witness bytes -/

theorem WitMem.readWords_n {w : List Byte} {t : MachineState} (h : WitMem w t) :
    ∀ k o, o % 8 = 0 → o + 8 * k ≤ 0x2B00 →
      t.readWords (BitVec.ofNat 64 (0x800 + o)) k = wordsOf (wbytes w o (8 * k)) := by
  intro k
  induction k with
  | zero => intro o _ _; simp [wbytes, wordsOf_nil]; try rfl
  | succ k ih =>
    intro o ho hk
    rw [readWords_ofNat_succ, show 8 * (k + 1) = 8 + 8 * k by ring, wbytes_add,
      wordsOf_append _ _ (by rw [length_wbytes]), wordsOf_eight _ (length_wbytes _ _ _),
      show 0x800 + o + 8 = 0x800 + (o + 8) by omega, ih (o + 8) (by omega) (by omega), h.get o ho (by omega)]
    rfl

theorem wbytes_zero (w : List Byte) (n : Nat) (h : n ≤ w.length) : wbytes w 0 n = w.take n := by
  rw [← slice_eq_wbytes _ _ _ (by omega)]; simp [slice]

theorem leNat_le32_pair (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    leNat (le32 a ++ le32 b) = a + 2 ^ 32 * b := by
  rw [Sign.leNat_append, Ref.leNat_le32, Ref.leNat_le32, length_le32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; rfl

/-- The witness buffer after `halt_ok`. -/
theorem final_witness (w : List Byte) (hw : w.length = 6348) (c0 c1 c2 c3 c4 : Nat) (h0 : c0 < 2 ^ 32)
    (h1 : c1 < 2 ^ 32) (h2 : c2 < 2 ^ 32) (h3 : c3 < 2 ^ 32) (h4 : c4 < 2 ^ 32) (t : MachineState)
    (hwit : ∀ k < 791, t.getMem (BitVec.ofNat 64 (0x800 + 8 * k)) = wword w (8 * k))
    (m0 : t.getMem (BitVec.ofNat 64 0x20B8) = BitVec.ofNat 64 (c0 + 2 ^ 32 * c1))
    (m1 : t.getMem (BitVec.ofNat 64 0x20C0) = BitVec.ofNat 64 (c2 + 2 ^ 32 * c3))
    (m2 : t.getMem (BitVec.ofNat 64 0x20C8) = BitVec.ofNat 64 c4) :
    readBuffer t 0x800 6348 = ofList 6348 (withCounters w [c0, c1, c2, c3, c4]) := by
  rw [readBuffer_bytesAt]
  apply congrArg (ofList 6348)
  rw [show (6348 : Nat) = 8 * 791 + (8 * 2 + 4) from rfl, bytesAt_add, bytesAt_add]
  have hA : bytesAt t 0x800 (8 * 791) = w.take 6328 := by
    have hwm : ∀ k o, o % 8 = 0 → o + 8 * k ≤ 6328 →
        t.readWords (BitVec.ofNat 64 (0x800 + o)) k = wordsOf (wbytes w o (8 * k)) := by
      intro k
      induction k with
      | zero => intro o _ _; simp [wbytes, wordsOf_nil]; try rfl
      | succ k ih =>
        intro o ho hk
        rw [readWords_ofNat_succ, show 8 * (k + 1) = 8 + 8 * k by ring, wbytes_add,
          wordsOf_append _ _ (by rw [length_wbytes]), wordsOf_eight _ (length_wbytes _ _ _),
          show 0x800 + o + 8 = 0x800 + (o + 8) by omega, ih (o + 8) (by omega) (by omega)]
        have := hwit (o / 8) (by omega)
        rw [show 8 * (o / 8) = o by omega] at this
        rw [this]; rfl
    rw [bytesAt_of_readWords t 791 0x800 (wbytes w 0 (8 * 791)) (by norm_num) (by norm_num)
      (length_wbytes _ _ _) (hwm 791 0 (by norm_num) (by norm_num)), wbytes_zero _ _ (by omega)]
  have hB : bytesAt t (0x800 + 8 * 791) (8 * 2) = le32 c0 ++ le32 c1 ++ (le32 c2 ++ le32 c3) := by
    refine bytesAt_of_readWords t 2 _ _ (by norm_num) (by norm_num) (by simp) ?_
    rw [readWords_ofNat_two, wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
      wordsOf_eight _ (by simp), leNat_le32_pair _ _ h0 h1, leNat_le32_pair _ _ h2 h3]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [m0, m1]; rfl
  have hC : bytesAt t (0x800 + 8 * 791 + 8 * 2) 4 = le32 c4 := by
    have h8 : bytesAt t (0x800 + 8 * 791 + 8 * 2) (8 * 1) = le32 c4 ++ le32 0 := by
      refine bytesAt_of_readWords t 1 _ _ (by norm_num) (by norm_num) (by simp) ?_
      rw [readWords_ofNat_one, wordsOf_eight _ (by simp), leNat_le32_pair _ _ h4 (by norm_num)]
      simp only [Nat.reduceMul, Nat.reduceAdd]
      rw [m2]; rfl
    rw [show 8 * 1 = 4 + 4 from rfl, bytesAt_add] at h8
    have := congrArg (List.take 4) h8
    rwa [List.take_left' (by simp), List.take_left' (by simp)] at this
  rw [hA, hB, hC]
  unfold withCounters
  rw [witCounters_eq]
  simp [List.append_assoc]

/-! ## The layer loop -/

/-- A HALT(0) state with the witness `withCounters w cs` in the witness buffer. -/
def DoneSt (w : List Byte) (cs : List Nat) (t : MachineState) : Prop :=
  fetch eimg t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
    readBuffer t 0x800 6348 = ofList 6348 (withCounters w cs)

/-- Outcome of the layers `n-1 .. 0` (`above`: the counters of the layers above, in layer order). -/
def LPost (w : List Byte) (above : List Nat) (n : Nat) : Option (List Nat) → MachineState → Prop
  | none, t => FailSt t
  | some cs, t => cs.length = n ∧ DoneSt w (cs ++ above) t

/-- The state at `layer_loop` for layer `lay` with message `M`; the counters `above` of the
layers `lay + 1 .. 4` are in `CT`. -/
structure LayInv (w : List Byte) (idx : Nat) (lay : Nat) (M : Val) (above : List Nat) (t : MachineState) :
    Prop where
  ctx : LCtx w idx t
  head : HeadRegs idx lay M t
  hab : above.length = 4 - lay
  ct : ∀ j < above.length, t.getMem (BitVec.ofNat 64 (0x30780 + 8 * (lay + 1 + j))) =
    BitVec.ofNat 64 (above.getD j 0)
  clt : ∀ j < above.length, above.getD j 0 < 2 ^ 22

theorem code381 : eimg.code[381]? = some 0x00000073#32 := by decide +kernel

theorem fetch_ecall_e (t : MachineState) (i : Nat) (hi : eimg.code[i]? = some 0x00000073#32)
    (hlt : 0x1000 + 4 * i < 2 ^ 64) (hpc : t.pc = pcOf i) : fetch eimg t = some (.base .ECALL) := by
  unfold fetch
  rw [hpc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [if_neg (by simp <;> omega), show (0x1000 + 4 * i - 0x1000) / 4 = i by omega, hi]
  rfl

theorem expandLayers_one (w : List Byte) (idx : Nat) (M : Val) :
    expandLayers w idx 1 M = (searchCounter 0 (route idx 0).2 (route idx 0).1 M 0 cMax >>= fun r =>
      match r with
      | none => pure none
      | some (c, _) => pure (some [c])) := rfl

theorem expandLayers_succ (w : List Byte) (idx lay : Nat) (M : Val) :
    expandLayers w idx (lay + 2) M =
      (searchCounter (lay + 1) (route idx (lay + 1)).2 (route idx (lay + 1)).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          verifyLeaf w (lay + 1) (route idx (lay + 1)).2 (route idx (lay + 1)).1 x >>= fun leaf =>
          foldPath (nodeInput (lay + 1) (route idx (lay + 1)).2) (route idx (lay + 1)).1 leaf
              (witPath w (lay + 1)) >>= fun root =>
          expandLayers w idx (lay + 1) root >>= fun r2 =>
            match r2 with
            | none => pure none
            | some cs => pure (some (cs ++ [c]))) := rfl

/-- Cycles per layer (the search dominates: `2^22` trials of 44 cycles). -/
def LW : Nat := 2 ^ 22 * 44 + 10000

/-- **The top layer** (`LAY = 0`): header, search, counter, `halt_ok`. -/
theorem top_layer (w : List Byte) (hw : w.length = 6348) (idx : Nat) (M : Val) (above : List Nat)
    (t : MachineState) (hinv : LayInv w idx 0 M above t) :
    Sim eimg t LW (expandLayers w idx 1 M) (LPost w above 1) := by
  have hc := hinv.ctx
  obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ :=
    layer_head eHeadCode idx 0 M t hinv.head
  set e := (route idx 0).1 with he
  set tau := (route idx 0).2 with htau
  rw [expandLayers_one, show cMax = 2 ^ 22 - 1 + 1 from rfl]
  have henc := encLoop_sim eHeadCode.toEncCode 0 tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
    ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
  refine (Sim.steps hs4 (Sim.bind henc (W₂ := 20) (fun r t5 h5 => ?_))).mono (by unfold LW; omega)
    (fun _ _ h => h)
  rcases r with _ | ⟨c, x⟩
  · obtain ⟨p5, x55, x510⟩ := h5
    exact (Sim.pure (Q := LPost w above 1) (a := none) (s := t5)
      ⟨fetch_ecall_e t5 381 code381 (by norm_num) p5, x55, x510⟩).mono (by omega) (fun _ _ h => h)
  obtain ⟨p5, x56, hcl, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
  dsimp only
  have R5 := r4.trans r5
  have F5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
  obtain ⟨t6, hs6, p6, m6, r6, f6⟩ := blk382_run t5 p5 0 c (by norm_num) hcl x56
    (by rw [R5.get .x8 (by decide), hinv.head.x8]) (by rw [R5.get .x25 (by decide), hc.x25])
  rw [if_pos rfl] at p6
  have F6 : Frame t t6 (fun a => ((a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) ∨ a = 0x30780 + 8 * 0) :=
    F5.trans f6
  have hab := hinv.hab
  have hct : ∀ l < 5, t6.getMem (BitVec.ofNat 64 (0x30780 + 8 * l)) = BitVec.ofNat 64 ((c :: above).getD l 0) := by
    intro l hl
    by_cases h0 : l = 0
    · subst h0; rw [m6]; rfl
    · rw [F6.getMem (by omega) (by simp only [encW]; omega)]
      have := hinv.ct (l - 1) (by omega)
      rw [show 0 + 1 + (l - 1) = l by omega] at this
      rw [this]; obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩; rfl
  have hclt : ∀ l < 5, (c :: above).getD l 0 < 2 ^ 22 := by
    intro l hl
    by_cases h0 : l = 0
    · subst h0; exact hcl
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      exact hinv.clt l' (by omega)
  obtain ⟨t7, hs7, e7, x75, x710, m70, m71, m72, f7⟩ := blk478_run t6 p6 (fun l => (c :: above).getD l 0) hclt
    (by rw [r6.get .x25, R5.get .x25 (by decide), hc.x25]) hct
  refine (Sim.pure_steps (hs6.trans hs7) ⟨rfl, e7, x75, x710, ?_⟩).mono (by omega) (fun _ _ h => h)
  have hlist : [c] ++ above = [(c :: above).getD 0 0, (c :: above).getD 1 0, (c :: above).getD 2 0,
      (c :: above).getD 3 0, (c :: above).getD 4 0] := by
    match above, hab with
    | [a1, a2, a3, a4], _ => rfl
  rw [hlist]
  refine final_witness w hw _ _ _ _ _ (by have := hclt 0 (by norm_num); omega)
    (by have := hclt 1 (by norm_num); omega) (by have := hclt 2 (by norm_num); omega)
    (by have := hclt 3 (by norm_num); omega) (by have := hclt 4 (by norm_num); omega) t7 ?_ m70 m71 m72
  intro k hk
  rw [f7.getMem (by omega) (by omega), F6.getMem (by omega) (by simp only [encW]; omega), hc.wit k (by omega)]

theorem witLayerOff_eq (lay : Nat) (h1 : 1 ≤ lay) (h5 : lay < 5) : witLayerOff lay = 2504 + 768 * lay := by
  interval_cases lay <;> decide

/-- **One layer below the top** (`LAY = n + 1`): header, search, counter, chains, leaf, folds, then
the layers `n .. 0`. -/
theorem layer_step (w : List Byte) (hw : w.length = 6348) (idx : Nat) (n : Nat) (hn : n + 1 < 5)
    (ih : ∀ (M : Val) (above : List Nat) (t : MachineState), LayInv w idx n M above t →
      Sim eimg t ((n + 1) * LW) (expandLayers w idx (n + 1) M) (LPost w above (n + 1)))
    (M : Val) (above : List Nat) (t : MachineState) (hinv : LayInv w idx (n + 1) M above t) :
    Sim eimg t ((n + 2) * LW) (expandLayers w idx (n + 2) M) (LPost w above (n + 2)) := by
  have hc := hinv.ctx
  have hidx := hc.hidx
  have hh := height_le (n + 1) (by omega) hn
  have hwl := witLayerOff_le (n + 1) hn
  have hwe := witLayerOff_eq (n + 1) (by omega) hn
  obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ :=
    layer_head eHeadCode idx (n + 1) M t hinv.head
  set e := (route idx (n + 1)).1 with he
  set tau := (route idx (n + 1)).2 with htau
  have he32 : e < 2 ^ height (n + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have htau30 := emem.htau
  have he2048 := emem.he
  rw [expandLayers_succ, show cMax = 2 ^ 22 - 1 + 1 from rfl]
  have henc := encLoop_sim eHeadCode.toEncCode (n + 1) tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
    ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
  refine (Sim.steps hs4 (Sim.bind henc (W₂ := 8000 + (n + 1) * LW) (fun r t5 h5 => ?_))).mono
    (by unfold LW; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, x⟩
  · obtain ⟨p5, x55, x510⟩ := h5
    exact (Sim.pure (Q := LPost w above (n + 2)) (a := none) (s := t5)
      ⟨fetch_ecall_e t5 381 code381 (by norm_num) p5, x55, x510⟩).mono (by omega) (fun _ _ h => h)
  obtain ⟨p5, x56, hcl, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
  subst hx
  dsimp only
  have R5 := r4.trans r5
  have F5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
  -- the counter, the chain setup
  obtain ⟨t6, hs6, p6, m6, r6, f6⟩ := blk382_run t5 p5 (n + 1) c hn hcl x56
    (by rw [R5.get .x8 (by decide), hinv.head.x8]) (by rw [R5.get .x25 (by decide), hc.x25])
  rw [if_neg (by omega)] at p6
  have R6 := R5.trans r6
  obtain ⟨t7, hs7, p7, y18, y19, y20, y21, y23, y24, mLF0, mLF8, mNB0, mCB8, r7, f7⟩ :=
    blk386_run t6 p6 (n + 1) tau hn htau30 (by rw [R6.get .x8 (by decide), hinv.head.x8])
      (by rw [r6.get .x30, r5.get .x30, x430]) (by rw [R6.get .x25 (by decide), hc.x25])
  have x31 : t6.getReg .x31 = BitVec.ofNat 64 (tau + 2 ^ 32 * e) := by rw [r6.get .x31, r5.get .x31, x431]
  rw [x31] at mLF8 mCB8
  have R7 := R6.trans r7
  have R57 := (r5.trans r6).trans r7
  have F7 : Frame t t7 (fun a => (((a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) ∨ a = 0x30780 + 8 * (n + 1)) ∨
      (a = 0x30240 ∨ a = 0x30248 ∨ a = 0x301C0 ∨ a = 0x30148)) := (F5.trans f6).trans f7
  have c7 : LCtx w idx t7 := hc.frame F7 R7 (fun a h1 h2 => by simp only [lctxA, witA, encW] at h1 h2; omega)
  -- the chains
  have hch := Sim.foldlM_range (image := eimg) 42 (leafF w (n + 1) tau e (digitsOfWord d0 ++ digitsOfWord d1)) []
    (ChInv w idx t7 (n + 1) d0 d1) 160
    (chain_body w idx t7 (n + 1) tau e d0 d1 hn htau30 he2048 hd0 hd1 hw
      (by rw [r7.get .x2, r6.get .x2, x52]) y21 mCB8)
    ⟨by rw [p7, if_pos (by norm_num)], c7, by norm_num, rfl, fun v hv => by simp at hv,
      fun i hi => by simp at hi, y18,
      fun _ => by rw [y19, r6.get .x1, x51]; unfold digWord; simp,
      by rw [y20]; try exact ofNat_congr (by ring), by rw [y23, hwe]; try exact ofNat_congr (by ring),
      by rw [y24]; try exact ofNat_congr (by ring), RegsEq.refl _ _, Frame.refl _ _⟩
  rw [verifyLeaf_eq, bind_assoc]
  simp only [foldPath_eq]
  refine (Sim.steps hs6 (Sim.steps hs7 (Sim.bind hch (W₂ := 300 + (n + 1) * LW) (fun ends t8 h8 => ?_)))).mono
    (by omega) (fun _ _ h => h)
  -- the leaf
  have g8 : ∀ a, a < 2 ^ 64 → ¬ chW a → t8.getMem (BitVec.ofNat 64 a) = t7.getMem (BitVec.ofNat 64 a) :=
    fun a ha hW => h8.frame a ha hW
  have hleaf := leaf_sim w idx (n + 1) tau e hn htau30 he2048 ends h8.len h8.vlen t8
    (by rw [h8.pc, if_neg (by norm_num)]) h8.ctx h8.slots
    (by rw [g8 _ (by norm_num) (by unfold chW; omega), mLF0]) (by rw [g8 _ (by norm_num) (by unfold chW; omega), mLF8])
  refine (Sim.bind hleaf (W₂ := 200 + (n + 1) * LW) (fun leaf t9 h9 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p9, c9, hl9, o9, r9, f9⟩ := h9
  -- the folds
  have R9 := h8.regs.trans r9
  obtain ⟨t10, hs10, p10, z18, z19, r10, m10⟩ := blk442_run t9 p9 (height (n + 1)) e (by omega) he32
    (by rw [R9.get .x9 (by decide), R57.get .x9 (by decide), x49])
    (by rw [R9.get .x13 (by decide), R57.get .x13 (by decide), x413])
  have c10 := c9.frame_nil m10 r10
  have F10 : Frame t7 t10 (fun a => chW a ∨ (0x30200 ≤ a ∧ a < 0x30220)) :=
    (h8.frame.trans f9).trans (fun a _ _ => m10 _ : Frame t9 t10 (fun _ => False)) |>.mono (by
      intro a ha; simp only [or_false] at ha; exact ha)
  have R10 := R9.trans r10
  have hfd := Sim.foldlM_range (image := eimg) (height (n + 1)) (fdF w (n + 1) tau e) leaf
    (FdInv w idx t10 (n + 1) e) 30
    (fold_step w idx t10 (n + 1) tau e (by omega) hn htau30 he32 hw
      (by rw [R10.get .x9 (by decide), R57.get .x9 (by decide), x49])
      (by rw [R10.get .x30 (by decide), R57.get .x30 (by decide), x430])
      (by rw [F10.getMem (by norm_num) (by unfold chW; omega), mNB0]))
    ⟨by rw [p10, if_pos (by omega)], c10, by omega, by rw [z18]; simp, z19,
      by rw [r10.get .x23, r9.get .x23, h8.x23]; try exact ofNat_congr (by ring), hl9,
      by rw [readWords_ofNat_two, m10, m10, ← readWords_ofNat_two, o9], RegsEq.refl _ _, Frame.refl _ _⟩
  refine (Sim.steps hs10 (Sim.bind hfd (W₂ := 6 + (n + 1) * LW) (fun root t11 h11 => ?_))).mono
    (by nlinarith) (fun _ _ h => h)
  obtain ⟨p11, c11, -, -, -, -, hl11, o11, r11, f11⟩ := h11
  rw [if_neg (by omega)] at p11
  have R11 := R10.trans r11
  obtain ⟨t12, hs12, p12, x8', w12, r12, f12⟩ := blk472_run t11 p11 (n + 1) (by omega) hn
    (by rw [R11.get .x8 (by decide), R7.get .x8 (by decide), hinv.head.x8]) c11.x25
  have c12 := c11.frame f12 r12 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
  have F12 : Frame t7 t12 (fun a => (chW a ∨ (0x30200 ≤ a ∧ a < 0x30220)) ∨ fdW a ∨ (a = 0x120 ∨ a = 0x128)) :=
    (F10.trans (f11.trans f12)).mono (fun a ha => ha)
  have R12 := R11.trans r12
  have hab := hinv.hab
  have hinv' : LayInv w idx n root (c :: above) t12 := by
    refine ⟨c12, ⟨by omega, hidx, hl11, p12, c12.x5, c12.x7, by rw [x8']; rfl, c12.x22, c12.x26, c12.x27,
      by rw [w12, o11], c12.ebP⟩, by simp; omega, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons] at hj
      rw [F12.getMem (a := 0x30780 + 8 * (n + 1 + j)) (by omega) (by simp only [chW, fdW]; omega)]
      cases j with
      | zero =>
        rw [f7.getMem (by omega) (by omega), Nat.add_zero, m6]; rfl
      | succ j =>
        rw [F7.getMem (a := 0x30780 + 8 * (n + 1 + (j + 1))) (by omega) (by simp only [encW]; omega)]
        have := hinv.ct j (by omega)
        rw [show n + 1 + 1 + j = n + 1 + (j + 1) by ring] at this
        rw [this]; rfl
    · intro j hj
      cases j with
      | zero => exact hcl
      | succ j => exact hinv.clt j (by simp only [List.length_cons] at hj; omega)
  refine (Sim.steps hs12 (Sim.bind (ih root (c :: above) t12 hinv') (W₂ := 0) (fun r2 t13 h13 => ?_))).mono
    (by omega) (fun _ _ h => h)
  rcases r2 with _ | cs
  · exact (Sim.pure (Q := LPost w above (n + 2)) (a := none) h13)
  obtain ⟨hlen, hdone⟩ := h13
  exact Sim.pure (Q := LPost w above (n + 2)) (a := some (cs ++ [c]))
    ⟨by simp [hlen], by rw [List.append_assoc]; exact hdone⟩

/-- **The counter phase** (`Ref.expandLayers`). -/
theorem layers_sim (w : List Byte) (hw : w.length = 6348) (idx : Nat) :
    ∀ n, n < 5 → ∀ (M : Val) (above : List Nat) (t : MachineState), LayInv w idx n M above t →
      Sim eimg t ((n + 1) * LW) (expandLayers w idx (n + 1) M) (LPost w above (n + 1)) := by
  intro n
  induction n with
  | zero => intro _ M above t hinv; simpa using top_layer w hw idx M above t hinv
  | succ n ih => intro hn M above t hinv; exact layer_step w hw idx n hn (ih (by omega)) M above t hinv

end SigGolfCandidate.ExP
