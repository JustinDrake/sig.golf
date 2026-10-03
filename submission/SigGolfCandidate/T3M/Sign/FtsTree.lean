import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Keygen.Tree

/-!
# Sign: one FTS coordinate tree (`buildFts`, words 186..255 + `build_levels`)

* `fl_pair` : one pair of the leaf loop (`fts_leaf`, words 189..249, twice): the PRF query
  `privatePair 8 coord index 0 p` into `SEC + 32 p`, then the leaf hashes `ftsLeaf index coord (2p) left`,
  `ftsLeaf index coord (2p+1) right` into heap nodes `2048 + 2p`, `2048 + 2p + 1` — exactly 163 steps,
  184 cycles, 3 calls, 3 compressions;
* `buildFts_tsim` : from `fts_coord` (186) with `coord < 7`, the machine refines Core's
  `buildFts index coord` exactly and returns from `build_levels` to word 256 with the whole coordinate
  tree in the heap arena at `FTS` (`HeapAt`) and the 2048 secrets at `SEC`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest buildFts ftsLeaf privatePair shortHash header pad64 zero16 privateInput
  buildLevels)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  LevArgs LevPre HeapAt levRegs LevW)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## The FTS leaf input -/

theorem ftsLeafInput_length (idx c l : Nat) (sec : Digest) :
    (zero16 ++ bytesLE 16 (header 9 c idx 0 l) ++ bytesLE 16 sec ++ zero16).length = 64 := by
  simp [bytesLE_length, zero16]

/-- `ℓ ^^^ 2048 = 2048 + ℓ` for a leaf index `ℓ < 2048`. -/
theorem leaf_xor2048 (n : Nat) (h : n < 2048) : n % 2 ^ 32 ^^^ 2048 = 2048 + n := by
  rw [Nat.mod_eq_of_lt (by omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, show (2048 : Nat) = 2 ^ 11 from rfl, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i 11 with hi | rfl | hi
  · rw [Nat.testBit_two_pow_add_gt hi]
    simp [show ¬ (11 = i) by omega]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]
    simp
  · have h1 : n < 2 ^ i := lt_of_lt_of_le h (by
      calc (2048 : Nat) = 2 ^ 11 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ 11 + n < 2 ^ i := by
      have : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [show ¬ (11 = i) by omega]

/-- The FTS leaf header word 1 (tag 9, position 0, leaf `ℓ < 2048`) is the reversed heap index `2048 + ℓ`. -/
theorem nodeWord_9_leaf (l : Nat) (hl : l < 2048) : T3.nodeWord 9 0 l = T3.Rev.revBits 64 (2048 + l) := by
  rw [nodeWord_9, leaf_xor2048 l hl, hdr1_eq (2048 + l) 0 (by omega) (by norm_num)]
  simp

theorem wordsOf_ftsLeafInput (idx c l : Nat) (sec : Digest) :
    wordsOf (zero16 ++ bytesLE 16 (header 9 c idx 0 l) ++ bytesLE 16 sec ++ zero16) =
      [0, 0, BitVec.ofNat 64 (hdr0 9 c idx idx), BitVec.ofNat 64 (T3.nodeWord 9 0 l), sec.extractLsb' 0 64,
        sec.extractLsb' 64 64, 0, 0] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [zero16]), wordsOf_zero16, wordsOf_packed_header 9 _ _ _ _ (by decide), wordsOf_bytesLE16]
  rfl

theorem toQ_ftsLeafInput_blocks (idx c l : Nat) (sec : Digest) :
    (toQ (pad64 (zero16 ++ bytesLE 16 (header 9 c idx 0 l) ++ bytesLE 16 sec ++ zero16))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ftsLeafInput_length]), blocks_toQ ⟨by rw [ftsLeafInput_length]; omega,
    by rw [ftsLeafInput_length]⟩, ftsLeafInput_length]

/-! ## The leaf loop -/

/-- Doublewords the leaf loop may change. -/
def FlW (A : Nat) : Prop :=
  A = PRIV + 16 ∨ A = PRIV + 24 ∨ (SEC ≤ A ∧ A < SEC + 32768) ∨ A = FLEAF + 16 ∨ A = FLEAF + 24 ∨
    A = FLEAF + 32 ∨ A = FLEAF + 40 ∨ (LFOUT ≤ A ∧ A < LFOUT + 32) ∨ (FTS + 32768 ≤ A ∧ A < FTS + 65536)

/-- Registers the leaf loop may change. -/
def flRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x28, .x29, .x30]

/-- Entry facts of coordinate `c`'s tree (index `idx`). -/
structure FlPre (sk : SecretKey) (cache : Bytes 131072) (c idx : Nat) (s : MachineState) : Prop where
  base : Base sk cache s
  x2 : s.getReg .x2 = BitVec.ofNat 64 FTS
  x8 : s.getReg .x8 = BitVec.ofNat 64 c
  x9 : s.getReg .x9 = BitVec.ofNat 64 idx
  hc : c < 7
  hidx : idx < 2 ^ 31

/-- At `fts_leaf` (189) after `p` pairs: the leaf hashes at heap `2048 ..`, the secrets at `SEC`. -/
structure FlInv (s0 : MachineState) (p : Nat) (st : List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 189
  x18 : t.getReg .x18 = BitVec.ofNat 64 (2 * p)
  regs : RegsExcept s0 t flRegs
  frame : Frame s0 t FlW
  len1 : st.1.length = 2 * p
  len2 : st.2.length = 2 * p
  leaves : DigsAt t (FTS + 32768) st.1
  secrets : DigsAt t SEC st.2

/-- Core's pair body of `buildFts`. -/
def flBody (c idx : Nat) (state : List Digest × List Digest) (pair : Nat) :
    T3.M (List Digest × List Digest) := do
  let (left, right) ← privatePair 8 c idx 0 pair
  let leftLeaf ← ftsLeaf idx c (2*pair) left
  let rightLeaf ← ftsLeaf idx c (2*pair+1) right
  pure (state.1 ++ [leftLeaf,rightLeaf], state.2 ++ [left,right])

theorem buildFts_eq (idx c : Nat) : buildFts idx c = (do
    let state ← (List.range 1024).foldlM (flBody c idx) ([], [])
    let levels ← buildLevels 10 c idx 11 state.1
    pure (levels, state.2)) := rfl

section loop
variable {sk : SecretKey} {cache : Bytes 131072} {c idx : Nat} {s0 : MachineState}
  (hpre : FlPre sk cache c idx s0)
include hpre

theorem FlPre.reg {t : MachineState} (h : RegsExcept s0 t flRegs) {r : Reg} (hr : r ∉ flRegs) :
    t.getReg r = s0.getReg r := h.get hr

/-- One leaf hash (words 211..249) of leaf `l` with its secret `sec` at `SEC + 16 l`: the FLEAF block, the
HASH, the heap node `2048 + l`, back to `fts_leaf` with `LEAF = l + 1`. -/
theorem fl_hash {l : Nat} (hl : l < 2048) {t : MachineState} (hpc : t.pc = pcOf 211)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 l) (hregs : RegsExcept s0 t flRegs) (hfr : Frame s0 t FlW)
    {sec : Digest} (hsec : DigAt t (SEC + 16 * l) sec) {β : Type} {f : Digest → T3.M β} {k c' n b : Nat}
    {Q : β → MachineState → Prop}
    (hk : ∀ v : Digest, ∀ u, u.pc = pcOf 189 → u.getReg .x18 = BitVec.ofNat 64 (l + 1) →
      RegsExcept s0 u flRegs → Frame s0 u FlW → DigAt u (FTS + 16 * (2048 + l)) v →
      Frame t u (fun A => A = FLEAF + 16 ∨ A = FLEAF + 24 ∨ A = FLEAF + 32 ∨ A = FLEAF + 40 ∨
        (LFOUT ≤ A ∧ A < LFOUT + 32) ∨ A = FTS + 16 * (2048 + l) ∨ A = FTS + 16 * (2048 + l) + 8) →
      TSim image sk u k c' n b (f v) Q) :
    TSim image sk t (54 + (1 + (13 + k))) (54 + (8 + (13 + c'))) (1 + n) (1 + b)
      (ftsLeaf idx c l sec >>= f) Q := by
  have hc := hpre.hc
  have hidx := hpre.hidx
  obtain ⟨t1, st1, t1pc, t1x10, t1x11, t1x12, m32, m40, m16, m24, t1r, t1f⟩ :=
    blk211_full t hpc c idx l (by omega) (by omega) hl
      (by rw [hpre.reg hregs (by simp [flRegs]), hpre.x8]) (by rw [hpre.reg hregs (by simp [flRegs]), hpre.x9])
      h18
  have hz : ∀ A, NeverW A → A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA hA'
    rw [t1f.get hA' (by unfold NeverW at hA; sg_omega),
      hfr.get hA' (by unfold NeverW at hA; unfold FlW; sg_omega), hpre.base.zero A hA' hA]
  have hq : hashInput t1 = toQ (pad64 (zero16 ++ bytesLE 16 (header 9 c idx 0 l) ++ bytesLE 16 sec ++ zero16)) := by
    rw [pad64_of_aligned _ (by rw [ftsLeafInput_length])]
    refine hashInput_toQ t1 _ 0 FLEAF (ftsLeafInput_length _ _ _ _) t1x10 (by decide) (by decide) t1x11
      (by decide) ?_
    rw [wordsOf_ftsLeafInput, readWords_eight, m16, m24, m32, m40, hsec.1, hsec.2,
      hdr0_eq 9 c idx idx (by norm_num) (by omega) (by omega) (by omega), nodeWord_9_leaf l hl,
      hz FLEAF (by unfold NeverW; simp) (by decide), hz (FLEAF + 8) (by unfold NeverW; simp) (by decide),
      hz (FLEAF + 48) (by unfold NeverW; simp) (by decide), hz (FLEAF + 56) (by unfold NeverW; simp) (by decide)]
    all_goals (congr 3 <;> ring_nf)
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 FLEAF 64 LFOUT t1x10 t1x11 t1x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t1.getReg .x5 = 0 := by
    rw [t1r.get (by simp), hpre.reg hregs (by simp [flRegs]), hpre.base.x5]
  have e : ftsLeaf idx c l sec >>= f =
      shortHash (zero16 ++ bytesLE 16 (header 9 c idx 0 l) ++ bytesLE 16 sec ++ zero16) >>= f := rfl
  refine TSim.steps st1 ((TSim.shortHash_bind (k := 13 + k) (c := 13 + c') (n := n) (b := b)
    (fetch_236 t1 t1pc) h5 hv hq (fun a => ?_)).of_eq e.symm rfl (by rw [toQ_ftsLeafInput_blocks]) rfl
    (by rw [toQ_ftsLeafInput_blocks]))
  have hwf := Frame.writeHash t1 a LFOUT t1x12 (by decide)
  have hlo := DigAt.writeHash_lo t1 a LFOUT t1x12 (by decide)
  obtain ⟨t2, st2, t2pc, t2x18, n0, n8, t2r, t2f⟩ := blk237_spec (writeHash t1 a)
    (by rw [pc_writeHash, t1pc, pcOf_add4]) l hl
    (by rw [getReg_writeHash, t1r.get (by simp), h18])
    (by rw [getReg_writeHash, t1r.get (by simp), hpre.reg hregs (by simp [flRegs]), hpre.x2])
  refine TSim.steps st2 (hk _ t2 t2pc t2x18 ?_ ?_ ⟨n0.trans hlo.1, n8.trans hlo.2⟩ ?_)
  · have hw0 : RegsExcept t1 (writeHash t1 a) [] := fun r _ => getReg_writeHash t1 a r
    exact (((hregs.trans t1r).trans hw0).trans t2r).mono (by decide)
  · refine ((hfr.trans t1f).trans (hwf.trans t2f)).mono (fun A _ h => ?_)
    unfold FlW at *
    rcases h with (h | h) | (h | h) <;> sg_omega
  · exact ((t1f.trans hwf).trans t2f).mono (fun A _ h => by rcases h with (h | h) | h <;> sg_omega)

/-- From `fts_leaf` with an odd leaf `l`: the loop test and the parity test to `fts_noprf` (5 steps). -/
theorem fl_odd {l : Nat} (hl : l < 2048) (hodd : l % 2 = 1) {t : MachineState} (hpc : t.pc = pcOf 189)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 l) :
    ∃ u, Steps image t 5 5 u ∧ u.pc = pcOf 211 ∧ RegsExcept t u [.x6] ∧ Frame t u (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk189_spec t hpc l (by omega) h18
  rw [if_pos hl] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := blk192_spec t1 t1pc l (by omega) (by rw [t1r.get (by simp)]; exact h18)
  rw [if_neg (by omega)] at t2pc
  exact ⟨t2, st1.trans st2, t2pc, (t1r.trans t2r).mono (by simp),
    (t1f.trans t2f).mono (fun _ _ h => by simp_all)⟩

/-- **One pair** of the leaf loop: the PRF query and the two leaf hashes (163 steps, 184 cycles). -/
theorem fl_pair {p : Nat} (hp : p < 1024) {st : List Digest × List Digest} {t : MachineState}
    (ht : FlInv s0 p st t) :
    TSim image sk t 163 184 3 3 (flBody c idx st p) (FlInv s0 (p + 1)) := by
  have hc := hpre.hc
  have hidx := hpre.hidx
  have g : ∀ r, r ∉ flRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk189_spec t ht.pc (2 * p) (by omega) ht.x18
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := blk192_spec t1 t1pc (2 * p) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x18)
  rw [if_pos (by omega)] at t2pc
  have e12 : RegsExcept t t2 [.x6] := (t1r.trans t2r).mono (by simp)
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3a, t3b, t3r, t3f⟩ := blk194_spec t2 t2pc c idx (2 * p)
    (by omega) (by omega) (by omega)
    (by rw [e12.get (by simp), g _ (by simp [flRegs]), hpre.x8])
    (by rw [e12.get (by simp), g _ (by simp [flRegs]), hpre.x9])
    (by rw [e12.get (by simp)]; exact ht.x18)
  rw [show 2 * p / 2 = p by omega] at t3b
  have f03 : Frame s0 t3 FlW := (ht.frame.trans ((t1f.trans t2f).trans t3f)).mono (fun X _ h => by
    unfold FlW at *; rcases h with h | ((h | h) | h) <;> first | exact h | (exact h.elim) | sgo)
  have r03 : RegsExcept s0 t3 flRegs := ((ht.regs.trans e12).trans t3r).mono (by decide)
  have hP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t3.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    f03.get (by sgo) (by unfold FlW; sgo)
  have hq : hashInput t3 = toQ (privateInput sk (.inl (header 8 c idx 0 p))) := by
    refine hashInput_toQ t3 _ 0 PRIV (privateInput_tweak_length _ _) t3x10 (by decide) (by decide) t3x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, hP PRIV (by simp),
      hP (PRIV + 8) (by simp), t3a, t3b, hP (PRIV + 32) (by simp), hP (PRIV + 40) (by simp),
      hP (PRIV + 48) (by simp), hP (PRIV + 56) (by simp), hpre.base.p0, hpre.base.p8, hpre.base.p32,
      hpre.base.p40, hpre.base.p48, hpre.base.p56,
      hdr0_eq 8 c idx 0 (by norm_num) (by omega) (by omega) (by norm_num), hdr1_eq idx p (by omega) (by omega)]
    congr 3 <;> ring_nf
  have hv : hashArgumentsValid t3 = true :=
    hashArgs_const t3 PRIV 64 (SEC + 16 * (2 * p)) t3x10 t3x11 t3x12 (by decide) (by decide) (by decide)
      (by sgo) (by sgo)
  have h5 : t3.getReg .x5 = 0 := by rw [r03.get (by simp [flRegs]), hpre.base.x5]
  unfold flBody
  refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.privatePair_bind (k := 68 + 5 + 68) (c := 75 + 5 + 75)
    (n := 2) (b := 2) (fetch_210 t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl (by omega) (by omega) rfl rfl
  -- the PRF answer at SEC + 32 p
  have hwf := Frame.writeHash t3 a (SEC + 16 * (2 * p)) t3x12 (by sgo)
  have hlo := DigAt.writeHash_lo t3 a (SEC + 16 * (2 * p)) t3x12 (by sgo)
  have hhi := DigAt.writeHash_hi t3 a (SEC + 16 * (2 * p)) t3x12 (by sgo)
  set w := writeHash t3 a with hw
  have wpc : w.pc = pcOf 211 := by rw [hw, pc_writeHash, t3pc, pcOf_add4]
  have r0w : RegsExcept s0 w flRegs := fun r hr => by rw [hw, getReg_writeHash]; exact r03 r hr
  have f0w : Frame s0 w FlW := (f03.trans hwf).mono (fun X _ h => by
    unfold FlW at *; rcases h with h | h <;> first | exact h | sgo)
  have w18 : w.getReg .x18 = BitVec.ofNat 64 (2 * p) := by
    rw [hw, getReg_writeHash, t3r.get (by simp), e12.get (by simp)]; exact ht.x18
  -- the left leaf
  refine (fl_hash hpre (l := 2 * p) (k := 5 + 68) (c' := 5 + 75) (n := 1) (b := 1) (by omega) wpc w18 r0w f0w hlo
    (fun ll u upc u18 ur uf uv utu => ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨u1, stu1, u1pc, u1r, u1f⟩ := fl_odd hpre (l := 2 * p + 1) (by omega) (by omega) upc u18
  have hsecR : DigAt u1 (SEC + 16 * (2 * p + 1)) (a.extractLsb' 128 128) := by
    have := (hhi.frame utu (by sgo) (by sgo) (by sgo)).frame u1f (by sgo) (by simp) (by simp)
    rwa [show SEC + 16 * (2 * p) + 16 = SEC + 16 * (2 * p + 1) by ring] at this
  refine TSim.steps stu1 ((fl_hash hpre (l := 2 * p + 1) (k := 0) (c' := 0) (n := 0) (b := 0) (by omega) u1pc
    (by rw [u1r.get (by simp)]; exact u18) ((ur.trans u1r).mono (by simp [flRegs]))
    (uf.trans u1f |>.mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)) hsecR
    (fun rl v vpc v18 vr vf vv vtv => TSim.pure ⟨vpc, by rw [v18, show 2 * p + 1 + 1 = 2 * (p + 1) by ring],
      vr, vf, ?_, ?_, ?_, ?_⟩)).of_eq
    rfl rfl rfl rfl rfl)
  · simp [ht.len1]; ring
  · simp [ht.len2]; ring
  · -- the leaves so far, then the two new leaf hashes
    have hl1 := ht.len1
    show DigsAt v (FTS + 32768) (st.1 ++ [ll, rl])
    rw [show st.1 ++ [ll, rl] = st.1 ++ [ll] ++ [rl] by simp]
    refine DigsAt.snoc (DigsAt.snoc ?_ ?_) ?_
    · refine ht.leaves.frame (((((t1f.trans t2f).trans t3f).trans hwf).trans utu).trans (u1f.trans vtv))
        (by rw [hl1]; sgo) (fun X h1 h2 h => ?_)
      rw [hl1] at h2
      rcases h with (((((h | h) | h) | h) | h) | h) | (h | h) <;> sgo
    · rw [hl1]
      exact (uv.frame (u1f.trans vtv) (by sgo) (by sgo) (by sgo)).congr rfl |>.congr rfl
        |> fun h => by rw [show FTS + 32768 + 16 * (2 * p) = FTS + 16 * (2048 + 2 * p) by ring]; exact h
    · rw [List.length_append, hl1, List.length_singleton]
      rw [show FTS + 32768 + 16 * (2 * p + 1) = FTS + 16 * (2048 + (2 * p + 1)) by ring]
      exact vv
  · -- the secrets so far, then the two PRF halves
    have hl2 := ht.len2
    show DigsAt v SEC (st.2 ++ [a.extractLsb' 0 128, a.extractLsb' 128 128])
    rw [show st.2 ++ [a.extractLsb' 0 128, a.extractLsb' 128 128] =
      st.2 ++ [a.extractLsb' 0 128] ++ [a.extractLsb' 128 128] by simp]
    refine DigsAt.snoc (DigsAt.snoc ?_ ?_) ?_
    · refine ht.secrets.frame (((((t1f.trans t2f).trans t3f).trans hwf).trans utu).trans (u1f.trans vtv))
        (by rw [hl2]; sgo) (fun X h1 h2 h => ?_)
      rw [hl2] at h2
      rcases h with (((((h | h) | h) | h) | h) | h) | (h | h) <;> sgo
    · rw [hl2]
      exact (hlo.frame utu (by sgo) (by sgo) (by sgo)).frame (u1f.trans vtv) (by sgo)
        (by sgo) (by sgo)
    · rw [List.length_append, hl2, List.length_singleton]
      exact hsecR.frame vtv (by sgo) (by sgo) (by sgo)

theorem flInv_zero (hpc : s0.pc = pcOf 189) (h18 : s0.getReg .x18 = BitVec.ofNat 64 0) :
    FlInv s0 0 ([], []) s0 :=
  ⟨hpc, h18, RegsExcept.refl _ _, Frame.refl _ _, rfl, rfl, DigsAt.nil _ _, DigsAt.nil _ _⟩

/-- **The leaf loop**: 1024 pairs (166,912 steps, 188,416 cycles, 3,072 calls and compressions). -/
theorem fl_loop (hpc : s0.pc = pcOf 189) (h18 : s0.getReg .x18 = BitVec.ofNat 64 0) :
    TSim image sk s0 (1024 * 163) (1024 * 184) (1024 * 3) (1024 * 3)
      ((List.range 1024).foldlM (flBody c idx) ([], [])) (FlInv s0 1024) := by
  have := TSim.foldlM_range (image := image) (sk := sk) 1024 (flBody c idx) ([], []) (FlInv s0)
    (fun _ => 163) (fun _ => 184) (fun _ => 3) (fun _ => 3) (fun j hj acc t ht => fl_pair hpre hj ht)
    (flInv_zero hpre hpc h18)
  simpa only [sumTo_const] using this

end loop

/-! ## The whole tree -/

/-- The `build_levels` call of coordinate `c` (index `idx`): tag 10, height 11, arena `FTS`, return 256. -/
def ftsLev (c idx : Nat) : LevArgs := ⟨10, c, idx, 11, FTS, 256⟩

theorem ftsLev_costs (c idx : Nat) : (ftsLev c idx).levK = 137220 ∧ (ftsLev c idx).levC = 151549 ∧
    (ftsLev c idx).levN = 2047 := by
  have e : (ftsLev c idx).levK = (ftsLev 0 0).levK ∧ (ftsLev c idx).levC = (ftsLev 0 0).levC ∧
      (ftsLev c idx).levN = (ftsLev 0 0).levN := ⟨rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2]
  decide

/-- The registers `buildFts` may change (from `fts_coord`). -/
def ftRegs : List Reg := [.x6, .x18] ++ flRegs ++ [.x1, .x15, .x21, .x30] ++ levRegs

/-- The doublewords `buildFts` may change. -/
def FtW (c idx : Nat) (X : Nat) : Prop := FlW X ∨ LevW (ftsLev c idx) X

/-- **`buildFts`** from `fts_coord` (word 186, `coord = c < 7`): the leaf loop and `build_levels`, exactly;
back at word 256 with the coordinate tree in the heap at `FTS` and the secrets at `SEC`. -/
theorem buildFts_tsim {sk : SecretKey} {cache : Bytes 131072} {c idx : Nat} {s : MachineState}
    (hs : FlPre sk cache c idx s) (hpc : s.pc = pcOf 186) :
    TSim image sk s (3 + 1024 * 163 + 9 + 137220) (3 + 1024 * 184 + 9 + 151549) (1024 * 3 + 2047)
      (1024 * 3 + 2047) (buildFts idx c)
      (fun r u => u.pc = pcOf 256 ∧ HeapAt u (ftsLev c idx) 11 r.1 ∧ r.2.length = 2048 ∧ DigsAt u SEC r.2 ∧
        RegsExcept s u ftRegs ∧ Frame s u (FtW c idx)) := by
  have hc := hs.hc
  have hidx := hs.hidx
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk186_spec s hpc c (by omega) hs.x8
  rw [if_pos hc] at t1pc
  obtain ⟨t2, st2, t2pc, t2x18, t2r, t2f⟩ := blk188_spec t1 t1pc
  have r02 : RegsExcept s t2 [.x6, .x18] := (t1r.trans t2r).mono (by simp)
  have f02 : Frame s t2 (fun _ => False) := (t1f.trans t2f).mono (fun _ _ h => by simp_all)
  have hp2 : FlPre sk cache c idx t2 :=
    ⟨hs.base.frame f02 r02 (by simp) (fun _ _ _ h => h), by rw [r02.get (by simp), hs.x2],
      by rw [r02.get (by simp), hs.x8], by rw [r02.get (by simp), hs.x9], hc, hidx⟩
  rw [buildFts_eq]
  refine (TSim.steps (st1.trans st2) (TSim.bind (k₂ := 9 + 137220) (c₂ := 9 + 151549) (n₂ := 2047) (b₂ := 2047)
    (fl_loop hp2 t2pc t2x18) (fun st t ht => ?_))).of_eq rfl (by norm_num) (by norm_num) rfl rfl
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := blk189_spec t ht.pc 2048 (by norm_num) ht.x18
  rw [if_neg (by norm_num)] at t3pc
  obtain ⟨t4, st4, t4pc, t4x1, t4x15, t4x21, t4r, t4f⟩ := blk250_spec t3 t3pc c (by omega)
    (by rw [t3r.get (by simp), ht.regs.get (by simp [flRegs]), hp2.x8])
  have r24 : RegsExcept t2 t4 (flRegs ++ [.x6] ++ [.x1, .x15, .x21, .x30]) := (ht.regs.trans t3r).trans t4r
  have f34 : Frame t t4 (fun _ => False) := (t3f.trans t4f).mono (fun _ _ h => by simp_all)
  have f24 : Frame t2 t4 FlW := (ht.frame.trans f34).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have hz : ∀ A, A < 2 ^ 64 → NeverW A → t4.getMem (BitVec.ofNat 64 A) = 0 := fun A hA hn =>
    (f24.get hA (by unfold NeverW at hn; unfold FlW; sgo)).trans (hp2.base.zero A hA hn)
  have hlp : LevPre t4 (ftsLev c idx) st.1 :=
    { x1 := t4x1
      x2 := by rw [r24.get (by decide), hp2.x2]; rfl
      x5 := by rw [r24.get (by decide), hp2.base.x5]
      x9 := by rw [r24.get (by decide), hp2.x9]; rfl
      x15 := t4x15
      x21 := by
        rw [t4x21]; show _ = BitVec.ofNat 64 (hdr0 10 c idx 0)
        rw [hdr0_eq 10 c idx 0 (by norm_num) (by omega) (by omega) (by norm_num)]; congr 1 <;> omega
      tag3 := Or.inr rfl
      htree := show idx < 2 ^ 32 by omega
      hh1 := show 1 ≤ 11 by norm_num
      hh := show 11 ≤ 12 by norm_num
      ha8 := show FTS % 8 = 0 by decide
      ha := show FTS + 16 * 2 ^ (11 + 1) ≤ 2 ^ 24 by decide
      has := Or.inl (show NOUT + 32 ≤ FTS by decide)
      z32 := hz _ (by decide) (by unfold NeverW; simp)
      z40 := hz _ (by decide) (by unfold NeverW; simp)
      hlen := by rw [ht.len1]; rfl
      hleaves := ht.leaves.frame f34 (by rw [ht.len1]; decide) (fun _ _ _ h => h) }
  have hlev := Keygen.buildLevels_tsim subAt_sign sk hlp (by rw [t4pc])
  rw [(ftsLev_costs c idx).1, (ftsLev_costs c idx).2.1, (ftsLev_costs c idx).2.2] at hlev
  refine (TSim.steps (st3.trans st4) (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) hlev
    (fun levels u hu => TSim.pure ⟨hu.1, hu.2.1, by rw [ht.len2], ?_, ?_, ?_⟩))).of_eq rfl (by norm_num)
    (by norm_num) rfl rfl
  · refine ht.secrets.frame (f34.trans hu.2.2.2) (by rw [ht.len2]; decide) (fun X h1 h2 h => ?_)
    rw [ht.len2] at h2
    rcases h with h | h
    · exact h
    · unfold LevW ftsLev at h; simp only at h; sgo
  · exact (r02.trans (r24.trans hu.2.2.1)).mono (by decide)
  · refine (f02.trans (f24.trans hu.2.2.2)).mono (fun X _ h => ?_)
    unfold FtW
    rcases h with h | h | h
    · exact h.elim
    · exact Or.inl h
    · exact Or.inr h

end SigGolfCandidate.T3M.Sign
