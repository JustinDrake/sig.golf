import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Search.CounterSearch
import SigGolfCandidate.T3M.Expand.LayersBlocks

/-!
# `expand`: the layer driver refines Core's `expandLayers` (stream E)

`layers_tbsim` : from the entry of layer `n - 1` (`entryOf n`: `layer_3` .. `layer_0`, or `compare` for `n = 0`) with
the current root at `ENC` (`LInv`), the machine refines `expandLayers sig index n value` within `lcost n` cycles:
per layer the entry block, `counter_search` at base 354 (`counterSearch_tbsim`), the counter into the witness
header, `recover_layer` (`recoverLayer_tbsim`); on success it reaches `compare` with the root at `ENC`, every layer's
counter in its header half, chain values and path siblings in the witness.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature route height chainCount target width maxDigit counterSearch counterLimit
  recoverLayer expandLayers decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsArgs CsPre CsPost CsW csRegs csT csOk
  counterSearch_tbsim KernAt kernAt_expand topDigits lowDigits decode_top decode_low)

set_option autoImplicit false

/-! ## Digit bounds -/

theorem decode_digit_le {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i := fun i hi => T3.decode_digit_max h i hi

/-! ## The driver's invariant -/

/-- Entry word of the driver with `n` layers left (`n = 0`: `compare`). -/
def entryOf : Nat → Nat
  | 0 => 342
  | n + 1 => lE (Fin.ofNat 4 n)

theorem lR2_eq (n : Nat) (hn : n < 4) : lR2 (Fin.ofNat 4 n) = entryOf n := by
  interval_cases n <;> rfl

theorem lE_eq (n : Nat) : lE (Fin.ofNat 4 n) = entryOf (n + 1) := rfl

/-- The layer pieces of the signature in memory (`lP lay`: values, then the path). -/
def SigLayersAt (s : MachineState) (sig : Signature) : Prop :=
  ∀ lay : Layer, (∀ i (h : i < chainCount lay), DigAt s (lP lay + 16 * i) ((sig.layers lay).values ⟨i, h⟩)) ∧
    (∀ j (h : j < height lay), DigAt s (lP lay + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩))

/-- The scratch words the layer phase reads as zero. -/
structure LZero (s : MachineState) : Prop where
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  c32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  c40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  l944 : s.getMem (BitVec.ofNat 64 (LEAFPK + 880)) = 0
  l952 : s.getMem (BitVec.ofNat 64 (LEAFPK + 888)) = 0
  e40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0

/-- The driver's invariant at the entry of layer `n - 1` (`compare` for `n = 0`), the current root at `ENC`. -/
structure LInv (sig : Signature) (index n : Nat) (value : T3.LayerMessage) (s : MachineState) : Prop where
  pc : s.pc = pcOf (entryOf n)
  hn : n ≤ 4
  x5 : s.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt s (if n = 0 then NOUT else ENC) value.1
  encR : n ≠ 0 → DigAt s (ENC + 48) value.2.2
  pad : value.2.1 = 0
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  sigl : SigLayersAt s sig
  z : LZero s
  table : Search.TableOK s

/-- Half `k` (low 0 / high 1) of a doubleword holds `v`. -/
def HalfAt (t : MachineState) (D k : Nat) (v : BitVec 32) : Prop :=
  (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = v

/-- The header halves of the layers `≥ n` (and every other doubleword half) are unchanged. -/
def HalfFrame (s t : MachineState) (n : Nat) : Prop :=
  ∀ D k, (D = 0x810 ∨ D = 0x818 ∨ D = 0x820) → k < 2 → (∀ lay : Layer, lay.val < n → ¬ (lD lay = D ∧ lk lay = k)) →
    (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = (s.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32

/-- The registers the layer phase changes. -/
def lRegs : List Reg :=
  [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
    .x25, .x26, .x27, .x28, .x29, .x30]

/-- The doublewords the layers `< n` change. -/
def LW (index n : Nat) (A : Nat) : Prop :=
  CsW A ∨ RlScratch A ∨ ∃ lay : Layer, lay.val < n ∧ (A = lD lay ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A)

/-- The layer facts of the witness after layer `lay` with counter `c`. -/
def LayerOut (t : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (c : BitVec 32) : Prop :=
  HalfAt t (lD lay) (lk lay) c ∧ (∀ i < chainCount lay, DigAt t (lWC lay - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (lWM lay - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j))

/-- Exit of the layer phase: `fail` (`HALT(1)`), or `compare` with the root at `ENC` and the layers' witness. -/
def LPost (s : MachineState) (sig : Signature) (index n : Nat) :
    Option (Digest × List (BitVec 32)) → MachineState → Prop
  | none, t => Search.FailedAt 354 t
  | some (root, counters), t => t.pc = pcOf 342 ∧ t.getReg .x5 = 0 ∧ DigAt t NOUT root ∧ counters.length = n ∧
      (∀ lay : Layer, lay.val < n → LayerOut t sig index lay (counters.getD lay.val 0)) ∧
      HalfFrame s t n ∧ RegsExcept s t lRegs ∧ Frame s t (LW index n)

/-- Cycles of one layer. -/
def layCost (lay : Layer) : Nat := lK lay + (10 + 2 ^ 22 * csT lay + csOk lay) + 10 + rlCost lay

/-- Cycles of the layers `< n`. -/
def lcost : Nat → Nat
  | 0 => 0
  | n + 1 => layCost (Fin.ofNat 4 n) + lcost n

theorem expandLayers_succ (sig : Signature) (index n : Nat) (value : T3.LayerMessage) :
    expandLayers sig index (n + 1) value =
      counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0
          counterLimit >>= fun r => match r with
        | some (counter, digits) => pairRoot sig index (Fin.ofNat 4 n) digits >>= fun pr =>
            expandLayers sig index n (if n = 0 then (pr.2, 0, 0) else pr.1) >>= fun r' => match r' with
              | some (root, counters) => pure (some (root, counters ++ [counter]))
              | none => pure none
        | none => pure none := by
  conv_lhs => unfold expandLayers
  simp only []
  congr 1
  funext r
  rcases r with _ | ⟨c, d⟩
  · rfl
  · simp only [T3.expandNext, pairRoot, bind_assoc, pure_bind]
    try (congr 1; funext pair; congr 1; funext root; congr 1; funext r'; rcases r' with _ | ⟨a, b⟩ <;> rfl)

theorem ltable (lay : Layer) :
    0x7000 ≤ lP lay ∧ lP lay + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616 ∧ lP lay % 8 = 0 ∧
    lWC lay % 8 = 0 ∧ lWM lay % 8 = 0 ∧ 0x800 + 64 * (height lay - 1) ≤ lWM lay ∧
    lWM lay + 64 + 64 * (chainCount lay - 1) ≤ lWC lay ∧ lWC lay + 64 ≤ 0x7000 ∧ lD lay + 8 ≤ 0x828 ∧
    0x810 ≤ lD lay ∧ lk lay < 2 := by
  fin_cases lay <;> decide

theorem fin_ofNat_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.ofNat, Nat.mod_eq_of_lt hn]

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

theorem rlWit_range {lay : Layer} {leaf A : Nat} (h : RlWit lay leaf (lWC lay) (lWM lay) A) :
    lWM lay - 64 * (height lay - 1) ≤ A ∧ A + 8 ≤ lWC lay + 64 := by
  have htab := ltable lay
  rcases h with ⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩ <;>
    first | omega | (have := sideOff_le leaf j; omega)

theorem ltable_disj (lay lay' : Layer) (h : lay ≠ lay') :
    lWC lay + 64 ≤ lWM lay' - 64 * (height lay' - 1) ∨ lWC lay' + 64 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> fin_cases lay' <;> simp_all <;> decide

theorem lhalf_inj (lay lay' : Layer) (h1 : lD lay = lD lay') (h2 : lk lay = lk lay') : lay = lay' := by
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lk]

theorem ltable_lo (lay : Layer) : 0x3418 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> decide

section step
variable {sk : BitVec 256}

/-- **One layer of the driver** (layer `n`, then the layers below). -/
theorem layer_step {sig : Signature} {index n : Nat} {value : T3.LayerMessage} {s : MachineState} (hn : n < 4)
    (hI : LInv sig index (n + 1) value s)
    (ih : ∀ v' s', LInv sig index n v' s' →
      TBSim image sk s' (lcost n) (expandLayers sig index n v') (LPost s' sig index n)) :
    TBSim image sk s (lcost (n + 1)) (expandLayers sig index (n + 1) value) (LPost s sig index (n + 1)) := by
  set lay : Layer := Fin.ofNat 4 n with hlay
  have hlv : lay.val = n := fin_ofNat_val n hn
  have htab := ltable lay
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hI.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨t1, s1, p1, x1, x8, x15, x26, x27, x17, x18, x9, r1, f1⟩ :=
    lentry_spec lay s (by rw [hI.pc]; rfl) index hI.hidx hI.idx
  have g1 : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1.get hA (fun h => h)
  obtain ⟨x, hx, hx32⟩ := hI.c32
  have htable1 : Search.TableOK t1 := hI.table.frame f1 (by intro i hi h; exact h)
  have hEnc : DigAt s ENC value.1 := by have h := hI.enc; rwa [if_neg (Nat.succ_ne_zero n)] at h
  have hEncR : DigAt s (ENC + 48) value.2.2 := hI.encR (Nat.succ_ne_zero n)
  have hcs : CsPre 354 ⟨lay, tree, leaf, value, lR1 lay⟩ t1 :=
    ⟨p1, x1, by rw [r1.get (by decide)]; exact hI.x5, x8, x9, x18, x17, x26, x27, htree, hleaf32,
      by rw [g1 _ (by decide)]; exact hEnc.1, by rw [g1 _ (by decide)]; exact hEnc.2,
      ⟨x, hx, by rw [g1 _ (by decide)]; exact hx32⟩, by rw [g1 _ (by decide)]; exact hI.z.e40,
      by rw [g1 _ (by decide)]; exact hEncR.1, by rw [g1 _ (by decide)]; exact hEncR.2, hI.pad, htable1⟩
  rw [expandLayers_succ]
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 10 + rlCost lay + lcost n)
    (counterSearch_tbsim (sk := sk) kernAt_expand hcs) (fun r t2 h2 => ?_))).mono
    (by simp only [lcost, layCost, ← hlay]; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · obtain ⟨p2, h5, h10, _⟩ := h2
    exact (TBSim.pure (Q := LPost s sig index (n + 1)) (a := none) ⟨p2, h5, h10⟩).mono (by omega) (fun _ _ h => h)
  · obtain ⟨p2, hc, x19, e32, ⟨v, hdec⟩, hlen, hdig, r2, f2, _⟩ := h2
    dsimp only at p2 hc x19 e32 hdec hlen hdig
    obtain ⟨t3, s3, p3, x1', hD, x16, x23, x24, r3, f3⟩ := lpost_spec lay t2 p2 c.toNat x19
    have g3 : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] → r ∉ csRegs →
        r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = s.getReg r :=
      fun r h1 h2 h3 => by rw [r3.get h3, r2.get h2, r1.get h1]
    have g3' : ∀ r, r ∉ csRegs → r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = t1.getReg r :=
      fun r h2 h3 => by rw [r3.get h3, r2.get h2]
    -- memory far from the counter-search and header writes
    have m3 : ∀ A, A < 2 ^ 64 → ¬ CsW A → A ≠ lD lay → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 => by rw [f3.get hA h2, f2.get hA h1, g1 A hA]
    have hcsw : ∀ A, (A < 0x20260 ∨ 0x20460 ≤ A) → ¬ CsW A := by
      intro A hA h; unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
    have hrl : RlPre t3 sig index lay ds (lP lay) (lWC lay) (lWM lay) (lR2 lay) := by
      refine ⟨p3, x1', by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI.x5,
        by rw [g3' _ (by decide) (by decide)]; exact x8, by rw [g3' _ (by decide) (by decide)]; exact x9,
        by rw [g3' _ (by decide) (by decide)]; exact x18, by rw [g3' _ (by decide) (by decide)]; exact x15,
        by rw [g3' _ (by decide) (by decide)]; exact x26, by rw [g3' _ (by decide) (by decide)]; exact x27,
        x16, x23, x24, hI.hidx, htab.1, htab.2.1, htab.2.2.1, htab.2.2.2.1, htab.2.2.2.2.1, htab.2.2.2.2.2.1,
        htab.2.2.2.2.2.2.1, htab.2.2.2.2.2.2.2.1, ?_, decode_digit_le hdec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Frame.getByte f3 (by simp only [DIGITS]; omega)
          (by have := htab.2.2.2.2.2.2.2.2.1; simp only [DIGITS]; omega)]
        exact hdig i hi
      · intro i hi
        have hv := (hI.sigl lay).1 i hi
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      · intro j hj
        have hv := (hI.sigl lay).2 j hj
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      all_goals
        first
          | (rw [m3 _ (by decide) (hcsw _ (by simp only [CHAIN, NODE, LEAFPK]; omega))
              (by have := htab.2.2.2.2.2.2.2.2.1; simp only [CHAIN, NODE, LEAFPK]; omega)]
             first | exact hI.z.c0 | exact hI.z.c8 | exact hI.z.c32 | exact hI.z.c40 | exact hI.z.n32 |
               exact hI.z.n40 | exact hI.z.l944 | exact hI.z.l952)
    refine (TBSim.steps s3 (TBSim.bind (W₂ := lcost n) (recoverLayer_tbsim (sk := sk) hrl)
      (fun pr t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
    obtain ⟨p4, n4, e4, e4R, e4p, cv4, pv4, r4, f4⟩ := h4
    -- memory far from the layer's writes
    have hfar4 : ∀ A, A < 2 ^ 64 → ¬ CsW A → A ≠ lD lay → (A < 0x3418 ∨ 0x7000 ≤ A) → ¬ RlScratch A →
        t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      have hw : ¬ (RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) := by
        rintro (h | h)
        · exact h4 h
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f4.get hA hw, m3 A hA h1 h2]
    have hd8 := htab.2.2.2.2.2.2.2.2.1
    have hd0 := htab.2.2.2.2.2.2.2.2.2.1
    have ncs : ∀ A, (A < 0x20260 ∨ (0x20260 + 40 ≤ A ∧ A < EOUT) ∨ 0x20460 ≤ A) → ¬ CsW A := by
      intro A hA h; unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h hA; omega
    have nrl : ∀ A, ((A < CHAIN + 16 ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 48) ∨ CHAIN + 80 ≤ A) ∧
        (A < NODE ∨ (NODE + 32 ≤ A ∧ A < NODE + 48) ∨ NOUT + 32 ≤ A) ∧ (A < LEAFPK ∨ LEAFPK + 880 ≤ A) ∧
        A ≠ ENC ∧ A ≠ ENC + 8 ∧ A ≠ ENC + 48 ∧ A ≠ ENC + 56 ∧ (A % 8 = 0)) → ¬ RlScratch A := by
      intro A hA h; unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h hA; omega
    have hI4 : LInv sig index n (if n = 0 then (pr.2, 0, 0) else pr.1) t4 := by
      have hx5 : t4.getReg .x5 = 0 := by
        rw [r4.get (by decide), g3 _ (by decide) (by decide) (by decide)]; exact hI.x5
      refine ⟨by rw [p4, hlay, lR2_eq n hn], by omega, hx5, hI.hidx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfar4 IDXV (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
        exact hI.idx
      · split_ifs
        · exact n4
        · exact e4
      · intro hn0; rw [if_neg hn0]; exact e4R
      · split_ifs
        · rfl
        · exact e4p
      · refine ⟨c.toNat, by omega, ?_⟩
        have hw : ¬ (RlScratch (ENC + 32) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (ENC + 32)) := by
          rintro (h | h)
          · exact nrl _ (by decide) h
          · have h1 := rlWit_range h; have := ltable_lo lay; have := htab.2.2.2.2.2.2.2.1
            simp only [ENC] at h1; omega
        rw [f4.get (by decide) hw, f3.get (by decide) (by simp only [ENC]; omega), e32]
      · intro lay'
        have htab' := ltable lay'
        have hb := htab'.2.1
        have hb0 := htab'.1
        have hb8 := htab'.2.2.1
        refine ⟨fun i hi => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
        · rw [hfar4 (lP lay' + 16 * i) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).1
        · rw [hfar4 (lP lay' + 16 * i + 8) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).2
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).1
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j + 8) (by omega) (ncs _ (by omega)) (by omega)
            (by omega) (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).2
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfar4 CHAIN (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c0
        · rw [hfar4 (CHAIN + 8) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c8
        · rw [hfar4 (CHAIN + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c32
        · rw [hfar4 (CHAIN + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c40
        · rw [hfar4 (NODE + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n32
        · rw [hfar4 (NODE + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n40
        · rw [hfar4 (LEAFPK + 880) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.l944
        · rw [hfar4 (LEAFPK + 888) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.l952
        · rw [hfar4 (ENC + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.e40
      · apply hI.table.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi h
        rcases h with ((h | h) | h) | h
        · exact h
        · unfold CsW Search.DigW at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
    refine (TBSim.bind (W₂ := 0) (ih _ t4 hI4) (fun r' t5 h5 => ?_)).mono (by omega) (fun _ _ h => h)
    rcases r' with _ | ⟨root', counters⟩
    · exact TBSim.pure h5
    · obtain ⟨p5, x5', e5, hlen5, hout5, hhf5, r5, f5⟩ := h5
      have hk := htab.2.2.2.2.2.2.2.2.2.2
      have hDv : lD lay = 0x810 ∨ lD lay = 0x818 ∨ lD lay = 0x820 := by
        clear_value lay; fin_cases lay <;> simp [lD]
      have hlo := ltable_lo lay
      have hnotLW : ∀ A, lWM lay - 64 * (height lay - 1) ≤ A → A + 8 ≤ lWC lay + 64 → ¬ LW index n A := by
        intro A h1 h2 h
        rcases h with h | h | ⟨lay'', h'', h | h⟩
        · unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
        · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
        · have := (ltable lay'').2.2.2.2.2.2.2.2.1; omega
        · have hne : lay'' ≠ lay := fun he => by rw [he] at h''; omega
          have hr := rlWit_range h
          rcases ltable_disj lay'' lay hne with hd | hd <;> omega
      have hgetD : ∀ lay' : Layer, lay'.val < n → (counters ++ [c]).getD lay'.val 0 = counters.getD lay'.val 0 :=
        fun lay' h => List.getD_append _ _ _ _ (by omega)
      refine TBSim.pure ⟨p5, x5', e5, by simp [hlen5], ?_, ?_, ?_, ?_⟩
      · intro lay' hlay'
        by_cases hlt : lay'.val < n
        · rw [hgetD lay' hlt]; exact hout5 lay' hlt
        · have heq : lay' = lay := Fin.ext (by omega)
          rw [heq, List.getD_append_right _ _ _ _ (by omega), show lay.val - counters.length = 0 by omega]
          simp only [List.getD_cons_zero]
          refine ⟨?_, fun i hi => ?_, fun j hj => ?_⟩
          · unfold HalfAt
            rw [hhf5 (lD lay) (lk lay) hDv hk (fun lay'' h'' ⟨h1, h2⟩ => by
              have := lhalf_inj _ _ h1 h2; rw [this] at h''; omega)]
            have hw : ¬ (RlScratch (lD lay) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (lD lay)) := by
              rintro (h | h)
              · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
              · have := rlWit_range h; omega
            rw [f4.get (by omega) hw, hD, replaceWord32_get _ _ hk]
            apply BitVec.eq_of_toNat_eq
            simp
          · have hv := cv4 i hi
            exact hv.frame f5 (by omega) (hnotLW _ (by omega) (by omega)) (hnotLW _ (by omega) (by omega))
          · have hv := pv4 j hj
            have hs := sideOff_le (route index lay).1 j
            exact hv.frame f5 (by omega) (hnotLW _ (by omega) (by omega)) (hnotLW _ (by omega) (by omega))
      · intro D k hD3 hk' hnot
        have hDw : ¬ (RlScratch D ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) D) := by
          rintro (h | h)
          · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
          · have := rlWit_range h; omega
        rw [hhf5 D k hD3 hk' (fun lay'' h'' => hnot lay'' (by omega)), f4.get (by omega) hDw]
        have hD2 : t2.getMem (BitVec.ofNat 64 D) = s.getMem (BitVec.ofNat 64 D) := by
          rw [f2.get (by omega) (ncs _ (by omega)), g1 D (by omega)]
        by_cases hDl : D = lD lay
        · have hkne : lk lay ≠ k := fun he => hnot lay (by omega) ⟨hDl.symm, he⟩
          rw [hDl, hD, replaceWord32_other _ _ _ hk hk' hkne, ← hDl, hD2]
        · rw [f3.get (by omega) hDl, hD2]
      · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
      · refine ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun A _ h => ?_)
        rcases h with ((((h | h) | h) | h | h) | h)
        · exact h.elim
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨lay, by omega, Or.inl h⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨lay, by omega, Or.inr h⟩)
        · rcases h with h | h | ⟨lay'', h'', h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨lay'', by omega, h⟩)

/-- **The layer driver refines Core's `expandLayers`** (layers `n - 1 .. 0`, then `compare`). -/
theorem layers_tbsim {sig : Signature} {index : Nat} :
    ∀ n (value : T3.LayerMessage) (s : MachineState), LInv sig index n value s →
      TBSim image sk s (lcost n) (expandLayers sig index n value) (LPost s sig index n)
  | 0, value, s, hI => by
    refine TBSim.pure (Q := LPost s sig index 0) (a := some (value.1, []))
      ⟨hI.pc, hI.x5, by have h := hI.enc; rwa [if_pos rfl] at h, rfl,
      fun lay h => absurd h (by omega), fun _ _ _ _ _ => rfl, RegsExcept.refl _ _, Frame.refl _ _⟩
  | n + 1, value, s, hI => layer_step (by have := hI.hn; omega) hI
      (fun v' s' h' => layers_tbsim n v' s' h')

end step

end SigGolfCandidate.T3M.Expand
