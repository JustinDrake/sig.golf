import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.ChainLeaf

/-! # V1 layers: the leaf-pk block (`xlpk*`) and `LeafOut` (the state at the Merkle dispatch)

At the chain code's return pc `trPc lay c + retOff lay` the leaf-pk block writes the leaf header word
`T(2) = s11 + 0x100` and the route word `tp` at `base + 16`, `base + 24` (`base = 0x300` lower, `0x200` top; the
top also zeroes `0x570`, `0x578`, the padding of its 944-byte input), sets `tp = s11 + 0x200` (word 0 of the node
headers of the Merkle levels), `a0 = base`, `a1 = 704` / `960` (the leaf-pk HASH arguments), `a5` = the window of
`stab_lay_0`, and jumps (`jalr`) to the table word of the leaf's chunk-0 bits. The leaf-pk HASH itself is the first
`ecall` of the Merkle shape block (V3); `LeafOut.hashInput` states its input.

`leafCheck` is `copyCheck`'s leaf-pk part with every register the block does not write kept (`keepLfAll`), checked
for every copy by the kernel (`leafCheck_at`).

**`LeafOut w pk index lay ends u`** (V3's input): `u` is at the `stab_lay_0` word of the leaf's chunk-0 bits; V2's
`Glob (lfK lay)` (the next transition's constants `s11 = T(1, lay)`, `s8`, `sp`, `s4`, `s5`, `t3`, the step registers
`1 .. 7`, `tp = T(3, lay)`, `a0`, `a1`, `a5`, `s6`); `s7 = 2^h + leaf`, `t5 = tree`; the chain ends in the leaf-pk
slots, the leaf header words (and the top's zero words); the witness of the layers below and of this layer's Merkle
blocks original. `leafL_step` (from the lower chain phase's `ChainOut 43`) and `leafT_step` (from the top's `TopOut`)
reach it in 11 resp. 13 steps (= cycles). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The leaf-pk block with all untouched registers kept -/

/-- The registers the leaf-pk block neither writes nor knows at its start. -/
def keepLfAll : List Reg := [.x1, .x2, .x6, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x19, .x20, .x21, .x22, .x23,
  .x24, .x25, .x26, .x28, .x29, .x30, .x31]

/-- `copyCheck`'s leaf-pk part, keeping `keepLfAll`. -/
def leafCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLfAll

/-- The leaf-pk blocks of the copies `lo .. lo + n - 1` of layer `lay`. -/
def leafChecks (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => leafCheck lay (trPc lay c)

set_option maxRecDepth 100000 in
theorem leafChecks_3 : leafChecks 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_2 : leafChecks 2 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_1 : leafChecks 1 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_0 : leafChecks 0 0 128 = true := by decide +kernel

theorem leafCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : leafCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ n, leafChecks lay 0 n = true → c < n → leafCheck lay (trPc lay c) = true :=
    fun n h h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  interval_cases lay
  · exact hall 128 leafChecks_0 (by omega)
  · exact hall 64 leafChecks_1 (by omega)
  · exact hall 64 leafChecks_2 (by omega)
  · exact hall 1 leafChecks_3 (by omega)

/-! ## `LeafOut` -/

/-- The leaf-pk input block: `0x200` (top, 58 ends, 960 bytes) or `0x300` (lower, 43 ends, 704 bytes). -/
def lfBase (lay : Nat) : Nat := if lay = 0 then 512 else 768
def lfBytes (lay : Nat) : Nat := if lay = 0 then 896 else 704
/-- Its 64-byte blocks. -/
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 14 else 11
/-- The leaf-pk slot of chain `j`. -/
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else slotL j
/-- The leaf bits of the first `stab` dispatch (the Merkle levels' chunk 0: 7 on layer 1, else 6). -/
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
/-- Steps (= cycles) of the leaf-pk block. -/
def lfSteps (lay : Nat) : Nat := if lay = 0 then 13 else 11

/-- The registers the block keeps that the Merkle code and the next transition read: `sp`, `t3`, the step
registers `1 .. 7`, `s6`; below the top also the 3-bit masks `s4`, `s5` and `s8 = 0x10000`. -/
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x2, 0x3fe00), (.x28, BitVec.ofNat 64 (2 ^ 40)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x31, 7), (.x22, BitVec.ofNat 64 (s6v lay))] ++
  (if lay = 0 then [] else [(.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x24, 0x10000)])

/-- The known registers at the Merkle dispatch: `postLf` (`t0`, `s2`, `s11 = T(1)`, `gp = T(2)`, `tp = T(3)`, `a0`,
`a1`, `a5`) and `lfKeepK`. -/
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay

/-- **The state at the Merkle dispatch** (V3's input): the `stab_lay_0` word of the leaf's chunk-0 bits, the
registers `lfK`, `s7 = 2^h + leaf`, `t5 = tree`, the `chainCount lay` ends in the leaf-pk slots, the leaf header
words `T(2, lay, tree, 0, leaf)` at `base + 16`, `base + 24` (and on the top the zero words at `0x570`, `0x578`), and
the witness offsets `[11288, layerBase lay + 64 h)` (the layers below and this layer's Merkle blocks) original. -/
structure LeafOut (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf (stabIdx lay.val + (route index lay).1 % 2 ^ stabBits lay.val)
  glob : Glob (lfK lay.val) w pk u
  s7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1)
  t5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) = BitVec.ofNat 64 (hdr0 2 lay.val (route index lay).2 0)
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) =
    BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1)
  zero : lay = 0 → u.getMem (BitVec.ofNat 64 0x570) = 0 ∧ u.getMem (BitVec.ofNat 64 0x578) = 0
  orig : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) u

/-- **The leaf-pk HASH input at `LeafOut`** (`a0`, `a1` and the block as left by the leaf-pk block): Core's
`leafHash` input, `lfBlocks lay` blocks. -/
theorem LeafOut.hashInput {w : WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    have r := topLeaf_hashInput u _ _ ends hn h10 h11 hS hT0 hT1 (h.zero rfl).1 (h.zero rfl).2
    exact ⟨r.1, r.2⟩
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    exact lowLeaf_hashInput u lay _ _ ends hn h10 h11 hS hT0 hT1

/-! ## Helpers -/

/-- V2's `Glob` through a frame that avoids the protected low words (`< 0x140`) and the witness header. -/
theorem glob_frame {gk gk' : List (Reg × Word)} {w : WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 0x140 ≤ A ∧ (A < 0x800 ∨ 0x840 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 0x140 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 0x140 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    rw [hf.get (by omega) (hn _ ha')]; exact hZ a ha
  · unfold PHalf CTRW at *; rw [hf.get (by norm_num) (hn _ (by norm_num))]; exact hh
  · exact hD.congr (fun A hA hB => hf.get (by omega) (fun hw => by
      have := hW A hw
      unfold Verify.Nonbinary.PAIR_DATA at hA
      omega))

theorem land4 (n k : Nat) : n &&& (4 * (2 ^ k - 1)) = 4 * (n / 4 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h2 : 2 ≤ j
  · simp only [h2, decide_true, Bool.true_and, show j - 2 + 2 = j by omega]
    by_cases hj : j - 2 < k
    · simp [hj]
    · simp [hj]
  · simp [h2]

theorem stabMask_eq (lay : Nat) : stabMask lay = 4 * (2 ^ stabBits lay - 1) := by
  unfold stabMask stabBits; split <;> rfl

/-- The dispatch target: the `stab_lay_0` word of the low `stabBits` bits of the leaf (`s7 = 2^h + leaf`). -/
theorem tgtLf_eval (lay : Nat) (t : MachineState) (h leaf : Nat) (hn : stabBits lay ≤ h) (hh : h ≤ 12)
    (hl : leaf < 2 ^ h) (hs : stabIdx lay < 2 ^ 32)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ h + leaf)) :
    (tgtLf lay).eval t = pcOf (stabIdx lay + leaf % 2 ^ stabBits lay) := by
  have hpow : 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
  have hb : stabBits lay ≤ 7 := by unfold stabBits; split <;> omega
  have hpb : 2 ^ stabBits lay ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hb
  have hX : 2 ^ h + leaf < 2 ^ 13 := by omega
  have hmod : (2 ^ h + leaf) % 2 ^ stabBits lay = leaf % 2 ^ stabBits lay := by
    rw [show 2 ^ h = 2 ^ stabBits lay * 2 ^ (h - stabBits lay) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_add_mod]
  have hm : ((t.getReg .x23) <<< ((BitVec.ofNat 64 2).toNat % 64) &&& BitVec.ofNat 64 (stabMask lay)) =
      BitVec.ofNat 64 (4 * (leaf % 2 ^ stabBits lay)) := by
    apply BitVec.eq_of_toNat_eq
    have hmk : stabMask lay < 2 ^ 64 := by unfold stabMask; split <;> norm_num
    rw [toNat_andc _ _ hmk, toNat_sll _ 2 (by norm_num), stabMask_eq, land4, h23, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ h + leaf < 2 ^ 64 by omega),
      show (2 ^ h + leaf) * 2 ^ 2 % 2 ^ 64 / 4 = 2 ^ h + leaf by omega, hmod, BitVec.toNat_ofNat]
    have := Nat.mod_lt leaf (show 0 < 2 ^ stabBits lay by positivity)
    omega
  simp only [tgtLf, E.eval, BinOp.eval, kw]
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  congr 1
  omega

theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide

theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp

theorem hw2_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 2 lay.val = hdr0 2 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring

/-- The lower layers' geometry: `s6 - 1024` is the machine address of the chain blocks, right above the Merkle
blocks. -/
theorem geomL (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = 2048 + layerBase lay + 64 * height lay + 1024 ∧ layerBase lay + 64 * height lay ≤ layerEnd lay.val ∧
      11288 ≤ layerBase lay ∧ layerEnd lay.val < 25241 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

theorem geomT : s6v 0 = 15064 ∧ layerBase 0 = 11288 ∧ height 0 = 12 ∧ layerEnd 0 = 15768 := by
  decide

/-! ## The leaf-pk block -/

/-- **The lower leaf-pk block**: from the lower chain phase's `ChainOut 43` (base `s0` = `encB_step`'s state) to
`LeafOut` in 11 steps. -/
theorem leafL_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2)
    (hG : Glob (layK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (h30 : s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a (trPc lay.val c)).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 11 11 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a (trPc lay.val c) with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ layK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [layK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [layK, baseK])
    · rw [hR .x27 (by simp [chainRegs])]; exact hkL (_, _) (by simp [layK])
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at lay.val c lay.isLt hc) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 11 by simp [specLf, h0], show (specLf lay.val).cycles = 11 by simp [specLf, h0]]
    at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay.val))] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 792 → A ≠ 784 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp <;> omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hlay, ?_⟩
  · -- the dispatch
    rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    have := hL_le lay
    exact tgtLf_eval lay.val t (hL lay.val) _ (stabBits_le lay) (by omega) hlf (stabIdx_lt _)
      (by rw [hR .x23 (by simp [chainRegs]), h23])
  · -- the registers and the protected memory
    have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        unfold LCtx.Wr LCtx.blk at hA; rw [hS6] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals rw [hkeep _ (by simp [keepLfAll]), hR _ (by simp [chainRegs])]
      all_goals first
        | exact h22
        | exact hkL (_, _) (by simp [layK])
  · rw [hkeep .x23 (by simp [keepLfAll]), hR .x23 (by simp [chainRegs]), h23]
  · rw [hkeep .x30 (by simp [keepLfAll]), hR .x30 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    rw [hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = 784 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    rw [hw2_hdr0 lay _ htr]
  · rw [show lfBase lay.val + 24 = 792 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    rw [hR .x4 (by simp [chainRegs]), hk (.x4, BitVec.ofNat 64 L.w1) (by simp [LCtx.known])]
    rfl
  · -- the witness below the chain blocks
    have hOt : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr at hw; rw [hS6] at hw
          unfold WIT at hw
          rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp⟩)

/-- Exact chain-end interface before the shared top leaf aggregation block. -/
structure TopLeafReady (w : WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc 0 c + 69)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : t.getReg .x30 = BitVec.ofNat 64 (route index 0).2
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase 0 + 64 * height 0) t

/-- The exact 13-instruction top leaf block, independent of the chain decoder representation. -/
theorem leafT_step (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 13 13 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at 0 c (by norm_num) hc) t ht.pc ht.glob.1
    (by intro b hb; simp [specLf] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf 0).steps = 13 by simp [specLf], show (specLf 0).cycles = 13 by simp [specLf]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0),
      (⟨none, BitVec.ofNat 64 536⟩, .reg .x4), (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))] A := by
    intro A; rw [hu.mem]; simp [specLf]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 1400 → A ≠ 1392 → A ≠ 536 → A ≠ 528 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
  have htr := tree_lt index 0 hidx
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLf])]
    exact tgtLf_eval 0 t (hL 0) _ (stabBits_le 0) (by decide) hlf (stabIdx_lt _) ht.s7
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll := by
        change p ∈ lfKeepK 0 at hp
        simp [lfKeepK] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepLfAll]
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
    rfl
  · rw [hkeep .x30 (by simp [keepLfAll]), ht.t5]
  · intro j hj
    have hj' : j < 54 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : slotT j = 512 ∨ (544 ≤ slotT j ∧ slotT j ≤ 1376) := by unfold slotT; split <;> omega
    exact ⟨(hfr (slotT j) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 528 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    exact hw2_hdr0 0 _ htr |>.symm ▸ rfl
  · rw [show lfBase (0 : Layer).val + 24 = 536 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    exact ht.tp
  · rw [show (0x570 : Nat) = 1392 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · rw [show (0x578 : Nat) = 1400 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by simp⟩)

end SigGolfCandidate.T3M
