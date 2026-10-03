import SigGolfCandidate.T3M.CanonicalPort.CombinedB
import SigGolfCandidate.T3M.CanonicalPort.CombinedC

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart66

/-! # V1 layers: the transition (`LayerIn` → counter, encoding hash, decode → the chain code)

**`LayerIn w pk index lay M s`** (the interface with V2's `FtsOut` for layer 3 and V3's Merkle root for layers 2, 1, 0):
at a transition copy of layer `lay`, V2's `Glob (preK lay) w pk s` (the layer's constant registers, the witness header,
`pk`, the zero words of the encoding block), the remaining index bits `index / 2^below` in `rReg lay` (`s6` for
layer 3, `t5` below), the previous root `M` at `0x100`, and the witness regions of the layers `≤ lay` original (V2's
`Orig` on the offsets `[11288, layerEnd lay)`).

* `encA_step` : from `LayerIn`, either the counter rejection (HALT(1)) or the encoding `ecall` with the input
  `encodingInput lay tree leaf M (wctr w lay)` (`EncPre`);
* `encB_step` (lower layers) : after the answer `a`, either a decode rejection (HALT(1)) when Core's `decode` fails,
  or the chain code's `ChainIn 0` with the context `lctx` built from `a` (digits = Core's). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## Layer facts -/

/-- The index bits below layer `lay` (Core's `route`). -/
def below (lay : Nat) : Nat := [19, 12, 6, 0].getD lay 0
/-- The end (witness offset) of layer `lay`'s region (memory order 0, 1, 2, 3). -/
def layerEnd (lay : Nat) : Nat := [15768, 18968, 22104, 25240].getD lay 0

theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = target lay := by fin_cases lay <;> rfl

/-- The message triple in the encoding block at `B`: `L` at `B`, `R` at `B + 48`, the 12 pad bytes in the high half
of `B + 32` and in `B + 40` (layer 3: `0x100`; below, E8: the last Merkle block of the layer above, in place). -/
structure MsgAt (B : Nat) (M : T3.LayerMessage) (s : MachineState) : Prop where
  lo : DigAt s B M.1
  hi : DigAt s (B + 48) M.2.2
  p32 : (s.getMem (BitVec.ofNat 64 (B + 32))).toNat / 2 ^ 32 = M.2.1.toNat % 2 ^ 32
  p40 : s.getMem (BitVec.ofNat 64 (B + 40)) = BitVec.ofNat 64 (M.2.1.toNat / 2 ^ 32)

theorem encB_facts (lay : Nat) (hlay : lay < 4) :
    encB lay % 8 = 0 ∧ encB lay + 64 < 16777216 ∧ (encB lay = 256 ∨ 0x800 + layerEnd lay ≤ encB lay) := by
  interval_cases lay <;> decide

/-- The encoding output slots (full E8): aligned, safe, past the layer's witness region (below layer 3), and valid
for the decode's two loads. -/
theorem dst_facts (lay : Nat) (hlay : lay < 4) (D : Nat) (hD : D ∈ dstSet lay) :
    safeDest D = true ∧ D % 8 = 0 ∧ D + 32 ≤ 2 ^ 23 ∧ (D = 320 ∨ 0x800 + layerEnd lay ≤ D) ∧ layerEnd lay % 8 = 0 ∧
    accessValid (BitVec.ofNat 64 D) 8 = true ∧ accessValid (BitVec.ofNat 64 (D + 8)) 8 = true := by
  interval_cases lay <;> simp [dstSet] at hD <;>
    first | (subst hD; decide +kernel) | (rcases hD with rfl | rfl <;> decide +kernel)

/-- The state at a transition copy of layer `lay`. -/
structure LayerIn (w : WBytes) (pk : Digest) (index lay : Nat) (M : T3.LayerMessage) (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : ∃ c, c < nCopy lay ∧ s.pc = pcOf (trPc lay c)
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  msg : MsgAt (encB lay) M s
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay) s
  /-- Full E8: below layer 3 the encoding output pointer `a2` is the previous fold's (the node slot). -/
  dst : lay = 3 ∨ ∃ D ∈ dstSet lay, s.getReg .x12 = BitVec.ofNat 64 D

/-! ## Route -/

theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]

theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]

theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide

theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))

/-- The route registers' values (`leafE`, `treeE`, `tpE`, `s7E`). -/
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x30 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · simp only [tpE, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · simp only [s7E, E.eval, BinOp.eval, hlE, kw]
    apply BitVec.eq_of_toNat_eq
    have hp : 2 ^ hL lay.val < 2 ^ 64 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (show 2 ^ hL lay.val + (route index lay).1 < 2 ^ 64 by
        have : 2 * 2 ^ hL lay.val ≤ 2 ^ 13 := by
          rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)
        omega)]
    rw [Nat.lor_comm, show 2 ^ hL lay.val = 2 ^ hL lay.val * 1 by ring, ← Nat.two_pow_add_eq_or_of_lt hl]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The counter -/

theorem ctrE_eval (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) :
    (ctrE lay.val).eval s = BitVec.ofNat 64 (wctr w lay).toNat := by
  have hj : 2 + (lay.val + 1) / 2 < 8 := by have := lay.isLt; omega
  have hw := hH (2 + (lay.val + 1) / 2) hj
  rw [show WIT + 8 * (2 + (lay.val + 1) / 2) = 0x810 + 8 * ((lay.val + 1) / 2) by unfold WIT; ring] at hw
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x810 + 8 * ((lay.val + 1) / 2))))
    (4 * ((lay.val + 1) % 2))).toNat = _
  rw [hw]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wctr, wle32, counterOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have e1 : 4 * ((lay.val + 1) % 2) / 4 * 32 = 32 * ((lay.val + 1) % 2) := by omega
  rw [e1]
  have e2 : w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) % 2 ^ 64 / 2 ^ (32 * ((lay.val + 1) % 2)) % 2 ^ 32 =
      w.toNat / 2 ^ (8 * (20 + 4 * lay.val)) % 2 ^ 32 := by
    have hk : 8 * (20 + 4 * lay.val) = 64 * (2 + (lay.val + 1) / 2) + 32 * ((lay.val + 1) % 2) := by omega
    rw [hk, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    generalize w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) = X
    have : (lay.val + 1) % 2 = 0 ∨ (lay.val + 1) % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num <;> omega
  rw [e2]

theorem ctr_lt (w : WBytes) (lay : Layer) : (wctr w lay).toNat < 2 ^ 32 := (wctr w lay).isLt

theorem ctrBr_iff (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) (d : Bool) :
    Br.holds s (ctrBr lay.val d) ↔ d = decide ((wctr w lay).toNat ≥ counterLimit) := by
  have hd := ctr_lt w lay
  simp only [ctrBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, ctrE_eval w lay s hH, kw]
  have e : (BitVec.ofNat 64 (wctr w lay).toNat >>> ((BitVec.ofNat 64 22).toNat % 64)) =
      BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (wctr w lay).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (wctr w lay).toNat / 2 ^ 22 < 2 ^ 64 by omega)]
  rw [e]
  by_cases h : (wctr w lay).toNat ≥ counterLimit
  · have hne : BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      unfold counterLimit at h
      simp at this; omega
    rw [show (BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) != (BitVec.ofNat 64 0 : Word)) = true from
      bne_iff_ne.mpr hne, decide_eq_true h]
    exact eq_comm
  · have h0 : (wctr w lay).toNat / 2 ^ 22 = 0 := by unfold counterLimit at h; omega
    rw [h0, decide_eq_false h, show (BitVec.ofNat 64 0 != (BitVec.ofNat 64 0 : Word)) = false by decide]
    exact eq_comm

/-! ## The checks of a copy, unpacked -/

theorem copy_parts (lay p : Nat) (h : copyCheck lay p = true) :
    specB (copyAllow lay) [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) (keepA lay) = true ∧
    specB (copyAllow lay) [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] = true ∧
    (lay = 0 →
      specB [] [] [] (runAt [] [96162] (p + stepsA lay + 1) []) (specTopCall p) ansObl [] keepTopCall = true) ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) ansObl
        (postBl lay p) keepB = true ∧
      specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) ansObl [] [] = true ∧
      specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) ansObl [] [] = true) ∧
    specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf = true := by
  unfold copyCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun h0 => ?_, fun h0 => ?_, h4⟩
  · rw [if_pos h0] at h3; exact h3
  · rw [if_neg h0] at h3; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-! ## A: up to the encoding `ecall` -/

/-- Before the encoding `ecall` (copy `c`; the route in `tp`, `s7`, `t5`). -/
structure EncPre (w : WBytes) (pk : Digest) (index lay c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay) w pk t
  tp : ∀ (L : Layer), L.val = lay → t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index L).2 (route index L).1)
  s7 : ∀ (L : Layer), L.val = lay → t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay + (route index L).1)
  t5 : ∀ (L : Layer), L.val = lay → t.getReg .x30 = BitVec.ofNat 64 (route index L).2
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay) t
  dst : ∃ D ∈ dstSet lay, t.getReg .x12 = BitVec.ofNat 64 D

theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring

/-- **A**: the counter rejection, or the encoding `ecall` with Core's `encodingInput`. -/
theorem encA_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : T3.LayerMessage) (s : MachineState)
    (hs : LayerIn w pk index lay.val M s) :
    ((wctr w lay).toNat ≥ counterLimit → ∃ u, Steps image s (rejSt lay.val) (rejSt lay.val) u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wctr w lay).toNat < counterLimit → ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
        fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = toQ (pad64 (encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay))) ∧
        ∃ c, c < nCopy lay.val ∧ EncPre w pk index lay.val c t) := by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := copy_parts lay.val (trPc lay.val c) (copyCheck_at lay.val c lay.isLt hc)
  have hk : KnownOK (preK lay.val) s := hs.glob.1
  have hH : WitHdr w s := hs.glob.2.1
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_run hcc.2.1 s hpc hk (by
      intro b hb; simp only [rejA, List.mem_singleton] at hb; subst hb
      exact (ctrBr_iff w lay s hH true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, kw 1) (by simp [rejA]), hu.regs (.x10, kw 1) (by simp [rejA])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run hcc.1 s hpc hk (by
      intro b hb; simp only [specA, List.mem_singleton] at hb; subst hb
      exact (ctrBr_iff w lay s hH false).mpr (by simp; omega)) (by simp)
    obtain ⟨hlE, htE, htpE, hs7E⟩ := route_evals index lay hs.idx s hs.route
    have hkt : KnownOK (bK lay.val) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (encB lay.val) := hkt (.x10, BitVec.ofNat 64 (encB lay.val)) (by simp [bK, bKB])
    have hB := encB_facts lay.val lay.isLt
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [bK, bKB, layK])
    obtain ⟨D, hD, h12⟩ : ∃ D ∈ dstSet lay.val, t.getReg .x12 = BitVec.ofNat 64 D := by
      by_cases h3 : lay.val = 3
      · exact ⟨320, by simp [dstSet, h3], hkt (.x12, 320) (by simp [bK, h3])⟩
      · obtain ⟨D, hD, h⟩ := hs.dst.resolve_left h3
        exact ⟨D, hD, by rw [ht.keep .x12 (by simp [keepA, h3]), h]⟩
    have hDf := dst_facts lay.val lay.isLt D hD
    have hG : Glob (bK lay.val) w pk t := by
      have := ht.glob _ w pk hs.glob (RelOK.nil s)
      exact ⟨hkt, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
    have hm : ∀ A, t.getMem A = memEval s (specA lay.val (trPc lay.val c)).mem A := ht.mem
    have frame : ∀ A, A < 2 ^ 64 → A ≠ encB lay.val + 32 → A ≠ encB lay.val + 24 → A ≠ encB lay.val + 16 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [specA, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp <;> omega
    have tree_lt' := tree_lt index lay hs.idx
    refine ⟨t, ht.steps, ht.ecall rfl, hkt (.x5, 0) (by simp [bK, bKB, layK, baseK]),
      hashArgs_of t (encB lay.val) 64 D h10 h11 h12 hB.1 (by norm_num) (by norm_num; omega) hDf.2.1 (by omega),
      ?_, c, hc, ⟨?_, hG, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, ?_, ⟨D, hD, h12⟩⟩⟩
    · -- the encoding block at `encB lay` (in place below layer 3)
      apply hashInput_words8 t _ (encB lay.val) (by rw [pad64_encodingInput, encodingInput_length'])
        h10 hB.1 (by omega) h11
      rw [wordsOf_encodingInput]
      have m0 := hs.msg
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [frame (encB lay.val) (by omega) (by omega) (by omega) (by omega)]; exact m0.lo.1
      · rw [frame (encB lay.val + 8) (by omega) (by omega) (by omega) (by omega)]; exact m0.lo.2
      · rw [hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_neg (by omega),
          memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_neg (by omega),
          memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
        simp only [E.eval, kw]
        rw [hw4_hdr0 lay _ tree_lt']
      · rw [hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_neg (by omega),
          memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl, htpE]
      · rw [hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
        simp only [E.eval, BinOp.eval, kw]
        rw [ctrE_eval w lay s hH]
        apply BitVec.eq_of_toNat_eq
        rw [merge_w0_toNat]
        have hph := m0.p32
        have := ctr_lt w lay
        simp only [BitVec.toNat_ofNat] at hph ⊢
        rw [hph]
        have := (M.2.1).isLt
        omega
      · rw [frame (encB lay.val + 40) (by omega) (by omega) (by omega) (by omega)]; exact m0.p40
      · rw [frame (encB lay.val + 48) (by omega) (by omega) (by omega) (by omega)]; exact m0.hi.1
      · rw [frame (encB lay.val + 56) (by omega) (by omega) (by omega) (by omega)]
        have := m0.hi.2
        rwa [show encB lay.val + 48 + 8 = encB lay.val + 56 by omega] at this
    · exact ht.pc rfl
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x4, tpE L.val) (by simp [specA]), htpE]
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x23, s7E L.val) (by simp [specA]), hs7E]
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x30, treeE L.val) (by simp [specA]), htE]
    · exact hs.orig.frame (fun j hj hp => by
        rw [hm]
        apply memEval_frame_ofNat s _ _ (by unfold WIT WX at *; omega)
        intro p hp'
        simp only [specA, List.mem_cons, List.not_mem_nil, or_false] at hp'
        unfold WIT at *
        rcases hB.2.2 with hb | hb <;> rcases hp' with rfl | rfl | rfl <;> simp <;> omega)

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The decode expressions (Word level) -/

theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]

theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]

theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']

/-- The two doublewords of the encoding answer at the output pointer `a2` (full E8). -/
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : u.getMem (u.getReg .x12) = a.extractLsb' 0 64
  hi : u.getMem (u.getReg .x12 + BitVec.ofNat 64 8) = a.extractLsb' 64 64

theorem ansAt_of (t : MachineState) (a : BitVec 256) (D : Nat) (h12 : t.getReg .x12 = BitVec.ofNat 64 D)
    (hD : D + 24 < 2 ^ 64) : AnsAt (writeHash t a) a := by
  constructor
  · rw [writeHash_getReg, h12]; exact writeHash_at0 t a D h12 hD
  · rw [writeHash_getReg, h12, ofNat_add_ofNat]; exact writeHash_at8 t a D h12 hD

/-- The decode loads' side conditions hold at an output slot. -/
theorem ansObl_holds (u : MachineState) (D : Nat) (h12 : u.getReg .x12 = BitVec.ofNat 64 D)
    (h0 : accessValid (BitVec.ofNat 64 D) 8 = true) (h8 : accessValid (BitVec.ofNat 64 (D + 8)) 8 = true) :
    ∀ o ∈ ansObl, o.holds u := by
  intro o ho
  simp only [ansObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · show accessValid (u.getReg .x12 + BitVec.ofNat 64 8) 8 = true
    rw [h12, ofNat_add_ofNat]; exact h8
  · show accessValid (u.getReg .x12 + BitVec.ofNat 64 0) 8 = true
    rw [h12, BitVec.add_zero]; exact h0

/-- The value of the answer's digest (Core's `shortHash`). -/
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat

theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]

theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega

theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega

theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi

/-- `sumE` is the lower decode's SWAR sum of the answer (`Decode.lowSum`) when `v1 < 2^62`. -/
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) :
    (sumE.eval u).toNat = lowSum (ansV a) := by
  have hb : (b1E.eval u).toNat = 2 * (ansV a / 2 ^ 64) := by
    simp only [b1E, E.eval, BinOp.eval, a7E_eval h, kw]
    rw [toNat_sll _ 1 (by norm_num), ← ansV_hi]
    rw [Nat.mod_eq_of_lt (by omega)]; ring
  have hsw : sw1E.eval u = sw1RefE.eval u := by
    have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide
    simp only [sw1E, swLowE, sw1RefE, E.eval, BinOp.eval, kw, M1c, he]
    exact swar7_eq _ _ (by rw [hb]; omega)
  have hs1 : (sw1E.eval u).toNat = sw1 (ansV a % 2 ^ 64) (2 * (ansV a / 2 ^ 64)) := by
    rw [hsw]
    simp only [sw1RefE, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_andc _ _ (by norm_num [M1c]),
      toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]),
      toNat_srl _ 3 (by norm_num), toNat_srl _ 3 (by norm_num)]
    have e1 := a6E_eval h
    simp only [a6E, E.eval] at e1
    simp only [a6E, E.eval]
    rw [e1, ← ansV_lo]
    have e2 : (E.eval u b1E) = BitVec.ofNat 64 (2 * (ansV a / 2 ^ 64)) := by
      apply BitVec.eq_of_toNat_eq; rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * (ansV a / 2 ^ 64) < 2 ^ 64 by omega)]
    unfold sw1; rfl
  unfold lowSum lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1]
  rfl

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## B (lower layers): decode and the chain prologue -/

theorem rngBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (k : Nat) (hk : k < 64) (d : Bool) :
    Br.holds u (rngBr k d) ↔ d = decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
  simp only [rngBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a7E_eval h, kw]
  have e : ((a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) != BitVec.ofNat 64 0) =
      decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
    by_cases h0 : (a.extractLsb' 64 64).toNat / 2 ^ k = 0
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) = BitVec.ofNat 64 0 := by
        apply BitVec.eq_of_toNat_eq; rw [toNat_srl _ _ hk, h0]; rfl
      rw [this, decide_eq_false (by omega)]; rfl
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) ≠ BitVec.ofNat 64 0 := by
        intro he; have := congrArg BitVec.toNat he
        rw [toNat_srl _ _ hk, BitVec.toNat_ofNat, Nat.zero_mod] at this; exact h0 this
      rw [decide_eq_true h0]; exact bne_iff_ne.mpr this
  rw [e]; exact eq_comm

theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) (lay : Layer)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
  have hS := lowSum_lt (ansV a)
  have hT : tgtL lay.val ≤ 195 := by fin_cases lay <;> decide
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hr, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔
      (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by omega
  have key : (BinOp.sltu.eval ((t4E lay.val).eval u) (BitVec.ofNat 64 8) == BitVec.ofNat 64 0) =
      decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
    simp only [BinOp.eval, BitVec.ult, ht4, BitVec.toNat_ofNat]
    by_cases hc : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8
    · have h1 : decide ((lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 % 2 ^ 64) = true := by
        rw [decide_eq_true_eq, show (8 : Nat) % 2 ^ 64 = 8 by norm_num]; exact hiff.mpr hc
      rw [h1, decide_eq_false (fun h => h hc)]; decide
    · have h1 : decide ((lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 % 2 ^ 64) = false := by
        rw [decide_eq_false_iff_not, show (8 : Nat) % 2 ^ 64 = 8 by norm_num]; exact fun h' => hc (hiff.mp h')
      rw [h1, decide_eq_true hc]; decide
  simp only [ckBr, Br.holds, CmpOp.eval]
  show (BinOp.sltu.eval ((t4E lay.val).eval u) (BitVec.ofNat 64 8) == BitVec.ofNat 64 0) = d ↔ _
  rw [key]; exact eq_comm

/-- The checksum digit of the lower decode. -/
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64

/-- `a7` of the lower chain code: `(v1 << 1) | v0 >> 63`. -/
def a7lW (a : BitVec 256) : Word := ((a.extractLsb' 64 64) <<< 1) ||| ((a.extractLsb' 0 64) >>> 63)

/-- The chain context of the lower layer `lay` from the answer `a` (transition copy at `p`). -/
def lctxOf (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a7lW a, ckOf lay a,
    p + retOff lay.val⟩

theorem a7lW_toNat (a : BitVec 256) (hr : ansV a / 2 ^ 64 < 2 ^ 62) : (a7lW a).toNat = ansV a / 2 ^ 63 := by
  have hv := ansV_split a
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 : (a.extractLsb' 64 64).toNat < 2 ^ 62 := by rw [← ansV_hi]; exact hr
  unfold a7lW
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show (a.extractLsb' 64 64).toNat * 2 ^ 1 < 2 ^ 64 by omega)]
  have hc : (a.extractLsb' 0 64).toNat / 2 ^ 63 < 2 ^ 1 := by omega
  rw [show (a.extractLsb' 64 64).toNat * 2 ^ 1 = 2 ^ 1 * (a.extractLsb' 64 64).toNat by ring,
    ← Nat.two_pow_add_eq_or_of_lt hc, hv]
  omega

/-- The machine's digits of the lower chain code are Core's decoded digits. -/
theorem lctx_digits (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    ∀ i < 43, (lctxOf w index lay a p).dig i = ds.getD i 0 := by
  rw [decode_lower lay hlay] at hds
  have hr : ansV a / 2 ^ 64 / 2 ^ 62 = 0 := by
    by_contra hne; rw [if_pos hne] at hds; cases hds
  rw [if_neg (by simpa using hr)] at hds
  split at hds
  · rename_i hck
    simp only [Option.some.injEq] at hds
    subst hds
    intro i hi
    unfold LCtx.dig lctxOf
    simp only []
    by_cases h21 : i < 21
    · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      show (a.extractLsb' 0 64).toNat / 8 ^ i % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
      rw [← ansV_lo, show (8 : Nat) ^ i = 2 ^ (3 * i) by rw [Nat.pow_mul]]
      have hV : ansV a = ansV a % 2 ^ 64 + 2 ^ 64 * (ansV a / 2 ^ 64) := (Nat.mod_add_div _ _).symm
      conv_rhs => rw [hV]
      exact (div_mod_add_pow (ansV a % 2 ^ 64) (ansV a / 2 ^ 64) (3 * i) 64 3 (by omega)).symm
    · by_cases h42 : i < 42
      · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some]
        show (a7lW a).toNat / 8 ^ (i - 21) % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
        rw [a7lW_toNat a (by omega), Nat.div_div_eq_div_mul, show (2 : Nat) ^ 63 * 8 ^ (i - 21) = 2 ^ (3 * i) by
          rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega]
        rfl
      · have hi42 : i = 42 := by omega
        subst hi42
        rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
        rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
        show ckOf lay a = _
        unfold ckOf
        rw [tgtL_eq]
  · cases hds

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 40000)) = true := by decide

theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2

theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2

theorem trPc_lt (lay c : Nat) : trPc lay c < 40000 :=
  getD_getD_lt xtrTab lay c 40000 (by norm_num) xtrTab_bound

/-- Witness words (V2's `Orig`) as the chain code's `OrigW`. -/
theorem origW_of {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w P s) (A : Nat)
    (hA : WIT ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - 0x800) by unfold WIT at *; omega]

/-- **B (lower layers)**: after the encoding answer `a`, a decode rejection (HALT(1)) or the chain code's `ChainIn 0`
for `lctxOf`. -/
theorem encB_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t) (a : BitVec 256) :
    (decode lay (a.extractLsb' 0 128) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (a.extractLsb' 0 128) ≠ none → ∃ s0, Steps image (writeHash t a) 29 32 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ok ∧
        (∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a (trPc lay.val c)).Orig0 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ChainIn s0 0 [] s0 ∧ Glob (lowerLayK lay.val) w pk s0 ∧
        SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) ∧
        s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2) := by
  set u := writeHash t a with hu
  have hcc := copy_parts lay.val (trPc lay.val c) (copyCheck_at lay.val c lay.isLt hc)
  have hB := (hcc.2.2.2.1 (fun h => hlay (Fin.ext h)))
  have hkt : KnownOK (bK lay.val) t := ht.glob.1
  obtain ⟨D, hD, h12⟩ := ht.dst
  have hDf := dst_facts lay.val lay.isLt D hD
  have hku : KnownOK (bKB lay.val) u := fun p hp => by
    rw [hu, writeHash_getReg]; exact hkt p (List.mem_append_left _ hp)
  have hob : ∀ o ∈ ansObl, o.holds u :=
    ansObl_holds u D (by rw [hu, writeHash_getReg]; exact h12) hDf.2.2.2.2.2.1 hDf.2.2.2.2.2.2
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := ansAt_of t a D h12 (by omega)
  have hdec := decode_lower lay hlay (a.extractLsb' 0 128)
  have hS := lowSum_lt (ansV a)
  constructor
  · intro hnone
    by_cases hr : (a.extractLsb' 64 64).toNat / 2 ^ 62 ≠ 0
    · obtain ⟨v, hv⟩ := spec_run hB.2.2 u hpcu hku (by
        intro b hb; simp only [rejRng, List.mem_singleton] at hb; subst hb
        exact (rngBr_iff hans 62 (by norm_num) true).mpr (by rw [decide_eq_true hr])) hob
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejRng]),
        hv.regs (.x10, kw 1) (by simp [rejRng]), by norm_num, by norm_num⟩
    · have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
      have hck : ¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
        intro hck
        rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr)] at hnone
        rw [if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := spec_run hB.2.1 u hpcu hku (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hr' lay true).mpr (by rw [decide_eq_true hck])
        · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false hr])) hob
      exact ⟨v, 22, 25, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by norm_num, by norm_num⟩
  · intro hsome
    have hr0 : (a.extractLsb' 64 64).toNat / 2 ^ 62 = 0 := by
      by_contra hne
      apply hsome; rw [hdec, if_pos (by rw [ansV_hi]; exact hne)]
    have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
    have hck : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr0), if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hku (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hr' lay false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false (fun h => h hr0)])) hob
    set L := lctxOf w index lay a (trPc lay.val c) with hL
    have htp := trPc_lt lay.val c
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := hs0.known
    have hkeep := hs0.keep
    have e17 : (a7lE.eval u) = a7lW a := by
      simp only [a7lE, b1E, E.eval, BinOp.eval, a7E_eval hans, a6E_eval hans, kw, a7lW]
      rfl
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 195 := by fin_cases lay <;> decide
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
      have hS' : lowSum (ansV a) < 4095 := lowSum_lt (ansV a)
      have hle : lowSum (ansV a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSum (ansV a) < 8 := by omega
      have hcv : ckOf lay a = tgtL lay.val - lowSum (ansV a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hr', BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, ?_, by simp [hL, lctxOf]⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; unfold ckOf at hck ⊢; omega
      · simp only [hL, lctxOf]; unfold retOff; split_ifs <;> omega
    have hGu : Glob (bK lay.val) w pk u := by
      have := Glob_writeHash ht.glob a D h12 hDf.1
      exact this
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) u := by
      intro j hj hP
      have := Orig_writeHash ht.orig a D h12 (by omega)
      exact this j hj ⟨hP, by unfold WIT; rcases hDf.2.2.2.1 with h | h <;> omega⟩
    have hOs0 : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc tgtl rfl]
      simp only [tgtl, E.eval, BinOp.eval, a6E_eval hans, kw]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      rw [hm]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 448800 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ lowerLayK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_⟩
    · -- the chain code's known registers
      intro p hp
      simp only [LCtx.known, hL, lctxOf, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only
      · exact hkL (.x5, 0) (by simp [lowerLayK, baseK])
      · exact hkL (.x11, 64) (by simp [lowerLayK])
      · exact hkL (.x6, 1) (by simp [lowerLayK])
      · exact hkL (.x7, 2) (by simp [lowerLayK])
      · exact hkL (.x8, 3) (by simp [lowerLayK])
      · exact hkL (.x9, 4) (by simp [lowerLayK])
      · exact hkL (.x13, 5) (by simp [lowerLayK])
      · exact hkL (.x26, 6) (by simp [lowerLayK])
      · exact hkL (.x28, BitVec.ofNat 64 (headerBank lay.val 0)) (by simp [lowerLayK])
      · exact hkL (.x2, 0x3fe00) (by simp [lowerLayK])
      · exact hko (.x15, 0x6e000) (by simp [postBl])
      · exact hko (.x22, BitVec.ofNat 64 (s6v lay.val)) (by simp [postBl])
      · rw [hkeep .x4 (by simp [keepB]), hu, writeHash_getReg, ht.tp lay rfl]; rfl
      · rw [hkL (.x27, BitVec.ofNat 64 (hw 1 lay.val)) (by simp [lowerLayK])]; unfold hw; congr 1
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7lE) (by simp [specBl]), e17]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
      · exact hko (.x1, pcOf (trPc lay.val c + retOff lay.val)) (by simp [postBl])
    · -- the chain blocks are original
      intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      have hlb : 0x800 + (layerEnd lay.val) = L.S6 + 64 + 64 * 0 + 0 ∨ True := Or.inr trivial
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hkeep .x23 (by simp [keepB]), hu, writeHash_getReg, ht.s7 lay rfl]
    · rw [hkeep .x30 (by simp [keepB]), hu, writeHash_getReg, ht.t5 lay rfl]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

end SigGolfCandidate.T3M.CanonicalPort
end CanonicalPortPart66

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart67

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

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The leaf-pk block with all untouched registers kept -/

/-- The registers the leaf-pk block neither writes nor knows at its start. -/
def keepLfAll (lay : Nat) : List Reg := [.x1, .x2, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x19, .x20, .x21, .x22, .x23,
  .x24, .x25, .x26, .x29, .x30, .x31] ++ (if lay = 0 then [.x6, .x28] else [])

/-- `copyCheck`'s leaf-pk part, keeping `keepLfAll`. -/
def leafCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) (keepLfAll lay)

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
  [(.x2, 0x3fe00), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
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
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) u

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
      unfold SigGolfCandidate.T3M.CanonicalPort.Verify.TAB at hA
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
theorem tgtLfOld_eval (lay : Nat) (t : MachineState) (h leaf : Nat) (hn : stabBits lay ≤ h) (hh : h ≤ 12)
    (hl : leaf < 2 ^ h) (hs : stabIdx lay < 2 ^ 32)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ h + leaf)) :
    (tgtLfOld lay).eval t = pcOf (stabIdx lay + leaf % 2 ^ stabBits lay) := by
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
  simp only [tgtLfOld, E.eval, BinOp.eval, kw]
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  congr 1
  omega

theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide

theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp

/-- A lower route has exactly the sentinel absorbed by the relocated dispatch. -/
theorem tgtLf_lower_eval (lay : Layer) (hlay : lay ≠ 0) (t : MachineState) (leaf : Nat)
    (hl : leaf < 2 ^ hL lay.val)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + leaf)) :
    (tgtLf lay.val).eval t = pcOf (stabIdx lay.val + leaf % 2 ^ stabBits lay.val) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have he : stabBits lay.val = hL lay.val := by fin_cases lay <;> simp_all [stabBits, hL]
  have hb : 2 ^ hL lay.val ≤ 128 := by fin_cases lay <;> simp_all [hL]
  have hi := stabIdx_lt lay.val
  have hbase : 4 * 2 ^ hL lay.val ≤ 0x1000 + 4 * stabIdx lay.val := by omega
  have hshift : t.getReg .x23 <<< ((BitVec.ofNat 64 2).toNat % 64) =
      BitVec.ofNat 64 (4 * (2 ^ hL lay.val + leaf)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ 2 (by norm_num), h23]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [tgtLf, if_neg h0, E.eval, BinOp.eval, kw]
  rw [hshift, ofNat_add_ofNat]
  have hn : 4 * (2 ^ hL lay.val + leaf) + (0x1000 + 4 * stabIdx lay.val - 4 * 2 ^ hL lay.val) =
      0x1000 + 4 * (stabIdx lay.val + leaf) := by omega
  rw [hn, even_andNot1' _ (by omega), he, Nat.mod_eq_of_lt hl]

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
    (hG : Glob (lowerLayK lay.val) w pk s0) (hO : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (h30 : s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a (trPc lay.val c)).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 11 11 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a (trPc lay.val c) with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ lowerLayK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, if_neg h0, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK, baseK])
    · rw [hR .x27 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK])
    · rw [hR .x6 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK])
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
    exact tgtLf_lower_eval lay hlay t _ hlf
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
      all_goals first
        | exact hku (.x28, BitVec.ofNat 64 (headerBank 0 0)) (by simp [postLf, h0])
        | exact hku (.x6, 1) (by simp [postLf, leafK, h0])
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]
      all_goals first
        | exact h22
        | exact hkL (_, _) (by simp [lowerLayK])
  · rw [hkeep .x23 (by simp [keepLfAll, h0]), hR .x23 (by simp [chainRegs]), h23]
  · rw [hkeep .x30 (by simp [keepLfAll, h0]), hR .x30 (by simp [chainRegs]), h30]
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
    have hOt : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr at hw; rw [hS6] at hw
          unfold WIT at hw
          rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp⟩)

/-- Exact chain-end interface before the shared top leaf aggregation block. -/
structure TopLeafReady (w : WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc 0 c + 19)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : t.getReg .x30 = BitVec.ofNat 64 (route index 0).2
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase 0 + 64 * height 0) t

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
    change (tgtLfOld 0).eval t = _
    exact tgtLfOld_eval 0 t (hL 0) _ (stabBits_le 0) (by decide) hlf (stabIdx_lt _) ht.s7
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
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

end SigGolfCandidate.T3M.CanonicalPort
end CanonicalPortPart67
