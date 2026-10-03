import SigGolfCandidate.T3M.Keygen.PackedRun
import SigGolfCandidate.T3.PackedChain

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option backward.isDefEq.respectTransparency false


/-- The machine's routing expression, without a source-graph truncation. -/
theorem routedAt_nat (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) = BitVec.ofNat 64 (tree * 2 ^ height lay + leaf) := by
  rw [routedAt, ht, hf, ofNat_shl, ofNat_add_ofNat]

/-- Actual producer coordinates have no high route spill. -/
theorem routedAt_high_zero (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) >>> 32 = 0 := by
  rw [routedAt_nat s lay tree leaf ht hf, ofNat_shr _ _ (by omega),
    Nat.div_eq_of_lt (by omega)]
  rfl

/-- RV64 bitwise packing is the exact actual low-word arithmetic. -/
theorem packedAt_nat (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = BitVec.ofNat 64
      (128 + i + step * 2^8 + (tree * 2^height lay + leaf) * 2^16 + lay.val * 2^48 + 193 * 2^56) := by
  have hl := lay.isLt
  have hm : BitVec.ofNat 64 step &&& 255#64 = BitVec.ofNat 64 step := by
    interval_cases step <;> rfl
  have hroute : ((BitVec.ofNat 64 (tree * 2^height lay + leaf) <<< 32) >>> 16) =
      BitVec.ofNat 64 ((tree * 2^height lay + leaf) * 2^16) := by
    rw [ofNat_shl, ofNat_shr _ _ (by omega)]
    congr 1
    omega
  rw [packedAt, routedAt_nat s lay tree leaf h9 h18, hroute, h8, h19, h20, hm,
    ofNat_shl, ofNat_shl, ofNat_shl]
  rw [ofNat_or_disjoint' i 128 7 (by omega) (by decide)]
  rw [ofNat_or_disjoint' _ _ 48 (by omega) (by omega)]
  rw [ofNat_or_disjoint' _ _ 56 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 16 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 8 (by omega) (by omega)]
  congr 1
  omega

private theorem low_ofNat (n : Nat) :
    (BitVec.ofNat 128 n).extractLsb' 0 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega

/-- Source agreement only needs actual routed bounds, not a narrowed source graph. -/
theorem packedAt_source (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = (chainHeader lay tree leaf i step).extractLsb' 0 64 := by
  exact (packedAt_nat s lay tree leaf i step hr hi hs h8 h9 h18 h19 h20).trans
    ((congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (low_ofNat _)).symm

private theorem high_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 128 n).extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change _ = 0
  omega

theorem source_high_actual (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 64 64 = 0#64 := by
  have hl := lay.isLt
  exact (congrArg (fun x : BitVec 128 => x.extractLsb' 64 64)
    (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (high_ofNat _ (by omega))

end SigGolfCandidate.T3M.Keygen.PackedBlocks
