import SigGolfCandidate.T3M.Verify.Nonbinary.Prologue

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- The packed top prefix uses the leaf in the high half of the control word.
The actual top tree is zero; neither the control word nor the witness pad changes. -/
def topPrefixWord (tp : Word) : Word :=
  BitVec.ofNat 64 (128 + 193 * 2 ^ 56) ||| ((tp >>> (32 : Word)) <<< (16 : Word))

def prefixCode : List (BitVec 32) :=
  [0x00ff4e37, 0x800e3e03, 0x02025193, 0x01019193, 0x003e6e33, 0x31c5d06f]
sym_block prefixBase := symRun { noAlias := true } prefixCode (pcOf 724) 200

theorem prefix_at : CodeAt Verify.image (pcOf 724) prefixCode := by
  have h := codeAt_from 724 (by decide)
  have hp : prefixCode <+: codeFrom 724 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

/-- Six actual helper instructions; the load reads an embedded constant. -/
theorem prefix_spec (s : MachineState) (hpc : s.pc = pcOf 724)
    (hmem : s.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ t, Steps Verify.image s 6 6 t ∧ t.pc = pcOf 96160 ∧
      t.getReg .x28 = topPrefixWord (s.getReg .x4) ∧
      RegsExcept s t [.x3,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound prefixBase prefix_at s hpc (by simp [prefixBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [prefixBase.res, rv_simp, pcOf]
  · simp [prefixBase.res, rv_simp, topPrefixWord, hmem]
  · intro r hr; cases r <;> simp at hr <;> simp [prefixBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prefixBase.res, rv_simp]

/-- Recover the mathematical prefix from the old, unchanged control register. -/
theorem topPrefixWord_hdr1 (tree leaf : Nat) (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ 32) :
    topPrefixWord (BitVec.ofNat 64 (hdr1 tree leaf)) =
      BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + leaf * 2 ^ 16) := by
  rw [hdr1_eq tree leaf ht hl]
  unfold topPrefixWord
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56) |||
    ((BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) >>> (32 : Nat)) <<< (16 : Nat)) = _
  rw [ofNat_shr _ _ (by omega), ofNat_shl]
  rw [show (tree + 2 ^ 32 * leaf) / 2 ^ 32 = leaf by omega]
  rw [show 128 + 193 * 2 ^ 56 = 193 * 2 ^ 56 + 128 by omega,
    ← ofNat_or_add 128 193 56 (by decide), BitVec.or_assoc,
    ofNat_or_disjoint' 128 (leaf * 2 ^ 16) 16 (by decide) (by omega),
    ofNat_or_add _ 193 56 (by omega)]
  congr 1
  omega

end SigGolfCandidate.T3M.Verify.Nonbinary
