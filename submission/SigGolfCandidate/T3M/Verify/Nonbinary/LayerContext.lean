import SigGolfCandidate.T3M.Verify.Nonbinary.LayerDecode
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- The actual mixed-radix top chain context after an encoding answer. -/
def nctxOf (w : WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 15048, coreDigit 0 v, p + 13⟩

theorem nctx_ok (w : WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩

theorem nctx_known (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (hidx : index < 2 ^ 31)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  have htree : (route index 0).2 = 0 := by
    rw [route_snd]
    exact Nat.div_eq_of_lt hidx
  have hleaf := leaf_lt32 index 0
  have hprefix : s.getReg .x28 = BitVec.ofNat 64
      (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).prefix := by
    rw [he.prefix, writeHash_getReg, ht.tp 0 rfl,
      Nonbinary.topPrefixWord_hdr1 _ _ (tree_lt index 0 hidx) hleaf]
    simp only [nctxOf, NCtx.prefix, htree, Nat.zero_mul, Nat.zero_add,
      Nat.mod_eq_of_lt hleaf]
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals try exact ht.tp 0 rfl
  all_goals exact ht.glob.1 _ (by simp [bK, layK, baseK, nctxOf, NCtx.w1, hw, t3In])

theorem topEntry_orig (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd 0) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have ho := Orig_writeHash ht.orig a 320 h12 (by norm_num)
  have hu : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    ho.mono (fun o h => ⟨h, Or.inr (by unfold WIT; omega)⟩)
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))

theorem nctx_orig (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 10568 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega

end SigGolfCandidate.T3M
