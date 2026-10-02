import SigGolfCandidate.Expand.Layers
import SigGolfCandidate.Expand.PorsRoot

/-!
# `expand`, phase 2 as a whole (instructions 495 .. 672 and 316 .. 494)

`phase2_sim` : from `pors_init` with the partial witness `w0` in its buffer, the digest's low dword
at `0x160` and the sorted keys at `0x6E0`, the machine refines `afterW w0 idx v` (verify's PORS
root on `w0`, then the counter phase, then `withCounters w0 cs`), ending at a HALT with the result
(`QP`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- The queries of `expand` after the partial witness: the PORS root, then the counter phase. -/
def afterW (w0 : List Byte) (idx : Nat) (v : List Nat) : OracleComp HashSpec (Option (List Byte)) := do
  match ← porsRoot idx v w0 with
  | none => pure none
  | some M =>
    match ← expandLayers w0 idx nLayers (P ++ M) with
    | none => pure none
    | some cs => pure (some (withCounters w0 cs))

/-- A HALT with the outcome `r` (for `some`, the 16384-byte view `0x800 .. 0x4800`; the witness is
the buffer `0x1270 .. 0x4800`, the view without its lead). -/
def QP (r : Option (List Byte)) (t : MachineState) : Prop :=
  fetch eimg t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
    r.map (fun l => ofList 13712 (cutW l)) = if t.getReg .x10 = 0 then some (readBuffer t 0x1270 13712) else none

theorem qp_fail (t : MachineState) (h : FailSt t) : QP none t :=
  ⟨h.1, h.2.1, by rw [if_neg (by rw [h.2.2]; decide)]; rfl⟩

/-- **Phase 2**. -/
theorem phase2_sim (w0 : List Byte) (hw : w0.length = 16384) (hz : ∀ j < 4, w0.getD (2692 + j) 0 = 0) (K : Nat → Nat) (v : List Nat) (N : Nat)
    (t : MachineState) (hpc : t.pc = pcOf 495)
    (h160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (N % 2 ^ 64)) (hwm : WitMem w0 t)
    (hk : ∀ p < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (K p))
    (hkl : ∀ p < 15, K p < 2 ^ 22)
    (hx : ∀ s < 15, (v ++ [porsT]).getD (witPi w0 s / 8 % 16) 0 = K s / 256) :
    Sim eimg t (400000 + (34 + 5 * LW)) (afterW w0 (idxOf N) v) QP := by
  have hidx : idxOf N = N % 2 ^ 64 % 2 ^ 34 := by
    unfold idxOf totalH; rw [Nat.mod_mod_of_dvd _ (by norm_num)]
  have hroot := porsRoot_sim w0 K v t hpc (N % 2 ^ 64) (Nat.mod_lt _ (by norm_num)) h160 hwm hk hkl
    (by omega) hx
  rw [← hidx] at hroot
  unfold afterW
  refine Sim.bind hroot (fun r t1 h1 => ?_)
  rcases r with _ | M
  · exact (Sim.pure (Q := QP) (a := none) (qp_fail t1 h1)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p1, c1, hM, o1⟩ := h1
  dsimp only
  obtain ⟨t2, hs2, p2, x7, x8, x22, x26, x27, eM, eP, ecb, elf, enb, r2, f2⟩ := blk639_run t1 p1 c1.x25
  have hidx34 : idxOf N < 2 ^ 34 := by unfold idxOf totalH; exact Nat.mod_lt _ (by norm_num)
  have hl : LayInv w0 (idxOf N) 4 (P ++ M) [] t2 := by
    have hw2 : WitMem w0 t2 := c1.wit.frame f2 (fun a h1 h2 => by unfold witA at h1; omega)
    have c2 : LCtx w0 (idxOf N) t2 := ⟨hidx34, by rw [r2.get .x5 (by decide), c1.x5], x7,
      by rw [x22, c1.x4], by rw [r2.get .x25 (by decide), c1.x25], x26, x27, ecb, elf, enb, hw2⟩
    have hPM : (P ++ M).length = 32 := by simp [P, zeros, hM]
    have heb : t2.readWords (BitVec.ofNat 64 0x120) 4 = wordsOf (P ++ M) := by
      have e4 := readWords_ofNat_add t2 0x120 2 2
      rw [show (2 + 2 : Nat) = 4 from rfl, show (0x120 + 8 * 2 : Nat) = 0x130 from rfl] at e4
      rw [e4, eP, eM, o1, wordsOf_append _ _ (by simp [P, zeros]),
        show wordsOf P = [0, 0] from wordsOf_zeros 2]
    exact ⟨c2, ⟨by norm_num, hidx34, hPM, p2, c2.x5, x7, x8, c2.x22, x26, x27, heb⟩,
      rfl, fun j hj => by simp at hj, fun j hj => by simp at hj⟩
  have hlay := layers_sim w0 hw hz (idxOf N) 4 (by norm_num) (P ++ M) [] t2 hl
  refine (Sim.steps hs2 (Sim.bind hlay (W₂ := 0) (fun r2 t3 h3 => ?_))).mono (by omega) (fun _ _ h => h)
  rcases r2 with _ | cs
  · exact Sim.pure (Q := QP) (a := none) (qp_fail t3 h3)
  obtain ⟨hlen, e3, x35, x310, hbuf⟩ := h3
  refine Sim.pure (Q := QP) (a := some (withCounters w0 cs)) ⟨e3, x35, ?_⟩
  rw [List.append_nil] at hbuf
  rw [if_pos x310, Option.map_some, readBuffer_cut t3 _ (by rw [length_withCounters_ref w0 cs (by omega), hw]) hbuf]

end SigGolfCandidate.ExP
