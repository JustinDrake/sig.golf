import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.T3M.Verify.ChainCheckAll
import SigGolfCandidate.T3M.Verify.Judg

/-! # V1 chains: the simulation judgment for one chain and for all chains of a lower-code run

From `ChainIn c s0 i` (code chain `i`'s code start: its `ttab` slot for `A = 3t`, the shared block for `B`, `C`,
`ctab[t4]` for the checksum chain 42) the machine performs Core's `chainP` with the block's pads and witness value
(`GoodQ` of V2's `Judg`), then the dispatch of the next triple (`ChainNext`).

Cycle cost of code chain `i` at digit `d` (`chainCost`): the table slot's `j` (A and chain 42: 1), the head 5,
rungs `d .. 6` (`sb` 1 + HASH 8 each, the last rung's `li a2` 1), or the max-digit copy (5; 4 for chain 42); then
the dispatch after `C` (`xCost`: 4, after triples 0/7/13: 3) and after chain 42 the return (1). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The kernel checks at a context -/

theorem kOf_digits (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t % 8 = c.dig (3 * t) ∧ c.kOf t / 8 % 8 = c.dig (3 * t + 1) ∧ c.kOf t / 64 = c.dig (3 * t + 2) := by
  unfold kOf
  have h0 : c.dig (3 * t) < 8 := by unfold dig; split_ifs <;> omega
  have h1 : c.dig (3 * t + 1) < 8 := by unfold dig; split_ifs <;> omega
  have h2 : c.dig (3 * t + 2) < 8 := by unfold dig; split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem dig_lt8 (c : LCtx) (i : Nat) (hi : i < 42) : c.dig i < 8 := by unfold dig; split_ifs <;> omega

/-- The shared block of triple `i / 3` is checked. -/
theorem blk_at (c : LCtx) (i : Nat) (hi : i < 42) :
    blkCheck (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2)) = true :=
  blkCheck_at _ _ _ (by omega) (c.dig_lt8 _ (by omega)) (c.dig_lt8 _ (by omega))

theorem chk_headJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i < 7) :
    vrun (c.startPc i) 7 = some (headJ .x22 (offL i) (i / 3 == 0) (c.rungPc i (c.dig i))) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  unfold entCheck at he
  rw [k1, k2, k3, if_neg (by omega)] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hr : c.rungPc (3 * t) (c.dig (3 * t)) = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * c.dig (3 * t) := by
    unfold rungPc tb; rw [if_neg (by omega), if_pos h0, et]
  rw [hs, hr, et]
  exact rOK_eq he

theorem chk_copyJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i = 7) :
    vrun (c.startPc i) 7 = some (copyJ .x22 (offL i) (slotL i) (i / 3 == 0) (c.endPc i)) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  unfold entCheck at he
  rw [k1, k2, k3, if_pos hd] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hq : c.endPc (3 * t) = pcB t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
    unfold endPc tB; rw [if_neg (by omega), if_pos h0, et]
  rw [hs, hq, et]
  exact rOK_eq he

/-- The inline part (`B`, `C`) check of chain `i` at its digit. -/
theorem part_at (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) :
    partOK i (c.dig i) (c.startPc i) = true := by
  obtain ⟨t, r, rfl, hr⟩ : ∃ t r, i = 3 * t + r ∧ r < 3 := ⟨i / 3, i % 3, by omega, by omega⟩
  have et : (3 * t + r) / 3 = t := by omega
  have hb := c.blk_at (3 * t + r) hi
  rw [et] at hb
  unfold blkCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-, hB⟩, hC⟩, -⟩ := hb
  unfold startPc tB tC
  rw [if_neg (by omega), et, if_neg (by omega)]
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · rw [if_pos (by omega)]; exact hB
  · rw [if_neg (by omega)]; exact hC

theorem chk_headR (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) (hd : c.dig i < 7) :
    vrun (c.startPc i) 8 =
      some (headR .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i)) := by
  have hp := c.part_at i hi h0
  unfold partOK at hp
  rw [if_neg (by omega), Bool.and_eq_true] at hp
  exact rOK_eq hp.1

theorem chk_copyF (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) (hd : c.dig i = 7) :
    vrun (c.startPc i) 5 = some (copyF .x22 (offL i) (slotL i) (c.startPc i)) := by
  have hp := c.part_at i hi h0
  unfold partOK at hp
  rw [if_pos hd] at hp
  exact rOK_eq hp

theorem rungPc_inline (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) :
    c.rungPc i (c.dig i) = c.startPc i + 5 := by
  simp only [rungPc, startPc, show i ≠ 42 by omega, h0, if_false]
  split_ifs <;> omega

theorem chk_rung (c : LCtx) (i m : Nat) (hi : i < 42) (hm : c.dig i ≤ m) (hm6 : m ≤ 6)
    (hfirst : i % 3 ≠ 0 → c.dig i < m) :
    vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)) := by
  by_cases h0 : i % 3 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have hb := c.blk_at (3 * t) hi
    rw [et] at hb
    unfold blkCheck at hb
    simp only [Bool.and_eq_true] at hb
    have := List.all_eq_true.mp hb.1.1.1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc (3 * t) m = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * m := by
      unfold rungPc tb; rw [if_neg (by omega), if_pos h0, et]
    rw [hr]
    simpa using rOK_eq this
  · have hp := c.part_at i hi h0
    have hd := hfirst h0
    unfold partOK at hp
    rw [if_neg (by have := c.dig_lt8 i hi; omega), Bool.and_eq_true] at hp
    have := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc i m = c.startPc i + 7 + 2 * (m - (c.dig i + 1)) := by
      simp only [rungPc, startPc, show i ≠ 42 by omega, h0, if_false]
      split_ifs <;> omega
    rw [hr]
    exact rOK_eq this

end LCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The checksum chain's checks -/

theorem ck_parts : (∀ c, c < 7 → vrun (ctabIdx + 8 * c) 7 = some (headJ .x22 (offL 42) false (ckR0 + 2 * c))) ∧
    vrun (ctabIdx + 56) 6 = some (copyN .x22 (offL 42) (slotL 42) ckDone) ∧
    vrun (ctabIdx + 64) 2 = some retR ∧
    (∀ m, m < 7 → vrun (ckR0 + 2 * m) 3 = some (rungR m (if m = 6 then some (slotL 42) else none) (ckR0 + 2 * m))) ∧
    vrun ckDone 2 = some retR := by
  have h := ckCheck_ok
  unfold ckCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun c hc => rOK_eq (List.all_eq_true.mp h1 c (List.mem_range.mpr hc)), rOK_eq h2, rOK_eq h3,
    fun m hm => ?_, rOK_eq h5⟩
  have := List.all_eq_true.mp h4 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  simpa using rOK_eq this

/-- Every rung after the first of a chain is checked (chain 42: the `ck_r*` rungs). -/
theorem chk_rung' (c : LCtx) (i m : Nat) (hi : i ≤ 42) (hm : c.dig i < m) (hm6 : m ≤ 6) (hm1 : 1 ≤ m)
    (hck : i = 42 → c.ck < 8) :
    vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)) := by
  by_cases h42 : i = 42
  · subst h42
    have := ck_parts.2.2.2.1 m (by omega)
    have hr : c.rungPc 42 m = ckR0 + 2 * m := by unfold rungPc; simp
    rw [hr]; exact this
  · exact c.chk_rung i m (by omega) (by omega) hm6 (fun _ => hm)

/-! ## The abstract chain steps -/

/-- Steps `m .. 6` of code chain `i` from the value `v`, with the block's pads (Core's fold). -/
def rest (c : LCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (7 - m)).foldlM
    (fun v step => shortHash (chainInputP c.lay c.tree c.leaf (i + c.koff) step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : LCtx) (i m : Nat) (h : m ≤ 6) (v : Digest) :
    c.rest i m v =
      shortHash (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m + 1) := by
  unfold rest
  rw [show 7 - m = (7 - (m + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem rest_7 (c : LCtx) (i : Nat) (v : Digest) : c.rest i 7 v = pure v := rfl

theorem chainP_rest (c : LCtx) (i d : Nat) (v : Digest) :
    chainP c.lay c.tree c.leaf (i + c.koff) d (7 - d) (c.pad0 i) (c.pad1 i) v = c.rest i d v := rfl

theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 v) = chainInputP lay tree leaf i step p0 p1 v :=
  pad64_of_aligned _ (by rw [chainInputP_length])

theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 v)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length]; omega, by rw [chainInputP_length]⟩, chainInputP_length]

/-! ## Code bounds -/

theorem triBaseTab_all : (triBaseTab.all fun x => decide (x < 82100)) = true := by decide +kernel

theorem triBase_lt (t dB dC : Nat) : triBase t dB dC < 82100 := by
  unfold triBase
  rw [List.getD_eq_getElem?_getD]
  cases hn : triBaseTab[64 * t + 8 * dB + dC]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp triBaseTab_all x (List.mem_of_getElem? hn)

theorem partLen_le (d : Nat) : partLen d ≤ 20 := by unfold partLen; split <;> omega

theorem tX_lt (c : LCtx) (i : Nat) : c.tX i < 82200 := by
  have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have := partLen_le (c.dig (3 * (i / 3) + 1)); have := partLen_le (c.dig (3 * (i / 3) + 2))
  unfold tX pcX pcC pcB; omega

theorem startPc_lt (c : LCtx) (i : Nat) (hi : i ≤ 42) (hck : c.ck ≤ 8) : c.startPc i < 209920 := by
  unfold startPc
  split_ifs with h1 h2 h3
  · unfold ctabIdx; omega
  · have := c.kOf_lt (i / 3) (by omega); unfold entW ttabIdx; omega
  · have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    unfold tB pcB; omega
  · have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    have := partLen_le (c.dig (3 * (i / 3) + 1))
    unfold tC pcC pcB; omega

theorem rungPc_lt (c : LCtx) (i m : Nat) (hm : m ≤ 6) : c.rungPc i m < 209920 := by
  have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have := partLen_le (c.dig (3 * (i / 3) + 1))
  unfold rungPc tb tB tC pcC pcB
  split_ifs <;> (try unfold ckR0) <;> omega

/-! ## After a chain: the next chain's code, the dispatch, or the return -/

/-- The state before code chain `j` (`j ≤ 42`), or after the chain code's return (`j = 43`). -/
def ChainNext (c : LCtx) (s0 : MachineState) (j : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  if j ≤ 42 then c.ChainIn s0 j acc s else c.ChainOut s0 43 acc s

/-- The dispatch after code chain `i`: after a triple's `C` 4 (after triples 0/7/13: 3), after chain 42 the return 1. -/
def xCost (i : Nat) : Nat := if i = 42 then 1 else if i % 3 = 2 then (if i = 41 ∨ i = 2 ∨ i = 23 then 3 else 4) else 0

theorem xCost_le (i : Nat) : xCost i ≤ 4 := by unfold xCost; split_ifs <;> omega

theorem end_next (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    ∃ u, Steps vimage s (xCost i) (xCost i) u ∧ c.ChainNext s0 (i + 1) acc u := by
  by_cases h42 : i = 42
  · subst h42
    obtain ⟨u, hst, hu⟩ := c.ckdone_step hc hk ck_parts.2.2.2.2 acc s hs
    refine ⟨u, by simpa [xCost] using hst, ?_⟩
    unfold ChainNext; rw [if_neg (by omega)]; exact hu
  · by_cases h2 : i % 3 = 2
    · by_cases h41 : i = 41
      · subst h41
        have hx := c.blk_at 41 (by omega)
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        have hrun : vrun (c.tX 41) 4 = some ctabX := by
          have := rOK_eq hx.2; exact this
        obtain ⟨u, hst, hu⟩ := c.x13_step hc hk (by omega) (by have := c.tX_lt 41; omega) hrun acc s hs
        refine ⟨u, by simpa [xCost] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega)]; exact hu
      · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t + 2 := ⟨i / 3, by omega⟩
        have hx := c.blk_at (3 * t + 2) (by omega)
        rw [show (3 * t + 2) / 3 = t by omega] at hx
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        rw [if_neg (by omega)] at hx
        have hrun := rOK_eq hx.2
        have htx : c.tX (3 * t + 2) = pcX t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
          unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
        rw [← htx] at hrun
        obtain ⟨u, hst, hu⟩ := c.x_step hc hk t (by omega) hi.1 (by have := c.tX_lt (3 * t + 2); omega) hrun acc s hs
        have he : (9 * ((t + 1) % 7) = 9) ↔ (3 * t + 2 = 2 ∨ 3 * t + 2 = 23) := by omega
        refine ⟨u, by simpa [xCost, h42, h41, he] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega), show 3 * t + 2 + 1 = 3 * t + 3 by ring]; exact hu
    · refine ⟨s, by simpa [xCost, h42, h2] using Steps.refl s, ?_⟩
      unfold ChainNext; rw [if_pos (by omega)]
      exact c.next_inline s0 i (by omega) h2 acc s hs

end LCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-- Cycles from just before step `m`'s `ecall` to the chain's last hash. -/
def preCost (m : Nat) : Nat := 8 + 9 * (6 - m) + (if m < 6 then 1 else 0)

/-- **The steps of a chain** from `PreHash` at step `m`: Core's remaining fold, then the dispatch. -/
theorem steps_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (acc : List Digest)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQ t N C Q A (K (acc ++ [v]))) :
    ∀ k m, m + k = 6 → c.dig i ≤ m → ∀ v s, c.PreHash s0 i acc m v s →
      Verify.GoodQ s (N + 3 * (7 - m) + 4) (C + preCost m + xCost i) Q (A + preCost m + xCost i)
        (Verify.ccM (c.rest i m v) (fun v => K (acc ++ [v]))) := by
  have hrc : ∀ m, m ≤ 6 → c.rungPc i m < 209920 := fun m hm => c.rungPc_lt i m hm
  have hx4 := xCost_le i
  intro k
  induction k with
  | zero =>
    intro m hm hd v s hs
    obtain rfl : m = 6 := by omega
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i 6 hi (le_refl _) hd acc v s hs
    rw [rest_succ c i 6 (le_refl _)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQ (writeHash s a) (N + xCost i) (C + xCost i) Q (A + xCost i)
        (Verify.ccM (c.rest i 7 (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      rw [rest_7, Verify.ccM_pure]
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ ((hpost a).2 rfl)
      exact Verify.GoodQ.steps' hu (hK _ _ hn) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQ.shortHash_bind (f := c.rest i 7) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    exact h3.mono (by omega) (by simp [preCost]; omega) (fun hq => ⟨hq, by simp [preCost]; omega⟩)
  | succ k ih =>
    intro m hm hd v s hs
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
    rw [rest_succ c i m (by omega)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQ (writeHash s a) (N + 3 * (7 - (m + 1)) + 4 + 2)
        (C + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1)) Q
        (A + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1))
        (Verify.ccM (c.rest i (m + 1) (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      have hrun := c.chk_rung' i (m + 1) hi.2 (by omega) (by omega) (by omega) hck
      obtain ⟨u, hu, hp⟩ := c.rung_step hc hk i (m + 1) hi (by omega) (hrc _ (by omega)) hrun acc _ _
        ((hpost a).1 (by omega))
      have := ih (m + 1) (by omega) (by omega) _ _ hp
      exact Verify.GoodQ.steps' hu this (by split <;> omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQ.shortHash_bind (f := c.rest i (m + 1)) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    refine h3.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega

end LCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-- Cycle cost of code chain `i` at digit `d`, including the dispatch after it. -/
def chainCost (i d : Nat) : Nat :=
  (if i % 3 = 0 then (if d = 7 then (if i = 42 then 5 else 6) else 70 - 9 * d)
   else (if d = 7 then 5 else 69 - 9 * d)) + xCost i

theorem dig42 (c : LCtx) : c.dig 42 = c.ck := by unfold dig; simp

/-- **One code chain**: from `ChainIn` to the next chain (or the return), Core's `chainP` with the block's
pads and witness value. -/
theorem chain_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQ t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQ s (N + 40) (C + chainCost i (c.dig i)) Q (A + chainCost i (c.dig i))
      (Verify.ccM (chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc ++ [v]))) := by
  have hx4 := xCost_le i
  have hdl : c.dig i < 8 := by
    by_cases h42 : i = 42
    · subst h42; rw [dig42]; exact hck rfl
    · exact c.dig_lt8 i (by omega)
  have hsp := c.startPc_lt i hi.2 hc.2.2.2.2.2.2.1
  by_cases h7 : c.dig i = 7
  · -- the max-digit copy
    rw [h7, show 7 - 7 = 0 from rfl]
    have hspec : chainP c.lay c.tree c.leaf (i + c.koff) 7 0 (c.pad0 i) (c.pad1 i) (c.val i) = pure (c.val i) := rfl
    rw [hspec, Verify.ccM_pure]
    by_cases h42 : i = 42
    · subst h42
      have hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)) := by
        have := ck_parts.2.1
        rw [dig42] at h7
        unfold startPc endPc; simp only [if_true, h7]; exact this
      obtain ⟨t, hst, hE⟩ := c.copyN_step hc hk h0 hi.1 hsp hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk 42 hi _ _ hE
      refine Verify.GoodQ.steps' hst (Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp; omega) (fun hq => ⟨hq, by unfold chainCost; simp; omega⟩)
    · by_cases h0' : i % 3 = 0
      · have hrun := c.chk_copyJ i (by omega) h0' h7
        obtain ⟨t, hst, hE⟩ := c.copyJ_step hc hk h0 i ⟨hi.1, by omega⟩ (i / 3 == 0)
          (fun h => by
            have : i = 0 := by simp at h; omega
            exact ⟨this, hko (by omega)⟩)
          (fun h => by simp at h; omega) hsp hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
        refine Verify.GoodQ.steps' hst (Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7, h42]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7, h42]; omega⟩)
      · have hrun := c.chk_copyF i (by omega) h0' h7
        have hend : c.startPc i + 5 = c.endPc i := by
          simp only [startPc, endPc, if_neg h42, if_neg h0']
          by_cases h1 : i % 3 = 1
          · have e1 : c.dig (3 * (i / 3) + 1) = 7 := by rw [show 3 * (i / 3) + 1 = i by omega, h7]
            rw [if_pos h1, if_pos h1]; unfold tB tC pcC; rw [e1]; rfl
          · have e2 : c.dig (3 * (i / 3) + 2) = 7 := by rw [show 3 * (i / 3) + 2 = i by omega, h7]
            rw [if_neg h1, if_neg h1]; unfold tC tX pcX; rw [e2]; rfl
        obtain ⟨t, hst, hE⟩ := c.copyF_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hsp hend hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
        refine Verify.GoodQ.steps' hst (Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7]; omega⟩)
  · -- a head and its rungs
    have hd : c.dig i < 7 := by omega
    rw [chainP_rest]
    have hsteps := c.steps_good hc hk h0 i hi hck acc K N C A Q hK (6 - c.dig i) (c.dig i) (by omega) (le_refl _)
    have hrp := c.rungPc_lt i (c.dig i) (by omega)
    by_cases h0' : i % 3 = 0
    · have hrun1 : vrun (c.startPc i) 7 = some (headJ .x22 (offL i) (i / 3 == 0) (c.rungPc i (c.dig i))) := by
        by_cases h42 : i = 42
        · subst h42
          have := ck_parts.1 c.ck (by rw [dig42] at hd; exact hd)
          have hst42 : c.startPc 42 = ctabIdx + 8 * c.ck := by unfold startPc; simp
          have hrp42 : c.rungPc 42 (c.dig 42) = ckR0 + 2 * c.ck := by unfold rungPc; simp [dig42]
          rw [hst42, hrp42]; simpa using this
        · exact c.chk_headJ i (by omega) h0' hd
      have hrun2 : vrun (c.rungPc i (c.dig i)) 3 = some (rungR (c.dig i)
          (if c.dig i = 6 then some (slotL i) else none) (c.rungPc i (c.dig i))) := by
        by_cases h42 : i = 42
        · subst h42
          have := ck_parts.2.2.2.1 c.ck (by rw [dig42] at hd; exact hd)
          have hrp42 : c.rungPc 42 (c.dig 42) = ckR0 + 2 * c.ck := by unfold rungPc; simp [dig42]
          rw [hrp42, dig42]; exact this
        · exact c.chk_rung i (c.dig i) (by omega) (le_refl _) (by omega) (fun h => absurd h0' h)
      obtain ⟨t, hst, hP⟩ := c.headJ_step hc hk h0 i hi hd (i / 3 == 0)
        (fun h => by
          have : i = 0 := by simp at h; omega
          exact ⟨this, hko (by omega)⟩)
        (fun h => by simp at h; omega) hsp hrp hrun1 hrun2 acc s hs
      refine Verify.GoodQ.steps' hst (hsteps _ _ hP) (by split <;> omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega
    · have hrun := c.chk_headR i (by omega) h0' hd
      obtain ⟨t, hst, hP⟩ := c.headR_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hd hsp
        (c.rungPc_inline i (by omega) h0') hrun acc s hs
      refine Verify.GoodQ.steps' hst (hsteps _ _ hP) (by split <;> omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega

end LCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## All code chains of a run -/

/-- Core's chain of code chain `i` (with the block's pads and witness value), appended to the ends so far. -/
def chainF (c : LCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends ++ [v])

/-- The cycles of the code chains `i .. i + k - 1`. -/
def chainsCost (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- **The code chains `i .. 41`** from `ChainIn i`, up to `ChainIn 42` (before the checksum dispatch). -/
theorem chains_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.ChainIn s0 42 ends t → Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, i + k = 42 → c.i0 ≤ i → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQ s (N + 40 * k) (C + c.chainsCost i k) Q (A + c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik _ acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik hi0 acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, Verify.ccM_bind]
    have := c.chain_good hc hk h0 hko i ⟨hi0, by omega⟩ (fun h => absurd h (by omega)) acc
      (fun ends => Verify.ccM ((List.range' (i + 1) k).foldlM c.chainF ends) K)
      (N + 40 * k) (C + c.chainsCost (i + 1) k) (A + c.chainsCost (i + 1) k) Q
      (fun v t ht => by
        have ht' : c.ChainIn s0 (i + 1) (acc ++ [v]) t := by
          unfold ChainNext at ht; rwa [if_pos (by omega)] at ht
        exact ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht') s hs
    refine this.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega

/-- **The checksum chain and the return** (`ck < 8`), from `ChainIn 42`. -/
theorem ck_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (hck : c.ck < 8)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQ t N C Q A (K ends))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    Verify.GoodQ s (N + 40) (C + chainCost 42 c.ck) Q (A + chainCost 42 c.ck)
      (Verify.ccM (c.chainF acc 42) K) := by
  have := c.chain_good hc hk h0 hko 42 ⟨hc.2.2.2.2.2.2.2.2, le_refl _⟩ (fun _ => hck) acc K N C A Q
    (fun v t ht => by
      have ht' : c.ChainOut s0 43 (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_neg (by omega)] at ht
      exact hK _ t ht') s hs
  simp only [chainF, Verify.ccM_bind, Verify.ccM_pure]
  rw [dig42] at this ⊢
  exact this

/-- **No checksum chain** (`ck = 8`, the top layer's run of the code chains 33..41): `ctab[8]` returns. -/
theorem ck8_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (X : OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop) (acc : List Digest)
    (hK : ∀ t, c.ChainOut s0 42 acc t → Verify.GoodQ t N C Q A X)
    (s : MachineState) (hs : c.ChainIn s0 42 acc s) : Verify.GoodQ s (N + 1) (C + 1) Q (A + 1) X := by
  obtain ⟨u, hst, hu⟩ := c.ck8_step hc hk h8 ck_parts.2.2.1 acc s hs
  exact Verify.GoodQ.steps hst (hK u hu)

end LCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The cost of the chain phase -/

/-- The digit-independent cost of code chain `i` (as if no digit were maximal). -/
def cbase (i : Nat) : Nat := (if i % 3 = 0 then 70 else 69) + xCost i

/-- The saving of a maximal digit (the copy instead of a head and the last rung): 1, the checksum chain 2. -/
def zc (i d : Nat) : Nat := if d = 7 then (if i = 42 then 2 else 1) else 0

theorem chainCost_add (i d : Nat) (hd : d < 8) : chainCost i d + 9 * d + zc i d = cbase i := by
  unfold chainCost zc cbase
  by_cases h7 : d = 7
  · subst h7
    by_cases h42 : i = 42
    · subst h42; simp [xCost]
    · by_cases h0 : i % 3 = 0
      · simp [h0, h42]; omega
      · simp [h0, h42]; omega
  · split_ifs <;> omega

theorem chainsCost_add (c : LCtx) (hck : c.ck < 8) : ∀ k i, i + k ≤ 43 →
    c.chainsCost i k + 9 * ((List.range' i k).map c.dig).sum + ((List.range' i k).map fun j => zc j (c.dig j)).sum =
      ((List.range' i k).map cbase).sum := by
  intro k
  induction k with
  | zero => intro i _; simp [chainsCost]
  | succ k ih =>
    intro i hik
    have h := ih (i + 1) (by omega)
    have hd : c.dig i < 8 := by
      by_cases h42 : i = 42
      · subst h42; rw [dig42]; exact hck
      · exact c.dig_lt8 i (by omega)
    have := chainCost_add i (c.dig i) hd
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons] at h ⊢
    omega

theorem cbase_sum43 : ((List.range' 0 43).map cbase).sum = 3036 := by decide
theorem cbase_sum_top : ((List.range' 33 9).map cbase).sum = 635 := by decide

/-- The weighted number of maximal digits of the code chains `i .. i + k - 1`. -/
def zSum (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => zc j (c.dig j)).sum

/-- **The chain phase of a lower layer**: `3036 - 9 target - Z` (the 43 digits sum to the target). -/
theorem chainsCost_lower (c : LCtx) (hck : c.ck < 8) (T : Nat) (hT : ((List.range' 0 43).map c.dig).sum = T) :
    c.chainsCost 0 42 + chainCost 42 c.ck + 9 * T + c.zSum 0 43 = 3036 := by
  have h := c.chainsCost_add hck 43 0 (le_refl _)
  rw [hT, cbase_sum43] at h
  have e : c.chainsCost 0 43 = c.chainsCost 0 42 + chainCost 42 c.ck := by
    unfold chainsCost
    rw [show (43 : Nat) = 42 + 1 from rfl, List.range'_concat, List.map_append, List.sum_append]
    simp [dig42]
  unfold zSum
  omega

/-- **The top layer's code chains 33..41** (the radix-8 chains 49..57) and the return: `635 + 1 - 9 S - Z`. -/
theorem chainsCost_top (c : LCtx) (hck : c.ck < 8) (S : Nat) (hS : ((List.range' 33 9).map c.dig).sum = S) :
    c.chainsCost 33 9 + 9 * S + c.zSum 33 9 = 635 := by
  have h := c.chainsCost_add hck 9 33 (by omega)
  rw [hS, cbase_sum_top] at h
  unfold zSum
  omega

end LCtx

end SigGolfCandidate.T3M
