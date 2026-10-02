import SigGolfCandidate.T3M.Verify.ChainQSem
import SigGolfCandidate.T3M.Verify.ChainGood
import SigGolfCandidate.T3M.Verify.Decode

/-! # V1 top chains: the simulation judgment for the top layer's chain phase

`QCtx.chain_good`: one radix-4 chain (`i ≤ 48`) from `ChainIn i` is Core's `chainP 0 tree leaf i d (3 - d)` with the
block's pads and witness value; `QCtx.chains_good` the chains `0 .. 48`; `QCtx.top_good` the whole top chain phase:
the quad code, `q48_done`, the lower code's chains `33 .. 41` (the top's `49 .. 57`) and the return `ctab[8]`.

Cycle cost of chain `i < 49` at digit `d` (`chainCost`): the table chains (`A = 4q` and 48) `34 - 9 d` (copy 6), the
inline chains `33 - 9 d` (copy 5), plus the dispatch after `D` (4) and after chain 48 (`q48_done`, 5). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace QCtx

/-! ## The kernel checks at a context -/

theorem blk_at (c : QCtx) (i : Nat) (hi : i < 48) :
    qblkCheck (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3)) = true :=
  qblkCheck_at _ _ _ _ (by omega) (c.dig_lt4 _) (c.dig_lt4 _) (c.dig_lt4 _)

theorem chk_headJ (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 = 0) (hd : c.dig i < 3) :
    vrun (c.startPc i) 7 = some (headJ .x19 (offT i) (i / 4 == 0) (c.rungPc i (c.dig i))) := by
  obtain ⟨q, rfl⟩ : ∃ q, i = 4 * q := ⟨i / 4, by omega⟩
  have eq : 4 * q / 4 = q := by omega
  have he := qentCheck_at q (c.kOf q) (by omega) (c.kOf_lt q (by omega))
  obtain ⟨k1, k2, k3, k4⟩ := c.kOf_digits q
  unfold qentCheck at he
  rw [k1, k2, k3, k4, if_neg (by omega)] at he
  have hs : c.startPc (4 * q) = qentW q (c.kOf q) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, eq]
  have hr : c.rungPc (4 * q) (c.dig (4 * q)) =
      quadBase q (c.dig (4 * q + 1)) (c.dig (4 * q + 2)) (c.dig (4 * q + 3)) + 2 * c.dig (4 * q) := by
    unfold rungPc qb; rw [if_neg (by omega), if_pos h0, eq]
  rw [hs, hr, eq]
  exact rOK_eq he

theorem chk_copyJ (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 = 0) (hd : c.dig i = 3) :
    vrun (c.startPc i) 7 = some (copyJ .x19 (offT i) (slotT i) (i / 4 == 0) (c.endPc i)) := by
  obtain ⟨q, rfl⟩ : ∃ q, i = 4 * q := ⟨i / 4, by omega⟩
  have eq : 4 * q / 4 = q := by omega
  have he := qentCheck_at q (c.kOf q) (by omega) (c.kOf_lt q (by omega))
  obtain ⟨k1, k2, k3, k4⟩ := c.kOf_digits q
  unfold qentCheck at he
  rw [k1, k2, k3, k4, if_pos hd] at he
  have hs : c.startPc (4 * q) = qentW q (c.kOf q) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, eq]
  have hq : c.endPc (4 * q) = qpcB q (c.dig (4 * q + 1)) (c.dig (4 * q + 2)) (c.dig (4 * q + 3)) := by
    unfold endPc qB; rw [if_neg (by omega), if_pos h0, eq]
  rw [hs, hq, eq]
  exact rOK_eq he

/-- The inline part (`B`, `C`, `D`) check of chain `i` at its digit. -/
theorem part_at (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 ≠ 0) :
    partOK2 i (c.dig i) (c.startPc i) = true := by
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, i = 4 * q + r ∧ r < 4 := ⟨i / 4, i % 4, by omega, by omega⟩
  have eq : (4 * q + r) / 4 = q := by omega
  have hb := c.blk_at (4 * q + r) hi
  rw [eq] at hb
  unfold qblkCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨-, hB⟩, hC⟩, hD⟩, -⟩ := hb
  unfold startPc qB qC qD
  rw [if_neg (by omega), if_neg h0, eq]
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl
  · rw [if_pos (by omega)]; exact hB
  · rw [if_neg (by omega), if_pos (by omega)]; exact hC
  · rw [if_neg (by omega), if_neg (by omega)]; exact hD

theorem chk_headR (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 ≠ 0) (hd : c.dig i < 3) :
    vrun (c.startPc i) 8 =
      some (headR2 .x19 (offT i) (c.dig i) (if c.dig i = 2 then some (slotT i) else none) (c.startPc i)) := by
  have hp := c.part_at i hi h0
  unfold partOK2 at hp
  rw [if_neg (by omega), Bool.and_eq_true] at hp
  exact rOK_eq hp.1

theorem chk_copyF (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 ≠ 0) (hd : c.dig i = 3) :
    vrun (c.startPc i) 5 = some (copyF .x19 (offT i) (slotT i) (c.startPc i)) := by
  have hp := c.part_at i hi h0
  unfold partOK2 at hp
  rw [if_pos hd] at hp
  exact rOK_eq hp

theorem rungPc_inline (c : QCtx) (i : Nat) (hi : i < 48) (h0 : i % 4 ≠ 0) :
    c.rungPc i (c.dig i) = c.startPc i + (if c.dig i = 2 then 4 else 5) := by
  simp only [rungPc, startPc, show i ≠ 48 by omega, h0, if_false]
  split_ifs <;> omega

theorem q48_parts : (∀ d, d < 3 → vrun (q48tabIdx + 8 * d) 7 = some (headJ .x19 (offT 48) false (q48R0 + 2 * d))) ∧
    vrun (q48tabIdx + 24) 7 = some (copyJ .x19 (offT 48) (slotT 48) false q48Done) ∧
    (∀ m, m < 3 → vrun (q48R0 + 2 * m) 3 = some (rungR m (if m = 2 then some (slotT 48) else none) (q48R0 + 2 * m))) ∧
    vrun q48Done 6 = some q48D := by
  have h := q48Check_ok
  unfold q48Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun d hd => rOK_eq (List.all_eq_true.mp h1 d (List.mem_range.mpr hd)), rOK_eq h2, fun m hm => ?_,
    rOK_eq h4⟩
  have := List.all_eq_true.mp h3 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  simpa using rOK_eq this

theorem chk_rung (c : QCtx) (i m : Nat) (hi : i ≤ 48) (hm : c.dig i ≤ m) (hm2 : m ≤ 2)
    (hfirst : i % 4 ≠ 0 → i ≠ 48 → c.dig i < m) :
    vrun (c.rungPc i m) 3 = some (rungR m (if m = 2 then some (slotT i) else none) (c.rungPc i m)) := by
  by_cases h48 : i = 48
  · subst h48
    have hr : c.rungPc 48 m = q48R0 + 2 * m := by unfold rungPc; simp
    rw [hr]; exact q48_parts.2.2.1 m (by omega)
  by_cases h0 : i % 4 = 0
  · obtain ⟨q, rfl⟩ : ∃ q, i = 4 * q := ⟨i / 4, by omega⟩
    have eq : 4 * q / 4 = q := by omega
    have hb := c.blk_at (4 * q) (by omega)
    rw [eq] at hb
    unfold qblkCheck at hb
    simp only [Bool.and_eq_true] at hb
    have := List.all_eq_true.mp hb.1.1.1.1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc (4 * q) m = quadBase q (c.dig (4 * q + 1)) (c.dig (4 * q + 2)) (c.dig (4 * q + 3)) + 2 * m := by
      unfold rungPc qb; rw [if_neg (by omega), if_pos h0, eq]
    rw [hr]
    simpa using rOK_eq this
  · have hp := c.part_at i (by omega) h0
    have hd := hfirst h0 h48
    unfold partOK2 at hp
    rw [if_neg (by have := c.dig_lt4 i; omega), Bool.and_eq_true] at hp
    have := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc i m = c.startPc i + (if c.dig i = 2 then 6 else 7) + 2 * (m - (c.dig i + 1)) := by
      simp only [rungPc, startPc, h48, h0, if_false]
      split_ifs <;> omega
    rw [hr]
    exact rOK_eq this

/-! ## Code bounds -/

theorem quadBaseTab_all : (quadBaseTab.all fun x => decide (x < 110700)) = true := by decide +kernel

theorem quadBase_lt (q dB dC dD : Nat) : quadBase q dB dC dD < 110700 := by
  unfold quadBase
  rw [List.getD_eq_getElem?_getD]
  cases hn : quadBaseTab[64 * q + 16 * dB + 4 * dC + dD]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp quadBaseTab_all x (List.mem_of_getElem? hn)

theorem partLen2_le (d : Nat) : partLen2 d ≤ 12 := by unfold partLen2; split <;> omega

theorem qX_lt (c : QCtx) (i : Nat) : c.qX i < 110800 := by
  have := quadBase_lt (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
  have := partLen2_le (c.dig (4 * (i / 4) + 1)); have := partLen2_le (c.dig (4 * (i / 4) + 2))
  have := partLen2_le (c.dig (4 * (i / 4) + 3))
  unfold qX qpcX qpcD qpcC qpcB; omega

theorem startPc_lt (c : QCtx) (i : Nat) (hi : i ≤ 48) : c.startPc i < 209920 := by
  have := quadBase_lt (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
  have := partLen2_le (c.dig (4 * (i / 4) + 1)); have := partLen2_le (c.dig (4 * (i / 4) + 2))
  have := c.dig_lt4 48
  unfold startPc
  split_ifs with h1 h2 h3 h4
  · unfold q48tabIdx; omega
  · have := c.kOf_lt (i / 4) (by omega); unfold qentW qtabIdx; omega
  · unfold qB qpcB; omega
  · unfold qC qpcC qpcB; omega
  · unfold qD qpcD qpcC qpcB; omega

theorem rungPc_lt (c : QCtx) (i m : Nat) (hm : m ≤ 2) : c.rungPc i m < 209920 := by
  have := quadBase_lt (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
  have := partLen2_le (c.dig (4 * (i / 4) + 1)); have := partLen2_le (c.dig (4 * (i / 4) + 2))
  unfold rungPc qb qB qC qD qpcD qpcC qpcB
  split_ifs <;> (try unfold q48R0) <;> omega

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace QCtx

/-! ## After a chain -/

/-- After `q48_done` (the 49 quad-code ends in their slots; the lower code's `ChainIn 33` with a fresh base). -/
def QOut (c : QCtx) (s0 : MachineState) (acc : List Digest) (u : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x14 → x ≠ .x15 → u.getReg x = s0.getReg x) ∧
    u.getReg .x15 = BitVec.ofNat 64 0x6e000 ∧ Frame s0 u (c.Wr 49) ∧ acc.length = 49 ∧
    (∀ j < acc.length, DigAt u (slotT j) (acc.getD j 0)) ∧ c.lctx.ChainIn u 33 [] u

def ChainNext (c : QCtx) (s0 : MachineState) (j : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  if j ≤ 48 then c.ChainIn s0 j acc s else c.QOut s0 acc s

/-- The dispatch after chain `i`: after a quad's `D` 4, after chain 48 (`q48_done`) 5. -/
def xCost (i : Nat) : Nat := if i = 48 then 5 else if i % 4 = 3 then 4 else 0

theorem xCost_le (i : Nat) : xCost i ≤ 5 := by unfold xCost; split_ifs <;> omega

theorem end_next (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (i : Nat)
    (hi : i ≤ 48) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    ∃ u, Steps vimage s (xCost i) (xCost i) u ∧ c.ChainNext s0 (i + 1) acc u := by
  by_cases h48 : i = 48
  · subst h48
    have hs' := hs
    obtain ⟨⟨hR, hF, hS⟩, hlen, -, -⟩ := hs'
    obtain ⟨u, hst, hu, hreg, h15, hmem⟩ := c.q48d_step hc hk q48_parts.2.2.2 acc s hs
    refine ⟨u, by simpa [xCost] using hst, ?_⟩
    unfold ChainNext; rw [if_neg (by omega)]
    refine ⟨fun x hx h14 h15' => (hreg x h14 h15').trans (hR x hx), h15,
      fun A hA hn => (hmem _).trans (hF A hA hn), hlen, fun j hj => ?_, hu⟩
    exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩
  · by_cases h3 : i % 4 = 3
    · by_cases h47 : i = 47
      · subst h47
        have hx := c.blk_at 47 (by omega)
        unfold qblkCheck qxOK at hx
        simp only [Bool.and_eq_true] at hx
        have hrun : vrun (c.qX 47) 5 = some q48X := rOK_eq hx.2
        obtain ⟨u, hst, hu⟩ := c.x11_step hc hk (by have := c.qX_lt 47; omega) hrun acc s hs
        refine ⟨u, by simpa [xCost] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega)]; exact hu
      · obtain ⟨q, rfl⟩ : ∃ q, i = 4 * q + 3 := ⟨i / 4, by omega⟩
        have hx := c.blk_at (4 * q + 3) (by omega)
        rw [show (4 * q + 3) / 4 = q by omega] at hx
        unfold qblkCheck qxOK at hx
        simp only [Bool.and_eq_true] at hx
        rw [if_neg (by omega)] at hx
        have hrun := rOK_eq hx.2
        have hqx : c.qX (4 * q + 3) = qpcX q (c.dig (4 * q + 1)) (c.dig (4 * q + 2)) (c.dig (4 * q + 3)) := by
          unfold qX; rw [show (4 * q + 3) / 4 = q by omega]
        rw [← hqx] at hrun
        obtain ⟨u, hst, hu⟩ := c.x_step hc hk q (by omega) (by have := c.qX_lt (4 * q + 3); omega) hrun acc s hs
        refine ⟨u, by simpa [xCost, h48, show (4 * q + 3) % 4 = 3 by omega] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega), show 4 * q + 3 + 1 = 4 * q + 4 by ring]; exact hu
    · refine ⟨s, by simpa [xCost, h48, h3] using Steps.refl s, ?_⟩
      unfold ChainNext; rw [if_pos (by omega)]
      exact c.next_inline s0 i (by omega) h3 acc s hs

/-! ## The steps of a chain -/

/-- Steps `m .. 2` of chain `i` from the value `v`, with the block's pads. -/
def rest (c : QCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (3 - m)).foldlM
    (fun v step => shortHash (chainInputP 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : QCtx) (i m : Nat) (h : m ≤ 2) (v : Digest) :
    c.rest i m v =
      shortHash (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m + 1) := by
  unfold rest
  rw [show 3 - m = (3 - (m + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem rest_3 (c : QCtx) (i : Nat) (v : Digest) : c.rest i 3 v = pure v := rfl

theorem chainP_rest (c : QCtx) (i d : Nat) (v : Digest) :
    chainP 0 c.tree c.leaf i d (3 - d) (c.pad0 i) (c.pad1 i) v = c.rest i d v := rfl

/-- Cycles from just before step `m`'s `ecall` to the chain's last hash. -/
def preCost (m : Nat) : Nat := 8 + 9 * (2 - m) + (if m < 2 then 1 else 0)

theorem steps_good (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48) (acc : List Digest)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQ t N C Q A (K (acc ++ [v]))) :
    ∀ k m, m + k = 2 → c.dig i ≤ m → ∀ v s, c.PreHash s0 i acc m v s →
      Verify.GoodQ s (N + 3 * (3 - m) + 5) (C + preCost m + xCost i) Q (A + preCost m + xCost i)
        (Verify.ccM (c.rest i m v) (fun v => K (acc ++ [v]))) := by
  have hrc : ∀ m, m ≤ 2 → c.rungPc i m < 209920 := fun m hm => c.rungPc_lt i m hm
  have hx5 := xCost_le i
  intro k
  induction k with
  | zero =>
    intro m hm hd v s hs
    obtain rfl : m = 2 := by omega
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i 2 hi (le_refl _) hd acc v s hs
    rw [rest_succ c i 2 (le_refl _)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQ (writeHash s a) (N + xCost i) (C + xCost i) Q (A + xCost i)
        (Verify.ccM (c.rest i 3 (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      rw [rest_3, Verify.ccM_pure]
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ ((hpost a).2 rfl)
      exact Verify.GoodQ.steps' hu (hK _ _ hn) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQ.shortHash_bind (f := c.rest i 3) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [LCtx.chainInputP_pad]; exact hin) H
    rw [LCtx.chainInputP_pad, LCtx.chainInputP_blocks] at h3
    exact h3.mono (by omega) (by simp [preCost]; omega) (fun hq => ⟨hq, by simp [preCost]; omega⟩)
  | succ k ih =>
    intro m hm hd v s hs
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
    rw [rest_succ c i m (by omega)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQ (writeHash s a) (N + 3 * (3 - (m + 1)) + 5 + 2)
        (C + preCost (m + 1) + xCost i + (if m + 1 = 2 then 2 else 1)) Q
        (A + preCost (m + 1) + xCost i + (if m + 1 = 2 then 2 else 1))
        (Verify.ccM (c.rest i (m + 1) (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      have hrun := c.chk_rung i (m + 1) hi (by omega) (by omega) (fun _ _ => by omega)
      obtain ⟨u, hu, hp⟩ := c.rung_step hc hk i (m + 1) hi (by omega) (hrc _ (by omega)) hrun acc _ _
        ((hpost a).1 (by omega))
      have := ih (m + 1) (by omega) (by omega) _ _ hp
      exact Verify.GoodQ.steps' hu this (by split <;> omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQ.shortHash_bind (f := c.rest i (m + 1)) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [LCtx.chainInputP_pad]; exact hin) H
    rw [LCtx.chainInputP_pad, LCtx.chainInputP_blocks] at h3
    refine h3.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · unfold preCost
      by_cases h2 : m + 1 = 2
      · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h2, if_pos (by omega), if_pos (by omega)]; omega
    · unfold preCost
      by_cases h2 : m + 1 = 2
      · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h2, if_pos (by omega), if_pos (by omega)]; omega

/-! ## One chain -/

/-- Cycle cost of chain `i < 49` at digit `d`, including the dispatch after it. -/
def chainCost (i d : Nat) : Nat :=
  (if i % 4 = 0 ∨ i = 48 then (if d = 3 then 6 else 34 - 9 * d) else (if d = 3 then 5 else 33 - 9 * d - (if d = 2 then 1 else 0))) + xCost i

/-- **One chain of the quad code**: Core's `chainP` (width 2) with the block's pads and witness value. -/
theorem chain_good (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQ t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQ s (N + 40) (C + chainCost i (c.dig i)) Q (A + chainCost i (c.dig i))
      (Verify.ccM (chainP 0 c.tree c.leaf i (c.dig i) (3 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc ++ [v]))) := by
  have hx5 := xCost_le i
  have hdl := c.dig_lt4 i
  have hsp := c.startPc_lt i hi
  by_cases h3 : c.dig i = 3
  · -- the max-digit copy
    rw [h3, show 3 - 3 = 0 from rfl]
    have hspec : chainP 0 c.tree c.leaf i 3 0 (c.pad0 i) (c.pad1 i) (c.val i) = pure (c.val i) := rfl
    rw [hspec, Verify.ccM_pure]
    by_cases h0' : i % 4 = 0 ∨ i = 48
    · have hrun : vrun (c.startPc i) 7 = some (copyJ .x19 (offT i) (slotT i) (i / 4 == 0 && i != 48) (c.endPc i)) := by
        by_cases h48 : i = 48
        · subst h48
          have hs48 : c.startPc 48 = q48tabIdx + 24 := by unfold startPc; simp [h3]
          have he48 : c.endPc 48 = q48Done := by unfold endPc; simp
          rw [hs48, he48]; simpa using q48_parts.2.1
        · have := c.chk_copyJ i (by omega) (by omega) h3
          rw [show (i != 48) = true from bne_iff_ne.mpr h48, Bool.and_true]; exact this
      obtain ⟨t, hst, hE⟩ := c.copyJ_step hc hk h0 i hi (i / 4 == 0 && i != 48)
        (fun h => by simp at h; omega) (fun h => by simp at h; omega) hsp hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
      refine Verify.GoodQ.steps' hst (Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h3]; omega)
        (fun hq => ⟨hq, by unfold chainCost; simp [h0', h3]; omega⟩)
    · have hn0 : i % 4 ≠ 0 := fun h => h0' (Or.inl h)
      have hn48 : i ≠ 48 := fun h => h0' (Or.inr h)
      have hrun := c.chk_copyF i (by omega) hn0 h3
      have hend : c.startPc i + 5 = c.endPc i := by
        simp only [startPc, endPc, if_neg hn48, if_neg hn0]
        have e : 4 * (i / 4) + i % 4 = i := by omega
        by_cases h1 : i % 4 = 1
        · have e1 : c.dig (4 * (i / 4) + 1) = 3 := by rw [show 4 * (i / 4) + 1 = i by omega, h3]
          rw [if_pos h1, if_pos h1]; unfold qB qC qpcC; rw [e1]; rfl
        · by_cases h2 : i % 4 = 2
          · have e2 : c.dig (4 * (i / 4) + 2) = 3 := by rw [show 4 * (i / 4) + 2 = i by omega, h3]
            rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]; unfold qC qD qpcD; rw [e2]; rfl
          · have e3 : c.dig (4 * (i / 4) + 3) = 3 := by rw [show 4 * (i / 4) + 3 = i by omega, h3]
            rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]; unfold qD qX qpcX; rw [e3]; rfl
      obtain ⟨t, hst, hE⟩ := c.copyF_step hc hk h0 i hi (by omega) hsp hend hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
      refine Verify.GoodQ.steps' hst (Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h3]; omega)
        (fun hq => ⟨hq, by unfold chainCost; simp [h0', h3]; omega⟩)
  · -- a head and its rungs
    have hd : c.dig i < 3 := by omega
    rw [chainP_rest]
    have hsteps := c.steps_good hc hk h0 i hi acc K N C A Q hK (2 - c.dig i) (c.dig i) (by omega) (le_refl _)
    have hrp := c.rungPc_lt i (c.dig i) (by omega)
    by_cases h0' : i % 4 = 0 ∨ i = 48
    · have hrun1 : vrun (c.startPc i) 7 =
          some (headJ .x19 (offT i) (i / 4 == 0 && i != 48) (c.rungPc i (c.dig i))) := by
        by_cases h48 : i = 48
        · subst h48
          have := q48_parts.1 (c.dig 48) hd
          have hst48 : c.startPc 48 = q48tabIdx + 8 * c.dig 48 := by unfold startPc; simp
          have hrp48 : c.rungPc 48 (c.dig 48) = q48R0 + 2 * c.dig 48 := by unfold rungPc; simp
          rw [hst48, hrp48]; simpa using this
        · have := c.chk_headJ i (by omega) (by omega) hd
          rw [show (i != 48) = true from bne_iff_ne.mpr h48, Bool.and_true]; exact this
      have hrun2 := c.chk_rung i (c.dig i) hi (le_refl _) (by omega) (fun h h' => absurd h0' (by omega))
      obtain ⟨t, hst, hP⟩ := c.headJ_step hc hk h0 i hi hd (i / 4 == 0 && i != 48)
        (fun h => by simp at h; omega) (fun h => by simp at h; omega) hsp hrp hrun1 hrun2 acc s hs
      refine Verify.GoodQ.steps' hst (hsteps _ _ hP) (by split <;> omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_pos h0', if_neg h3]
        by_cases h2 : c.dig i = 2
        · rw [if_pos h2, h2]; norm_num; omega
        · rw [if_neg h2, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_pos h0', if_neg h3]
        by_cases h2 : c.dig i = 2
        · rw [if_pos h2, h2]; norm_num; omega
        · rw [if_neg h2, if_pos (by omega)]; omega
    · have hn0 : i % 4 ≠ 0 := fun h => h0' (Or.inl h)
      have hrun := c.chk_headR i (by omega) hn0 hd
      obtain ⟨t, hst, hP⟩ := c.headR_step hc hk h0 i hi (by omega) hd hsp
        (c.rungPc_inline i (by omega) hn0) hrun acc s hs
      refine Verify.GoodQ.steps' hst (hsteps _ _ hP) (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_neg h0', if_neg h3]
        by_cases h2 : c.dig i = 2
        · rw [if_pos h2, h2]; norm_num; omega
        · rw [if_neg h2, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_neg h0', if_neg h3]
        by_cases h2 : c.dig i = 2
        · rw [if_pos h2, h2]; norm_num; omega
        · rw [if_neg h2, if_pos (by omega)]; omega

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace QCtx

/-! ## All chains of the quad code -/

/-- Core's chain `i < 49` (width 2, the block's pads and witness value), appended to the ends so far. -/
def chainF (c : QCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (3 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends ++ [v])

/-- The cycles of the chains `i .. i + k - 1`. -/
def chainsCost (c : QCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- **The chains `i .. 48`** of the quad code, up to `q48_done`'s dispatch into the lower code. -/
theorem chains_good (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.QOut s0 ends t → Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, i + k = 49 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQ s (N + 40 * k) (C + c.chainsCost i k) Q (A + c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ h; omega
  | succ k ih =>
    intro i hik _ acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, Verify.ccM_bind]
    have := c.chain_good hc hk h0 i (by omega) acc
      (fun ends => Verify.ccM ((List.range' (i + 1) k).foldlM c.chainF ends) K)
      (N + 40 * k) (C + c.chainsCost (i + 1) k) (A + c.chainsCost (i + 1) k) Q
      (fun v t ht => by
        by_cases hk0 : k = 0
        · subst hk0
          have ht' : c.QOut s0 (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_neg (by omega)] at ht
          simpa [chainsCost] using hK _ t ht'
        · have ht' : c.ChainIn s0 (i + 1) (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_pos (by omega)] at ht
          exact ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht') s hs
    refine this.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace QCtx

/-! ## The whole top chain phase -/

/-- The memory the top chain phase writes: the leaf-pk area and the top's chain blocks (chains 57 .. 0). -/
def TopW (c : QCtx) (A : Nat) : Prop := (0x200 ≤ A ∧ A < 0x5D0) ∨ (c.S6 - 960 ≤ A ∧ A < c.blk 0 + 80)

/-- After the top chain phase's return (`ctab[8] = jr ra`): the 58 ends in the top leaf-pk slots, registers outside
`chainRegs`, `a5` as at the start, `a5` = the `ttab` window, memory outside `TopW` as at the start. -/
def TopOut (c : QCtx) (s0 : MachineState) (ends : List Digest) (t : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → t.getReg x = s0.getReg x) ∧ t.getReg .x15 = BitVec.ofNat 64 0x6e000 ∧
    Frame s0 t c.TopW ∧ ends.length = 58 ∧ (∀ j < 58, DigAt t (slotT j) (ends.getD j 0)) ∧ t.pc = pcOf c.ret

/-- The top chain phase as a program: the quad code's 49 chains, then the lower code's 9 (the top's 49 .. 57). -/
def topP (c : QCtx) : M (List Digest) := do
  let e1 ← (List.range' 0 49).foldlM c.chainF []
  let e2 ← (List.range' 33 9).foldlM c.lctx.chainF []
  pure (e1 ++ e2)

/-- The cycles of the top chain phase (the quad code, the lower code's chains 33 .. 41, the return). -/
def topCost (c : QCtx) : Nat := c.chainsCost 0 49 + c.lctx.chainsCost 33 9 + 1

/-- The geometry of the top: the quad code's blocks sit right above the lower code's (`s3 = s6 + 704`). -/
def TopOk (c : QCtx) : Prop := c.ok ∧ c.lctx.ok ∧ c.S3 = c.S6 + 704

theorem lctx_i0 (c : QCtx) : c.lctx.i0 = 33 := rfl
theorem lctx_slot0 (c : QCtx) : slotL c.lctx.i0 = 1312 := by rw [lctx_i0]; unfold slotL; simp
theorem lctx_blk (c : QCtx) (i : Nat) : c.lctx.blk i = c.S6 - 1024 + 64 * (42 - i) := rfl
theorem lctx_S6 (c : QCtx) : c.lctx.S6 = c.S6 := rfl

theorem lctx_Wr42 (c : QCtx) (A : Nat) (h : c.lctx.Wr 42 A) :
    (1312 ≤ A ∧ A < 0x5D0) ∨ (c.S6 - 1024 + 64 ≤ A ∧ A < c.S6 - 1024 + 64 * 9 + 80) := by
  unfold LCtx.Wr at h; rw [lctx_slot0, lctx_S6, lctx_blk, lctx_i0] at h
  rcases h with h | h
  · exact Or.inl h
  · right; constructor <;> omega

/-- **The top chain phase**: from the quad code's `ChainIn 0` to the return, Core's 58 chains. -/
theorem top_good (c : QCtx) (hc : c.TopOk) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hl0 : c.lctx.Orig0 s0) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.TopOut s0 ends t → Verify.GoodQ t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N + 2321) (C + c.topCost) Q (A + c.topCost) (Verify.ccM c.topP K) := by
  obtain ⟨hq, hl, h36⟩ := hc
  unfold topP
  rw [Verify.ccM_bind]
  have H := c.chains_good hq hk h0
    (fun e1 => Verify.ccM ((List.range' 33 9).foldlM c.lctx.chainF [] >>= fun e2 => pure (e1 ++ e2)) K)
    (N + 1 + 40 * 9) (C + 1 + c.lctx.chainsCost 33 9) (A + 1 + c.lctx.chainsCost 33 9) Q
    (fun e1 u hu => by
      obtain ⟨hRu, h15u, hFu, hlen1, hSu, hIn⟩ := hu
      have hku := c.lctx_known hk hRu h15u
      have hb0 : c.lctx.Orig0 u := by
        intro i hi1 hi2 k hk8
        have hb := c.lctx.blk_props hl i hi2
        unfold OrigW
        rw [hFu _ (by omega) (by
          intro hw
          have := hq.2.2.2.1
          unfold Wr at hw; unfold LCtx.blk lctx at *; simp only at *
          unfold blk at hw
          omega)]
        exact hl0 i hi1 hi2 k hk8
      rw [Verify.ccM_bind]
      have HL := c.lctx.chains_good hl hku hb0 (fun h => absurd h (by simp [lctx]))
        (fun e2 => Verify.ccM (pure (e1 ++ e2)) K) (N + 1) (C + 1) (A + 1) Q
        (fun e2 t ht => by
          rw [Verify.ccM_pure]
          refine c.lctx.ck8_good hl hku rfl (K (e1 ++ e2)) N C A Q e2 (fun t' ht' => hK _ t' ?_) t ht
          obtain ⟨⟨hR', hF', hS'⟩, hlen2, hpc'⟩ := ht'
          have hl2 : e2.length = 9 := by simpa [lctx] using hlen2
          refine ⟨fun x hx h15 => ?_, ?_, ?_, by simp [hlen1, hl2], fun j hj => ?_, hpc'⟩
          · by_cases h14 : x = .x14
            · subst h14; exact absurd (by decide) hx
            · exact (hR' x hx).trans (hRu x hx h14 h15)
          · rw [hR' .x15 (by decide)]; exact h15u
          · refine (hFu.trans hF').mono ?_
            intro A _ h
            have := hq.2.2.2.1
            have hs6 := hl.2.2.2.2.1
            rw [lctx_S6] at hs6
            rcases h with h | h
            · unfold Wr at h; unfold TopW; unfold blk at *; omega
            · have h' := c.lctx_Wr42 A h; unfold TopW; unfold blk; omega
          · by_cases hj1 : j < 49
            · have hd := hSu j (by omega)
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
              have hsj := slotT_props j (by omega)
              refine hd.frame hF' (by omega) ?_ ?_
              · intro hw; have h' := c.lctx_Wr42 _ hw
                have := hl.2.2.2.2.1; rw [lctx_S6] at this; omega
              · intro hw; have h' := c.lctx_Wr42 _ hw
                have := hl.2.2.2.2.1; rw [lctx_S6] at this; omega
            · have hd := hS' (j - 49) (by omega)
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen1,
                ← List.getD_eq_getElem?_getD]
              have e : slotL (c.lctx.i0 + (j - 49)) = slotT j := by
                unfold slotL slotT lctx; simp only; split_ifs <;> omega
              rwa [e] at hd)
        9 33 (by omega) (le_refl _) [] u hIn
      exact HL.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
    49 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold topCost; omega
  · unfold topCost; omega

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

/-! ## The top chain phase as Core's `mapM` -/

theorem mapM_congr' {α β : Type} {f g : α → M β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp), mapM_congr' l (fun y hy => h y (by simp [hy]))]

theorem finRange_mapM {β : Type} (n : Nat) (g : Nat → M β) :
    (List.finRange n).mapM (fun i => g i.val) = (List.range n).mapM g := by
  have e : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  rw [← e, List.mapM_map]; rfl

/-- A fold that appends one result per index is the `mapM` of the indices. -/
theorem foldlM_app_mapM (f : Nat → M Digest) : ∀ (n a : Nat) (acc : List Digest),
    (List.range' a n).foldlM (fun e i => do let v ← f i; pure (e ++ [v])) acc =
      (fun l => acc ++ l) <$> (List.range' a n).mapM f
  | 0, a, acc => by simp
  | n + 1, a, acc => by
    rw [List.range'_succ, List.foldlM_cons, List.mapM_cons]
    simp only [bind_assoc, pure_bind, foldlM_app_mapM f n (a + 1), map_bind, bind_map_left, map_pure]
    congr 1; funext v
    rw [← bind_pure_comp]
    congr 1; funext l; simp

theorem four_mul_div (Y k : Nat) : 4 * Y / 2 ^ (k + 2) = Y / 2 ^ k := by
  rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by norm_num, Nat.mul_comm (2 ^ k) 4, Nat.mul_div_mul_left _ _ (by norm_num)]

theorem dataDigits0_getD (value : Digest) (j : Nat) (hj : j < 58) :
    (dataDigits 0 value).getD j 0 =
      value.toNat / 2 ^ (if j < 49 then 2 * j else 98 + 3 * (j - 49)) % 2 ^ width 0 j := by
  unfold dataDigits
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa [dataCount] using hj)]
  simp

namespace QCtx

/-- Core's chain `i` of the top layer with the witness's pads and value. -/
def coreChain (c : QCtx) (D : List Nat) (i : Nat) : M Digest :=
  chainP 0 c.tree c.leaf i (D.getD i 0) (2 ^ width 0 i - 1 - D.getD i 0) (wchainPads c.w 0 i).1
    (wchainPads c.w 0 i).2 (wvalue c.w 0 i)

/-- The quad code's digits and blocks are Core's (`a6 = v0`, `a7 = v1 << 2`, `s3`, `s6` of the image). -/
structure TopFit (c : QCtx) (value : Digest) : Prop where
  d0 : c.d0.toNat = value.toNat % 2 ^ 64
  d1 : c.d1.toNat = 4 * (value.toNat / 2 ^ 64)
  range : value.toNat / 2 ^ 64 < 2 ^ 61
  s3 : c.S3 = 15768
  s6 : c.S6 = 15064

theorem fit_dig (c : QCtx) {value : Digest} (h : c.TopFit value) (i : Nat) (hi : i < 49) :
    c.dig i = (dataDigits 0 value).getD i 0 := by
  rw [dataDigits0_getD value i (by omega), if_pos hi, show width 0 i = 2 by simp [width, hi]]
  unfold dig
  by_cases h32 : i < 32
  · rw [if_pos h32, h.d0, show (4 : Nat) ^ i = 2 ^ (2 * i) by rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul],
      show (4 : Nat) = 2 ^ 2 by rfl]
    have hV : value.toNat = value.toNat % 2 ^ 64 + 2 ^ 64 * (value.toNat / 2 ^ 64) := (Nat.mod_add_div _ _).symm
    conv_rhs => rw [hV]
    exact (div_mod_add_pow _ _ _ _ _ (by omega)).symm
  · rw [if_neg h32, h.d1, show (4 : Nat) ^ (i - 31) = 2 ^ (2 * (i - 32) + 2) by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]; congr 1; omega, four_mul_div, Nat.div_div_eq_div_mul,
      ← Nat.pow_add, show 64 + 2 * (i - 32) = 2 * i by omega]
    rfl

theorem fit_ldig (c : QCtx) {value : Digest} (h : c.TopFit value) (m : Nat) (hm : m < 9) :
    c.lctx.dig (33 + m) = (dataDigits 0 value).getD (49 + m) 0 := by
  rw [dataDigits0_getD value _ (by omega), if_neg (by omega), show width 0 (49 + m) = 3 by simp [width]]
  unfold LCtx.dig
  rw [if_neg (by omega), if_pos (by omega)]
  show c.d1.toNat / 8 ^ (33 + m - 21) % 8 = _
  rw [h.d1, show (8 : Nat) ^ (33 + m - 21) = 2 ^ ((34 + 3 * m) + 2) by
      rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul]; congr 1; omega, four_mul_div, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, show 64 + (34 + 3 * m) = 98 + 3 * (49 + m - 49) by omega]
  rfl

theorem fit_chain (c : QCtx) {value : Digest} (h : c.TopFit value) (i : Nat) (hi : i < 49) :
    chainP 0 c.tree c.leaf i (c.dig i) (3 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i) =
      c.coreChain (dataDigits 0 value) i := by
  unfold coreChain
  rw [← c.fit_dig h i hi, show width 0 i = 2 by simp [width, hi]]
  have e : c.blk i - 0x800 = chainBlock 0 i := by
    unfold blk chainBlock; rw [h.s3]; simp [layerBase, height, chainCount]; omega
  unfold pad0 pad1 val wchainPads wvalue
  rw [e]
  rfl

theorem fit_lchain (c : QCtx) {value : Digest} (h : c.TopFit value) (m : Nat) (hm : m < 9) :
    chainP c.lctx.lay c.lctx.tree c.lctx.leaf (33 + m + c.lctx.koff) (c.lctx.dig (33 + m)) (7 - c.lctx.dig (33 + m))
      (c.lctx.pad0 (33 + m)) (c.lctx.pad1 (33 + m)) (c.lctx.val (33 + m)) =
      c.coreChain (dataDigits 0 value) (49 + m) := by
  unfold coreChain
  rw [← c.fit_ldig h m hm, show width 0 (49 + m) = 3 by simp [width], show 33 + m + c.lctx.koff = 49 + m by
    simp [lctx]; omega]
  have e : c.lctx.blk (33 + m) - 0x800 = chainBlock 0 (49 + m) := by
    unfold LCtx.blk chainBlock; simp only [lctx]; rw [h.s6]; simp [layerBase, height, chainCount]; omega
  unfold LCtx.pad0 LCtx.pad1 LCtx.val wchainPads wvalue
  rw [e]
  rfl

/-- **The top chain phase is Core's**: `topP` = the 58 chains of `layerP 0` (`mapM` over `finRange 58`) with the
digits of `dataDigits 0 value`. -/
theorem topP_eq (c : QCtx) {value : Digest} (h : c.TopFit value) :
    c.topP = (List.finRange 58).mapM fun i => c.coreChain (dataDigits 0 value) i.val := by
  rw [finRange_mapM, List.range_eq_range', show (58 : Nat) = 49 + 9 from rfl,
    (List.range'_append_1 (s := 0) (m := 49) (n := 9)).symm, List.mapM_append]
  · unfold topP
    have hQ : (List.range' 0 49).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 49).mapM
        (fun i => chainP 0 c.tree c.leaf i (c.dig i) (3 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)) :=
      foldlM_app_mapM _ 49 0 []
    have hL : (List.range' 33 9).foldlM c.lctx.chainF [] = (fun l => [] ++ l) <$> (List.range' 33 9).mapM
        (fun i => chainP c.lctx.lay c.lctx.tree c.lctx.leaf (i + c.lctx.koff) (c.lctx.dig i) (7 - c.lctx.dig i)
          (c.lctx.pad0 i) (c.lctx.pad1 i) (c.lctx.val i)) :=
      foldlM_app_mapM _ 9 33 []
    rw [hQ, hL, mapM_congr' (List.range' 0 49) (fun i hi => c.fit_chain h i (by
      have := List.mem_range'_1.mp hi; omega))]
    have hm : (List.range' (0 + 49) 9) = (List.range' 33 9).map (· + 16) := by
      decide
    rw [hm, List.mapM_map, mapM_congr' (List.range' 33 9) (g := fun i => c.coreChain (dataDigits 0 value) (i + 16))
      (fun i hi => by
        have := List.mem_range'_1.mp hi
        obtain ⟨m, rfl⟩ : ∃ m, i = 33 + m := ⟨i - 33, by omega⟩
        rw [show 33 + m + 16 = 49 + m by omega]; exact c.fit_lchain h m (by omega))]
    simp only [List.nil_append, map_bind, bind_map_left, Function.comp_def, id_map']

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace QCtx

/-! ## The cost of the top chain phase -/

/-- The digit-independent cost of chain `i < 49` (as if no digit were maximal). -/
def cbase (i : Nat) : Nat := (if i % 4 = 0 ∨ i = 48 then 34 else 33) + xCost i

/-- The saving of a maximal digit (the copy instead of a head and the last rung). -/
def zc (i d : Nat) : Nat := if d = 3 then 1 else if i % 4 ≠ 0 ∧ d = 2 then 1 else 0

theorem chainCost_add (i d : Nat) (hd : d < 4) : chainCost i d + 9 * d + zc i d = cbase i := by
  unfold chainCost zc cbase
  split_ifs <;> omega

theorem chainsCost_add (c : QCtx) : ∀ k i,
    c.chainsCost i k + 9 * ((List.range' i k).map c.dig).sum + ((List.range' i k).map fun j => zc j (c.dig j)).sum =
      ((List.range' i k).map cbase).sum := by
  intro k
  induction k with
  | zero => intro i; simp [chainsCost]
  | succ k ih =>
    intro i
    have h := ih (i + 1)
    have := chainCost_add i (c.dig i) (c.dig_lt4 i)
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons] at h ⊢
    omega

theorem cbase_sum : ((List.range' 0 49).map cbase).sum = 1683 := by decide

theorem lchainsCost_add (c : QCtx) : ∀ k i, i + k ≤ 42 →
    c.lctx.chainsCost i k + 9 * ((List.range' i k).map c.lctx.dig).sum +
      ((List.range' i k).map fun j => LCtx.zc j (c.lctx.dig j)).sum = ((List.range' i k).map LCtx.cbase).sum := by
  intro k
  induction k with
  | zero => intro i _; simp [LCtx.chainsCost]
  | succ k ih =>
    intro i hik
    have h := ih (i + 1) (by omega)
    have := LCtx.chainCost_add i (c.lctx.dig i) (c.lctx.dig_lt8 i (by omega))
    simp only [LCtx.chainsCost, List.range'_succ, List.map_cons, List.sum_cons] at h ⊢
    omega

/-- The weighted number of maximal digits of the top layer (the quad code's and the lower code's). -/
def topZ (c : QCtx) : Nat := ((List.range' 0 49).map fun j => zc j (c.dig j)).sum + c.lctx.zSum 33 9

/-- The digit sum of the top layer as the machine sees it. -/
def topS (c : QCtx) : Nat := ((List.range' 0 49).map c.dig).sum + ((List.range' 33 9).map c.lctx.dig).sum

theorem topCost_add (c : QCtx) : c.topCost + 9 * c.topS + c.topZ = 2319 := by
  have h1 := c.chainsCost_add 49 0
  have h2 := c.lchainsCost_add 9 33 (by omega)
  rw [cbase_sum] at h1
  rw [LCtx.cbase_sum_top] at h2
  unfold topCost topS topZ LCtx.zSum
  omega

theorem sum_range'_eq (f g : Nat → Nat) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → f i = g i) :
    ((List.range' a n).map f).sum = ((List.range' a n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range'_1.mp hi
  exact h i this.1 this.2

/-- The machine's digit sum is Core's. -/
theorem topS_eq (c : QCtx) {value : Digest} (h : c.TopFit value) : c.topS = (dataDigits 0 value).sum := by
  have hD : dataDigits 0 value = (List.range 58).map fun i => (dataDigits 0 value).getD i 0 := by
    apply List.ext_getElem (by simp [dataDigits, dataCount])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have hA : ((List.range' 0 49).map c.dig).sum =
      ((List.range' 0 49).map fun i => (dataDigits 0 value).getD i 0).sum :=
    sum_range'_eq _ _ 0 49 (fun i _ hi => c.fit_dig h i (by omega))
  have hB : ((List.range' 33 9).map c.lctx.dig).sum =
      ((List.range' 49 9).map fun i => (dataDigits 0 value).getD i 0).sum := by
    have hm : List.range' 49 9 = (List.range' 33 9).map (· + 16) := by decide
    rw [hm, List.map_map]
    exact sum_range'_eq _ _ 33 9 (fun i h1 h2 => by
      obtain ⟨m, rfl⟩ : ∃ m, i = 33 + m := ⟨i - 33, by omega⟩
      simp only [Function.comp_apply]
      rw [c.fit_ldig h m (by omega), show 33 + m + 16 = 49 + m by omega])
  have hC : ((List.range 58).map fun i => (dataDigits 0 value).getD i 0).sum =
      ((List.range' 0 49).map fun i => (dataDigits 0 value).getD i 0).sum +
        ((List.range' 49 9).map fun i => (dataDigits 0 value).getD i 0).sum := by
    rw [List.range_eq_range', show (58 : Nat) = 49 + 9 from rfl,
      (List.range'_append_1 (s := 0) (m := 49) (n := 9)).symm, List.map_append, List.sum_append]
  unfold topS
  rw [hA, hB]
  conv_rhs => rw [hD]
  rw [hC]

/-- **The cost of an accepting top chain phase**: `1185 - Z` (the 58 digits sum to `125`). -/
theorem topCost_accept (c : QCtx) {value : Digest} (h : c.TopFit value) (hsum : (dataDigits 0 value).sum = 125) :
    c.topCost + c.topZ = 1194 := by
  have := c.topCost_add
  rw [c.topS_eq h, hsum] at this
  omega

/-- Below the new savings threshold, top digits cannot sum to the required 125. -/
def noSave (i : Nat) : Nat := if i % 4 = 0 then 2 else 1

theorem digit_le_noSave (i d : Nat) (hd : d < 4) : d ≤ noSave i + 2 * zc i d := by
  unfold noSave zc
  split_ifs <;> omega

theorem quadSum_le (c : QCtx) : ∀ n i,
    ((List.range' i n).map c.dig).sum ≤ ((List.range' i n).map noSave).sum +
      2 * ((List.range' i n).map fun j => zc j (c.dig j)).sum := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    have h := ih (i + 1)
    have h1 := digit_le_noSave i (c.dig i) (c.dig_lt4 i)
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega

theorem triSum_le (c : QCtx) : ∀ n i, i + n ≤ 42 →
    ((List.range' i n).map c.lctx.dig).sum ≤ 6 * n +
      2 * ((List.range' i n).map fun j => LCtx.zc j (c.lctx.dig j)).sum := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ n ih =>
    intro i hi
    have h := ih (i + 1) (by omega)
    have hd := c.lctx.dig_lt8 i (by omega)
    have h1 : c.lctx.dig i ≤ 6 + 2 * LCtx.zc i (c.lctx.dig i) := by
      unfold LCtx.zc
      split_ifs <;> omega
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega

theorem topZ_ge_five (c : QCtx) {value : Digest} (h : c.TopFit value)
    (hsum : (dataDigits 0 value).sum = 125) : 5 ≤ c.topZ := by
  have hq := c.quadSum_le 49 0
  have hl := c.triSum_le 9 33 (by decide)
  have hb : ((List.range' 0 49).map noSave).sum = 62 := by decide
  rw [hb] at hq
  have ht : c.topS = 125 := by rw [c.topS_eq h, hsum]
  unfold topS at ht
  unfold topZ LCtx.zSum
  omega

end QCtx

end SigGolfCandidate.T3M
